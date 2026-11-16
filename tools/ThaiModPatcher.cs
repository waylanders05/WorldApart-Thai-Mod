// World Apart Thai mod - rebuilds a modded bundle from the player's ORIGINAL bundle + a .wtp patch.
// Loaded by install.ps1 with Add-Type (Windows PowerShell 5.1 / .NET Framework, C# 5 syntax only).
//
// Steps: read original A1 bundle -> LZ4-decode its UnityFS data stream -> apply patch controls
// (copy ranges of the original stream + insert patch payload) -> check sha256 of the new stream
// -> LZ4-encode it again in 128 KiB blocks -> write A1 header + UnityFS header + blocks.
// The output is deterministic, so install.ps1 can verify it against a known sha256.
using System;
using System.Collections.Generic;
using System.IO;
using System.IO.Compression;
using System.Security.Cryptography;
using System.Text;

public static class ThaiModPatcher
{
    const int Chunk = 0x20000;

    static uint BE32(byte[] b, int p) { return (uint)(b[p] << 24 | b[p + 1] << 16 | b[p + 2] << 8 | b[p + 3]); }
    static long BE64(byte[] b, int p) { return ((long)BE32(b, p) << 32) | BE32(b, p + 4); }
    static int Align16(int p) { return (p + 15) / 16 * 16; }

    static void PutBE32(Stream s, uint v) { s.WriteByte((byte)(v >> 24)); s.WriteByte((byte)(v >> 16)); s.WriteByte((byte)(v >> 8)); s.WriteByte((byte)v); }
    static void PutBE64(Stream s, long v) { PutBE32(s, (uint)(v >> 32)); PutBE32(s, (uint)v); }
    static void PutLE32(Stream s, uint v) { s.WriteByte((byte)v); s.WriteByte((byte)(v >> 8)); s.WriteByte((byte)(v >> 16)); s.WriteByte((byte)(v >> 24)); }

    static string CStr(byte[] b, ref int p)
    {
        int e = Array.IndexOf(b, (byte)0, p);
        string s = Encoding.UTF8.GetString(b, p, e - p);
        p = e + 1;
        return s;
    }

    // ---------------------------------------------------------------- LZ4 block format
    public static void Lz4Decode(byte[] src, int sp, int slen, byte[] dst, int dp, int dlen)
    {
        int send = sp + slen, d = dp, dend = dp + dlen;
        while (sp < send)
        {
            int token = src[sp++];
            int lit = token >> 4;
            if (lit == 15) { int b; do { b = src[sp++]; lit += b; } while (b == 255); }
            if (d + lit > dend) throw new InvalidDataException("LZ4: literal overrun");
            Buffer.BlockCopy(src, sp, dst, d, lit); sp += lit; d += lit;
            if (sp >= send) break;
            int off = src[sp] | (src[sp + 1] << 8); sp += 2;
            int ml = token & 15;
            if (ml == 15) { int b; do { b = src[sp++]; ml += b; } while (b == 255); }
            ml += 4;
            int m = d - off;
            if (off == 0 || m < dp || d + ml > dend) throw new InvalidDataException("LZ4: bad match");
            if (off >= ml) { Buffer.BlockCopy(dst, m, dst, d, ml); d += ml; }
            else { for (int k = 0; k < ml; k++) dst[d++] = dst[m++]; }
        }
        if (d != dend) throw new InvalidDataException("LZ4: size mismatch");
    }

    const int HashLog = 16;
    static readonly int[] HashTable = new int[1 << HashLog];

    static uint Read32(byte[] b, int p) { return (uint)(b[p] | b[p + 1] << 8 | b[p + 2] << 16 | b[p + 3] << 24); }

    static void PutLen(byte[] dst, ref int op, int r)
    {
        while (r >= 255) { dst[op++] = 255; r -= 255; }
        dst[op++] = (byte)r;
    }

    // Greedy LZ4 compressor. dst needs slen + slen/255 + 16 bytes. Returns compressed length.
    // Matches never reach before sp (blocks must decode on their own) and the block ends with
    // >= 5 literal bytes, the last match starting >= 12 bytes before the end (LZ4 spec rules).
    public static int Lz4Encode(byte[] src, int sp, int slen, byte[] dst, int dp)
    {
        // cleared every call: output must depend only on this block (deterministic sha256)
        Array.Clear(HashTable, 0, HashTable.Length);
        int send = sp + slen, mflimit = send - 12, matchlimit = send - 5;
        int anchor = sp, ip = sp, op = dp;
        while (ip < mflimit)
        {
            uint seq = Read32(src, ip);
            int h = (int)((seq * 2654435761u) >> (32 - HashLog));
            int r = HashTable[h] - 1;
            HashTable[h] = ip + 1;
            if (r < sp || ip - r > 65535 || Read32(src, r) != seq) { ip++; continue; }
            int ml = 4;
            while (ip + ml < matchlimit && src[r + ml] == src[ip + ml]) ml++;
            int lit = ip - anchor;
            int tokenPos = op++;
            int token = (lit >= 15 ? 15 : lit) << 4;
            if (lit >= 15) PutLen(dst, ref op, lit - 15);
            Buffer.BlockCopy(src, anchor, dst, op, lit); op += lit;
            int off = ip - r;
            dst[op++] = (byte)off; dst[op++] = (byte)(off >> 8);
            int mc = ml - 4;
            token |= mc >= 15 ? 15 : mc;
            if (mc >= 15) PutLen(dst, ref op, mc - 15);
            dst[tokenPos] = (byte)token;
            ip += ml;
            anchor = ip;
        }
        int last = send - anchor;
        int tp = op++;
        dst[tp] = (byte)((last >= 15 ? 15 : last) << 4);
        if (last >= 15) PutLen(dst, ref op, last - 15);
        Buffer.BlockCopy(src, anchor, dst, op, last); op += last;
        return op - dp;
    }

    // ---------------------------------------------------------------- UnityFS
    class Bundle
    {
        public byte[] A1Header;
        public uint Version, Flags;
        public string UnityVer, UnityRev;
        public byte[] Hash;
        public byte[] Data;
    }

    static Bundle ReadBundle(string path)
    {
        byte[] raw = File.ReadAllBytes(path);
        if (Encoding.ASCII.GetString(raw, 0, 8) != "A1BNDLHP") throw new InvalidDataException("not an A1 bundle");
        int b0 = 24;  // UnityFS payload starts after the 24-byte A1 header; offsets below are payload-relative
        Bundle bd = new Bundle();
        bd.A1Header = new byte[24];
        Buffer.BlockCopy(raw, 0, bd.A1Header, 0, 24);
        if (Encoding.ASCII.GetString(raw, b0, 8) != "UnityFS\0") throw new InvalidDataException("not UnityFS");
        int p = 8;
        bd.Version = BE32(raw, b0 + p); p += 4;
        int q = b0 + p;
        bd.UnityVer = CStr(raw, ref q);
        bd.UnityRev = CStr(raw, ref q);
        p = q - b0;
        int csize = (int)BE32(raw, b0 + p + 8), usize = (int)BE32(raw, b0 + p + 12);
        bd.Flags = BE32(raw, b0 + p + 16);
        p += 20;
        if (bd.Version >= 7) p = Align16(p);
        int infoAt, dataStart;
        if ((bd.Flags & 0x80) != 0) { infoAt = raw.Length - b0 - csize; dataStart = p; }
        else { infoAt = p; dataStart = p + csize; }
        byte[] info = new byte[usize];
        int ic = (int)(bd.Flags & 0x3F);
        if (ic == 0) Buffer.BlockCopy(raw, b0 + infoAt, info, 0, usize);
        else if (ic == 2 || ic == 3) Lz4Decode(raw, b0 + infoAt, csize, info, 0, usize);
        else throw new InvalidDataException("unsupported block-info compression " + ic);
        if ((bd.Flags & 0x200) != 0) dataStart = Align16(dataStart);
        bd.Hash = new byte[16];
        Buffer.BlockCopy(info, 0, bd.Hash, 0, 16);
        int ip = 16;
        int nb = (int)BE32(info, ip); ip += 4;
        long total = 0;
        int[] us = new int[nb], cs = new int[nb], fl = new int[nb];
        for (int i = 0; i < nb; i++)
        {
            us[i] = (int)BE32(info, ip); cs[i] = (int)BE32(info, ip + 4); fl[i] = (info[ip + 8] << 8) | info[ip + 9];
            ip += 10; total += us[i];
        }
        bd.Data = new byte[total];
        int src = b0 + dataStart, dst = 0;
        for (int i = 0; i < nb; i++)
        {
            int c = fl[i] & 0x3F;
            if (c == 0) Buffer.BlockCopy(raw, src, bd.Data, dst, us[i]);
            else if (c == 2 || c == 3) Lz4Decode(raw, src, cs[i], bd.Data, dst, us[i]);
            else throw new InvalidDataException("unsupported block compression " + c);
            src += cs[i]; dst += us[i];
        }
        return bd;
    }

    // ---------------------------------------------------------------- patch
    static ulong UVarint(byte[] b, ref int p)
    {
        ulong v = 0; int shift = 0;
        while (true)
        {
            byte x = b[p++];
            v |= (ulong)(x & 0x7F) << shift;
            if (x < 0x80) return v;
            shift += 7;
        }
    }

    public static void Build(string origPath, string patchPath, string outPath)
    {
        Bundle bd = ReadBundle(origPath);
        byte[] body;
        using (FileStream fs = File.OpenRead(patchPath))
        {
            byte[] magic = new byte[8];
            if (fs.Read(magic, 0, 8) != 8 || Encoding.ASCII.GetString(magic) != "WATHPAT1") throw new InvalidDataException("not a WATHPAT1 patch");
            using (DeflateStream ds = new DeflateStream(fs, CompressionMode.Decompress))
            using (MemoryStream ms = new MemoryStream())
            {
                ds.CopyTo(ms);
                body = ms.ToArray();
            }
        }
        int p = 0;
        if (BitConverter.ToUInt32(body, p) != 1) throw new InvalidDataException("unknown patch version");
        long newLen = BitConverter.ToInt64(body, p + 4);
        byte[] want = new byte[32];
        Buffer.BlockCopy(body, p + 12, want, 0, 32);
        p += 44;
        int nn = BitConverter.ToInt32(body, p); p += 4;
        long[] noff = new long[nn], nsz = new long[nn]; uint[] nfl = new uint[nn]; string[] nname = new string[nn];
        for (int i = 0; i < nn; i++)
        {
            noff[i] = BitConverter.ToInt64(body, p); nsz[i] = BitConverter.ToInt64(body, p + 8);
            nfl[i] = BitConverter.ToUInt32(body, p + 16); int ln = BitConverter.ToUInt16(body, p + 20);
            nname[i] = Encoding.UTF8.GetString(body, p + 22, ln); p += 22 + ln;
        }
        int nc = BitConverter.ToInt32(body, p); p += 4;
        int[] add = new int[nc], cp = new int[nc]; long[] seek = new long[nc];
        for (int i = 0; i < nc; i++)
        {
            add[i] = (int)UVarint(body, ref p); cp[i] = (int)UVarint(body, ref p);
            ulong z = UVarint(body, ref p);
            seek[i] = (z & 1) == 0 ? (long)(z >> 1) : -(long)((z + 1) >> 1);
        }
        long plen = BitConverter.ToInt64(body, p); p += 8;
        if (p + plen != body.Length) throw new InvalidDataException("patch payload size mismatch");

        byte[] orig = bd.Data;
        byte[] data = new byte[newLen];
        long o = 0, src = 0; int pp = p;
        for (int i = 0; i < nc; i++)
        {
            if (o + add[i] > newLen || pp + add[i] > body.Length) throw new InvalidDataException("patch add out of range");
            Buffer.BlockCopy(body, pp, data, (int)o, add[i]); pp += add[i]; o += add[i];
            src += seek[i];
            if (src < 0 || src + cp[i] > orig.Length || o + cp[i] > newLen) throw new InvalidDataException("patch copy out of range");
            Buffer.BlockCopy(orig, (int)src, data, (int)o, cp[i]); src += cp[i]; o += cp[i];
        }
        if (o != newLen) throw new InvalidDataException("patched size mismatch");
        bd.Data = null; orig = null; body = null;
        byte[] got;
        using (SHA256 sha = SHA256.Create()) got = sha.ComputeHash(data);
        for (int i = 0; i < 32; i++) if (got[i] != want[i]) throw new InvalidDataException("patched data checksum mismatch");

        // ---- LZ4 blocks
        int nb = (int)((newLen + Chunk - 1) / Chunk);
        byte[] comp = new byte[newLen + newLen / 255 + 16L * nb];
        int[] bus = new int[nb], bcs = new int[nb];
        int cpos = 0;
        for (int i = 0; i < nb; i++)
        {
            int start = i * Chunk, len = (int)Math.Min(Chunk, newLen - start);
            bus[i] = len;
            bcs[i] = Lz4Encode(data, start, len, comp, cpos);
            cpos += bcs[i];
        }
        data = null;

        // ---- block info (hash, blocks, nodes), LZ4 too
        MemoryStream info = new MemoryStream();
        info.Write(bd.Hash, 0, 16);
        PutBE32(info, (uint)nb);
        for (int i = 0; i < nb; i++) { PutBE32(info, (uint)bus[i]); PutBE32(info, (uint)bcs[i]); info.WriteByte(0); info.WriteByte(3); }
        PutBE32(info, (uint)nn);
        for (int i = 0; i < nn; i++)
        {
            PutBE64(info, noff[i]); PutBE64(info, nsz[i]); PutBE32(info, nfl[i]);
            byte[] nm = Encoding.UTF8.GetBytes(nname[i]); info.Write(nm, 0, nm.Length); info.WriteByte(0);
        }
        byte[] infoRaw = info.ToArray();
        byte[] infoC = new byte[infoRaw.Length + infoRaw.Length / 255 + 16];
        int infoCLen = Lz4Encode(infoRaw, 0, infoRaw.Length, infoC, 0);

        uint flags = (bd.Flags & ~0x3Fu & ~0x80u) | 3u;  // block info right after header, LZ4
        MemoryStream head = new MemoryStream();
        byte[] sig = Encoding.ASCII.GetBytes("UnityFS\0"); head.Write(sig, 0, 8);
        PutBE32(head, bd.Version);
        byte[] uv = Encoding.UTF8.GetBytes(bd.UnityVer); head.Write(uv, 0, uv.Length); head.WriteByte(0);
        byte[] ur = Encoding.UTF8.GetBytes(bd.UnityRev); head.Write(ur, 0, ur.Length); head.WriteByte(0);
        int fixedLen = (int)head.Length + 20;
        int bodyPos = bd.Version >= 7 ? Align16(fixedLen) : fixedLen;
        int dataPos = bodyPos + infoCLen;
        if ((flags & 0x200) != 0) dataPos = Align16(dataPos);
        long total = (long)dataPos + cpos;
        PutBE64(head, total); PutBE32(head, (uint)infoCLen); PutBE32(head, (uint)infoRaw.Length); PutBE32(head, flags);
        while (head.Length < bodyPos) head.WriteByte(0);
        head.Write(infoC, 0, infoCLen);
        while (head.Length < dataPos) head.WriteByte(0);

        using (FileStream outf = new FileStream(outPath, FileMode.Create, FileAccess.Write))
        {
            outf.Write(bd.A1Header, 0, 16);           // magic + version + header length (LE)
            PutLE32(outf, (uint)total);                // payload length
            outf.Write(bd.A1Header, 20, 4);           // reserved
            head.WriteTo(outf);
            outf.Write(comp, 0, cpos);
        }
    }
}
