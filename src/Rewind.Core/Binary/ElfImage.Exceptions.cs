namespace Rewind.Binary;

/// <summary>
/// One entry of an Itanium C++ exception table's call-site list (addresses absolute). Filter: the type filter
/// of its first action - the selector its landing pad is entered with for that action (positive: a catch
/// clause, 0: a cleanup, negative: an exception specification); 0 when there is no action.
/// </summary>
public readonly record struct CallSite(ulong Start, ulong End, ulong LandingPad, int Action, long Filter = 0, bool CatchAll = false)
{
    /// <summary>
    /// The landing pad catches a type (rather than only cleaning up before the exception goes on). A catch of
    /// everything is no such catch here: IL2CPP never writes one; clang does, to call std::terminate when an
    /// exception leaves a function that may not throw.
    /// </summary>
    public bool Catches => LandingPad != 0 && Action != 0 && Filter > 0 && !CatchAll;
}

/// <summary>What an Itanium LSDA says about one function: its call sites, and the type table the actions index.</summary>
public sealed class ItaniumExceptionTable
{
    public ulong Lsda;
    public List<CallSite> CallSites = [];
    /// <summary>True when some call site has a landing pad (cleanup code or a catch).</summary>
    public bool HasLandingPads => CallSites.Any(c => c.LandingPad != 0);
}

public sealed partial class ElfImage
{
    private Dictionary<ulong, ulong>? _fdeOf;
    private readonly List<(ulong Start, ulong End)> _relro = [];

    /// <summary>
    /// True for memory the dynamic loader makes read-only once it has applied the relocations (PT_GNU_RELRO: the
    /// GOT and relocated constant tables). What it holds here, relocations applied, is what it holds at run time,
    /// except for the slots of imported symbols, which are filled from other libraries.
    /// </summary>
    public override bool IsReadOnlyAfterLoad(ulong va)
    {
        foreach (var (start, end) in _relro)
            if (va >= start && va < end)
                return !ImportSlots.ContainsKey(va);
        return false;
    }
    private readonly Dictionary<ulong, ItaniumExceptionTable?> _tables = [];

    /// <summary>
    /// Code that does nothing but jump through an import slot (AArch64 PLT stubs), with the imported name. Calls
    /// to imported functions go there.
    /// </summary>
    public Dictionary<ulong, string> ImportStubs { get; } = [];

    /// <summary>
    /// The symbol each GOT and PLT slot is bound to, whether another library or this one defines it (a function
    /// this library both defines and exports is still called through its PLT slot).
    /// </summary>
    public Dictionary<ulong, string> SlotSymbols { get; } = [];

    private void ReadPltStubs()
    {
        if (Arch != CpuArch.Arm64) return;
        foreach (ImageSection s in Sections)
        {
            if (s.Name != ".plt" || !s.IsExecutable) continue;
            for (ulong at = s.Va; at + 16 <= s.End; at += 4)
            {
                if (!IsMapped(at, 16)) break;
                uint adrp = U32(at), ldr = U32(at + 4), br = U32(at + 12);
                // adrp x16, page ; ldr x17, [x16, #off] ; add x16, x16, #off ; br x17
                if ((adrp & 0x9F00001F) != 0x90000010 || (ldr & 0xFFC003FF) != 0xF9400211 || br != 0xD61F0220) continue;
                long immlo = (adrp >> 29) & 3, immhi = (adrp >> 5) & 0x7FFFF;
                long page = ((immhi << 2 | immlo) << 43) >> 31; // sign-extended 21 bits, shifted left by 12
                ulong slot = (ulong)((long)(at & ~0xFFFUL) + page) + (((ldr >> 10) & 0xFFF) << 3);
                if (SlotSymbols.TryGetValue(slot, out string? name) || ImportSlots.TryGetValue(slot, out name)) ImportStubs[at] = name;
                at += 12;
            }
        }
    }

    private static ulong Uleb(NativeImage image, ref ulong p)
    {
        ulong result = 0;
        for (int shift = 0; shift < 64 && image.IsMapped(p); shift += 7)
        {
            byte b = image.U8(p++);
            result |= (ulong)(b & 0x7F) << shift;
            if ((b & 0x80) == 0) break;
        }
        return result;
    }

    private static long Sleb(NativeImage image, ref ulong p)
    {
        long result = 0;
        int shift = 0;
        byte b = 0;
        while (shift < 64 && image.IsMapped(p))
        {
            b = image.U8(p++);
            result |= (long)(b & 0x7F) << shift;
            shift += 7;
            if ((b & 0x80) == 0) break;
        }
        if (shift < 64 && (b & 0x40) != 0) result |= -1L << shift;
        return result;
    }

    /// <summary>Reads one DWARF pointer encoding, the LEB128 forms included.</summary>
    private bool ReadEncoded(ref ulong p, byte encoding, out ulong value)
    {
        value = 0;
        if (encoding == 0xFF) return true;
        ulong at = p;
        long raw;
        switch (encoding & 0x0F)
        {
            case 0x01: raw = (long)Uleb(this, ref p); break;
            case 0x09: raw = Sleb(this, ref p); break;
            case 0x02: if (!IsMapped(p, 2)) return false; raw = U16(p); p += 2; break;
            case 0x0A: if (!IsMapped(p, 2)) return false; raw = (short)U16(p); p += 2; break;
            default: return TryReadEncoded(ref p, encoding, 0, out value);
        }
        value = (encoding & 0x70) switch
        {
            0x10 => (ulong)((long)at + raw),
            _ => (ulong)raw,
        };
        return (encoding & 0x70) is 0x00 or 0x10;
    }

    private Dictionary<ulong, ulong> FdeTable()
    {
        if (_fdeOf != null) return _fdeOf;
        var table = new Dictionary<ulong, ulong>();
        ulong hdr = 0;
        foreach (ImageSection s in Sections)
            if (s.Name == ".eh_frame_hdr") hdr = s.Va;
        if (hdr != 0 && IsMapped(hdr, 4) && U8(hdr) == 1 && U8(hdr + 3) == 0x3B)
        {
            byte framePointerEncoding = U8(hdr + 1), countEncoding = U8(hdr + 2);
            ulong p = hdr + 4;
            if (TryReadEncoded(ref p, framePointerEncoding, hdr, out _) && TryReadEncoded(ref p, countEncoding, hdr, out ulong count) && count < 10_000_000)
                for (ulong i = 0; i < count && IsMapped(p, 8); i++, p += 8)
                    table.TryAdd((ulong)((long)hdr + (int)U32(p)), (ulong)((long)hdr + (int)U32(p + 4)));
        }
        lock (_tables) _fdeOf ??= table;
        return _fdeOf;
    }

    /// <summary>The Itanium exception table (LSDA) of the function starting at <paramref name="start"/>, or null when it has none.</summary>
    public ItaniumExceptionTable? ExceptionTableOf(ulong start)
    {
        lock (_tables)
            if (_tables.TryGetValue(start, out ItaniumExceptionTable? known)) return known;
        ItaniumExceptionTable? result = null;
        try
        {
            result = ReadExceptionTable(start);
        }
        catch (ArgumentOutOfRangeException)
        {
        }
        lock (_tables) _tables[start] = result;
        return result;
    }

    private ItaniumExceptionTable? ReadExceptionTable(ulong start)
    {
        if (!FdeTable().TryGetValue(start, out ulong fde) || !IsMapped(fde, 12)) return null;
        uint length = U32(fde);
        if (length == 0 || length == 0xFFFFFFFF) return null;
        ulong cie = fde + 4 - U32(fde + 4);
        if (!IsMapped(cie, 9) || U32(cie + 4) != 0) return null;
        // CIE: length, id 0, version, augmentation string, code/data alignment, return register, augmentation data.
        ulong p = cie + 9;
        var augmentation = new System.Text.StringBuilder();
        while (IsMapped(p) && U8(p) != 0) augmentation.Append((char)U8(p++));
        p++;
        string aug = augmentation.ToString();
        if (!aug.StartsWith('z') || !aug.Contains('L')) return null;
        Uleb(this, ref p);
        Sleb(this, ref p);
        if (U8(cie + 8) == 1) p++; else Uleb(this, ref p);
        Uleb(this, ref p); // augmentation data length
        byte lsdaEncoding = 0xFF, fdeEncoding = 0;
        foreach (char c in aug[1..])
        {
            switch (c)
            {
                case 'L': lsdaEncoding = U8(p++); break;
                case 'R': fdeEncoding = U8(p++); break;
                case 'P':
                {
                    byte personalityEncoding = U8(p++);
                    if (!ReadEncoded(ref p, (byte)(personalityEncoding & 0x7F), out _)) return null;
                    break;
                }
                case 'S' or 'B' or 'G': break;
                default: return null;
            }
        }
        if (lsdaEncoding == 0xFF) return null;
        // FDE: pc begin and range in the CIE's encoding, then its own augmentation data.
        ulong q = fde + 8;
        if (!ReadEncoded(ref q, fdeEncoding, out ulong begin) || begin != start) return null;
        if (!ReadEncoded(ref q, (byte)(fdeEncoding & 0x0F), out _)) return null;
        Uleb(this, ref q);
        if (!ReadEncoded(ref q, (byte)(lsdaEncoding & 0x7F), out ulong lsda) || lsda == 0) return null;
        return ReadLsda(lsda, start);
    }

    private ItaniumExceptionTable? ReadLsda(ulong lsda, ulong functionStart)
    {
        if (!IsMapped(lsda, 4)) return null;
        ulong p = lsda;
        byte lpStartEncoding = U8(p++);
        ulong lpStart = functionStart;
        if (lpStartEncoding != 0xFF && !ReadEncoded(ref p, lpStartEncoding, out lpStart)) return null;
        byte ttypeEncoding = U8(p++);
        ulong ttypeBase = 0;
        if (ttypeEncoding != 0xFF)
        {
            ulong offset = Uleb(this, ref p);
            ttypeBase = p + offset;
        }
        int ttypeSize = (ttypeEncoding & 0x0F) switch { 0x02 or 0x0A => 2, 0x03 or 0x0B => 4, _ => 8 };
        byte callSiteEncoding = U8(p++);
        ulong tableLength = Uleb(this, ref p);
        ulong end = p + tableLength;
        var table = new ItaniumExceptionTable { Lsda = lsda };
        while (p < end && table.CallSites.Count < 100_000)
        {
            if (!ReadEncoded(ref p, callSiteEncoding, out ulong siteStart) || !ReadEncoded(ref p, callSiteEncoding, out ulong siteLength) ||
                !ReadEncoded(ref p, callSiteEncoding, out ulong pad)) return null;
            int action = (int)Uleb(this, ref p);
            long filter = 0;
            bool catchAll = false;
            if (action != 0)
            {
                // The action table follows the call-site table; an action is its byte offset there, plus one.
                ulong record = end + (ulong)(action - 1);
                if (IsMapped(record)) filter = Sleb(this, ref record);
                // The type a positive filter catches is entry -filter of the type table, counted back from its
                // end; an entry of zero catches everything.
                if (filter > 0 && ttypeBase != 0)
                {
                    ulong entry = ttypeBase - (ulong)(filter * ttypeSize);
                    if (IsMapped(entry, ttypeSize))
                        catchAll = ttypeSize switch { 2 => U16(entry) == 0, 4 => U32(entry) == 0, _ => U64(entry) == 0 };
                }
            }
            table.CallSites.Add(new CallSite(lpStart + siteStart, lpStart + siteStart + siteLength, pad == 0 ? 0 : lpStart + pad, action, filter, catchAll));
        }
        return table;
    }
}
