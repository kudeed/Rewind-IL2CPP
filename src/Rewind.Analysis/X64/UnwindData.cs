using Rewind.Binary;

namespace Rewind.Analysis.X64;

/// <summary>One catch clause of a C++ try block as the compiler recorded it.</summary>
public sealed class CxxHandler
{
    /// <summary>Start of the handler's own code (a separate "funclet" that runs with the parent's frame).</summary>
    public ulong Funclet;
    /// <summary>Addresses in the parent function where execution may continue after the handler returns.</summary>
    public List<ulong> Continuations = [];
    public uint Adjectives;
    public ulong TypeDescriptor;
    public uint CatchObjectOffset;
}

public sealed class CxxTryBlock
{
    public int TryLow, TryHigh, CatchHigh;
    public List<CxxHandler> Handlers = [];
}

/// <summary>What happens when an exception unwinds through one state: a cleanup call, or nothing.</summary>
public readonly record struct CxxUnwindAction(int NextState, int Kind, ulong Action, uint Object);

/// <summary>
/// The C++ exception handling tables MSVC attaches to a function ("FH4" format): which instruction ranges are
/// in which state, which states form try blocks, and where their handlers are.
/// </summary>
public sealed class CxxFunctionInfo
{
    public ulong FunctionStart;
    public List<CxxTryBlock> TryBlocks = [];
    public List<CxxUnwindAction> UnwindMap = [];
    /// <summary>(first address, state) pairs in ascending address order; a state holds until the next entry. -1 is "no state".</summary>
    public List<(ulong Address, int State)> IpToState = [];
    public bool IsCatchFunclet;

    public int StateAt(ulong address)
    {
        int state = -1;
        foreach (var (start, s) in IpToState)
        {
            if (start > address) break;
            state = s;
        }
        return state;
    }

    public bool HasRegions => TryBlocks.Count != 0 || UnwindMap.Any(u => u.Kind != 0);
}

/// <summary>Reads x64 unwind information and the language-specific exception tables behind it.</summary>
public static class UnwindData
{
    private const int FlagExceptionHandler = 1, FlagUnwindHandler = 2, FlagChainInfo = 4;

    /// <summary>The address of the language handler and of its data for a function, or false when it has none.</summary>
    public static bool TryGetHandler(NativeImage image, FunctionRange function, out ulong handler, out ulong data)
    {
        handler = data = 0;
        ulong info = function.UnwindInfo;
        if (info == 0 || !image.IsMapped(info, 4)) return false;
        byte first = image.U8(info);
        int version = first & 7, flags = first >> 3;
        if (version is not (1 or 2) || (flags & (FlagExceptionHandler | FlagUnwindHandler)) == 0 || (flags & FlagChainInfo) != 0) return false;
        int codes = image.U8(info + 2);
        ulong after = info + 4 + (ulong)((codes + 1) & ~1) * 2;
        if (!image.IsMapped(after, 8)) return false;
        handler = image.ImageBase + image.U32(after);
        data = after + 4;
        return true;
    }

    private sealed class Reader(NativeImage image, ulong position)
    {
        public ulong Position = position;
        public byte Byte() => image.U8(Position++);

        public int Rva()
        {
            int value = (int)image.U32(Position);
            Position += 4;
            return value;
        }

        /// <summary>The variable-length unsigned integer of the FH4 tables: the low bits of the first byte give the length.</summary>
        public uint Compressed()
        {
            byte b0 = image.U8(Position);
            int length = (b0 & 1) == 0 ? 1 : (b0 & 3) == 1 ? 2 : (b0 & 7) == 3 ? 3 : (b0 & 15) == 7 ? 4 : 5;
            uint value;
            switch (length)
            {
                case 1: value = (uint)(b0 >> 1); break;
                case 2: value = (uint)(image.U16(Position) >> 2); break;
                case 3: value = (uint)((image.U16(Position) | (image.U8(Position + 2) << 16)) >> 3); break;
                case 4: value = image.U32(Position) >> 4; break;
                default: value = image.U32(Position + 1); break;
            }
            Position += (ulong)length;
            return value;
        }
    }

    /// <summary>
    /// Parses the FH4 function information at <paramref name="data"/> (the language-specific data of a
    /// function whose handler is __CxxFrameHandler4). Returns null when the tables do not parse.
    /// </summary>
    public static CxxFunctionInfo? ReadFh4(NativeImage image, ulong functionStart, ulong data)
    {
        try
        {
            if (!image.IsMapped(data, 4)) return null;
            ulong funcInfo = image.ImageBase + image.U32(data);
            if (!image.IsMapped(funcInfo, 2)) return null;
            var r = new Reader(image, funcInfo);
            byte header = r.Byte();
            bool isCatch = (header & 1) != 0, isSeparated = (header & 2) != 0, bbt = (header & 4) != 0;
            bool hasUnwindMap = (header & 8) != 0, hasTryMap = (header & 16) != 0;
            if (bbt) r.Compressed();
            int unwindMap = hasUnwindMap ? r.Rva() : 0;
            int tryMap = hasTryMap ? r.Rva() : 0;
            int ipMap = r.Rva();
            var result = new CxxFunctionInfo { FunctionStart = functionStart, IsCatchFunclet = isCatch };
            if (isSeparated) return result; // code split across sections: not produced for the builds handled here

            if (unwindMap != 0)
            {
                var u = new Reader(image, image.ImageBase + (uint)unwindMap);
                uint count = u.Compressed();
                if (count > 4096) return null;
                // Each entry stores the distance back to the entry of its next state.
                var offsets = new List<ulong>();
                var raw = new List<(uint NextOffset, int Kind, ulong Action, uint Object)>();
                for (uint i = 0; i < count; i++)
                {
                    offsets.Add(u.Position);
                    uint typeAndNext = u.Compressed();
                    int kind = (int)(typeAndNext & 3);
                    uint nextOffset = typeAndNext >> 2;
                    ulong action = 0;
                    uint obj = 0;
                    if (kind is 1 or 2)
                    {
                        action = image.ImageBase + (uint)u.Rva();
                        obj = u.Compressed();
                    }
                    else if (kind == 3) action = image.ImageBase + (uint)u.Rva();
                    raw.Add((nextOffset, kind, action, obj));
                }
                for (int i = 0; i < raw.Count; i++)
                {
                    ulong target = offsets[i] - raw[i].NextOffset;
                    int next = raw[i].NextOffset == 0 ? -1 : offsets.IndexOf(target);
                    if (raw[i].NextOffset != 0 && next < 0) next = -1;
                    result.UnwindMap.Add(new CxxUnwindAction(next, raw[i].Kind, raw[i].Action, raw[i].Object));
                }
            }

            if (tryMap != 0)
            {
                var t = new Reader(image, image.ImageBase + (uint)tryMap);
                uint count = t.Compressed();
                if (count > 1024) return null;
                for (uint i = 0; i < count; i++)
                {
                    var block = new CxxTryBlock { TryLow = (int)t.Compressed(), TryHigh = (int)t.Compressed(), CatchHigh = (int)t.Compressed() };
                    int handlers = t.Rva();
                    var h = new Reader(image, image.ImageBase + (uint)handlers);
                    uint handlerCount = h.Compressed();
                    if (handlerCount > 256) return null;
                    for (uint k = 0; k < handlerCount; k++)
                    {
                        byte flags = h.Byte();
                        var handler = new CxxHandler();
                        if ((flags & 1) != 0) handler.Adjectives = h.Compressed();
                        if ((flags & 2) != 0) handler.TypeDescriptor = image.ImageBase + (uint)h.Rva();
                        if ((flags & 4) != 0) handler.CatchObjectOffset = h.Compressed();
                        handler.Funclet = image.ImageBase + (uint)h.Rva();
                        bool continuationIsRva = (flags & 8) != 0;
                        int continuations = (flags >> 4) & 3;
                        for (int c = 0; c < continuations; c++)
                            handler.Continuations.Add(continuationIsRva ? image.ImageBase + (uint)h.Rva() : functionStart + h.Compressed());
                        block.Handlers.Add(handler);
                    }
                    result.TryBlocks.Add(block);
                }
            }

            if (ipMap != 0)
            {
                var m = new Reader(image, image.ImageBase + (uint)ipMap);
                uint count = m.Compressed();
                if (count > 65536) return null;
                ulong address = functionStart;
                for (uint i = 0; i < count; i++)
                {
                    address += m.Compressed();
                    int state = (int)m.Compressed() - 1;
                    result.IpToState.Add((address, state));
                }
            }
            return result;
        }
        catch (Exception e) when (e is ArgumentException or IndexOutOfRangeException or InvalidOperationException)
        {
            return null;
        }
    }
}
