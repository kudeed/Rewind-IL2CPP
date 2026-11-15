using Rewind.Analysis;
using Rewind.Analysis.Runtime;
using Rewind.Analysis.X64;
using Rewind.Binary;
using Rewind.Model;

namespace Rewind.Lab;

/// <summary>Research commands for exception handling tables.</summary>
internal static class EhLab
{
    /// <summary>eh-stats &lt;input&gt; [name filter]: how many managed functions carry C++ exception tables, and of what shape.</summary>
    public static int Stats(Il2CppModel model, string? filter)
    {
        NativeImage image = model.Image;
        var context = new ModelCodeContext(model);
        var index = new CodeIndex(context);
        var byHandler = new Dictionary<ulong, int>();
        int managed = 0, withHandler = 0, parsed = 0, withTry = 0, withUnwindOnly = 0, empty = 0, failed = 0;
        long tryBlocks = 0, handlers = 0;
        foreach (FunctionRange f in image.FunctionTable)
        {
            if (f.Chained || !context.IsManaged(f.Start)) continue;
            managed++;
            if (!UnwindData.TryGetHandler(image, f, out ulong handler, out ulong data)) continue;
            withHandler++;
            byHandler[handler] = byHandler.GetValueOrDefault(handler) + 1;
            CxxFunctionInfo? info = UnwindData.ReadFh4(image, f.Start, data);
            if (info == null) { failed++; continue; }
            parsed++;
            if (info.TryBlocks.Count != 0) { withTry++; tryBlocks += info.TryBlocks.Count; handlers += info.TryBlocks.Sum(t => t.Handlers.Count); }
            else if (info.UnwindMap.Any(u => u.Kind != 0)) withUnwindOnly++;
            else empty++;

            if (filter != null && model.MethodsByAddress.TryGetValue(f.Start, out List<MethodDef>? methods) && methods.Any(m => m.FullName.Contains(filter, StringComparison.Ordinal)))
            {
                Console.WriteLine($"=== {methods[0].FullName} @0x{f.Start:X}..0x{f.End:X}");
                foreach (var (address, state) in info.IpToState) Console.WriteLine($"    ip 0x{address:X} state {state}");
                for (int i = 0; i < info.UnwindMap.Count; i++)
                    Console.WriteLine($"    unwind {i}: next {info.UnwindMap[i].NextState} kind {info.UnwindMap[i].Kind} action 0x{info.UnwindMap[i].Action:X} object {info.UnwindMap[i].Object}");
                foreach (CxxTryBlock t in info.TryBlocks)
                {
                    Console.WriteLine($"    try states {t.TryLow}..{t.TryHigh} catchHigh {t.CatchHigh}");
                    foreach (CxxHandler h in t.Handlers)
                        Console.WriteLine($"      handler funclet 0x{h.Funclet:X} adjectives 0x{h.Adjectives:X} type 0x{h.TypeDescriptor:X} continuations {string.Join(",", h.Continuations.Select(c => "0x" + c.ToString("X")))}");
                }
            }
        }
        Console.WriteLine($"managed functions: {managed}; with a language handler: {withHandler}; tables parsed: {parsed} (failed {failed})");
        Console.WriteLine($"  with try blocks: {withTry} ({tryBlocks} try blocks, {handlers} handlers); cleanup actions only: {withUnwindOnly}; no regions: {empty}");
        foreach (var (handler, count) in byHandler.OrderByDescending(kv => kv.Value).Take(5))
            Console.WriteLine($"  handler 0x{handler:X}: {count} functions  {string.Join(" ", index.Get(index.ThunkTarget(handler))?.Names.Take(3) ?? [])}");
        return 0;
    }
}
