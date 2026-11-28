using Rewind.Analysis.Ir;
using Rewind.Analysis.X64;
using Rewind.Binary;

namespace Rewind.Analysis.Arm64;

public sealed partial class A64Lifter
{
    private readonly HashSet<Block> _inlineReturns = [];
    private readonly Dictionary<ulong, A64Cfg?> _inlineBodies = [];

    // Only independently approved, bounded functions without their own exception
    // handlers are eligible. Unknown control flow remains an explicit native call.
    private A64Cfg? InlineBody(ulong target, ulong caller)
    {
        if (target == caller || !_ctx.ShouldInline(target)) return null;
        if (_inlineBodies.TryGetValue(target, out var cached)) return cached;
        A64Cfg? body = A64Cfg.Build(_ctx, target);
        if ((_image is ElfImage elf && elf.ExceptionTableOf(target) is { HasLandingPads: true }) ||
            body.Problems.Count != 0 || body.Blocks.Count is 0 or > 128 ||
            body.Blocks.Sum(b => b.Instructions.Count) > 512 ||
            !body.Blocks.Any(b => b.End == BlockEnd.Return) ||
            body.Blocks.Any(b => b.End is BlockEnd.TailCall or BlockEnd.IndirectTailCall ||
                b.Instructions.Any(i => i.IsInvalid || i.Op is A64Op.Unknown or A64Op.Vector ||
                    (i.Op == A64Op.Bl && (i.Target == target || i.Target == caller)))))
            body = null;
        if (body != null)
        {
            var starts = body.Blocks.Select(b => b.Start).ToHashSet();
            if (body.Blocks.Any(b => b.Successors.Any(s => !starts.Contains(s)))) body = null;
        }
        return _inlineBodies[target] = body;
    }

    // Plan the caller's EH first. A pasted helper inherits exactly its callsite's
    // scope; its RET rejoins that callsite rather than returning from the caller.
    private void InlineCalls(Dictionary<Block, A64Block> rawOf)
    {
        int budget = 4096;
        var pending = new Queue<Block>(rawOf.Keys);
        void Link(Block from, Block to) { from.Succs.Add(to); to.Preds.Add(from); }
        Block Make(A64Block raw, int scope)
        {
            var b = new Block { Id = _fn.Blocks.Count, Start = raw.Start, End = raw.EndAddress, Scope = scope };
            _fn.Blocks.Add(b); rawOf.Add(b, raw); return b;
        }
        while (pending.TryDequeue(out var site))
        {
            var raw = rawOf[site];
            for (int at = 0; at < raw.Instructions.Count; at++)
            {
                var call = raw.Instructions[at];
                if (call.Op != A64Op.Bl || (at == raw.Instructions.Count - 1 && raw.End != BlockEnd.FallThrough)) continue;
                var body = InlineBody(call.Target, _fn.Address);
                if (body == null) continue;
                int cost = body.Blocks.Sum(b => b.Instructions.Count);
                if (cost > budget) continue;
                bool hasRest = at + 1 < raw.Instructions.Count;
                if (!hasRest && site.Succs.Count != 1) continue;
                budget -= cost;
                Block continuation;
                if (hasRest)
                {
                    var rest = new A64Block { Start = raw.Instructions[at + 1].Address, End = raw.End,
                        Successors = raw.Successors };
                    rest.Instructions.AddRange(raw.Instructions.Skip(at + 1));
                    continuation = Make(rest, site.Scope);
                    foreach (var next in site.Succs.ToArray())
                    {
                        next.Preds.Remove(site); Link(continuation, next);
                    }
                    pending.Enqueue(continuation);
                }
                else
                {
                    continuation = site.Succs[0]; continuation.Preds.Remove(site);
                }
                site.Succs.Clear();
                var prefix = new A64Block { Start = raw.Start, End = BlockEnd.InlinedCall };
                prefix.Instructions.AddRange(raw.Instructions.Take(at + 1));
                rawOf[site] = prefix; site.End = prefix.EndAddress;
                var copies = new Dictionary<ulong, Block>();
                foreach (var piece in body.Blocks) copies.Add(piece.Start, Make(piece, site.Scope));
                foreach (var piece in body.Blocks)
                {
                    var copy = copies[piece.Start];
                    foreach (ulong successor in piece.Successors) Link(copy, copies[successor]);
                    if (piece.End == BlockEnd.Return)
                    {
                        _inlineReturns.Add(copy); Link(copy, continuation);
                    }
                }
                Link(site, copies[call.Target]);
                break;
            }
        }
    }
}
