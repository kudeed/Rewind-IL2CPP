using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Analysis.Passes;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

public sealed partial class HirBuilder
{
    private sealed record TypedForwardCopy(FrameCopyPlan Proof, TypeSig Type);
    private readonly Dictionary<Node, TypedForwardCopy> _forwardedCopies = [];

    private void FindForwardedCopies()
    {
        var candidates = new HashSet<Node>();
        foreach (Block block in _fn.Blocks)
        {
            var region = new List<Node>();
            foreach (Node node in block.Nodes)
            {
                if (node.Dead) continue;
                if (node.Op is not (Op.Call or Op.TailCall)) { region.Add(node); continue; }
                if (node.Aux is CallInfo { Indirect: false, Intrinsic: null } info)
                {
                    var target = _p.Resolve(info.Target);
                    if (target.IsManaged)
                        for (int i = 0; i < info.Slots.Count && i < node.In.Length; i++)
                        {
                            int position = _fn.Regs.IntPositionOfSlot(info.Slots[i]);
                            if (position < 0 || FrameCopyProof.Offset(_fn, node.In[i]) is not int offset ||
                                !_frameTypes.TryGetValue(offset, out TypeSig? type) || !IsStructType(type) || Open(type)) continue;
                            var pointees = target.Methods.Select(m => PointeeOf(_p.Abi.For(m, [], []), position))
                                .Concat(target.Insts.Select(m => PointeeOf(_p.Abi.For(m), position))).ToArray();
                            if (pointees.Length == 0 || pointees.Any(t => t?.Key != type.Key)) continue;
                            var layout = _p.Layouts.Of(type);
                            if (!layout.Known || layout.Fields.Length == 0) continue;
                            var fields = layout.Fields.Select(f => (f.Offset, f.Size)).ToArray();
                            var proof = FrameCopyProof.TryProve(_fn, block, region, offset, layout.Size, fields, out _);
                            if (proof == null || !_frameTypes.TryGetValue(proof.Source, out TypeSig? source) || source.Key != type.Key ||
                                proof.Stores.Any(n => _pieceMembers.Contains(n) || _spillStores.Contains(n) || _caughtStores.Contains(n))) continue;
                            if (_forwardedCopies.ContainsKey(proof.Complete)) throw new InvalidOperationException("Two typed forwarded copies claim one completion store");
                            _forwardedCopies.Add(proof.Complete, new(proof, type));
                            foreach (Node store in proof.Stores) _pieceMembers.Add(store);
                            foreach (Node dependency in proof.Dependencies) candidates.Add(dependency);
                        }
                }
                region.Clear();
            }
        }
        // Retain every value that has an observable consumer outside the proven copies. Shared dependencies
        // are suppressed only after every consuming copy has been collected, including repeated loop calls.
        bool changed;
        do
        {
            changed = false;
            foreach (Node n in candidates)
                if (!_pieceMembers.Contains(n) && (!_uses.TryGetValue(n, out var users) || users.All(u => u.Dead || _pieceMembers.Contains(u))))
                { _pieceMembers.Add(n); changed = true; }
        } while (changed);
    }

    private void EmitForwardedCopy(TypedForwardCopy copy)
    {
        if (!_frameTypes.TryGetValue(copy.Proof.Source, out var source) || source.Key != copy.Type.Key ||
            !_frameTypes.TryGetValue(copy.Proof.Target, out var target) || target.Key != copy.Type.Key)
            throw new InvalidOperationException("Proven forwarded struct copy lost its exact frame types");
        Emit(new HAssign(new HLocal(FrameVar(copy.Proof.Target, copy.Type)) { Type = copy.Type },
            new HLocal(FrameVar(copy.Proof.Source, copy.Type)) { Type = copy.Type }), copy.Proof.Complete.Addr);
    }
}
