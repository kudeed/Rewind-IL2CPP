using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;

namespace Rewind.Analysis.Recover;

public sealed partial class HirBuilder
{
    private ManagedStoreBarrierProof.Witness? _managedStoreBarrier;

    private void RecordManagedStoreBarrier(Node store, HAssign assignment)
    {
        // Emit can discard a redundant self-store. It cannot witness a barrier if it was not retained.
        _managedStoreBarrier = _cur.Statements.Count != 0 && ReferenceEquals(_cur.Statements[^1], assignment)
            ? ManagedStoreBarrierProof.Record(store, assignment) : null;
    }

    private void PreserveManagedBarrierReturns(Node call, Dictionary<int, Node> projections)
    {
        // FinishCall has already emitted the one opaque helper effect and bound x0, if used.
        // Other live machine lanes must not fall through SJunk: HalfBits would turn that into zero.
        foreach (var (which, projection) in projections)
        {
            if (which == CallResult.IntReturn || !IsUsed(projection)) continue;
            string why = $"mark-only write barrier physical return projection {which} was used";
            Problem(why);
            var type = TypeForBits(projection.Type);
            HVar local = Temp(type, projection.Type);
            var held = new HLocal(local) { Type = type };
            Emit(new HAssign(held, Site(new HOpaque("write_barrier_return_" + which) { Type = type }, why)), call.Addr);
            _sem[projection] = new SVal(new HLocal(local) { Type = type });
        }
    }
}
