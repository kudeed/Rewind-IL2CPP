using Rewind.Analysis.Hir;

namespace Rewind.Analysis.Recover;

/// <summary>For tools outside this assembly: every expression of a statement, in turn.</summary>
public static class FinallyFoldingAccess
{
    public static void Visit(HStmt statement, Action<HExpr> visit) => FinallyFolding.Visit(statement, visit);
}
