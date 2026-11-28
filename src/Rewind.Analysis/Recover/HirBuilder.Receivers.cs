using Rewind.Analysis.Ir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

public sealed partial class HirBuilder
{
    /// <summary>
    /// The extra input was proved to be the adjacent null-checked object of a call whose native body
    /// ignores its instance register. Its managed type must independently fit the method's declaring type.
    /// Unknown types, pointers, value types and unrelated references never acquire a cast to make them fit.
    /// </summary>
    private Node? CheckedReceiverFor(Node call, int position, TypeSig expected)
    {
        if (expected.IsValueType || ReceiverRecovery.CheckedReceiver(call, position) is not { } owner) return null;
        TypeSig? actual = Peek(owner) switch
        {
            SVal value => value.Type,
            SNewObject made => made.Type,
            _ => null,
        };
        return actual is { IsValueType: false, Definition: not null } && IsAssignable(actual, expected) ? owner : null;
    }
}
