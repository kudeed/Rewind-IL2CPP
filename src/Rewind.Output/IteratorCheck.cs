using ICSharpCode.Decompiler.CSharp.Syntax;

namespace Rewind.Output;

/// <summary>
/// Finds iterators the C# decompiler rebuilt wrongly: "yield return" code whose state can never change.
///
/// The decompiler turns an iterator's state machine back into "yield return" by following the state field
/// through MoveNext. Where it cannot follow it all the way, it may still go on: the state field becomes an
/// ordinary variable, the writes that advanced it are dropped as part of the machine, and what is left switches
/// on a variable nothing ever changes - the first "yield return" again and again, for ever. Such a body is
/// detected here (a switch on a local that, through the copies made of it, is only ever given its first value),
/// and the type is then written with its state machines as the classes the compiler made of them, which say
/// exactly what the recovered code does.
/// </summary>
internal static class IteratorCheck
{
    public static bool HasStuckIterator(AstNode tree)
    {
        foreach (AstNode body in tree.Descendants.Where(n => n is BlockStatement && n.Parent is EntityDeclaration or Accessor))
        {
            if (!body.Descendants.Any(n => n is YieldReturnStatement or YieldBreakStatement)) continue;
            if (Stuck((BlockStatement)body)) return true;
        }
        return false;
    }

    private static bool Stuck(BlockStatement body)
    {
        // Every local's declarations (with what they start as) and other assignments.
        var starts = new Dictionary<string, Expression?>();
        var assigned = new HashSet<string>();
        foreach (AstNode n in body.Descendants)
        {
            switch (n)
            {
                case VariableInitializer v when v.Parent is VariableDeclarationStatement:
                    if (!starts.TryAdd(v.Name, v.Initializer)) assigned.Add(v.Name);
                    break;
                case AssignmentExpression { Left: IdentifierExpression target }:
                    assigned.Add(target.Identifier);
                    break;
                case UnaryOperatorExpression { Operator: UnaryOperatorType.Increment or UnaryOperatorType.Decrement or UnaryOperatorType.PostIncrement or UnaryOperatorType.PostDecrement, Expression: IdentifierExpression changed }:
                    assigned.Add(changed.Identifier);
                    break;
                case DirectionExpression { Expression: IdentifierExpression handed }:
                    assigned.Add(handed.Identifier);
                    break;
                case ForeachStatement each:
                    foreach (SingleVariableDesignation one in each.VariableDesignation.DescendantsAndSelf.OfType<SingleVariableDesignation>())
                        assigned.Add(one.Identifier);
                    break;
                case CatchClause { VariableName: { Length: > 0 } caught }:
                    assigned.Add(caught);
                    break;
            }
        }

        // A local read that was never given anything (not even a first value): the state the writes were dropped from.
        foreach (var (name, start) in starts)
            if (start == null && !assigned.Contains(name) &&
                body.Descendants.OfType<IdentifierExpression>().Any(id => id.Identifier == name))
                return true;

        foreach (SwitchStatement s in body.Descendants.OfType<SwitchStatement>())
        {
            // Through casts and the copies made of it ("int num = num2"), back to where the value comes from.
            Expression e = s.Expression;
            for (int depth = 0; depth < 8; depth++)
            {
                while (e is CastExpression c) e = c.Expression;
                while (e is ParenthesizedExpression p) e = p.Expression;
                if (e is not IdentifierExpression id || !starts.TryGetValue(id.Identifier, out Expression? start) || assigned.Contains(id.Identifier)) break;
                if (start is IdentifierExpression or CastExpression or ParenthesizedExpression)
                {
                    e = start;
                    continue;
                }
                // Given its first value and nothing else, ever: a constant or "default".
                if (start == null || start is PrimitiveExpression or DefaultValueExpression || start is NullReferenceExpression) return true;
                break;
            }
        }
        // Some recovered MoveNext bodies dispatch with ifs rather than a switch. When
        // ILSpy drops the state writes, the surviving outer int defaults to zero and
        // is copied into each loop iteration. Keep the original compiler state class
        // for this bounded pattern: an immutable outer int, 0/1 equality dispatch,
        // and an unconditional while containing yields. Single configuration tests,
        // mutable locals, calls/fields and comparisons outside such a loop do not qualify.
        var dispatch = new Dictionary<(string Name, WhileStatement Loop), HashSet<int>>();
        foreach (IfElseStatement branch in body.Descendants.OfType<IfElseStatement>())
        {
            if (Unwrap(branch.Condition) is not BinaryOperatorExpression comparison ||
                comparison.Operator is not (BinaryOperatorType.Equality or BinaryOperatorType.InEquality) ||
                comparison.Left is not Expression leftOperand || comparison.Right is not Expression rightOperand) continue;
            Expression left = Unwrap(leftOperand), right = Unwrap(rightOperand);
            if (left is PrimitiveExpression) (left, right) = (right, left);
            if (right is not PrimitiveExpression { Value: int value } || value < 0) continue;
            string? root = null;
            Expression current = left;
            for (int depth = 0; depth < 8; depth++)
            {
                current = Unwrap(current);
                if (current is not IdentifierExpression id || assigned.Contains(id.Identifier) ||
                    !starts.TryGetValue(id.Identifier, out Expression? initial) || initial == null) break;
                initial = Unwrap(initial);
                if (initial is IdentifierExpression) { current = initial; continue; }
                if (initial is DefaultValueExpression or PrimitiveExpression { Value: int }) root = id.Identifier;
                break;
            }
            if (root == null) continue;
            var declaration = body.Statements.OfType<VariableDeclarationStatement>()
                .SingleOrDefault(d => d.Type.ToString() == "int" && d.Variables.Any(v => v.Name == root));
            if (declaration == null) continue;
            WhileStatement? loop = null;
            for (AstNode? parent = branch.Parent; parent != null && parent != body; parent = parent.Parent)
                if (parent is WhileStatement found) { loop = found; break; }
            if (loop == null || Unwrap(loop.Condition) is not PrimitiveExpression { Value: true } ||
                !loop.Descendants.Any(n => n is YieldReturnStatement)) continue;
            var key = (root, loop);
            if (!dispatch.TryGetValue(key, out HashSet<int>? states)) dispatch.Add(key, states = new());
            states.Add(value);
            if (states.Contains(0) && states.Contains(1)) return true;
        }
        return false;
    }

    private static Expression Unwrap(Expression expression)
    {
        while (true)
        {
            if (expression is CastExpression cast) expression = cast.Expression;
            else if (expression is ParenthesizedExpression parentheses) expression = parentheses.Expression;
            else return expression;
        }
    }
}
