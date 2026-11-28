using Rewind.Analysis.Hir;
using Rewind.Model;
using Rewind.Runtime;

internal static partial class Program
{
    private sealed record ResultFlow(Fixture Fixture, HMethod Body, MethodDef Api, MethodDef SourceApi, MethodDef Continue,
        HMethod Caller, FieldDef Source, FieldDef Cached, FieldDef Token, HBlock SourceBlock, HBlock CachedBlock);

    private static ResultFlow ResultFixture(TypeSig payload, bool consume = false)
    {
        Fixture f = Fresh(payload);
        TypeSig task = f.Receiver, awaiter = f.ReturnType;
        FieldDef source = task.Definition!.Fields[0], cached = task.Definition.Fields[1], token = task.Definition.Fields[2];
        var sourceApi = new MethodDef { Name = "GetResult", DeclaringType = Define("IResultSource", false), Flags = 6,
            ReturnType = payload, Parameters = [new ParamDef { Position = 0, Name = "token", Type = Int }] };
        var api = new MethodDef { Name = "GetResult", DeclaringType = awaiter.Definition!, Flags = 6,
            ReturnType = Sigs.GenericParam(awaiter.Definition!.GenericParameters[0]) };
        var continuation = new MethodDef { Name = "Continue", DeclaringType = Define("Game", false),
            Flags = MethodDef.Static | 6, ReturnType = Sigs.Primitive(Il2CppTypeEnum.Void) };
        HExpr Task(HExpr owner) => Field(owner, f.Field, task);
        HExpr Read(HExpr owner, FieldDef field, TypeSig type) => Field(Task(owner), field, type);
        var body = new HMethod { Method = api };
        var entry = new HBlock { Id = 0 }; var called = new HBlock { Id = 1 }; var ready = new HBlock { Id = 2 }; var finish = new HBlock { Id = 3 };
        body.Blocks.AddRange([entry, called, ready, finish]);
        HLocal src = Local(body.NewLocal(Object)), returned = Local(body.NewLocal(payload));
        HExpr self = new HArg(-1) { Type = awaiter };
        entry.Statements.Add(new HAssign(src, Read(self, source, Object)));
        entry.Statements.Add(new HBranch(new HCompare(HCompareOp.Eq, src, new HConst(null, Object)), ready, called));
        var sourceCall = new HCall { Method = sourceApi, This = src, Arguments = [Read(self, token, Int)], Type = payload };
        if (payload.Definition is { IsValueType: true } parts)
        {
            HLocal whole = Local(body.NewLocal(payload));
            called.Statements.Add(new HAssign(whole, sourceCall));
            foreach (FieldDef field in parts.Fields)
                called.Statements.Add(new HAssign(Field(returned, field, field.Type), Field(whole, field, field.Type)));
            foreach (FieldDef field in parts.Fields)
                ready.Statements.Add(new HAssign(Field(returned, field, field.Type), Field(Read(self, cached, payload), field, field.Type)));
        }
        else
        {
            called.Statements.Add(new HAssign(returned, sourceCall));
            ready.Statements.Add(new HAssign(returned, Read(self, cached, payload)));
        }
        called.Statements.Add(new HJump(finish));
        ready.Statements.Add(new HJump(finish));
        finish.Statements.Add(new HReturn(returned));

        var caller = new HMethod { Method = new MethodDef { Name = "Caller", DeclaringType = continuation.DeclaringType,
            ReturnType = continuation.ReturnType, Parameters = [new ParamDef { Position = 0, Type = awaiter }] } };
        var a = new HBlock { Id = 0 }; var b = new HBlock { Id = 1 }; var c = new HBlock { Id = 2 }; var d = new HBlock { Id = 3 };
        caller.Blocks.AddRange([a, b, c, d]);
        HLocal kept = Local(caller.NewLocal(Object)); HExpr arg = new HArg(0) { Type = awaiter };
        a.Statements.Add(new HAssign(kept, Read(arg, source, Object)));
        a.Statements.Add(new HBranch(new HCompare(HCompareOp.Eq, kept, new HConst(null, Object)), c, b));
        var call = new HCall { Method = sourceApi, This = kept, Arguments = [Read(arg, token, Int)], Type = payload };
        b.Statements.Add(consume ? new HAssign(Local(caller.NewLocal(payload)), call) : new HEval(call));
        b.Statements.Add(new HJump(d)); c.Statements.Add(new HJump(d));
        d.Statements.Add(new HEval(new HCall { Method = continuation, Type = continuation.ReturnType }));
        d.Statements.Add(new HReturn(null));
        return new ResultFlow(f, body, api, sourceApi, continuation, caller, source, cached, token, b, c);
    }

    private static object Discarded(ResultFlow f)
    {
        object template = Inline.GetMethod("MakeDiscardedFlow", All)!.Invoke(null, [f.Api, f.Body])
            ?? throw new InvalidOperationException("discarded fixture has no template");
        template.GetType().GetField("ClassArguments", All)!.SetValue(template, f.Fixture.Arguments);
        template.GetType().GetField("SiteArguments", All)!.SetValue(template, f.Fixture.Arguments);
        template.GetType().GetField("Declaring", All)!.SetValue(template, f.Fixture.ReturnType);
        return template;
    }
    private static bool FoldDiscarded(ResultFlow f, object template)
    {
        object counts = Counts.GetMethod("Of", All)!.Invoke(null, [f.Caller])!;
        return (bool)Inline.GetMethod("TryFoldFlow", All)!.Invoke(f.Fixture.Folder,
            [f.Caller, f.Caller.Blocks[0], 0, template, counts])!;
    }

    private static void IgnoredResults()
    {
        var value = Define("Scene", true, ("handle", Int), ("operation", Object));
        foreach (TypeSig payload in new[] { Int, Object, value.Sig })
        {
            ResultFlow f = ResultFixture(payload); object template = Discarded(f);
            var flow = (HMethod)template.GetType().GetField("Flow", All)!.GetValue(template)!;
            Check(flow.Blocks.SelectMany(b => b.Statements).OfType<HEval>().Count(e => e.Expression is HCall) == 1,
                "discarded template retains the original source call exactly once");
            Check(f.Body.Blocks[3].Statements[0] is HReturn { Value: not null }, "normal result body is unchanged");
            var before = new List<(bool HasSource, bool Throws, int Calls, int Token, int Continued)>();
            foreach (bool hasSource in new[] { false, true })
                foreach (bool throws in new[] { false, true })
                {
                    var state = new ResultState { Throws = throws }; RunResult(f, f.Caller, hasSource, state);
                    before.Add((hasSource, throws, state.Calls, state.Token, state.Continued));
                }
            Check(FoldDiscarded(f, template), "discarded branch flow becomes one public result call");
            foreach (var expected in before)
            {
                var state = new ResultState { Throws = expected.Throws }; RunResult(f, f.Caller, expected.HasSource, state);
                Check((state.Calls, state.Token, state.Continued) == (expected.Calls, expected.Token, expected.Continued),
                    "null/source branch, nonzero token, call count and exception order are unchanged");
            }
            Cases.Add("discarded generic result: " + payload.DisplayName);
        }
        void Reject(string name, Action<ResultFlow> alter, bool consumed = false)
        {
            ResultFlow f = ResultFixture(Int, consumed); alter(f);
            Check(!FoldDiscarded(f, Discarded(f)), name); Cases.Add(name);
        }
        Reject("used source result is never treated as ignored", _ => { }, true);
        Reject("different continuation is retained", f => f.CachedBlock.Statements[0] = new HReturn(null));
        Reject("wrong source token is refused", f => ((HCall)((HEval)f.SourceBlock.Statements[0]).Expression).Arguments[0] = new HConst(0, Int));
        Reject("cached getter side effect cannot be erased", f => ((HAssign)f.Body.Blocks[2].Statements[0]).Value =
            new HCall { Method = f.SourceApi, This = new HConst(null, Object), Arguments = [new HConst(0, Int)], Type = Int });
        Reject("discarding a value must preserve division exceptions", f => ((HAssign)f.Body.Blocks[2].Statements[0]).Value =
            new HBinary(HBinaryOp.Div, new HConst(1, Int), new HConst(0, Int)) { Type = Int });
        Reject("discarding a value must preserve class dereferences", f => ((HAssign)f.Body.Blocks[2].Statements[0]).Value =
            Field(new HConst(null, Object), Define("Container", false, ("value", Int)).Fields[0], Int));
        Reject("address-visible return storage cannot be pruned", f => f.Body.Blocks[2].Statements.Insert(0,
            new HEval(new HCall { Method = f.Continue, Arguments = [new HAddressOf(Local(f.Body.Locals[1]))] })));
    }

    private sealed class ResultState
    {
        public bool Throws;
        public int Calls, Token, Continued;
        public readonly object Operation = new();
    }
    private static void RunResult(ResultFlow f, HMethod method, bool hasSource, ResultState state)
    {
        object? result = f.Fixture.Arguments[0].Definition is { IsValueType: true } definition
            ? definition.Fields.ToDictionary(field => field, field => (object?)(field.Type.IsValueType ? 572 : state.Operation))
            : f.Fixture.Arguments[0].IsValueType ? 572 : state.Operation;
        var task = new Dictionary<FieldDef, object?> { [f.Source] = hasSource ? state : null, [f.Cached] = result, [f.Token] = 1911 };
        var awaiter = new Dictionary<FieldDef, object?> { [f.Fixture.Field] = task };
        try { Evaluate(method, awaiter); }
        catch (ArithmeticException) { Check(state.Throws && hasSource && state.Continued == 0, "source exception reaches caller before continuation"); }
        object? Evaluate(HMethod h, object? input)
        {
            var locals = new Dictionary<HVar, object?>();
            object? Expr(HExpr e) => e switch
            {
                HArg => input, HLocal l => locals[l.Variable], HConst c => c.Value,
                HField field => ((Dictionary<FieldDef, object?>)Expr(field.Object!)!)[field.Field],
                HCompare compare when compare.Op == HCompareOp.Eq => Equals(Expr(compare.Left), Expr(compare.Right)),
                HCall call when ReferenceEquals(call.Method, f.Api) => Evaluate(f.Body, Expr(call.This!)),
                HCall call when ReferenceEquals(call.Method, f.SourceApi) => Source(call),
                HCall call when ReferenceEquals(call.Method, f.Continue) => Continue(),
                _ => throw new NotSupportedException(e.GetType().Name),
            };
            object? Source(HCall call)
            {
                Check(ReferenceEquals(Expr(call.This!), state), "source identity is preserved");
                state.Token = (int)Expr(call.Arguments[0])!; state.Calls++;
                if (state.Throws) throw new ArithmeticException("original source failure");
                return result;
            }
            object? Continue() { state.Continued++; return null; }
            HBlock block = h.Blocks[0]; int index = 0;
            for (int guard = 0; guard < 100; guard++)
            {
                HStmt statement = block.Statements[index++];
                switch (statement)
                {
                    case HAssign { Target: HLocal local, Value: var expression }: locals[local.Variable] = Expr(expression); break;
                    case HAssign { Target: HField { Object: HLocal local } field, Value: var expression }:
                        if (!locals.ContainsKey(local.Variable)) locals[local.Variable] = new Dictionary<FieldDef, object?>();
                        ((Dictionary<FieldDef, object?>)locals[local.Variable]!)[field.Field] = Expr(expression); break;
                    case HEval eval: Expr(eval.Expression); break;
                    case HBranch branch: block = (bool)Expr(branch.Condition)! ? branch.WhenTrue : branch.WhenFalse; index = 0; break;
                    case HJump jump: block = jump.Target; index = 0; break;
                    case HReturn ret: return ret.Value == null ? null : Expr(ret.Value);
                    default: throw new NotSupportedException(statement.GetType().Name);
                }
            }
            throw new InvalidOperationException("fixture flow did not terminate");
        }
    }
}
