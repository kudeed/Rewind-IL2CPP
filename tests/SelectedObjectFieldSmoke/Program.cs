using System.Linq.Expressions;
using System.Reflection;
using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Analysis.Recover;
using Rewind.Model;
using Rewind.Runtime;

int checks = 0;
void Check(bool ok, string why) { checks++; if (!ok) throw new Exception(why); }

Fixture Make() => new();
HSelect? Read(Fixture f, int offset = 0x30, int size = 8) =>
    SelectedObjectFields.TryRead(f.Condition, f.LeftValue, f.RightValue, offset, size, f.Layout);
var valid = Make();
var read = Read(valid);
Check(read is { WhenTrue: HField, WhenFalse: HField } &&
      ReferenceEquals(((HField)read.WhenTrue).Field, valid.LeftField) &&
      ReferenceEquals(((HField)read.WhenFalse).Field, valid.RightField), "separate exact field owners");
Check(ReferenceEquals(((HField)read!.WhenTrue).Object, valid.LeftValue) &&
      ReferenceEquals(((HField)read.WhenFalse).Object, valid.RightValue), "operand captures reused without casts");
var execute = Compile(read, valid);
var left = new LeftRecord { Data = "left" };
var right = new RightRecord("right");
Check(execute(true, left, right) == "left", "left selected");
Check(execute(false, left, right) == "right", "right selected");
Check(execute(true, left, null) == "left", "unselected null right is not read");
Check(execute(false, null, right) == "right", "unselected null left is not read");
Check(execute(true, new LeftRecord(), right) == null, "selected field may itself be null");
bool Throws(Action a) { try { a(); return false; } catch (NullReferenceException) { return true; } }
Check(Throws(() => execute(true, null, right)), "selected null left still throws");
Check(Throws(() => execute(false, left, null)), "selected null right still throws");
Check(Throws(() => execute(false, null, null)), "both null preserve selected throw");

// The field keeps its original access flags. Existing automatic-property lookup
// supplies the declared accessor; this transformation never changes visibility.
Check(valid.RightField.Attrs == 1 &&
      ReferenceEquals(new AccessorIndex(null!).GetterOf(valid.RightField), valid.Getter) &&
      (valid.Getter.Flags & MethodDef.AccessMask) == 6, "private storage has existing public getter");
Check(Read(valid)!.WhenFalse is HField { Field.Attrs: 1 }, "private field visibility unchanged");

var negatives = new (string Name, Action<Fixture> Change)[]
{
    ("different value type", f => { f.RightField.Type = f.Sigs.Primitive(Il2CppTypeEnum.I8); f.Rebuild(); }),
    ("static field", f => f.RightField.Attrs |= FieldDef.Static),
    ("wrong declaring class", f => f.RightField.DeclaringType = f.Left),
    ("missing field", f => f.RightLayout.Fields = []),
    ("overlapping fields", f => f.RightLayout.Fields = [f.RightLayout.Fields[0], f.RightLayout.Fields[0]]),
    ("unknown layout", f => f.RightLayout.Known = false),
    ("wrong recorded offset", f => f.RightField.Offset++),
    ("partial field", f => f.RightLayout.Fields = [new FieldSlot(f.RightField, f.RightField.Type, 0x30, 16)]),
    ("slot disagrees with metadata type", f => f.RightLayout.Fields = [new FieldSlot(f.RightField, f.Sigs.Primitive(Il2CppTypeEnum.I8), 0x30, 8)]),
    ("struct owner", f => f.Right.IsValueType = true),
    ("interface owner", f => f.Right.Flags |= TypeDef.Interface),
    ("open owner", f => f.Right.GenericParameters = [new GenericParam { Name = "T", Position = 0, OwnerType = f.Right }]),
    ("address-taken capture", f => f.RightLocal.AddressTaken = true),
    ("capture type disagreement", f => f.RightLocal.Type = f.Left.Sig),
    ("nested receiver read", f => f.RightValue = new HField { Object = f.LeftValue, Field = f.RightField, Type = f.Right.Sig }),
    ("receiver call", f => f.RightValue = new HCall { Method = f.Getter, Type = f.Right.Sig }),
    ("receiver cast", f => f.RightValue = new HTypeExpr(HTypeOp.CastClass, f.Right.Sig, f.LeftValue) { Type = f.Right.Sig }),
    ("same receiver class", f => f.RightValue = new HArg(2) { Type = f.Left.Sig }),
    ("untyped condition", f => f.Condition.Type = null)
};
foreach (var (name, change) in negatives) { var f = Make(); change(f); Check(Read(f) == null, name); }
Check(Read(Make(), size: 4) == null, "narrow read rejected");
Check(Read(Make(), size: 16) == null, "aggregate read rejected");
Check(Read(Make(), offset: 0x31) == null, "inside field rejected");
Check(Read(Make(), offset: 0) == null, "object header rejected");

// Full-width scalar fields are valid too; equal byte width alone is insufficient.
var numeric = Make();
numeric.LeftField.Type = numeric.RightField.Type = numeric.Sigs.Primitive(Il2CppTypeEnum.I4);
numeric.Rebuild(4);
Check(Read(numeric, size: 4) is { Type: PrimitiveSig { Element: Il2CppTypeEnum.I4 } }, "whole equal scalar fields");

AddressFixture Address() => new();
bool Matches(AddressFixture a) => SelectedObjectFields.TryAddress(a.Load, a.Uses, out Node choice, out int offset) &&
    ReferenceEquals(choice, a.Choice) && offset == 0x30;
Check(Matches(Address()), "exclusive same-block load address");
var reversed = Address(); (reversed.Address.In[0], reversed.Address.In[1]) = (reversed.Address.In[1], reversed.Address.In[0]);
Check(Matches(reversed), "commuted constant address");
var subtract = Address(); subtract.Address.Op = Op.Sub; subtract.Address.In[1].Imm = -0x30;
Check(Matches(subtract), "constant subtraction address");
var addressNegatives = new (string Name, Action<AddressFixture> Change)[]
{
    ("store is not a read", a => a.Load.Op = Op.Store),
    ("narrow address arithmetic", a => a.Address.Type = VT.I32),
    ("shared choice", a => a.Uses[a.Choice].Add(new Node { Op = Op.Return })),
    ("shared address", a => a.Uses[a.Address].Add(new Node { Op = Op.Load })),
    ("unknown choice users", a => a.Uses.Remove(a.Choice)),
    ("different block", a => a.Choice.Block = new Block()),
    ("exception scope", a => a.Block.Scope = 0),
    ("effect between choice and read", a => a.Block.Nodes.Insert(2, new Node { Op = Op.Call, Block = a.Block })),
    ("other load between choice and read", a => a.Block.Nodes.Insert(2, new Node { Op = Op.Load, Block = a.Block })),
    ("not a choice", a => a.Choice.Op = Op.Phi),
    ("not a predicate", a => a.Choice.In[0].Type = VT.I32),
    ("narrow choice arm", a => a.Choice.In[1].Type = VT.I32),
    ("unknown offset", a => a.Address.In[1].Op = Op.Param),
    ("dead selection", a => a.Choice.Dead = true),
    ("read ordered before choice", a => { a.Block.Nodes.Remove(a.Load); a.Block.Nodes.Insert(0, a.Load); }),
    ("offset overflow", a => a.Address.In[1].Imm = long.MaxValue)
};
foreach (var (name, change) in addressNegatives) { var a = Address(); change(a); Check(!Matches(a), name); }
Console.WriteLine($"SELECTED_OBJECT_FIELD_SMOKE_PASS checks={checks} semantic_cases=8 negative_cases={negatives.Length + addressNegatives.Length + 4}");

static Func<bool, LeftRecord?, RightRecord?, string?> Compile(HSelect value, Fixture fixture)
{
    var condition = Expression.Parameter(typeof(bool), "condition");
    var left = Expression.Parameter(typeof(LeftRecord), "left");
    var right = Expression.Parameter(typeof(RightRecord), "right");
    Expression Visit(HExpr e) => e switch
    {
        HArg { Index: 0 } => condition,
        HArg { Index: 1 } => left,
        HLocal l when ReferenceEquals(l.Variable, fixture.RightLocal) => right,
        HSelect s => Expression.Condition(Visit(s.Condition), Visit(s.WhenTrue), Visit(s.WhenFalse)),
        HField f => Expression.Field(Visit(f.Object!), (ReferenceEquals(f.Field.DeclaringType, fixture.Left) ? typeof(LeftRecord) : typeof(RightRecord))
            .GetField(f.Field.Name, BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic)!),
        _ => throw new Exception("unexpected expression in recovered field choice")
    };
    return Expression.Lambda<Func<bool, LeftRecord?, RightRecord?, string?>>(Visit(value), condition, left, right).Compile();
}

sealed class Fixture
{
    public readonly SigFactory Sigs = new();
    public readonly TypeDef Left, Right;
    public readonly FieldDef LeftField, RightField;
    public readonly MethodDef Getter;
    public readonly HVar RightLocal;
    public HExpr Condition, LeftValue, RightValue;
    public TypeLayout LeftLayout = null!, RightLayout = null!;
    public Fixture()
    {
        var assembly = new AssemblyModel { Name = "Synthetic" };
        Left = new TypeDef { Index = 1, Name = "LeftRecord", Assembly = assembly };
        Right = new TypeDef { Index = 2, Name = "RightRecord", Assembly = assembly };
        Left.Sig = Sigs.TypeDef(Left); Right.Sig = Sigs.TypeDef(Right);
        var text = Sigs.Primitive(Il2CppTypeEnum.String);
        LeftField = new FieldDef { Name = "Data", DeclaringType = Left, Type = text, Offset = 0x30, Attrs = 6 };
        RightField = new FieldDef { Name = "<Data>k__BackingField", DeclaringType = Right, Type = text, Offset = 0x30, Attrs = 1 };
        Left.Fields = [LeftField]; Right.Fields = [RightField];
        Getter = new MethodDef { Name = "get_Data", DeclaringType = Right, ReturnType = text, Flags = 6 };
        Right.Methods = [Getter];
        Right.Properties = [new PropertyDef { Name = "Data", DeclaringType = Right, Getter = Getter }];
        Condition = new HArg(0) { Type = Sigs.Primitive(Il2CppTypeEnum.Boolean) };
        LeftValue = new HArg(1) { Type = Left.Sig };
        RightLocal = new HVar { Type = Right.Sig };
        RightValue = new HLocal(RightLocal) { Type = Right.Sig };
        Rebuild();
    }
    public void Rebuild(int size = 8)
    {
        LeftLayout = new TypeLayout { Fields = [new FieldSlot(LeftField, LeftField.Type, LeftField.Offset, size)] };
        RightLayout = new TypeLayout { Fields = [new FieldSlot(RightField, RightField.Type, RightField.Offset, size)] };
    }
    public TypeLayout Layout(TypeSig type) => ReferenceEquals(type, Left.Sig) ? LeftLayout : RightLayout;
}

sealed class AddressFixture
{
    public readonly Block Block = new();
    public readonly Node Choice, Address, Load;
    public readonly Dictionary<Node, List<Node>> Uses = [];
    public AddressFixture()
    {
        Choice = new Node { Op = Op.Select, Type = VT.I64, Block = Block, In = [
            new Node { Op = Op.Param, Type = VT.I1 }, new Node { Op = Op.Param, Type = VT.I64 },
            new Node { Op = Op.Param, Type = VT.I64 }] };
        Address = new Node { Op = Op.Add, Type = VT.I64, Block = Block, In = [Choice, new Node { Op = Op.Const, Type = VT.I64, Imm = 0x30 }] };
        Load = new Node { Op = Op.Load, Type = VT.I64, Block = Block, In = [Address] };
        Block.Nodes = [Choice, Address, Load];
        Uses[Choice] = [Address]; Uses[Address] = [Load];
    }
}
sealed class LeftRecord { public string? Data; }
sealed class RightRecord(string? data) { public string? Data { get; } = data; }
