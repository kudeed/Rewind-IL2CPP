using Rewind.Analysis.Ir;
using Rewind.Analysis.Arm64;
using Rewind.Binary;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>Recover an optimized-away receiver before deleting its explicit
/// native null guard. Only the exact checked, typed static field can be used;
/// the immediately following unambiguous native callee must ignore x0.</summary>
public sealed partial class Normalizer
{
    internal static Node? NullGuardValue(Node condition,int throwingSide)
    {
        if(condition.In.Length!=2||condition.Op is not (Op.CmpEq or Op.CmpNe))return null;
        if((condition.Op==Op.CmpEq)!=(throwingSide==0))return null;
        Node a=condition.In[0],b=condition.In[1];
        Node? value=a.IsConstValue(0)?b:b.IsConstValue(0)?a:null;
        return value?.Type==VT.I64?value:null;
    }

    internal static Node? FirstDirectCall(Block guard,Block continuation,Node? stackPointer=null)
    {
        if(guard.Scope!=-1||continuation.Scope!=-1||continuation==guard||
            continuation.Preds.Count!=1||continuation.Preds[0]!=guard)return null;
        foreach(Node n in continuation.Nodes)
        {
            if(n.Dead)continue;
            if(n.Op is Op.Call or Op.TailCall)
                return n.Aux is CallInfo {Indirect:false,Intrinsic:null,NoReturn:false}?n:null;
            // No intervening effects: don't move the original null check
            // past another call, load, write or control transfer.
            if(n.IsEffect)
            {
                // The native tail-call epilogue may restore saved registers.
                // Only fixed 8-byte loads inside the existing stack frame are
                // allowed; never move the guard past a heap access or a call.
                if(continuation.Terminator?.Op!=Op.TailCall || !IsFixedStackRestore(n,stackPointer))return null;
            }
        }
        return null;
    }

    internal static bool IsFixedStackRestore(Node n,Node? sp)
    {
        if(sp==null||n.Op!=Op.Load||n.Type!=VT.I64||n.In.Length!=1||n.In[0] is not {Op:Op.Add} a||
            a.In.Length!=2)return false;
        Node? offset=ReferenceEquals(a.In[0],sp)?a.In[1]:ReferenceEquals(a.In[1],sp)?a.In[0]:null;
        if(offset?.IsConst!=true)return false;
        long v=IrBuilder.SImm(offset);
        return v is >= -4096 and <= -8 && v%8==0;
    }

    private void RestoreGuardedReceiver(Block guard,Block continuation,Node condition,int side)
    {
        if(Environment.GetEnvironmentVariable("REWIND_NO_GUARDED_RECEIVER")!=null||
            program.Model.Image.Arch!=CpuArch.Arm64||_fn.TryRegions.Count!=0||
            NullGuardValue(condition,side) is not { Op:Op.Load,Type:VT.I64 } checkedObject||
            checkedObject.Block!=guard||
            FirstDirectCall(guard,continuation,_fn.Params.GetValueOrDefault(_fn.Regs.StackPointer)) is not {Aux:CallInfo ci} call)
            return;

        // A static reference field is Load(Load(Klass+static_fields)+offset).
        // Only a metadata-identified class and exact recorded field identity
        // qualify. No arbitrary pointer, integer, or guessed singleton name.
        static (Node Base,long Offset) Split(Node address)
        {
            if(address.Op==Op.Add&&address.In.Length==2)
            {
                if(address.In[1].IsConst)return(address.In[0],address.In[1].Imm);
                if(address.In[0].IsConst)return(address.In[1],address.In[0].Imm);
            }
            return(address,0);
        }
        var (statics,offset)=Split(checkedObject.In[0]);
        if(statics.Op!=Op.Load||statics.Type!=VT.I64)return;
        var (klass,klassOffset)=Split(statics.In[0]);
        if(klassOffset!=program.Klass.StaticFields||klass.Op!=Op.SlotValue||
            program.Model.ResolveUsageSlot((ulong)klass.Imm) is not {Kind:UsageKind.TypeInfo,Type:TypeDefSig t}||
            t.Definition is not {IsValueType:false,IsGenericDefinition:false} owner)
            return;
        var fields=owner.Fields.Where(f=>f.IsStatic&&!f.IsLiteral&&f.Offset==offset&&
            f.Type is TypeDefSig&&ReferenceEquals(f.Type.Definition,owner)).ToArray();
        if(fields.Length!=1)return;

        // Direct and unique definition, with an exactly matching class and
        // a nonvirtual/nonconstructor instance signature.
        if(!program.Model.MethodsByAddress.TryGetValue(ci.Target,out var methods)||methods.Count!=1||
            methods[0] is not {IsStatic:false,IsVirtual:false,IsAbstract:false,IsConstructor:false,IsGenericDefinition:false} callee||
            !ReferenceEquals(callee.DeclaringType,owner)||
            program.RangeOf(ci.Target) is not {} range||
            !Arm64ReceiverProof.IsUnused(program.Model.Image,range.Start,range.End))return;

        int index=ci.Slots.FindIndex(s=>s.Kind==ArgSlotKind.IntReg&&s.Index==0);
        if(index<0||index>=call.In.Length||ReferenceEquals(call.In[index],checkedObject))return;
        int readAt=guard.Nodes.IndexOf(checkedObject);
        if(readAt<0||checkedObject.Dead)return;
        bool crossesEffect=guard.Nodes.Skip(readAt+1).Any(n=>!n.Dead&&n!=guard.Terminator&&n.IsEffect);
        // An earlier call may have overwritten x0 after the exact checked
        // instance was saved. Keep that call and reuse the original Load node;
        // do not read the static field again at the call. HirBuilder captures a
        // Load that crosses a call/store (or leaves its block) at its original
        // position. The null check still occurs after those earlier effects:
        // FirstDirectCall permits no heap effect between the guard and callee.
        // This extension requires the precise original native direct transfer,
        // in addition to the unique metadata target and unused-x0 entry proof.
        if(crossesEffect&&!Arm64ReceiverProof.ExactDirectTransfer(program.Model.Image,call.Addr,ci.Target,call.Op==Op.TailCall))return;
        call.In[index]=checkedObject;
        _result.ReceiverNotes.Add($"guarded receiver at 0x{call.Addr:X} to 0x{ci.Target:X} via {owner.ReflectionName}::{fields[0].Name}");
    }
}
