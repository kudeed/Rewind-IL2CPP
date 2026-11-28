using Rewind.Binary;

namespace Rewind.Analysis.Arm64;

/// <summary>Proves incoming x0 independence through bounded, exact direct callee entries. Unknown ranges and recursion reject.</summary>
public static class Arm64DirectReceiverProof
{
    public static bool IsUnused(ProgramAnalysis program,ulong start,ulong end,bool allowArglessThrow=false)
    {
        (ulong Start,ulong End)? Resolve(ulong target)
        {
            var model=program.Model;
            if(!model.MethodsByAddress.TryGetValue(target,out var methods)||methods.Count!=1||
               model.InstsByAddress.ContainsKey(target)||methods[0].Address!=target||
               methods[0].IsGenericDefinition||methods[0].DeclaringType.IsGenericDefinition||
               program.RangeOf(target) is not {} range)return null;
            return (range.Start,range.End);
        }
        return Through(program.Model.Image,start,end,Resolve,allowArglessThrow?
            target=>program.Helpers.KindAt(target)==Rewind.Analysis.Runtime.HelperKind.ThrowNullReference:null);
    }

    public static bool Through(NativeImage image,ulong start,ulong end,
        Func<ulong,(ulong Start,ulong End)?> resolve,Func<ulong,bool>? arglessThrow=null)
    {
        var cache=new Dictionary<(ulong Start,ulong End),bool>();var active=new HashSet<ulong>();int entries=0;
        bool Visit(ulong at,ulong limit,int depth)
        {
            if(depth>8||active.Contains(at))return false;
            if(cache.TryGetValue((at,limit),out bool known))return known;
            if(++entries>32)return false;
            active.Add(at);
            bool result=Arm64ReceiverProof.IsUnused(image,at,limit,arglessThrow:arglessThrow,independentCall:target=>
                resolve(target) is {} callee&&callee.Start==target&&Visit(callee.Start,callee.End,depth+1));
            active.Remove(at);cache[(at,limit)]=result;return result;
        }
        return Visit(start,end,0);
    }
}
