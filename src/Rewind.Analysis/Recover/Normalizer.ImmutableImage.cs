using Rewind.Analysis.Ir;

namespace Rewind.Analysis.Recover;

public sealed partial class Normalizer
{
    // The lifter already folds literal-address immutable reads. Merging an
    // identical address on several paths can hide it until SSA cleanup.
    private bool FoldImmutableImageLoads()
    {
        if(Environment.GetEnvironmentVariable("REWIND_NO_LATE_IMMUTABLE_IMAGE_LOADS")!=null)return false;
        int count=0;
        foreach(var block in _fn.Blocks)
        foreach(var node in block.Nodes)
        {
            if(node.Dead||!ImmutableImageLoad.TryRead(program.Model.Image,node,out long bits))continue;
            _replace[node]=_b.Const(node.Type,bits);node.Dead=true;count++;
        }
        if(count==0)return false;
        ApplyReplacements();
        foreach(var block in _fn.Blocks)block.Nodes.RemoveAll(node=>node.Dead);
        _result.ReceiverNotes.Add($"proven late immutable image literals: {count} loads");
        return true;
    }
}
