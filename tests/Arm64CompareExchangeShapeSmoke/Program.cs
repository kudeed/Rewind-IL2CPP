using System.Buffers.Binary;
using Rewind.Analysis.Runtime;

static byte[] Bytes(params uint[] words)
{
    var bytes = new byte[words.Length * 4];
    for (int i = 0; i < words.Length; i++) BinaryPrimitives.WriteUInt32LittleEndian(bytes.AsSpan(i * 4), words[i]);
    return bytes;
}
static void Check(bool condition, string label)
{
    if (!condition) throw new Exception(label);
}
var wrapper = Bytes(0xA9BF4FFE,0xAA0203F3,0xAA0003E2,0xAA1303E0,
    0x94000010,0xEB13001F,0xD5033BBF,0x9A800260,0xA8C14FFE,0xD65F03C0);
var atomic = Bytes(0xD503245F,0x90000010,0x39400210,0x34000070,0xC8E0FC41,
    0xD65F03C0,0xAA0003F0,0xC85FFC40,0xEB10001F,0x54000061,0xC811FC41,0x35FFFF91,0xD65F03C0);
Check(Arm64CompareExchangeShape.TryGetAtomicTarget(wrapper,0x1000,out ulong target)&&target==0x1050,"forward BL");
BinaryPrimitives.WriteUInt32LittleEndian(wrapper.AsSpan(16),0x97FFFFF0);
Check(Arm64CompareExchangeShape.TryGetAtomicTarget(wrapper,0x1000,out target)&&target==0xFD0,"backward BL");
Check(Arm64CompareExchangeShape.IsOutlinedAtomic(atomic),"positive atomic");
BinaryPrimitives.WriteUInt32LittleEndian(atomic.AsSpan(4),0xB0000030);
BinaryPrimitives.WriteUInt32LittleEndian(atomic.AsSpan(8),0x3952C210);
Check(Arm64CompareExchangeShape.IsOutlinedAtomic(atomic),"relocated feature flag");
Check(!Arm64CompareExchangeShape.TryGetAtomicTarget(wrapper.AsSpan(0,36),0x1000,out _),"truncated wrapper");
Check(!Arm64CompareExchangeShape.IsOutlinedAtomic(atomic.AsSpan(0,48)),"truncated atomic");
foreach(int i in new[]{0,1,2,3,4,5,6,7,8,9}) {
    var changed=(byte[])wrapper.Clone();
    changed[4*i]^=1;
    if(i==4) changed[4*i+3]=0x14; // replace BL by B
    Check(!Arm64CompareExchangeShape.TryGetAtomicTarget(changed,0x1000,out _),"wrapper mutation "+i);
}
foreach(int i in Enumerable.Range(0,13)) {
    var changed=(byte[])atomic.Clone();changed[4*i]^=1;
    Check(!Arm64CompareExchangeShape.IsOutlinedAtomic(changed),"atomic mutation "+i);
}
Console.WriteLine("ARM64_COMPARE_EXCHANGE_SHAPE_PASS positive=4 negative=25");
