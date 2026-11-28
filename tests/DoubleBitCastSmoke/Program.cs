using Mono.Cecil;
using Mono.Cecil.Cil;
using Rewind.Output;
using System.Reflection;
using TypeAttributes=Mono.Cecil.TypeAttributes;
using MethodAttributes=Mono.Cecil.MethodAttributes;

static void Check(bool ok,string why){if(!ok)throw new Exception(why);}
using var asm=AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("BitCastFixture",new Version(1,0)),"BitCastFixture",ModuleKind.Dll);
var mod=asm.MainModule;
var host=new TypeDefinition("Fixture","Probe",TypeAttributes.Public|TypeAttributes.Abstract|TypeAttributes.Sealed,mod.TypeSystem.Object);mod.Types.Add(host);
var pass=new DoubleBitCast();
var valueType=mod.ImportReference(typeof(ValueType));
// Cecil's fresh synthetic module can use mscorlib while its real
// imported ValueType comes from CoreLib. Use one consistent core scope.
var i64=mod.ImportReference(typeof(long));var u64=mod.ImportReference(typeof(ulong));var f64=mod.ImportReference(typeof(double));var i32=mod.ImportReference(typeof(int));
MethodDefinition Make(string name,TypeReference source,TypeReference dest,bool eh=false)
{
    var m=new MethodDefinition(name,MethodAttributes.Public|MethodAttributes.Static,dest);host.Methods.Add(m);
    m.Parameters.Add(new ParameterDefinition(source));m.Body.InitLocals=true;
    var local=new VariableDefinition(source);m.Body.Variables.Add(local);
    var il=m.Body.GetILProcessor();
    var start=Instruction.Create(OpCodes.Ldarg_0);il.Append(start);il.Emit(OpCodes.Stloc,local);il.Emit(OpCodes.Ldloca,local);il.Emit(OpCodes.Ldobj,dest);
    if(!eh)il.Emit(OpCodes.Ret);
    else{
        var result=new VariableDefinition(dest);m.Body.Variables.Add(result);il.Emit(OpCodes.Stloc,result);
        var exit=Instruction.Create(OpCodes.Ldloc,result);il.Emit(OpCodes.Leave,exit);
        var end=Instruction.Create(OpCodes.Endfinally);il.Append(end);il.Append(exit);il.Emit(OpCodes.Ret);
        m.Body.ExceptionHandlers.Add(new ExceptionHandler(ExceptionHandlerType.Finally){TryStart=start,TryEnd=end,HandlerStart=end,HandlerEnd=exit});
    }
    return m;
}
var signed=Make("Signed",i64,f64);
var unsigned=Make("Unsigned",u64,f64);
var protectedMethod=Make("Protected",i64,f64,true);
foreach(var m in new[]{signed,unsigned,protectedMethod})Check(pass.Run(m.Body,valueType)==1,"valid bitcast "+m.Name);
Check(mod.Types.Count(t=>t.Name==DoubleBitCast.HelperName)==1,"helper dedup");
var t=mod.Types.Single(t=>t.Name==DoubleBitCast.HelperName);
Check(t.IsExplicitLayout&&t.ClassSize==8&&t.Fields.Count==2&&t.Fields.All(f=>f.Offset==0),"layout metadata");
var wrong=Make("WrongWidth",i32,f64);
Check(pass.Run(wrong.Body,valueType)==0,"wrong width");host.Methods.Remove(wrong);
wrong=Make("WrongResult",i64,i32);
Check(pass.Run(wrong.Body,valueType)==0,"wrong result");host.Methods.Remove(wrong);
wrong=Make("BranchIntoRead",i64,f64);
var read=wrong.Body.Instructions.Single(i=>i.OpCode==OpCodes.Ldobj);
wrong.Body.GetILProcessor().InsertBefore(wrong.Body.Instructions[0],Instruction.Create(OpCodes.Br,read));
Check(pass.Run(wrong.Body,valueType)==0,"branch enters middle");host.Methods.Remove(wrong);
wrong=Make("WrongCore",i64,f64);
Check(pass.Run(wrong.Body,mod.TypeSystem.Object)==0,"wrong ValueType");host.Methods.Remove(wrong);
wrong=Make("Collision",i64,f64);
Check(new DoubleBitCast().Run(wrong.Body,valueType)==0,"same named existing type rejected");host.Methods.Remove(wrong);
using var stream=new MemoryStream();asm.Write(stream);
var runtime=Assembly.Load(stream.ToArray()).GetType("Fixture.Probe",true)!;
var a=runtime.GetMethod("Signed")!.CreateDelegate<Func<long,double>>();
var b=runtime.GetMethod("Unsigned")!.CreateDelegate<Func<ulong,double>>();
var c=runtime.GetMethod("Protected")!.CreateDelegate<Func<long,double>>();
var patterns=new List<ulong>{0,1,0x8000000000000000UL,0x8000000000000001UL,0x3ff0000000000000UL,0x7ff0000000000000UL,0xfff0000000000000UL,0x7ff8000000000012UL,0xfff8000000000012UL,0x7ff0000000000001UL,0xffffffffffffffffUL};
var rng=new Random(155);var bytes=new byte[8];for(int j=0;j<4096;j++){rng.NextBytes(bytes);patterns.Add(BitConverter.ToUInt64(bytes));}
foreach(var bits in patterns)
{
    var x=unchecked((long)bits);
    Check(BitConverter.DoubleToInt64Bits(a(x))==x,"signed bit identity");
    Check(BitConverter.DoubleToInt64Bits(b(bits))==x,"unsigned bit identity");
    Check(BitConverter.DoubleToInt64Bits(c(x))==x,"protected bit identity");
}
Console.WriteLine($"DOUBLE_BITCAST_SMOKE_PASS patterns={patterns.Count} calls={patterns.Count*3} negative=5 eh=1");
