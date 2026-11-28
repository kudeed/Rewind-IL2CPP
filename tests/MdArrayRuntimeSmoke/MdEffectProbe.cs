using System.Reflection;
using System.Security.Cryptography;
using System.Text.Json;
using Rewind.Analysis.Hir;
using Rewind.Analysis.Recover;
using Rewind.Model;
using Rewind.Runtime;
using Rewind.Output;
using RuntimeObject = System.Runtime.CompilerServices.RuntimeHelpers;

internal static class MdEffectProbe
{
    internal static void Run(Il2CppModel model, AssemblyEmitter emitter, BodyEmitter bodies, string dest)
    {
        Directory.CreateDirectory(dest);
        MethodDef maze = model.Methods.Single(m => m.DeclaringType.FullName == "Unicorn.MazeManager" && m.Name == "get_Maze");
        MethodDef target = model.Methods.Single(m => m.DeclaringType.FullName == "Unicorn.MazeManager" && m.Name == "get_SpecialMazeFloor");
        MethodDef range = model.Methods.Single(m => m.DeclaringType.FullName == "UnityEngine.Random" && m.Name == "Range" &&
            m.ReturnType is PrimitiveSig { Element: Il2CppTypeEnum.I4 } && m.Parameters.Length == 2 && m.Parameters.All(p => p.Type is PrimitiveSig { Element: Il2CppTypeEnum.I4 }));
        var type = (ArraySig)maze.ReturnType;
        FieldDef field = maze.DeclaringType.Fields.Single(f => !f.IsStatic && f.Type.Key == type.Key);
        TypeSig integer = model.Sigs.Primitive(Il2CppTypeEnum.I4), obj = model.Sigs.Primitive(Il2CppTypeEnum.Object);
        MethodDef ArrayMethod(string name, int count) => model.Methods.Single(m => m.DeclaringType.FullName == "System.Array" && m.Name == name && !m.IsStatic &&
            m.Parameters.Length == count && m.Parameters.All(p => p.Type.Key == integer.Key));
        var rows = new List<object>();
        foreach (string mode in new[] { "call", "field" })
        {
            var h = new HMethod { Method = target }; var block = new HBlock(); h.Blocks.Add(block);
            var builder = (HirBuilder)RuntimeObject.GetUninitializedObject(typeof(HirBuilder));
            void Set(string name, object value) => typeof(HirBuilder).GetField(name, BindingFlags.Instance | BindingFlags.NonPublic)!.SetValue(builder, value);
            Set("_h", h); Set("_cur", block); Set("_int", integer); Set("_object", obj);
            Set("_mdGetLowerBound", ArrayMethod("GetLowerBound", 1));
            Set("_mdGetValue", ArrayMethod("GetValue", 2));
            var self = new HArg(-1) { Type = maze.DeclaringType.Sig };
            HExpr array = mode == "call"
                ? new HCall { Method = maze, This = self, Type = type }
                : new HField { Field = field, Object = self, Type = type };
            HExpr Index(int marker) => new HCall { Method = range, Arguments = [new HConst(marker, integer), new HConst(marker + 1, integer)], Type = integer };
            var member = typeof(HirBuilder).GetMethod("MdElementRead", BindingFlags.Instance | BindingFlags.NonPublic)!;
            HExpr expression = (HExpr)member.Invoke(builder, [array, type, Index(10), Index(20), 0x20738A0UL])!;
            block.Statements.Add(new HReturn(expression)); HirCleanup.Run(h);
            string? error = bodies.Emit(target, h);
            if (error != null || h.Problems.Count != 0) throw new Exception("effect probe emit " + error);
            string file = Path.Combine(dest, mode + ".dll"); emitter[target].Module.Assembly.Write(file);
            File.WriteAllText(Path.Combine(dest, mode + ".hir.txt"), HirPrinter.Print(h));
            File.WriteAllText(Path.Combine(dest, mode + ".il.txt"), string.Join("\n", emitter[target].Body.Instructions));
            rows.Add(new { mode, token = target.Token, source_sha256 = Convert.ToHexString(SHA256.HashData(File.ReadAllBytes(file))).ToLowerInvariant(),
                field = field.Name, description = "Real MdElementRead and BodyEmitter; effectful producer expressions exercise native argument-before-dereference contract." });
        }
        File.WriteAllText(Path.Combine(dest, "effects-manifest.json"), JsonSerializer.Serialize(rows, new JsonSerializerOptions { WriteIndented = true }));
    }
}
