using System.Security.Cryptography;
using Rewind.Binary;
using Rewind.Model;
using Rewind.Metadata;
using Rewind.Analysis;
using Rewind.Analysis.Recover;
using Rewind.Analysis.Runtime;
if (args.Length != 4) throw new ArgumentException("native ELF, metadata, signature file, output directory required");
byte[] native = File.ReadAllBytes(args[0]), metadata = File.ReadAllBytes(args[1]);
static string Sha(byte[] bytes) => Convert.ToHexString(SHA256.HashData(bytes)).ToLowerInvariant();
if (Sha(native) != "f0808ccac104a950c6b99a3f4a148c21ae0daed078105714b14ac2b58f1dd583" ||
    Sha(metadata) != "71482caf047b22970845f0f2e733ffe9b23e6c7ba7a07ba623fb16937b3f6c1d")
    throw new ArgumentException("This native regression fixture requires the hash-bound mj0 input pair");
UnityVersion.TryParse("6000.3.12f1", out var unity);
var model = Il2CppModel.Load(NativeImage.Load(native, "libil2cpp.so"), metadata, unity);
var found = HelperDiscovery.Discover(model, [args[2]], _ => { });
var program = new ProgramAnalysis(model, found.Helpers, found.Context);
MdMutationProbe.Run(model, program, new MethodPipeline(program), args[3]);

var emitter = new Rewind.Output.AssemblyEmitter(model); emitter.Build();
var bodies = new Rewind.Output.BodyEmitter(emitter, model) { RawAllocator=program.RawAllocator, TypeFromHandle=program.TypeFromHandle };
MdEffectProbe.Run(model, emitter, bodies, Path.Combine(args[3], "effects"));
