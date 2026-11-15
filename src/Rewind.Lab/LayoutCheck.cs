using Rewind.Model;

namespace Rewind.Lab;

/// <summary>
/// Checks the computed layout rules against the offsets IL2CPP recorded: for every non-generic type, laying the
/// fields out from scratch must reproduce the recorded offsets and size.
/// </summary>
internal static class LayoutCheck
{
    public static int Run(Il2CppModel model)
    {
        var calc = new LayoutCalculator(model);
        int header = 2 * model.Image.PointerSize;
        int types = 0, typeOk = 0, fields = 0, fieldOk = 0, sizeOk = 0, skipped = 0;
        var samples = new List<string>();

        foreach (TypeDef def in model.Types)
        {
            if (def.IsInterface || def.GenericParameters.Length != 0 || def.IsEnum) continue;
            if (def.Sizes.InstanceSize == 0) continue;
            FieldDef[] instance = def.Fields.Where(f => !f.IsStatic).ToArray();
            TypeLayout computed = calc.Recompute(def);
            if (!computed.Known)
            {
                skipped++;
                continue;
            }
            types++;
            int bias = def.IsValueType ? header : 0;
            bool allOk = true;
            for (int i = 0; i < instance.Length && i < computed.Fields.Length; i++)
            {
                fields++;
                int recorded = instance[i].Offset - bias;
                if (computed.Fields[i].Offset == recorded) fieldOk++;
                else
                {
                    allOk = false;
                    if (samples.Count < 25)
                        samples.Add($"{def.ReflectionName}::{instance[i].Name} ({instance[i].Type.DisplayName}): computed 0x{computed.Fields[i].Offset:X}, recorded 0x{recorded:X}");
                }
            }
            int recordedSize = (int)def.Sizes.InstanceSize - bias;
            // A type with a layout row may have an explicit size, which the fields cannot predict.
            if (computed.Size == recordedSize || !def.ClassSizeIsDefault) sizeOk++;
            else
            {
                allOk = false;
                if (samples.Count < 25)
                    samples.Add($"{def.ReflectionName}: computed size 0x{computed.Size:X}, recorded 0x{recordedSize:X} (pack {def.PackingSize}, layout 0x{def.Flags & TypeDef.LayoutMask:X})");
            }
            if (allOk) typeOk++;
        }

        Console.WriteLine($"layout check ({(calc.ReuseBaseTailPadding ? "Itanium" : "MSVC")} rules): {typeOk}/{types} types reproduce exactly " +
                          $"({fieldOk}/{fields} field offsets, {sizeOk}/{types} sizes); {skipped} skipped (unknown member sizes)");
        foreach (string s in samples) Console.WriteLine("  ! " + s);
        return 0;
    }
}
