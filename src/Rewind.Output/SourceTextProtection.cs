using System.Text;
using System.Text.RegularExpressions;

namespace Rewind.Output;

/// <summary>
/// Temporarily protects C# literals and comments during identifier-only text rewrites.
/// Interpolated strings remain opaque to the outer rewrite. Their expression spans
/// can be rewritten recursively, while literal text and format components stay exact.
/// </summary>
internal sealed class SourceTextProtection
{
    private readonly List<(string Placeholder, string Original)> tokens = [];
    private string markerPrefix = "";
    public string Text { get; private set; } = "";

    public static SourceTextProtection Mask(string source, Func<string, string>? rewriteExpression = null)
    {
        var result = new SourceTextProtection();
        string prefix = "__RewindProtected";
        while (source.Contains(prefix, StringComparison.Ordinal)) prefix += "_";
        result.markerPrefix = prefix;
        var output = new StringBuilder(source.Length);
        int copied = 0;
        for (int at = 0; at < source.Length;)
        {
            int end = ProtectedEnd(source, at);
            if (end <= at) { at++; continue; }
            output.Append(source, copied, at - copied);
            string id = prefix + result.tokens.Count + "__";
            bool comment = source[at] == '/' && at + 1 < source.Length
                && source[at + 1] is '/' or '*';
            string placeholder = comment ? "/*" + id + "*/" : "\"" + id + "\"";
            string original = source[at..end];
            if (rewriteExpression is not null)
                original = RewriteInterpolationExpressions(original, rewriteExpression);
            result.tokens.Add((placeholder, original));
            output.Append(placeholder);
            copied = at = end;
        }
        output.Append(source, copied, source.Length - copied);
        result.Text = output.ToString();
        return result;
    }

    public string Restore(string source)
    {
        foreach (var (placeholder, _) in tokens)
        {
            int first = source.IndexOf(placeholder, StringComparison.Ordinal);
            if (first < 0 || source.IndexOf(placeholder, first + placeholder.Length,
                    StringComparison.Ordinal) >= 0)
                throw new InvalidOperationException("An identifier rewrite altered a protected source token.");
        }
        foreach (var (placeholder, original) in tokens)
            source = source.Replace(placeholder, original, StringComparison.Ordinal);
        return source;
    }

    public string RewriteIdentifiers(string source, string pattern, MatchEvaluator rewrite) =>
        Regex.Replace(source, pattern, match => match.Value.Contains(markerPrefix, StringComparison.Ordinal)
            ? match.Value : rewrite(match));

    private static string RewriteInterpolationExpressions(string token, Func<string, string> rewrite)
    {
        int quote = 0, dollars = 0;
        bool verbatim = false;
        while (quote < token.Length && token[quote] is '$' or '@')
        {
            if (token[quote] == '$') dollars++;
            else verbatim = true;
            quote++;
        }
        if (dollars == 0 || quote >= token.Length || token[quote] != '"') return token;
        int quotes = Run(token, quote, '"');
        bool raw = quotes >= 3 && !verbatim;
        int closingBraces = raw ? dollars : 1;
        var output = new StringBuilder(token.Length);
        int copied = 0;
        for (int p = quote + (raw ? quotes : 1); p < token.Length;)
        {
            char c = token[p];
            if (!raw && !verbatim && c == '\\') { p = Math.Min(p + 2, token.Length); continue; }
            if (c == '"')
            {
                if (raw && Run(token, p, '"') < quotes) { p++; continue; }
                if (!raw && verbatim && p + 1 < token.Length && token[p + 1] == '"') { p += 2; continue; }
                break;
            }
            if (c != '{') { p++; continue; }
            int braces = Run(token, p, '{');
            if (!raw && braces >= 2) { p += 2; continue; }
            if (raw && braces < closingBraces) { p += braces; continue; }
            // In a raw string, a run longer than the delimiter has literal
            // leading braces. Expressions begin after the complete opening run.
            int start = p + (raw ? braces : 1);
            var bounds = InterpolationBounds(token, start, closingBraces);
            if (!bounds.Closed) return token; // Keep malformed input intact for diagnostics.
            output.Append(token, copied, start - copied);
            output.Append(rewrite(token[start..bounds.ExpressionEnd]));
            copied = bounds.ExpressionEnd;
            p = bounds.End;
        }
        output.Append(token, copied, token.Length - copied);
        return output.ToString();
    }

    private static int ProtectedEnd(string source, int at)
    {
        if (source[at] == '/' && at + 1 < source.Length)
        {
            if (source[at + 1] == '/')
            {
                int end = source.IndexOf('\n', at + 2);
                return end < 0 ? source.Length : end;
            }
            if (source[at + 1] == '*')
            {
                int end = source.IndexOf("*/", at + 2, StringComparison.Ordinal);
                return end < 0 ? source.Length : end + 2;
            }
        }
        if (source[at] == '\'')
        {
            for (int p = at + 1; p < source.Length; p++)
            {
                if (source[p] == '\\') { p++; continue; }
                if (source[p] == '\'') return p + 1;
            }
            return source.Length;
        }
        int quote = at, dollars = 0;
        bool verbatim = false;
        while (quote < source.Length && source[quote] is '$' or '@')
        {
            if (source[quote] == '$') dollars++;
            else verbatim = true;
            quote++;
        }
        if (quote >= source.Length || source[quote] != '"') return -1;
        int quotes = Run(source, quote, '"');
        if (quotes >= 3 && !verbatim)
        {
            for (int p = quote + quotes; p < source.Length;)
            {
                if (source[p] == '"' && Run(source, p, '"') >= quotes) return p + quotes;
                if (dollars > 0 && source[p] == '{' && Run(source, p, '{') >= dollars)
                {
                    p = InterpolationEnd(source, p + Run(source, p, '{'), dollars);
                    continue;
                }
                p++;
            }
            return source.Length;
        }
        for (int p = quote + 1; p < source.Length;)
        {
            char c = source[p];
            if (!verbatim && c == '\\') { p = Math.Min(p + 2, source.Length); continue; }
            if (c == '"')
            {
                if (verbatim && p + 1 < source.Length && source[p + 1] == '"') { p += 2; continue; }
                return p + 1;
            }
            if (dollars > 0 && c == '{')
            {
                if (p + 1 < source.Length && source[p + 1] == '{') { p += 2; continue; }
                p = InterpolationEnd(source, p + 1, 1);
                continue;
            }
            p++;
        }
        return source.Length;
    }

    private static int InterpolationEnd(string source, int at, int closingBraces)
        => InterpolationBounds(source, at, closingBraces).End;

    private static (int ExpressionEnd, int End, bool Closed) InterpolationBounds(string source, int at, int closingBraces)
    {
        int depth = 0, parentheses = 0, brackets = 0;
        for (int p = at; p < source.Length;)
        {
            // A format component is literal text. Slashes or quotes in it must
            // not be read as C# comments/strings, or the following code is hidden.
            if (source[p] == ':' && depth == 0 && parentheses == 0 && brackets == 0
                && (p == 0 || source[p - 1] != ':')
                && (p + 1 >= source.Length || source[p + 1] != ':'))
            {
                int expressionEnd = p;
                for (p++; p < source.Length; p++)
                    if (source[p] == '}' && Run(source, p, '}') >= closingBraces)
                        return (expressionEnd, p + closingBraces, true);
                return (expressionEnd, source.Length, false);
            }
            int tokenEnd = ProtectedEnd(source, p);
            if (tokenEnd > p) { p = tokenEnd; continue; }
            if (source[p] == '{') depth++;
            else if (source[p] == '(') parentheses++;
            else if (source[p] == ')') parentheses--;
            else if (source[p] == '[') brackets++;
            else if (source[p] == ']') brackets--;
            else if (source[p] == '}')
            {
                if (depth > 0) depth--;
                else if (Run(source, p, '}') >= closingBraces) return (p, p + closingBraces, true);
            }
            p++;
        }
        return (source.Length, source.Length, false);
    }

    private static int Run(string source, int at, char character)
    {
        int end = at;
        while (end < source.Length && source[end] == character) end++;
        return end - at;
    }
}
