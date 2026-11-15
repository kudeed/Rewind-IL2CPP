namespace Rewind.Analysis.Ir;

/// <summary>
/// On-the-fly SSA construction (Braun, Buchwald, Hack et al., "Simple and Efficient Construction of Static
/// Single Assignment Form"). Machine locations are numbered variables; reads resolve to the reaching definition,
/// inserting phi nodes only where control flow really merges different values.
/// </summary>
public sealed class SsaBuilder
{
    private readonly Function _fn;
    private readonly VT[] _varTypes;
    private readonly Dictionary<Block, Node?[]> _defs = [];
    private readonly Dictionary<Block, List<(int Var, Node Phi)>> _incomplete = [];
    private readonly HashSet<Block> _sealed = [];
    private readonly Dictionary<Node, Node> _forward = [];
    private readonly Dictionary<Node, List<Node>> _phiUsers = [];
    private readonly Dictionary<Node, int> _phiVar = [];

    private readonly Func<int, Node> _entryValue;

    /// <param name="entryValue">
    /// Supplies the value a variable holds on entry to the function; defaults to a Param node recorded in
    /// <see cref="Function.Params"/> under the variable's number.
    /// </param>
    public SsaBuilder(Function fn, VT[] varTypes, Func<int, Node>? entryValue = null)
    {
        _fn = fn;
        _varTypes = varTypes;
        _entryValue = entryValue ?? DefaultEntryValue;
    }

    private Node DefaultEntryValue(int variable)
    {
        if (!_fn.Params.TryGetValue(variable, out Node? param))
        {
            param = _fn.NewNode(Op.Param, _varTypes[variable], null);
            param.Imm = variable;
            _fn.Params[variable] = param;
        }
        return param;
    }

    private Node?[] Defs(Block b)
    {
        if (!_defs.TryGetValue(b, out Node?[]? d)) _defs[b] = d = new Node?[_varTypes.Length];
        return d;
    }

    /// <summary>Follows replacements made when trivial phis were removed.</summary>
    public Node Resolve(Node n)
    {
        while (_forward.TryGetValue(n, out Node? next)) n = next;
        return n;
    }

    public void Write(int variable, Block block, Node value) => Defs(block)[variable] = value;

    public Node Read(int variable, Block block)
    {
        Node? local = Defs(block)[variable];
        return local != null ? Resolve(local) : ReadRecursive(variable, block);
    }

    public bool IsSealed(Block b) => _sealed.Contains(b);

    private Node NewPhi(int variable, Block block)
    {
        Node phi = _fn.NewNode(Op.Phi, _varTypes[variable], block);
        block.Phis.Add(phi);
        _phiVar[phi] = variable;
        return phi;
    }

    private Node ReadRecursive(int variable, Block block)
    {
        Node value;
        if (!_sealed.Contains(block))
        {
            value = NewPhi(variable, block);
            if (!_incomplete.TryGetValue(block, out var list)) _incomplete[block] = list = [];
            list.Add((variable, value));
        }
        else if (block.Preds.Count == 0)
        {
            // Entry: the value the location held when the function was called.
            value = _entryValue(variable);
        }
        else if (block.Preds.Count == 1)
        {
            value = Read(variable, block.Preds[0]);
        }
        else
        {
            Node phi = NewPhi(variable, block);
            Write(variable, block, phi); // break cycles before visiting predecessors
            value = AddPhiOperands(variable, phi);
        }
        Write(variable, block, value);
        return value;
    }

    private Node AddPhiOperands(int variable, Node phi)
    {
        var inputs = new Node[phi.Block!.Preds.Count];
        for (int i = 0; i < inputs.Length; i++)
        {
            Node operand = Read(variable, phi.Block.Preds[i]);
            inputs[i] = operand;
            if (operand.Op == Op.Phi && !ReferenceEquals(operand, phi))
            {
                if (!_phiUsers.TryGetValue(operand, out List<Node>? users)) _phiUsers[operand] = users = [];
                users.Add(phi);
            }
        }
        phi.In = inputs;
        return TryRemoveTrivialPhi(phi);
    }

    private Node TryRemoveTrivialPhi(Node phi)
    {
        if (_forward.ContainsKey(phi)) return Resolve(phi);
        Node? same = null;
        foreach (Node raw in phi.In)
        {
            Node operand = Resolve(raw);
            if (ReferenceEquals(operand, same) || ReferenceEquals(operand, phi)) continue;
            if (same != null) return phi; // merges at least two distinct values
            same = operand;
        }
        same ??= _fn.NewNode(Op.Undef, phi.Type, null);

        _forward[phi] = same;
        phi.Dead = true;
        phi.Block!.Phis.Remove(phi);

        // Removing this phi may make phis that used it trivial too.
        if (_phiUsers.TryGetValue(phi, out List<Node>? users))
        {
            foreach (Node user in users.ToArray())
                if (!user.Dead && !ReferenceEquals(user, phi))
                    TryRemoveTrivialPhi(user);
            if (same.Op == Op.Phi)
            {
                if (!_phiUsers.TryGetValue(same, out List<Node>? sameUsers)) _phiUsers[same] = sameUsers = [];
                sameUsers.AddRange(users);
            }
        }
        return Resolve(same);
    }

    /// <summary>Declares that all predecessors of <paramref name="block"/> have been processed.</summary>
    public void Seal(Block block)
    {
        if (!_sealed.Add(block)) return;
        if (_incomplete.Remove(block, out var pending))
            foreach (var (variable, phi) in pending)
                if (!phi.Dead)
                    AddPhiOperands(variable, phi);
    }

    /// <summary>Rewrites every node input through the trivial-phi replacements. Call once construction is done.</summary>
    public void Finish()
    {
        foreach (Block b in _fn.Blocks)
        {
            foreach (Node phi in b.Phis) RewriteInputs(phi);
            foreach (Node n in b.Nodes) RewriteInputs(n);
        }
    }

    private void RewriteInputs(Node n)
    {
        for (int i = 0; i < n.In.Length; i++)
        {
            Node input = n.In[i];
            if (_forward.Count != 0 && _forward.ContainsKey(input)) n.In[i] = Resolve(input);
        }
    }

    public int VariableOf(Node phi) => _phiVar.GetValueOrDefault(phi, -1);
}
