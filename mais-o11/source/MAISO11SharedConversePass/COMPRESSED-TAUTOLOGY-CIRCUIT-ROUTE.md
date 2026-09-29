# MAIS-O11 Part 2: compressed Boolean evaluation as the tautology bridge

**27 September 2026.** This note sharpens the remaining arbitrary-tautology
case in the proposed Part 2 internalizer. It identifies a route that avoids
expanding an arbitrary propositional axiom, and separates an established
compressed-algorithm fact from the still-missing PA-bin proof certificate.
It does not prove Part 2.

## The local target

Let `G` be the PA-bin abbreviation grammar for a valid propositional-axiom
formula `F`, and let `|G|` count every written definition, fragment atom, and
identifier. Let `A_F` be the fixed arithmetic formula saying that the
canonical tautology checker accepts the code of `F` (equivalently, under a
fixed truth-table arithmetization, that `F` evaluates to true under every
Boolean assignment). The sought local compiler is:

```text
input:  G, promised to expand to a propositional tautology F
output: an actual PA-bin derivation of A_F
cost:   polynomial in |G|, with the exact Bew/quotation conventions fixed
```

The promise matters: the printer need not decide tautology. Its output proof
may contain propositional tautology axioms whose validity follows from the
promise. No claim about the polynomial-time complexity of checking those lines
is needed.

## Why the grammar route must preserve string compression

The raw PA-bin definitions form an SLP-like grammar over strings, not a tree
grammar: a definition may be an arbitrary fragment and can split connective,
token, and delimiter boundaries. Converting such a grammar into an ordinary
shared syntax tree is not a valid general step. Published work shows that
SLPs for tree traversals can be exponentially more succinct than tree
straight-line programs, while also giving polynomial-time algorithms for
some direct queries on the string-compressed tree. In particular, Boolean
expression evaluation on SLP-compressed trees is a known polynomial-time
problem. This is relevant algorithmic evidence for a route that works on the
fragment grammar directly; it is not an internal proof-length theorem.

The unary-nesting family in `PA-BIN-THIRD-AUDIT.md` is the simplest witness
to the conversion problem: a grammar of size `O(m)` can describe a Boolean
tree with a chain of depth `2^m`. An ordinary tree DAG needs `2^m` nodes for
that chain. The Boolean function of that particular context is easy (negation
parity), but that special summary does not settle arbitrary fragments.

## Circuit certificate route

The desired intermediate representation is a polynomial-size **description**
`C_G` of a Boolean evaluator whose output equals the truth value of the fully
expanded `F`. It may need to be a succinct or parameterized circuit, with
potentially exponentially many gate instances and addressable atom inputs.
We have not proved that the number of distinct propositional atoms is
polynomial in `|G|`, so a compiler cannot charge one explicit input per
expanded atom without a separate size theorem. A plain finite circuit is a
sufficient special case, not yet a justified general representation. A
circuit description, unlike an ordinary syntax-tree DAG, may summarize an
exponentially repeated context.

Assume a compiler provides all three items below with polynomial written
cost, including the macro definitions for gate names, atom codes, and the
gate-constraint formula:

1. `C_G` and a compact way to name its input and gate indices, even when its
   expansion is large;
2. a PA-bin proof of the uniform correctness statement
   `∀a (Eval_F(a) = C_G(a))`, using a compact representation of the source
   expansion and the exact chosen `Bew` formula;
3. a PA-bin proof that the primitive-recursive truth-table checker for `F`
   agrees with `Eval_F` on every assignment.

From these, the tautology record has a short internal proof. For a finite
circuit, let `v_i` be each gate's Boolean value and `E_i` its local gate
equation. The gate formula

```text
H_C := (E_1 ∧ ... ∧ E_r) → v_root
```

is a propositional tautology exactly when the circuit output is always true.
For a succinct circuit, the same gate formula must be emitted as a compressed
conjunction, with a PA proof of its uniform gate-index meaning. Since `F` is
promised tautological and `C_G` computes `F`, this gate formula's arithmetic
substitution instance is an allowed Enderton tautology axiom. PA can use that
line, the local equations defining the circuit, and items 2–3 to derive
`A_F`. All gate indices and reused bit predicates must be named through the
existing abbreviation mechanism, so the written cost is polynomial in the
circuit-description and compiler-certificate sizes.

The point at which this is noncircular is important. The generated PA-bin
proof is a proof *of the source record's arithmetic acceptance fact*. We
establish externally that the generated proof file is valid. We do not need
to prove inside that same file that its own tautology-axiom records pass the
checker. This is the legitimate use of the promised-validity condition in a
proof transformer.

## What the literature result does and does not buy

Ganardi, Hucke, Lohrey, and Nöth show that Boolean expression evaluation on
SLP-compressed tree traversals can be done in polynomial time, even though
SLPs may be exponentially more succinct than standard tree grammars. This
suggests that the missing representation should be a directly generated
circuit or a proof-producing compressed evaluator, not an expanded AST or
ordinary tree DAG.

However, a polynomial-time algorithm for one explicit assignment does not
yet give items 1–3. The Part 2 compiler needs a *uniform symbolic* circuit
with assignment-bit inputs, plus an object-PA derivation of its correctness
for all assignments. It also needs a parser from the precise PA-bin raw
fragment syntax to the compressed Boolean skeleton, including maximal
first-order subformula atoms, Gödel quotation, and the specified truth-table
program. These are not supplied by the external complexity result.

The literature result also does not imply that a TSLP conversion is
polynomial. It is not: the cited work exhibits an exponential succinctness
gap between traversal SLPs and tree grammars. The hoped-for proof object must
retain the stronger string compression or use another directly compressed
evaluation representation.

## Audit outcome and next lemma

This narrows the exact obstacle from “the tautology axiom family is too hard
to recognize” to the following proof-producing theorem:

> **Compressed tautology internalization lemma.** For the fixed PA-bin
> checker and its literal fragment grammar, every valid propositional-axiom
> record of written length `L` admits a PA-bin proof of its arithmetized
> acceptance condition of length at most `(L+1)^c` for one fixed `c`.

A sufficient route is the `C_G` compiler above with polynomial PA proof of
uniform correctness and a polynomially written gate-constraint formula. A
tree-DAG compiler is insufficient. A pure polynomial
running-time evaluator is insufficient unless its correctness proof can be
serialized uniformly inside PA-bin. Failure of either route would identify
the next specific barrier; it would not establish a lower bound for
`F_PA_bin`.

No Lean kernel check was run for this note. It is a research specification,
not a certificate. The project's current Lean files formalize selected
compressed-string and finite-summary facts, not this compiler or the fixed
`Bew` bridge.

## Reference

M. Ganardi, D. Hucke, M. Lohrey, and E. Nöth, “Tree Compression Using String
Grammars,” arXiv:1504.05535 (2015; revised 2015), especially the comparison
of SLP and tree-grammar compression and its polynomial-time Boolean
expression evaluation result. The source is available at
<https://arxiv.org/abs/1504.05535>.
