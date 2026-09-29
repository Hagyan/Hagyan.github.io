# MAIS-O11 Part 2: the promised-valid axiom compiler and fragment depth

This note investigates one *possible route* to a polynomial upper bound for
the actual PA-bin system. It proves no bound on MAIS-O11. Its purpose is to
give an exact intermediate lemma and an adversarial test for a common
shortcut. The input grammar follows `MAIS-A1.tex:100,104`: abbreviations may
name fixed **string fragments**, need not be syntactic subformulas, and may
refer to previous fragments. A literal Enderton calculus includes all
propositional tautologies as axioms (`SPEC-AUDIT.md`).

## Conditional local lemma to target

Fix a concrete PA-bin checker formula `Proof_PA_bin(m,y)`. For a file `w`
of length `L` whose only proof line is an arbitrary propositional tautology
axiom, the local construction sought by the usual *per-record*
internalization method is:

> Given a promise that `w` is valid, produce an ordinary PA-bin proof of
> `Proof_PA_bin(⌜w⌝,⌜conclusion(w)⌝)` of at most `L^c` symbols, for one
> fixed exponent `c`, and prove this output property uniformly.

Here the expanded conclusion can be exponentially long, and its
base-alphabet Gödel code can then have exponentially many *binary digits*.
An output format that literally writes every digit therefore cannot have
polynomial written length in `L`. This is a limitation on that output format,
not on arbitrary PA-bin proof files: their fragment definitions may themselves
compress a canonical numeral. The correct local target
must instead use a compact *arithmetic term / defined register / existential
witness* for the expanded conclusion code (or avoid naming it in the line
certificate), together with a polynomial written-size derivation of the
equation connecting this code to the compressed file's conclusion. One may
represent enormous numbers by nested term abbreviations; the formal size
accounting must charge the definitions, their scopes and references, not the
expanded binary numeral. In particular the agenda's estimate
`|⌜P⌝| = O(|P|)` does not imply `|⌜P⌝| = poly(L)` when `P` was obtained from
an `L`-character compressed proof file.

**This is an input/output size obstacle for a printer that expands every
numeral digit, independent of proving the axiom is a tautology.** It applies
even when the tautology has a two-gate skeleton
`Q → Q`: the fully expanded `Q` can have exponentially many characters. If
the intended internalization lemma uses the literal formula
`Bew(⌜w⌝,⌜P⌝)` with a binary numeral of the expanded Gödel code, its
conclusion already has exponential written size. To rescue a polynomial
overhead bound one needs either a proof convention allowing a compressed
representation of this numeral inside formulas at polynomial cost, or a
different construction that does not contain it. The PA-bin proof-file
abbreviation grammar permits nested string fragments, so a proof of the
compressed-numeral *construction and arithmetical denotation* is a realistic
target. The standard fixed-point ledger must track the extra definitions
and avoid writing an expanded quote at any intermediate step.

## Exponential-depth unary adversary

Choose an atomic arithmetic sentence `R`; let `H := (R → R)`, a
propositional tautology. Use one fragment `o` spelling the opening of a
fully parenthesized negation and one fragment `c` spelling its closing
delimiter. Define `o_0 := o`, `c_0 := c`, and for each `i < n` define
`o_{i+1} := o_i o_i`, `c_{i+1} := c_i c_i`. The final line writes

`A_n := o_n H c_n`.

After expansion, this is exactly `2^n` nested negations of `H`; because
`2^n` is even for `n ≥ 1`, it is itself a propositional tautology. The
written grammar and final line have polynomial length in `n` even when
every identifier uses the stipulated self-delimiting binary name. The
expanded formula has `Ω(2^n)` characters, and its syntax-tree depth is
`Ω(2^n)`. Define alternatively `B_n := A_n → A_n`; this is a tautology
for every `n` without needing to certify parity.

The exponential size of a literal positional-code numeral is robust to a
minor encoding nuisance: if the opening delimiter happens to carry digit
zero and creates leading zeros, its *distinct* closing delimiter has a
nonzero digit, and at least `2^n` closing characters remain after the first
nonzero code digit. If opening has a nonzero digit, the first character is
already nonzero. This assumes the base-alphabet coding is made injective on
strings as required for proof Gödel codes; a length-tagged variant gives the
same bound immediately.

A compiler performing one proof step per expanded connective has
exponential output on this family. The same holds for an evaluation lemma
whose proof simply inducts along the *expanded* syntax tree, even if every
individual connective receives a constant-size certificate. The expression
`B_n` shows that the tautology itself can be used as a one-line axiom in a
polynomially written proof, thanks to the fragment definitions. Hence
exponential depth alone is no lower bound on *shortest PA-bin proofs*.
For `A_n`, an algorithm can summarize a unary negation fragment as a Boolean
transformation and compose the summary under doubling; a polynomial
certificate is plausible but needs to be written in the specified object
calculus. Thus the adversary invalidates the naive expanded-syntax proof
compiler; it does not refute the desired polynomial bound.

## What reusing the tautology actually buys

For an ordinary **uncompressed** tautology `T(p_1,…,p_r)` of length `s`, a
promised-valid compiler can instantiate the same tautology with arithmetic
truth-value predicates for a valuation `v`. That instance is itself one
Enderton logical axiom. Then local gate equations can in principle derive
the corresponding statement about a fixed arithmetized Boolean evaluator
with `poly(s)` symbols; the construction does not need to decide TAUT.

The source may instead have `s = 2^{Ω(L)}`. Writing the substituted
tautology by visiting all its expanded connectives is no longer affordable.
To lift this approach, one needs a compressed-substitution theorem for
**arbitrary string fragments**, showing that both the substituted axiom and
each evaluation equation can be generated using at most `poly(L)` written
symbols *and* that the arithmetized checker recognizes their expanded
meanings. A graph of syntactic *subformulas* suffices only when every macro
boundary respects a subformula boundary; `def u := τ` permits much more.
The unary family already crosses connective boundaries with separately
shared opens and closes. A full theorem must describe an interface for
partially parsed contexts, their composition and variable binding.

Even a proof of local tautology acceptance leaves the other Enderton
families, PA arithmetic and induction, generalization, interleaved
definitions and exact formula quotation. The quantitative Löb construction
then must avoid expanded quotes at every step. These are the exact points
where the present Lean fragment checker and its shared-graph lemmas stop.

## Necessary qualification of the code-length claim

There is a tempting but false inference:

`|file w| = L` and `|P| ≤ 2^{O(L)}` imply
`|binary numeral for ⌜P⌝| = O(|P|) ≤ poly(L)`.

The final implication fails: the bound is exponential in `L`. Moreover,
the agenda defines `□P` literally with the binary numeral for the expanded
code of `P` (`MAIS-A1.tex:109–119`). Thus if a very short proof line
abbreviates a huge `P`, the standalone sentence `□P → P` itself may be
exponentially large, though a **proof file** of it may still introduce
abbreviations for its long subterms. Since the premise length `k` charges
the proof file for `□P → P`, it may already pay for constructing that code;
this can rescue the *joint polynomial in `k+n`* statement. Any valid bound
must use the actual input `k` and the ordinary *uncompressed formula length*
`n=|P|`, not merely the compressed size `L` of a line proof. The unary
adversary separates these size parameters and prevents an unjustified
`poly(L)` internalization assertion. It does **not** by itself refute
`F_PA_bin(k,n) ≤ poly(k+n)`, because `n` is already exponential in `L`.

## Intermediate formulas can exceed the final formula

Even `poly(L+|P|)` is insufficient to justify an **expanded-intermediate-line
compiler** for arbitrary proofs of `□P → P`. Fix the small tautology
`P := (R → R)` and write `C := (□P → P)`, itself a fixed propositional
tautology. For `j ≥ 1`, let `A_j` be the exponentially deep tautology of the
unary family above. The following three lines form a legitimate Enderton
derivation of `C`:

1. `A_j` (tautology axiom);
2. `A_j → C` (tautology axiom, because `C` is a tautology);
3. `C` (modus ponens on the first two lines).

Both first and second lines can reuse the polynomial written-size fragment
definitions of `A_j`; hence the whole proof file has length `poly(j)` while
`|P|` and `|C|` are constants. The *expanded intermediate* formulas have
length `2^{Ω(j)}`. A method that literally writes `⌜A_j⌝` as a binary
numeral, or emits one object-level proof step per expanded connective of
`A_j`, spends `2^{Ω(j)}` symbols even though `L+|P|=poly(j)`.

This example proves a limitation of **that method only**. The large lines
are dispensable: `C` is itself a one-line tautology axiom. It gives no lower
bound on shortest proofs of `C`, on the lengths of PA proofs of the given
file's validity, or on `F`. In a nontrivial input the giant intermediate
could be used essentially, and there is no proved normalization theorem
eliminating every such line at polynomial cost. A general per-record
compiler must therefore handle **all** compressed intermediate expressions
without embedding their expanded codes as literal binary numerals; the
alternative is a global transformation that bypasses large intermediate
lines with a proved polynomial bound.

The required positive statement for the per-record route can be phrased
without assuming a polynomial-time validity decider. For every *valid*
written PA-bin proof file `w` of length `L` with expanded final conclusion
`C`, produce a PA-bin proof of the fixed-formula statement
`Proof_PA_bin(⌜w⌝,z)`, with an object-language representation `z` of the
possibly huge code of `C`, in at most `poly(L+|C|)` symbols. The compiler
must use compact definitions for all large intermediate codes, prove their
evaluation relation at polynomial written cost, and exploit the promised
validity of each arbitrary-tautology axiom. For the actual Löb ledger,
`C = □P → P`, and `|C|` can itself grow with `|P|`; there must be an explicit
polynomial bound on the relevant formula and quotation sizes in `k+|P|`.
The existing source certificates do not establish this statement.
