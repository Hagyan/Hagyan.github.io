# MAIS-O11: object-language trace access

23 September 2026 · Supplement to the consolidated progress report

## Result and scope

This milestone supplies literal first-order arithmetic formula syntax,
capture-avoiding substitution, a small Enderton-compatible Hilbert calculus,
and object-calculus proofs of access to every entry of the existing compact
trace. It also assembles the entry formulas into a program-specialized trace
formula and verifies its exact agreement with the previous typed checker.

For every straight-line arithmetic program `p : Program n`, let `T_p` be the
closed arithmetic term obtained by expanding its existing trace-packing
definitions. There is a first-order arithmetic formula `Trace_p(z)` such that:

1. For every natural-number value of `z`, including malformed trace codes,
   `Trace_p(z)` is true in the standard natural-number structure if and only
   if `checkTrace p z = true`.
2. The finite object calculus has a derivation of `Trace_p(T_p)` with at most
   **`n * (14*n + 10) + 3` proof-tree nodes**.
3. A corresponding lookup assertion for entry `i < n` has a derivation with
   at most **`14*i + 7` proof-tree nodes**.
4. The witness term used in these proofs is **syntactically identical** to
   the expansion of the previously constructed compact packing definitions.
   The connection is not merely equality of their interpreted numbers.

All four statements are Lean-verified. Neither part of MAIS-O11 is resolved
for ordinary PA-bin. In particular, the bounds above count proof-tree nodes,
**not written characters**. `Trace_p` is a family indexed in the metatheory
by the program, not a single uniform PA formula receiving a program code.

## 1. The arithmetic formulas

Use the earlier pairing polynomial

\[
\pi(a,b)=(a+b)^2+a+1,
\qquad V(l,s,v)=\pi(l,\pi(s,v)).
\]

The formulas below use only equality, binary-numeral term constructors,
addition, multiplication, implication, negation, and universal quantification.
Existential quantification and conjunction are logical abbreviations:
`exists f := not (forall (not f))` and
`conj A B := not (A -> not B)`.

For each fixed natural index `i`, define:

\[
\begin{aligned}
L_0(z,l,s,v)&\equiv\exists t\;z=\pi(V(l,s,v),t),\\
L_{i+1}(z,l,s,v)&\equiv
\exists h\,\exists t\;[z=\pi(h,t)\land L_i(t,l,s,v)].
\end{aligned}
\]

The implementation uses finite de Bruijn variable contexts. Lifting and
simultaneous substitution prevent capture underneath quantifiers. The
substitution and instantiation semantic lemmas are proved, not assumed.

The theorem `lookup_realize` states exactly:

\[
\mathbb N\models L_i(z,l,s,v)
\quad\Longleftrightarrow\quad
\operatorname{readValue}(z,i)=\operatorname{some}(l,s,v).
\]

The reverse implication needs more than the earlier decoder round-trip
theorem: it must exclude accidental successful decodings of malformed codes.
The new lemmas `unpair_some_iff` and `decodeValue_some_iff` prove that a
successful decode is exactly a pairing-polynomial representation. The
induction for `lookup_realize` then follows the two displayed formulas.
`lookup_zero_rejected` covers every missing-entry query against the empty
trace code. Extra irrelevant entries remain permitted, matching the old checker.

The unrolling is finite for each index. It is **not** a formalization of one
uniform sequence-access formula with `i` as a free arithmetic variable.

## 2. Genuine object-level derivations

The new `Derivation` type has only the following axiom families and rule:

- Universally closed variable reflexivity: `forall x, x = x`.
- Capture-avoiding universal instantiation: `(forall x, A) -> A[t/x]`.
- The propositional tautology `(A -> not B) -> (B -> not A)`.
- The propositional tautology `A -> (B -> conj A B)`.
- Modus ponens.

These are legal cases of the Enderton logical axioms (including universal
closure of variable reflexivity) and MP. The project does not add semantic
truth, trace acceptance, or arbitrary arithmetic equations as inference rules.
Its calculus is a restricted object language, distinct from Lean's metatheory.
The full file checker and its axiom classifier have not been implemented.

In particular, `t=t` is **derived**, not added as a shortcut axiom: use the
universal reflexivity axiom, its instantiation axiom, and MP. This costs three
nodes. Existential introduction is also derived. From a proof of `A[t/x]`:

1. Instantiate `forall x, not A` to get `not A[t/x]` conditionally.
2. Use the displayed contraposition tautology.
3. Apply MP to obtain `A[t/x] -> not (forall x, not A)`.
4. Apply MP using the supplied proof.

This adds four nodes. Conjunction introduction adds three nodes beyond its
two input proof trees.

For the head entry of a symbolic packed list, choose its actual tail as the
existential witness. The remaining equation expands to reflexivity. Thus
the base lookup proof uses `3+4=7` nodes.

For each preceding entry, choose its head and tail, combine the reflexive
decomposition equation with the recursively supplied lookup proof, then
introduce the two existential quantifiers. The additional cost is
`3+3+4+4=14` nodes. Therefore access at index `i` has a proof of at most
`14*i+7` nodes. `lookupProof` is an explicit structural proof constructor;
`lookup_within` certifies existence of proofs with this bound.

These proofs never evaluate the enormous packed integer or run its
bounded-search decoder. They work with symbolic arithmetic terms.

## 3. Connection to the old compact witness

The previous compiler defines source summaries and then packs the trace
tail-first. Its arithmetic expression for pairing is literally the same
polynomial used above. `packRefs_expansion` proves the expanded syntax
matches a nested list of those pairing terms. `packedRoot_exact` specializes
this identity to a program's complete trace.

Consequently `packedRoot_lookup_within` supplies object-level lookup proofs
about the term represented by the **existing compact definitions**, without
assuming an additional PA equality proof that identifies two different
representations.

`programTraceTerm_eval` and `compiledTraceTerm_eval` also retain the numerical
connections to the previous trace code and packed witness. For a quotation
grammar, the earlier `compile_correct` and `compiled_expansion_value` identify
each summary's denotation with the source fragment's length, scale, and value.
Those semantic connections are not themselves new PA proofs of an expansion
predicate.

## 4. A whole-trace formula and its proof bound

For each `p : Program n`, take the finite conjunction

\[
\operatorname{Trace}_p(z)=
\bigwedge_{i<n} L_i(z,L_{p,i},S_{p,i},V_{p,i}),
\]

where the three terms are the expanded symbolic registers of the program.
For an empty conjunction use `0=0`.

The previous checker accepts exactly when every needed entry equals the
program's interpreted register value, by `checkTrace_sound` and
`checkTrace_of_lookup`. Combining these facts with `lookup_realize` gives
`traceFormula_realize`, the equivalence for arbitrary input codes.

Each entry proof has at most `14*n+7` nodes. Combining `n` entries by the
three-node conjunction construction, starting from a three-node proof of the
empty conjunction, gives

\[
n\bigl((14n+7)+3\bigr)+3=14n^2+10n+3.
\]

This is `traceFormula_within`. The estimate is intentionally coarse.
For the earlier 64-doubling example there are 65 source definitions, giving
a whole-trace bound of 59,803 nodes and a last-entry bound of 903 nodes.
These numbers are **not** measured or minimum PA-bin file lengths.

## 5. What this closes, and what it does not

The earlier trace milestone only had a typed Lean checker, a compact witness,
and semantic correctness. There are now explicit arithmetic formulas and
finite object-calculus derivations of their canonical witness instances.
The proof constructors do not take trace correctness as an axiom.

Three distinctions remain essential:

1. **Program-specialized versus uniform.** `Trace_p` changes with `p`, and
   `L_i` changes with `i`. We still need one fixed arithmetic relation for the
   checker and short PA proofs connecting its instances to these specialized
   formulas. Standard-model equivalence alone is not that internal proof.
2. **Inference count versus written length.** Expanded terms in the current
   proof trees can be enormous. The old witness has a small abbreviation
   representation, but the complete derivations still need a verified
   serialized representation that reuses those definitions, charges formulas,
   variables, identifiers and line references, and respects binder scope.
   A node bound cannot be substituted for that character bound.
3. **Trace checking versus the full PA proof checker.** Source-byte parsing,
   full Enderton axiom recognition, substitution and generalization checks,
   and agreement with the actual fixed `Bew` remain unfinished.

No PA model, consistency assumption, polynomial proof-cost hypothesis, or
custom Lean axiom is supplied to the new main theorems. Their conclusion is
about the explicitly defined formula family and restricted object calculus.
This is progress on the report's second implementation obligation, not an
instance of the entire `QuantitativeLobTools` interface.

The next concrete implementation target is to serialize the symbolic lookup
proofs against the existing compact term definitions, with a checked byte
bound. The uniform arithmetic relation and its internal equivalence must
then be supplied before claiming polynomial internalization for PA-bin.

## 6. Certificate and reproduction

The new standalone project is `MAISO11ArithmeticPass`, pinned to Lean 4.19.0,
using Core/Std only. It includes the unchanged quotation dependencies.

```bash
lake build
lake env lean -DwarningAsError=true Audit.lean
```

New files:

- `PAFormula.lean`: arithmetic terms, formulas, substitution, semantic lemmas,
  Hilbert derivations, derived reflexivity/existential introduction, and node
  counting.
- `PairingGraph.lean`: exact decoder graphs, lookup formulas and proofs,
  connection to compact packing syntax, and whole-trace equivalence/bounds.
- `Audit.lean`: precise theorem types, inference constructors, axiom audit,
  and small boundary checks.

The principal names are in namespace `MAISO11.Arithmetic`:

| Declaration | Statement |
|---|---|
| `lookup_realize` | Arithmetic lookup formula agrees exactly with `readValue`. |
| `lookupProof` | Explicit object-calculus proof constructor for a symbolic entry. |
| `lookup_within` | Entry proof exists within `14*i+7` nodes. |
| `packedRoot_exact` | Syntactic agreement with the old packing compiler's expansion. |
| `packedRoot_lookup_within` | Entry proof for the actual compact witness's expansion. |
| `traceFormula_realize` | Specialized arithmetic trace formula agrees with `checkTrace`. |
| `traceFormula_within` | Canonical trace instance has a proof within `14*n^2+10*n+3` nodes. |

The dependency audit uses only Lean's standard `propext`, `Quot.sound`, and,
for classical semantic equivalences, `Classical.choice`. The main
`traceFormula_within` theorem depends only on `propext` and `Quot.sound`.
There are no admitted proofs, custom axiom declarations, unsafe declarations,
or `native_decide` proofs. `checked-output.txt` records a clean build and
audit; `SHA256SUMS` identifies the delivered bytes.
