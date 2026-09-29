# MAIS-O11: complete compact trace proofs with polynomial character bounds

23 September 2026. Continuation of the compact trace-conclusion milestone.

## What has now been proved

The preceding certificate bounded only the final compact trace formula and
provided a conditional accounting lemma for proof records. This certificate
discharges those conditions for a complete trace proof: every intermediate
formula has a verified size bound, every inference satisfies the specified
object-calculus rules after expansion, and all modus-ponens references point
to preceding records.

For the earlier quotation compiler's `p : Program n`, define

\[
N_n=n(14n+10)+3,\qquad D_n=2n+1,\qquad W_n=1000(n+1)^2.
\]

Lean proves that there is a structured compact proof file with at most
\(N_n\) formula records, maximum formula depth \(D_n\), maximum compact
formula weight \(W_n\), and written length at most

\[
C_n=N_n\bigl((12n+9)W_n+4N_n+14\bigr).
\]

The final record is the compact `trace n` formula from the preceding
certificate. Expansion uses the concrete dictionary containing the original
\(3n\) source-slot definitions and \(n\) packed-tail definitions.
The last expanded formula is syntactically equal to

```
traceFormula p (Term.ofClosed (packedRoot p))
```

This is a degree-five upper bound for the **entire trace proof section**.
It is deliberately loose; optimizing the exponent or constants is not part
of this milestone. Nothing here is a lower bound or a comparison between
the shortest proofs of a sentence and its Löb reflection sentence.

## Including the definition prelude

Let `g : Grammar b n`, and let \(M\) be its written grammar mass. The old
compiler proves \(n\le M\). Lean now proves the existence of a file with the
same checked structured proof section such that the concatenation

```
(compile g).wire ++ (tracePacking n).wire ++ proof.wire
```

has at most

\[
\begin{aligned}
F_b(M)={}&(6M+20)\bigl(4(b+4)M^2+3M\bigr)\\
&+(8M+20)(112M)+C_M
\end{aligned}
\]

characters. For each fixed alphabet base \(b\), this is polynomial in \(M\).
The first two summands charge the source definitions and the packed-tail
definitions. The last summand charges all formulas, tags, MP reference names,
punctuation, and newlines in the trace proof section.

This prelude contains **definitions only**. Earlier optional local equality
certificates are unnecessary for this trace-access proof, which uses
syntactic expansion of the closed definitions. Accordingly, the formula
record indices in the proof section start at zero and count formula records;
definition records do not consume these indices. Connecting this convention
to a selected PA-bin byte checker remains an explicit integration step.

## Proof construction

### 1. Logical validity is checked on expansions

`IsAxiom` has exactly the four axiom families already used in our restricted
Enderton calculus: universally closed variable reflexivity, universal
instantiation, contraposition, and conjunction introduction. Semantic truth
is not an axiom family or an inference rule.

A compact `Proof` is a tree whose leaves carry proofs that their expanded
formulas are instances of these axioms. At an MP node, Lean checks the
syntactic equality

\[
\operatorname{expand}(B)
=\operatorname{expand}(A)\to\operatorname{expand}(C).
\]

The antecedent, implication, and conclusion may use different abbreviation
spellings; their expanded formulas must match exactly. No unproved arithmetic
equality or semantic equivalence is substituted for this equality.

Term reflexivity still costs three records: the universal variable axiom,
its universal-instantiation axiom, and MP. Existential introduction is still
derived using universal instantiation, contraposition, and MP, adding four
records. These costs are not silently replaced by additional axiom rules.

### 2. Compact tails prevent repeated expansion

The compiler builds the packed list from the tail upward. The new
`compiler_chain` theorem proves that every compact tail register expands
to precisely the pairing of its head code and its next tail. The proof uses
the actual source and saved-register indices of the old compiler.

Each source-slot reference and each tail reference has weight one. A head
code, written as a pair of three slot references, has weight at most 34.
Thus an intermediate proof can introduce a head or a tail using compact
terms even when its full arithmetic expansion is enormous.

For the entry at zero-based position \(i\), `entry_small` proves:

\[
\text{records}\le14i+7,\qquad
\text{depth}\le2i+1,\qquad
\text{weight of every formula}\le1000(i+1).
\]

The head case takes seven records. Prepending an entry adds a reflexivity
proof, a conjunction introduction, and two existential introductions,
for fourteen additional records. The induction bounds the **entire proof
tree**, including instantiation and contraposition axiom formulas.

### 3. Combine the entries

`allConj_small` builds the conjunction of the lookup statements, finishing
with the same zero-equals-zero base case used in the earlier trace formula.
Its proof controls the conjunction-introduction axioms as well as the final
conjunction. `trace_small` specializes it to the compiler's entries and
establishes \(N_n,D_n,W_n\).

### 4. Turn the tree into records

`Proof.emit` appends a proof tree to an already valid prefix. It emits the
antecedent subtree first, then the implication subtree, then the MP record.
The second subtree preserves the first subtree's indices. Lean verifies:

- the extended file preserves every formula in the original prefix;
- every MP reference is a `Fin k` for the preceding prefix length \(k\);
- each emitted record satisfies the expanded axiom/MP rule;
- the final formula occupies the final record;
- the number of new records equals the proof-tree node count;
- the depth and weight bounds hold for every emitted formula.

`Records.valid_derivable` independently proves that every formula in a
valid structured file has a derivation in the earlier object calculus.
`trace_file_conclusion` connects the final expanded sentence to the exact
earlier arithmetic trace formula.

### 5. Charge the characters

The previous ledger says that \(N\) records with \(r\) available term
references, depth at most \(D\), and weight at most \(W\) have length at most

\[
N\bigl((2r+2D+7)W+4N+14\bigr).
\]

Substitution of \(r=4n\), \(D=D_n\), and \(W=W_n\) gives \(C_n\).
`compiled_trace_file_mass` adds the prelude and replaces \(n\) by \(M\)
using certified monotonicity.

## Exact scope and remaining work

This closes the previous milestone's **all-intermediate-formulas and
complete structured trace-file size** obligation. The result has no
hypothesis assuming polynomial intermediate-formula size or correctness of
the emitted inference steps: those properties are now proved.

Several different obligations remain:

1. **Byte-level checker connection.** The formal validity predicate operates
   on the structured records and their concrete dictionary expansions.
   Their serialized character lengths are certified. A complete parser
   round-trip theorem, parsing of the definition prelude, and the theorem
   that a chosen PA-bin byte checker accepts the concatenated string are
   not yet supplied. Fresh variable naming was addressed by the preceding
   level-based serializer, but that alone is not the entire parser theorem.
2. **Executable extraction.** `Proof.emit` is currently a `noncomputable def`
   using Lean's proof recursor. It is kernel checked and supports the file
   existence theorem; this package does not provide a standalone executable
   that exports the complete proof for arbitrary input programs. The
   `#eval` examples evaluate upper bounds, not exported files. This
   distinction does not invalidate the existence/length theorem.
3. **Uniform arithmetization.** The trace statement is still a family of
   program-specific arithmetic formulas, with lookup positions unrolled
   at the metalevel. It is not yet a short PA proof verifying an arbitrary
   PA-bin proof file against a fixed uniform `Bew` predicate. Trace access
   and ordinary proof-checker internalization remain distinct tasks.
4. **The open problem.** Neither MAIS-O11 part 1 nor part 2 follows from
   this certificate. Even a finished polynomial internalization theorem
   would still need a separate argument giving the requested proof-length
   separation or resolving its structural alternative.

The next integration milestone is a certified executable representation of
the definition environment and proof records, with a parser/serializer
round trip and agreement with the structured expansion rules. It should
retain the character convention above and make any required renumbering
explicit. Then the uniform checker can be arithmetized without relying on
uncertified serialization assumptions.

## Verification and assumptions

Extract the accompanying ZIP, enter `MAISO11ProofPass`, and run:

```sh
lake build
lake env lean Audit.lean
```

Lean is pinned to version 4.19.0, with no Mathlib dependency. New work is in
`CompactProof.lean`; earlier compiler, arithmetic, and compact-wire modules
are included unchanged. The archive includes a clean-build transcript and
SHA-256 checksums.

The central file-existence theorems depend on Lean's standard axioms
`propext`, `Classical.choice`, and `Quot.sound`. `Proof.emit` itself depends
on `propext` and `Quot.sound`; `Records.valid_derivable` uses `propext`.
There are no `sorry`/`admit` placeholders, no added research axioms, and no
`native_decide` calls in the Lean sources. Lean verifies the explicit formal
statements described here, not the outstanding PA-bin integration steps.
