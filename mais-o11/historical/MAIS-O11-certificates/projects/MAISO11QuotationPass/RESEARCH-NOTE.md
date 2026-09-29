# PA-bin: polynomial quotation and a checked arithmetic trace

22 September 2026

**Status:** Lean 4.19.0 verifies the raw-string quotation compiler, an arithmetic encoding of its witness trace, a checker for that trace, polynomial character bounds, and the associated local equality proof records. Polynomial internalization for the complete PA-bin checker, and both requested parts of MAIS-O11, remain unproved.

The new result supplies compact arithmetic terms for the Gödel codes of expanded fragments and for a single integer encoding all their values. It removes a concrete size obstacle in the internalization construction. Its statement starts with a well-scoped, parsed abbreviation grammar; it does not assume that an efficient internalizer already exists.

## The theorem proved in this pass

Fix an alphabet with (b\ge 2) characters, numbered (0,\ldots,b-1). A grammar is a sequence of fresh definitions. Each right-hand side is an arbitrary list of literal characters and references to earlier definitions. Empty strings are allowed. A fragment need not be a complete term or formula.

Let

\[
M=\#\{\text{definitions}\}+\sum_i\#\{\text{atoms in the }i\text{th right-hand side}\}.
\]

An atom is one literal character or one occurrence of an earlier abbreviation. For a correctly lexed source file, this mass is bounded by its written character count: every atom consumes at least one character and every record has a tag or header. **The complete source-file lexer and that connection to its character count are not yet formalized.** The Lean budget theorem explicitly takes (M\le k) when a bound in an external budget (k) is wanted.

The implemented compiler creates three arithmetic-term definitions per source definition. If source abbreviation (i) expands to the string (w_i), their values are exactly

\[
L_i=|w_i|,\qquad S_i=b^{|w_i|},\qquad V_i=\operatorname{raw}_b(w_i).
\]

Here (\operatorname{raw}_b) is the ordinary unmarked, big-endian base-(b) value. Length is retained separately, so leading zero digits cause no information loss. For the conventional base-(b) code with a leading marker digit 1, the code is (S_i+V_i).

The arithmetic definitions use only binary numerals, addition, multiplication, and previously defined arithmetic terms. They contain no exponentiation symbol and do not print the enormous binary numeral for (S_i) or (V_i).

The complete serialized definition file has at most

\[
(6M+20)\bigl(4(b+4)M^2+3M\bigr)
\]

characters. Including the local equality certificates described below, the checked upper bound is

\[
\boxed{20+(40M+100)\bigl(4(b+4)M^2+3M\bigr).}
\]

This is cubic in (M) for each fixed alphabet. It counts the actual serialized identifiers, numeral constructors, definition headers, axiom records, modus ponens records, and line references. The estimate is intentionally coarse; no optimality claim is made.

The main Lean theorems are `compile_correct`, `compiled_expansion_value`, `compile_characters`, and `compile_certificate_characters`. These are proved for all grammars in the implemented raw-string model, not just the examples.

The trace-packing extension described below adds at most ((8n+20)(112n)) characters for a grammar with (n) definitions. Since (n\le M), the complete bound is

\[
20+(40M+100)\bigl(4(b+4)M^2+3M\bigr)+(8M+20)(112M).
\]

`compiled_bundle_characters` verifies this still-cubic bound.

## Why concatenation suffices

For strings (x,y), write their summaries as (L_x,S_x,V_x) and (L_y,S_y,V_y). Then

\[
\begin{aligned}
L_{xy}&=L_x+L_y,\\
S_{xy}&=S_xS_y,\\
V_{xy}&=V_xS_y+V_y.
\end{aligned}
\]

The empty-string summary is ((0,1,0)); a literal digit (a<b) has summary ((1,b,a)). An abbreviation reference uses the three terms already defined for it.

The compiler applies these rules directly to the list of atoms in each right-hand side. There is no parsing into subformulas, no tree-DAG conversion, and no traversal of the expanded word. In particular, the same construction handles a fragment such as the incomplete prefix `(>`.

The direct right-hand-side construction can repeat a suffix's scale expression, so it is not claimed to have linear size. The verified estimate is quadratic in that right-hand side's atom count. Summing the estimates gives a quadratic total term weight. Charging the serialized names gives the cubic bound above.

The source reference type `Fin n` enforces the rule that the (n)th definition can only refer to earlier definitions. It records definition order. A future frontend must connect that representation to the original names and original proof-file code.

## The local object-language proofs

The compiler also emits short proofs of each generated definitional equation. For a fresh arithmetic abbreviation `u := t`, it uses the following scheme after the definition has been introduced:

\[
\begin{array}{ll}
1.&\forall x\,(x=x),\\
2.&(\forall x\,(x=x))\to(u=t),\\
3.&u=t.
\end{array}
\]

Line 1 is shared across the entire file. After abbreviation expansion, line 2 is the closed-term instantiation axiom with conclusion (t=t). Line 3 follows by modus ponens. Thus the construction uses Enderton's actual generalized equality axiom and universal-instantiation axiom. It does not silently treat every closed equation (t=t) as a primitive axiom.

`LocalCertificates.lean` implements an executable checker for precisely these two axiom cases and modus ponens with earlier line indices. `compiled_localCertificate_checked` proves that all generated expanded proof-record sequences are accepted. `localFormulas_derivable` separately proves their derivability in the explicitly defined Enderton fragment.

The identifiers have the form `u` followed by a unary bit-length header, a separator `0`, and the binary digits of the index plus one. For example, index 0 is `u101`. `readIdentifier_encode` proves decoding with an arbitrary following suffix; `identifier_injective` and `fresh_register` establish that the generated names do not collide.

The Lean checker consumes structured, expanded proof records. The Lean character theorem measures a separate, explicit text serialization. A full proof of the complete text parser's agreement with that structured checker has not been supplied. An independent Python diagnostic parses and checks the generated example file; this is additional testing, not a replacement for a Lean parser theorem.

## A single arithmetic witness for the whole trace

It would not suffice to exhibit separate huge values and assume that their sequence could be written cheaply. The extension implements that packing explicitly.

Use the positive arithmetic pairing function

\[
\pi(a,b)=(a+b)^2+a+1.
\]

It contains only addition and multiplication when the square is expanded. Lean proves its injectivity, the bounds (a,b<\pi(a,b)), and correctness of a concrete bounded-search decoder. Encode one summary by

\[
\langle L,S,V\rangle=\pi(L,\pi(S,V)),
\]

and a list by (\operatorname{nil}=0) and

\[
\operatorname{cons}(v,t)=\pi(\langle v\rangle,t).
\]

`readValue_encode` proves that the decoder retrieves exactly the requested entry, including `none` for an index outside the list.

The executable `checkTrace` receives a typed arithmetic program and an integer trace code. It checks each register against its defining arithmetic recurrence, using only decoded earlier entries. It does not compare against an expanded source word. Lean proves:

* `checkTrace_sound`: every in-range entry of an accepted trace is the program's actual value;
* `checkTrace_complete`: the encoding of the actual values is accepted;
* `checkTrace_rejects_missing`: the empty trace is rejected for every nonempty program;
* `compiled_trace_sound`: for compiled grammars, every accepted entry is the correct expanded length, scale, and raw string code.

Extra entries beyond the program's register count are irrelevant to this checker. The in-range entries must all be present and correct.

The second compiler, `tracePacking`, builds the list from the tail toward the head. Each new term references the original quotation registers and the previously defined tail. Thus repeated squaring during numerical evaluation causes no duplication of the printed tail term.

For (n) source definitions it emits exactly (n) additional definitions, with total term weight (111n) and the checked character bound

\[
|\operatorname{tracePacking}(n)|\le(8n+20)(112n).
\]

`packedWitness_checked` proves that the value of this compactly represented integer passes `checkTrace`. `packedWitness_lookup` identifies every decoded entry with the expanded source fragment's summary. `PackingProgram.expansion_eval` checks the denotation after ordinary closed-term expansion, and the freshness theorems cover the new identifiers.

This checker is a uniform Lean program over typed arithmetic syntax and a natural-number trace code. It has not yet been translated to a literal first-order PA formula with an object-level PA correctness proof. Its bounded-search decoder is deliberately simple and can take enormous time. No polynomial running-time claim is made. The intended short PA proofs must use the algebraic decoding lemmas, rather than an execution transcript of that search.

## What these certificates assert

There are three different assertions here:

1. **The Lean metatheorem:** the generated arithmetic terms denote the lengths and codes of the expanded source fragments.
2. **The generated object proofs:** the arithmetic abbreviations satisfy their defining equations.
3. **The encoded-trace metatheorem:** the compactly generated witness passes the arithmetic trace checker and decodes to the correct summaries.

The local object proofs do **not** yet prove, inside PA, that the original proof-file code satisfies the fixed `Bew` formula. In particular, neither a Lean semantic correctness theorem, a list of definitional equalities, nor a Lean proof of trace-checker acceptance automatically supplies that internal PA statement.

The notation `markedCode` makes the leading-marker convention explicit. The compiler also exposes the unmarked value and length. Connecting either convention to the agenda's fixed, fully specified Gödel numbering remains part of the representation interface; the upload does not provide its literal implementation.

## Checked examples

The first example uses these raw fragments, with names shortened for readability:

```text
u0 := (>
u1 := (=00)
u2 := u0 u1 u1 )
```

Spaces in the last right-hand side above separate atoms for exposition. Its expansion is `(>(=00)(=00))`, of length 13. The first fragment is not a formula. The example has mass 14; the emitted arithmetic definitions contain 1,216 characters and the local certificate contains 3,874 characters. The trace definitions add 1,569 characters, for a complete fragment of 5,443 characters.

For another family, start with one literal character and repeatedly define the next fragment by concatenating the previous fragment with itself. Lean proves, for every (n), that the final expanded length is (2^n) and the source mass is (3n+2).

| Doublings | Source mass | Expanded length | Local certificate | Extra trace definitions | Total |
|---:|---:|---:|---:|---:|---:|
| 8 | 26 | 256 | 5,113 | 5,671 | 10,784 |
| 16 | 50 | 65,536 | 10,697 | 11,921 | 22,618 |
| 32 | 98 | 4,294,967,296 | 22,871 | 25,643 | 48,514 |
| 64 | 194 | (2^{64}) | 49,287 | 55,677 | 104,964 |

The last three columns count characters. Mass is not the full input file's character count. These figures are compiler outputs, not shortest-proof measurements. The large examples generate only compact syntax: they never evaluate the enormous arithmetic code or materialize the expanded word.

For the small boundary example, an independent diagnostic also evaluates the printed term DAG, decodes the packed trace using integer square roots, and compares all three recovered summaries with the original strings. It recovers the expected entries from a 2,925-bit trace integer. This specifically exercises the text serialization and packing order.

## The next internalization obligation

The next missing statement is a short **PA proof**, for a single fixed arithmetic expansion predicate, of an instance such as

\[
\operatorname{Expand}(\overline{\#G},\bar i,L_i,S_i,V_i).
\]

The predicate must be defined so that PA proves its agreement with literal source-grammar expansion. Supplying it requires:

* a fixed arithmetic encoding of the source grammar and a literal PA formula for the now-implemented trace relation;
* object-level PA proofs of the pairing, sequence-access, and trace-checker lemmas;
* PA proofs connecting the local concatenation equations to the uniform expansion predicate;
* the connection from the original proof file, including its actual names and code, to the ordered grammar used here.

The compact witness, pairing identities, sequence-access facts, and typed trace-checker correctness are now proved in Lean. What remains here is their PA arithmetization and the generation of short PA proofs of the required instances. The intermediate numbers need not be small, so a polynomial-time numerical-verification theorem cannot simply be applied to them.

After expansion has been internalized, the accepted-proof predicate still has to be handled: axiom recognition, substitution and binding conditions, generalization, and modus ponens. Enderton's unrestricted tautology axioms require their own argument. The earlier arithmetic-substitution idea for tautology axioms has not been established for arbitrary compressed input by this compiler.

Consequently, the present result does not yet prove

\[
\text{a proof }r\text{ of }A
\quad\Longrightarrow\quad
\text{a polynomial-size PA-bin proof of }\operatorname{Bew}(\overline{\#r},\overline{\#A}).
\]

That is the outstanding internalization target. The internal Löb instance and proof assembly must also receive character bounds before the proposed route proves part 2. Part 1 still needs an actual PA-bin separation witness and a lower-bound argument.

## Verification and reproduction

The accompanying project uses Lean 4.19.0 and `Std`, with no Mathlib dependency. Its audited dependencies are among Lean's foundational `propext`, `Quot.sound`, and `Classical.choice`; the exact list for each theorem is printed by `Audit.lean`. There are no admitted proofs, `native_decide` proofs, or user-declared axioms.

After extracting the archive, run inside `MAISO11QuotationPass`:

```bash
lake build
lake env lean Audit.lean
lake exe quotationdemo
```

The demo writes `boundary-quotation.pabin` and `boundary-quotation-with-trace.pabin`. The latter appends witness definitions to the local proof fragment; it still does not assert a `Bew` statement. The optional diagnostic checks are:

```bash
python3 check_local_file.py boundary-quotation.pabin --self-test
python3 check_local_file.py boundary-quotation-with-trace.pabin --self-test
python3 verify_boundary.py
```

The first file has 9 definitions and 19 proof lines; the trace extension has 12 definitions and the same proof lines. The diagnostic rejects deliberately reversed modus ponens references and a reused definition identifier. It only recognizes the documented local equality fragment. `verify_boundary.py` performs the independent numeric round trip for the small example.

`checked-output.txt` records a clean build, the axiom audit, demo output, and diagnostic checks. `SHA256SUMS` identifies the delivered source files.

## References and provenance

* Uploaded `MAIS-A1.tex`, background conventions: raw-string abbreviations, charged self-delimiting names, binary numerals, and the default Enderton calculus.
* H. B. Enderton, *A Mathematical Introduction to Logic*, second edition, §2.4, pp. 112–115: generalized logical axioms, equality reflexivity, universal instantiation, and the full tautology axiom group. The local proof scheme above uses groups 5 and 2.
* M. Ganardi, D. Hucke, M. Lohrey, E. Noeth, [Tree Compression Using String Grammars](https://arxiv.org/abs/1504.05535): background on string-grammar compression. The quotation construction here works directly with string concatenation.

The milestone is the implemented and checked quotation construction. No novelty or resolution of MAIS-O11 is claimed.
