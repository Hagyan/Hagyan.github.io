# MAIS-O11: compact trace conclusions and proof-record accounting

23 September 2026. Supplement to the arithmetic-access milestone.

## New certified result

Let `p : Program n` be a program in the existing quotation compiler. Its
prelude supplies `3n` source registers and `n` packed-tail registers. The new
compact formula `trace n` references those registers, rather than copying
their expanded arithmetic terms.

Lean proves that expanding this formula using the concrete compiler dictionary
gives exactly the preceding milestone's arithmetic trace formula:

```
(trace n).expand (dictionary p)
  = traceFormula p (Term.ofClosed (packedRoot p))
```

The expanded formula has an object-calculus derivation with at most
`n*(14*n+10)+3` proof-tree nodes. Independently, the compact conclusion has
at most

\[
(12n+9)\bigl(n(23n+119)+3\bigr)
\]

written characters in the explicit serializer. This is a coarse cubic bound
for the **conclusion only**, not a character bound for its entire proof.
The compact formula depends only on `n`; the prelude supplies the
program-specific terms. The prelude's characters are not included in this
new conclusion bound and must still be charged separately.

## Why abbreviations survive binding

Compact references expand to closed arithmetic terms. Lean proves their
invariance under substitution and proves expansion commutes with compact
renaming. Variables use levels `n-1-i` in a context of size `n`.
Introducing a binder preserves every existing variable's level and assigns
the new variable the fresh level `n`. These properties, level injectivity,
and the variable-token decoding equation are certified.

This does not yet provide a complete parser/round-trip theorem for formulas
or a certified implementation of the agenda's entire PA-bin checker.

## Character accounting for records

The new record datatype has axiom-labelled records and modus-ponens records.
Each MP reference is a `Fin k`, where `k` is the number of preceding records:
forward references cannot be constructed. The serializer charges all of its
tags, punctuation, reference names, formula characters, and newlines.

For a file of `N` records, if each compact formula has depth at most `D` and
weight at most `W`, with `r` available term abbreviations, Lean proves

\[
|\mathrm{file}|\le
N\bigl((2r+2D+7)W+4N+14\bigr).
\]

This is a conditional ledger. An axiom label does not establish that its
formula is an axiom, and the record type does not check whether an MP step
is valid. No generalized PA-bin proof checker is claimed. The records cover
the axiom/MP fragment used by the preceding derivations; definition records
belong to the separately charged prelude.

## Remaining mathematical and implementation obligations

1. Construct compact representatives of **all intermediate formulas** in the
   existing trace-access derivation, with the right binder handling.
2. Generate a backward-referencing proof file and prove each record expands
   to a valid object-calculus step. Prove bounds on its record count, maximum
   formula weight, and depth; instantiate the new ledger with those bounds.
3. Connect the complete wire format to the specified PA-bin parser/checker,
   charging its definition prelude and any translation overhead.
4. Internalize the relevant checker computations in PA with the needed
   quantitative bounds. Program-specific trace access alone is not a uniform
   theorem about the ordinary provability predicate.
5. Establish the proof-length separation requested in MAIS-O11. Polynomial
   internalization, even if completed, would not by itself establish that
   Löb's detour saves symbols or resolve either part of the problem.

The new result removes repeated expanded terms from the final trace formula
and makes its written size explicit. It leaves the full proof-file bound as
an explicit obligation, rather than inferring it from a proof-node count.

## Reproduction

Unzip the accompanying certificate, enter `MAISO11WirePass`, and run:

```sh
lake build
lake env lean Audit.lean
```

The project pins Lean 4.19.0. `CompactWire.lean` is the new source;
the earlier arithmetic-access and quotation sources are included as
dependencies. `Audit.lean` prints axiom dependencies of the central theorems
and exact character lengths for small compact conclusions. The archive also
contains a clean-build transcript and SHA-256 checksums. Lean's certification
applies to the stated formal theorems, not the unresolved obligations above.
