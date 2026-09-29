# MAIS-O11: exact equivalence of compact and expanding file decoders

## What changed

The previous certificate proved only the forward direction: any definition
prelude accepted by the compact parser was accepted by the original expanding
reader with the same meaning. `SharedConverse.lean` proves the converse on
**every input byte string**. Its `oldTerm_sound` lemma reconstructs a compact
closed term from any successful run of the old recursive reader, preserving
both the exact consumed bytes and the expanded term. `oldDefinition_complete`
and `oldCount_complete` lift this fact through definition lines and lists.

The resulting exact statement is `sharedPrelude_iff_old`:

```lean
(parseSharedPrelude r cs).map CDefs.terms = readDefinitionPrelude r cs
```

The `Option.map CDefs.terms` is a mathematical bridge for comparing returned
values; evaluating that map can be exponentially expensive. The actual
`parseSharedPrelude` computes compact syntax without expanding definitions.
The result removes the previous uncertainty about whether the new parser
silently rejects some valid strings in this restricted grammar.

The certificate also introduces `decodeWholeShared`, which feeds those
definitions into the **existing proof-record parser**. Theorems
`decodeWholeShared_iff_old` and `checkWholeSharedReference_eq_old` prove exact
agreement, including rejection, with `decodeWhole` and `checkWhole` for every
input string and any declared definition and record counts. The reference
checker expands definitions before recognizing axioms; the theorem does not
give a fast proof checker. `checkWholeSharedReference_sound` inherits the
previous theorem that accepted conclusions have a derivation in the formalized
fragment.

`SharedConverseDemo.lean` builds a complete serialized file with 61 nested
definitions and a reflexivity axiom record. `decodeWholeShared` parses it
without constructing its final abbreviation's `2^61-1`-node expanded tree.
Lean also proves this exact decoding result (`decodeActualDoublingFile`).
The executable `#eval` checks only decoding; evaluating the reference
checker on that file would trigger expansion.

## Important scope audit against the uploaded agenda

The agenda (`MAIS-A1.tex`, §2) specifies PA in Enderton's Hilbert calculus,
generalization records, abbreviations for previously defined strings, and a
specific coding and written proof length. Our previous Lean checker
(`CompactProof.lean` / `CompactChecker.lean`) supports **four logical axiom
families**, axiom and MP records, and **closed-term** abbreviation definitions.
It omits the full PA axiom schemes, generalization records, abbreviation
behavior for arbitrary strings/formulas, and the agenda's full arithmetized
proof predicate. Thus all the equivalence statements here refer to the
**implemented fragment**, not the full PA-bin proof system. Earlier shorthand
calling the local serializer “the actual PA-bin checker” should be read with
that restriction. This mismatch is a concrete obstruction to treating the
current Lean work as a proof of either open question.

The next mathematical steps are to specify the remaining agenda grammar and
prove that the expanded and compact decoders agree on it; compile compact
terms and formulas into a general shared equality procedure; certify
substitution/axiom recognition without expanding abbreviations; and then
obtain PA-internal proof-length bounds for that complete checker and Löb's
rule. A Lean theorem about the external parser alone supplies none of those
PA proof-length bounds.

## Verification

Lean 4.19.0 with Std, from the project root:

```bash
lake build
lake env lean SharedConverseDemo.lean
```

These commands were run successfully. The `#print axioms` audit of all new
principal theorems shows `[propext, Quot.sound]`; the new modules contain no
`sorry`, `admit`, custom axioms, or `native_decide`. The executable demo
prints `PASS: 61-definition complete proof file decoded compactly`.

This checkpoint neither establishes a polynomial-time full checker nor gives
an MAIS-O11 Part 1 witness or a bound for its Part 2 overhead function.
