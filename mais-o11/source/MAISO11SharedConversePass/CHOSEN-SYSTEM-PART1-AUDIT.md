# MAIS-O11 Part 1: structural audit of the chosen-system construction

**27 September 2026.** This file is an index and scope audit. The canonical
quantitative argument and current proof obligations are in
`CHOSEN-SYSTEM-PART1-ROBUST-LEDGER.md`.

## Finding

The literal MAIS-O11(1) wording permits “any efficient system of your choice.”
Under MAIS-A1's stated efficiency conditions, the guarded-verifier construction
is a conditional candidate for that branch, assuming consistency of the base
PA calculus. It uses a primitive-recursive verifier whose finite guard checks
are true on every standard instance. MAIS-A1 does not require a polynomial-time
proof checker.

The current quantitative ledger uses the cutoff `2^n`, permits arbitrary
nested string-fragment abbreviations, and derives only the robust lower bound
`ell_S(p_n) > sqrt(n/C)-1`. This supports a tail witness for the permissive
chosen-system branch with `delta=1`, conditional on the proof obligations in
the ledger. It is not a result for fixed `PA_bin` or MAIS-O11(2).

## Superseded claims

Earlier drafts used cutoff `n`, a token-origin argument, and a linear proof
translation. Those quantitative claims are withdrawn. They are not supported
for arbitrary string-fragment abbreviations. Use only the `2^n` cutoff and the
`2^(C(m+1)^2)` translation bound in the robust ledger.

## Formal status

The construction is still a mathematical proof draft. The current ledger
freezes the binary numeral term grammar, closes the local code-numeral
specialization and axiom-instance cost at `O(log n)`, and derives an `O(E^3)`
uncompressed translation after correcting the macro-expansion recurrence. It
also specifies the finite-alphabet record grammar, guarded proof relation,
separate diagonal and checker fixed points, root-occurrence guard lemma,
D1-D3 proof constructions, and consistency interpretation. The current
`ChosenSystemExpansion.lean` serializer bridge and expansion bound build with
Lean 4.19.0; all four checked declarations report only `propext` and
`Quot.sound`, without `sorryAx`. In this workspace, that check required
rebuilding a corrupted bundled `Init.Data.List.MinMax.olean` from matching
Lean source. `ChosenSystemSerialization.lean` now builds as well and proves
round trips for the tagged grammar-plus-root model; its six checked
declarations report only `propext` and `Quot.sound`. The new
`ChosenSystemInterleaving.lean` verifies preservation of expanded output and
the same size bound when abstract definitions occur between output fragments;
its four checked declarations also have no `sorryAx`. The actual AX/MP/GEN
proof-file parser, generated checker source/constants, PA derivation objects
for the guard and derivability lemmas, and an end-to-end accepted-file run
remain open. These Lean results do not certify those metatheoretic components.

The connective-tag Lean variant is a separate construction and is not a
certificate for this nullary-predicate system. Its earlier blanket claim that
all Hilbert axioms preserve a tag guard was corrected: conjunction-introduction
axioms can create a fresh tag. This does not replace the distinct D2 argument
for the guarded checker described in the robust ledger.

## Scope against the agenda

- MAIS-O11 explicitly permits any efficient system in Part 1 and fixes
  `PA_bin` only for Part 2.
- MAIS-A1 requires a primitive-recursive proof checker, binary numerals, and
  abbreviations; it states no polynomial-time checker requirement.
- The fixed-`PA_bin` Part 1 branch and Part 2 remain open. The slow-verifier
  construction cannot be imported into those fixed-system questions.

This is a conditional chosen-system candidate, not a completed formal result.
