# MAIS-O11: narrow the internalization target

**27 September 2026.** Both parts remain open. This note redirects the Part 2
strategy from a global compiler for every PA-bin proof file to the internalizer
actually used by the standard Löb construction. It makes no new bound on
`F_PA_bin`.

## The cost ledger

Fix a sentence `P` and a PA-bin proof `π` of `□P → P`, with written length
`k`; put `n = |P|`. Let `D_P` be a diagonal sentence satisfying

```text
PA_bin ⊢ D_P ↔ (□D_P → P).
```

The usual Löb derivation uses `π` once. It builds a proof `ρ(P,π)` of `D_P`
from the fixed-point equivalence, the derivability-condition proofs, and `π`.
It then needs a proof of `□D_P` from the fact that `ρ(P,π)` proves `D_P`;
that is the internalization step. The rest is a fixed number of applications
of implication distribution and modus ponens. With abbreviation-aware formula
sharing, the ledger has the form

```text
|ρ(P,π)| ≤ k + A(n)
|proof of □D_P| ≤ I_Lob(k,n)
|proof of P| ≤ I_Lob(k,n) + O(k + A(n) + n),
```

where `A` is the written cost of the chosen diagonal construction and
`I_Lob(k,n)` is the cost of internalizing this *particular assembled proof*.
Consequently, polynomial bounds for `A` and `I_Lob` imply the polynomial
alternative in Part 2. The agenda's global expansion function `E_S` is one
sufficient upper bound for `I_Lob`, but it ranges over all proofs and all
formulas. Part 2 does not ask for that global bound; Problem O12 does.

The exact residual obligation in this route is therefore narrower than
“polynomially internalize every PA-bin proof.” Given `P` and an accepted
reflection proof `π`, construct a PA-bin proof of the arithmetized fact that
the assembled `ρ(P,π)` is an accepted proof of `D_P`, with written length
polynomial in `k+n`. This target still implies the desired upper bound only
when paired with a polynomial diagonal ledger, and it has not been proved.

## Why the global compiler was the wrong immediate target

The fixed Enderton presentation accepts arbitrary propositional tautologies
as axiom records. Thus a length-`k` input proof may contain a compressed
tautology line whose expansion is much larger than `k`. The checker is
primitive recursive, but that alone gives no polynomial bound on an
arithmetic PA-bin proof of the assertion that this record passed the
tautology test. A compiler that handles every accepted file must solve this
additional issue for every such record. The direct Löb route only needs the
records occurring in `π` and the fixed appended proof skeleton, so a global
compiler is stronger than the route requires.

There is a useful restricted case. If every propositional-axiom record in
`π` comes with a supplied derivation in a fixed finite Frege basis, then the
assembled file can replace those records by the supplied derivations. The
replacement has polynomial written cost when the total certificate size is
polynomial in `k+n`. The remaining PA axiom, modus-ponens, generalization,
and abbreviation checks are syntactic, but proving a polynomial PA-bin cost
for the exact string-fragment decoder remains a separate obligation. This is
a conditional compiler for certified inputs, not a result for arbitrary
shortest reflection proofs: their one-line tautology axioms need not carry
Frege certificates of polynomial size.

The `T → T` stress test is not an obstruction to all compression methods. A
checker can recognize that pattern directly even when `T` is a large shared
fragment. Likewise the unary-negation family can be summarized by a small
Boolean transformation. These show that expanded-size lower bounds defeat a
compiler that prints one step per expanded symbol, but do not rule out a
polynomial proof in the actual system. Conversely, the fact that a tautology
checker is computable does not prove such a polynomial proof exists.

## What this says about the previous finite-table work

`SummaryFiniteCheck.lean` handles one fixed 204-production grammar and its
407 local summary equations. Its root is balanced and has expanded length
`2^101 + 1`; the generated Lean source is still awaiting a kernel run in an
environment with Lean 4.19.0. Even after that run, the theorem would certify
only that finite summary instance. It would not establish a bound on
`I_Lob`, on `E_S`, or on either part of MAIS-O11. The prior arithmetic path
was exploring one possible service for an internalization argument, not the
missing Löb construction itself.

## Next proof obligation

The next useful theorem is a costed, fixed-point-specific internalization
lemma, with a fully explicit PA-bin record decoder:

```text
Input:   P, a PA-bin proof π of □P → P
Output:  a PA-bin proof q of Bew(code(ρ(P,π)), code(D_P))
Bound:   |q| ≤ poly(|π| + |P|), with the same abbreviation grammar and
         numeral/code convention as the problem.
```

Its proof must account for every tautology axiom occurring in `π`; it may not
assume a polynomial-time checker, a polynomial-size truth table, or a generic
polynomial internalization theorem. If this restricted lemma fails, the
failure should be traced to a specific family of reflection proofs and a
lower bound on all short proofs of their internalized checker assertions.

This is not yet a route to Part 1. A Part 1 witness needs a lower bound on
*every* direct proof of a family `P_i`, while the current work only gives
finite computation certificates. Nor does a Part 1 witness by itself settle
Part 2's polynomial-versus-superpolynomial dichotomy.

## Source scope

The current upstream statement still asks for Part 1 in `PA_bin` or any
efficient system, and Part 2 specifically for `F_PA_bin`; it marks the
problem open. Critch's underlying three conditions are representability of
computable functions, binary numerals, and abbreviations. His derivation of
constant-cost implication distribution also uses ordinary proof-file
concatenation. The quadratic-trailer example in `CONTINUATION-NOTE.md`
meets the three bare conditions but violates that composition property, so it
is a loophole in the weakened definition, not a robust Part 1 result for the
intended PA-bin calculus.

References:

- [MAIS-O11](https://github.com/lionellevine/MAIS/blob/main/open-problems/MAIS-O11.md)
- [MAIS-A1, Question 3.6](https://github.com/lionellevine/MAIS/blob/main/agendas/A1/MAIS-A1.tex)
- A. Critch, [*Parametric Bounded Löb's Theorem and Robust Cooperation of Bounded Agents*](https://arxiv.org/abs/1602.04184), §§2.2 and 4.2.
