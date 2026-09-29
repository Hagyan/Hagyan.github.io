# MAIS-O11 Part 2: a provability-predicate specification trap

**Scope.** This note concerns the specification of the arithmetic formula
`Bew(m,y)`, not a counterexample to polynomial overhead for the intended
canonical PA-bin proof predicate. It uses consistency of PA-bin, which the
agenda explicitly assumes at `MAIS-A1.tex:98` for its efficient systems.
It also assumes the ordinary proof
relation has a primitive-recursive (therefore PA-representable `Δ₁`) checker,
as the agenda requires at line 86.

## An extensionally exact `Δ₁` formula for which Löb's rule fails

Write `Prf(m,y)` for the intended PA-bin proof relation and let
`b = ⌜0=1⌝`. Consider the *arithmetical formula*

`Bew⋆(m,y) := Prf(m,y) ∧ ¬Prf(m,b)`.

If PA-bin is consistent, there is no standard `m` with `Prf(m,b)`.
Consequently, for every pair of standard natural numbers `m,y`,
`Bew⋆(m,y)` holds if and only if `Prf(m,y)` holds. Its standard extension is
*exactly the same proof relation*. The new relation is primitive recursive
whenever the original proof checker is, and has a `Δ₁` arithmetic
representation. The formula can be chosen with a PA-provable equivalence to
the displayed conjunction, so the following elementary argument is formal.

PA proves `∀m ¬(Prf(m,b) ∧ ¬Prf(m,b))`, purely by logic. Therefore, with
`□⋆φ := ∃m Bew⋆(m,⌜φ⌝)`, PA proves `¬□⋆(0=1)`, and hence proves the
reflection premise `□⋆(0=1) → (0=1)`. Consistency says PA does **not** prove
`0=1`. Thus Löb's rule does not hold for this formula despite its exact
agreement with the intended relation on standard proof codes.

The consequences for the displayed definition of `F` are concrete. Let `k₀`
be the fixed length of the PA proof of `□⋆(0=1) → (0=1)` and take
`k ≥ k₀` and `n ≥ |0=1|`. The set over which the agenda maximizes at
`MAIS-A1.tex:242–249` includes `0=1`, whose minimal direct PA proof length
is `∞` by lines 91–93. Accordingly its proposition of finite totality
(`MAIS-A1.tex:254–260`) does not follow from the premises "extensionally
correct `Δ₁` proof predicate" alone. A false `Bew⋆` sentence about a *fixed*
standard proof is PA-decidable; the failure lies in the *uniform*
arithmetical statement about all codes, including nonstandard ones.

## What the example does and does not imply

The uploaded `MAIS-A1.tex:109` says to "fix a `Δ₁` proof predicate" and
`MAIS-A1.tex:167–174` asserts Löb's theorem, explicitly citing the three
derivability conditions in the explanation of its proof. The latter sentence
strongly signals the intended *intensional* restriction; if those conditions
are read as hypotheses, `Bew⋆` is excluded. The earlier grammar paragraph
(`MAIS-A1.tex:104`) describes a written PA-bin checker, but does not provide
an actual arithmetical formula or a PA proof of uniform equivalence to it.
An *extensional-only* reading of line 109 admits `Bew⋆`; an
*intensional, canonical-checker* reading, or explicit acceptance of the
derivability conditions cited at line 174, excludes it. This is a
specification issue, not a refutation of Conjecture 3.5 for the intended
predicate. The conventions at lines 121–141 further postulate uniform
properties of the chosen bounded boxes and expansion function, which
`Bew⋆` need not satisfy. Their role should be stated as assumptions or proved
for the completed canonical implementation, not inferred from external
`Δ₁` representability.

One sufficient repair is to fix a concrete `Prf` formula and prove in PA the
usual three Hilbert–Bernays–Löb derivability conditions for its existential
closure (with explicit quantitative bounds in this problem). An equivalent
replacement formula should be accompanied by a *PA proof of its uniform
equivalence* to that reference checker. The counterexample fails this test:
PA could not prove `∀m,y (Bew⋆(m,y) ↔ Prf(m,y))`, because such an equivalence
combined with ordinary provability conditions would yield the invalid Löb
inference above. At the computational layer, the exact wire grammar and
arithmetized acceptance formula must be pinned down separately from the
external fact that the checker accepts the right standard strings.

## The distinct all-tautologies obstacle

Literal Enderton logical axioms include every propositional tautology.
Deciding whether an arbitrary candidate single-line axiom is in this family
is coNP-hard (indeed TAUT reduces directly by viewing its atoms as distinct
atomic arithmetic formulas). Thus the natural strategy "prove the checker
runs in polynomial time and internalize that computation" faces a complexity
barrier. It is **not** a barrier to a polynomial *proof-length* theorem:
the input is promised to be a valid proof, and the target Hilbert calculus
allows an arbitrary tautology as a one-line axiom. A prospective compiler may
use that very axiom to prove its own finite evaluation correctness, with
uniformly short substitution and truth-evaluation derivations. That program
still requires a polynomial-size translation through the full nested string
abbreviation grammar and PA proofs of each local acceptance condition.

In particular, the existing Lean `SharedOracle` proves equivalence of a
restricted checker and its expanding reference semantics. It cannot be
identified with a PA proof of `Bew(⌜π⌝,⌜P⌝)`, and the extensional `Δ₁`
example shows why simply naming a representation of that semantics is
insufficient. The viable Part 2 target is an **actual fixed arithmetization**
with PA-verified derivability and explicit polynomial-length internalization
for each valid PA-bin proof file.
