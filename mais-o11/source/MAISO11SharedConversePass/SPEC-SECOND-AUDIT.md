# MAIS-O11: second audit and a transfer between the two parts

25 September 2026. Sources are the recovered uploaded `MAIS-A1.tex` and the existing research notes. The mathematical transfer below is an elementary consequence of the definitions and finite proof syntax; it is not a resolution of either part.

## A useful theorem connecting Part 1 and Part 2

Fix one actual proof system and one actual provability formula for which Löb's rule holds. Assume a finite proof alphabet, decidable proof checking, and a unique designated conclusion for each proof. Use exactly the agenda's lengths and overhead:

\[
d(P)=\ell_S(P),\qquad r(P)=\ell_S(\Box P\to P),\qquad s(P)=|P|,
\]

\[
F(k,n)=\max\{d(P):s(P)\le n,\ r(P)\le k\},
\qquad\max\varnothing=0.
\]

This is A1 lines 242–249. Only sentences with finite reflection lengths enter a maximum. Löb's rule makes their direct lengths finite.

**Theorem.** If there is no constant `A` such that

\[
F(k,n)\le A(k+n+1)\quad\text{for all }k,n,
\]

then there is a sequence of sentences `P_i` such that `r(P_i) → ∞` and, for every fixed real `δ>0` and every fixed real `C≥0`, eventually

\[
d(P_i)\ge (1+\delta)r(P_i)+C(s(P_i)+1).
\]

In particular, Part 1 holds with the agenda's chosen `C₁`. The *same sequence* eventually satisfies every fixed factor and toll.

**Proof.** For each integer `i≥1`, choose `(k_i,n_i)` with

\[
F(k_i,n_i)>i(k_i+n_i+1).
\]

The absence of a linear bound guarantees such a pair for each `i`. The right side is positive, so the maximizing set is nonempty. Choose any maximizer `P_i`; no preference among ties is required. Then

\[
d(P_i)=F(k_i,n_i)>i(k_i+n_i+1),\qquad
r(P_i)\le k_i,\qquad s(P_i)\le n_i.
\]

Given fixed `δ,C`, take `i≥max(1+δ,C)`. It follows that

\[
\begin{aligned}
(1+\delta)r(P_i)+C(s(P_i)+1)
&\le (1+\delta)k_i+C(n_i+1)\\
&\le i(k_i+n_i+1)\\
&<d(P_i).
\end{aligned}
\]

It remains to check the requirement `r(P_i)→∞`; unboundedness alone would not suffice. Fix any `R`. There are finitely many proof strings of length at most `R`. Their conclusions contain only finitely many distinct reflection formulas. The map `P ↦ (□P→P)` is injective as syntax, because `P` is recoverable as the consequent. Consequently

\[
\mathcal P_R=\{P:r(P)\le R\}
\]

is finite. Every member is directly provable by Löb, so

\[
M_R=\max\bigl(\{d(P):P\in\mathcal P_R\}\cup\{0\}\bigr)
\]

is a finite natural number. But `d(P_i)>i`. For all `i>M_R`, membership in `𝒫_R` is impossible. Hence `r(P_i)>R` for every sufficiently large `i`. This holds for every `R`, proving convergence to infinity. ∎

The same proof gives the simpler quantified form, convenient for Lean: for all integers `a,c,R≥0`, there is `P` such that

\[
r(P)>R,\qquad d(P)>a\,r(P)+c(s(P)+1).
\]

To see this directly without selecting an infinite sequence, choose `i>max(a,c,M_R)` and a maximizing pair as above.

**Lean certificate.** `SpecTransfer.lean` formalizes `numericGap`, `unboundedOverheadGivesWitness`, and `reflectionLengthsTendToInfinity`. The main theorem assumes attainment of every positive maximum and bounded direct lengths on each bounded-reflection-length fiber, with all three length functions valued in natural numbers on an abstract eligible-sentence type. It proves the displayed quantified witness statement; the final theorem proves the convergence argument for arbitrary maximizing choices. The finite-alphabet and Löb arguments supplying these hypotheses are given above in prose, not implemented as a full PA proof system in this module. Verification with Lean 4.19.0 succeeded using `lake env lean SpecTransfer.lean`. The printed axiom dependencies are `propext` and, for the latter two theorems, `Quot.sound`; there are no custom axioms or unfinished proofs.

**Consequences and limits.**

1. A negative answer to Part 2 necessarily gives a positive answer to Part 1 in the same PA-bin system: failure of every polynomial upper bound implies failure of a linear upper bound. Thus the two parts cannot both have negative answers, provided the intended Löb hypotheses hold.
2. More strongly, proving any actual unbounded growth of `F(k,n)/(k+n+1)` would already produce arbitrarily large factor separations. A superpolynomial lower bound is unnecessary for this implication.
3. The contrapositive is informative: if Part 1 has no witness, `F` has some global linear upper bound, which is stronger than Part 2's polynomial conjecture.
4. A quadratic or higher polynomial *upper bound* does not establish the premise. The theorem requires a lower-bound fact excluding every linear bound. No such fact is proved here.
5. This argument does not provide explicit numerical witnesses without that missing lower-bound premise. It identifies a sufficient target and a logical dependency, not a solved instance.

**Effective extraction.** Under the same decidability and Löb hypotheses, the agenda's proof at lines 254–260 computes `F`. If its ratio to `k+n+1` is unbounded, enumerate pairs until the displayed inequality for `i` holds; then compute the finite list of qualifying sentences and their shortest direct proofs, choosing the first maximizer in a fixed ordering. This gives a computable witness sequence, conditionally on unboundedness. No polynomial running-time or PA-provable totality claim follows.

**Edge cases.** The added `1` avoids a zero denominator. A pair with `F=0`, including an empty maximizing set, is never selected for `i≥1`. Empty proof files or length-zero proofs, if the chosen syntax permits them, cause no problem: finitely many such files still give a finite `M_0`. Infinite direct lengths are excluded exactly where Löb is used, not by an unstated convention. With a nonstandard box for which Löb fails, this theorem does not apply to the agenda's purported natural-valued `F`.

## A sharper converse formulation

Fix the agenda's particular toll `C₁≥0`. Suppose Part 1 fails. Then for every fixed `δ>0` there is a finite constant `B_δ` such that

\[
F(k,n)\le
\max\{(1+\delta)k+C_1(n+1),\ B_\delta\}
\quad\text{for all }k,n.
\]

Indeed, consider the exceptional sentences satisfying

\[
d(P)\ge(1+\delta)r(P)+C_1(s(P)+1).
\]

If their reflection lengths were unbounded, choosing one above each successive threshold would be a Part 1 sequence. Thus their reflection lengths are bounded. Finite proof syntax makes the exceptional set finite, so their direct lengths have a finite maximum `B_δ`. Every nonexceptional candidate is bounded by the first term in the displayed maximum. Taking the maximum over eligible `P` proves the assertion, including empty sets. This makes precise how strong an impossibility theorem for Part 1 would be.

## There is no primitive-recursive / tautology contradiction

A1 line 86 requires a primitive-recursive checker, not a polynomial-time checker. Enderton's all-tautologies axiom family is compatible with that requirement: parsing a finite formula, enumerating all assignments to its finitely many propositional atoms, and evaluating the formula form a primitive-recursive procedure. Acyclic abbreviation expansion is likewise terminating with primitive-recursive size and time bounds.

The genuine obstacle is more specific: one cannot infer polynomial-time checking from those requirements. The earlier strategy of internalizing a polynomial computation therefore lacks its premise for this axiom family. A direct proof-producing construction on inputs promised to be valid may still have polynomial output length; it need not decide validity. The current tautology work is aimed at precisely that distinction.

## The fixed `Bew` issue

A1 line 109 specifies a Delta-1 predicate verbally, but does not provide its exact arithmetic formula. Lines 167–174 then invoke Löb and its derivability conditions. Those conditions must be treated as hypotheses or established for the chosen formula; they do not follow just from correctness on standard proof codes.

The separate `PART2-ADVERSARIAL-NOTE.md` already supplies a decisive example. If `Prf` is the ordinary proof predicate and `b` is the code of `0=1`, then

\[
\operatorname{Bew}^{\star}(p,y)=\operatorname{Prf}(p,y)\land
\neg\operatorname{Prf}(p,b)
\]

has exactly the same standard extension under consistency, but its existential closure satisfies a provable consistency statement by propositional logic. It cannot satisfy the ordinary Löb conclusion. This is a counterexample to an extensional-only specification, not a refutation of the intended canonical PA-bin conjecture.

There is also a quantitative repair. Suppose two fixed boxes `□₁,□₂` use the same underlying proofs and direct length `d`. Assume actual proof transformations establish, with one constant `A`,

\[
|r_1(P)-r_2(P)|\le A(s(P)+1)
\]

for every provable sentence. Then

\[
F_2(k,n)\le F_1(k+A(n+1),n),\qquad
F_1(k,n)\le F_2(k+A(n+1),n).
\]

Each inequality follows by inserting a sentence eligible for its left-hand maximum into the right-hand maximum. Consequently polynomial boundedness is invariant under such controlled replacement. A fixed PA proof of uniform equivalence between the two proof predicates is a natural starting point for these transformations, but its instantiation, abbreviation handling, and MP costs must still be accounted for. Extensional equivalence alone is insufficient, as the starred example shows.

## Symbol accounting exposes another missing bridge

The cheap-direction lemma at A1 lines 267–271 appends an axiom and MP and charges only `O(|P|+1)` additional symbols. That is correct for an appropriate deduction serialization. It is not yet proved for the current certified **indexed** record syntax.

`CompactWire.lean:369–372` writes the two premise identifiers explicitly in every MP record. Appending to a proof with `q` records incurs the lengths of names for approximately `q` and `q+1`, as well as the new formulas. With the current binary identifiers the straightforward append construction gives an additional term `O(log(q+2))`. It has not been shown that this term is bounded by `O(|P|+1)` for shortest proofs. Similarly, joining independently written files requires handling collisions among globally scoped abbreviation names. The assertion of constant MP gluing at A1 lines 121–125 does not itself supply that transformation in this grammar.

This is a gap in the claimed accounting bridge, not a proof that the optimal inequalities are false. Possible completions include citation-free MP tags whose checker searches previous records, relative-reference conventions, or a new proof transformation with verified bounds. Because the agenda leaves the exact tags unspecified, such a completion must be recorded explicitly rather than attributed to already fixed bytes.

There is a second small quantifier issue: `C₁` in A1 line 267 is an existential constant. Any larger constant also satisfies that lemma, but Part 1 uses it in a lower-bound inequality at line 312. A numerical or canonical choice should therefore be fixed for literal witnesses. The transfer theorem above avoids dependence on that choice: its sequence eventually works for every fixed toll, however large.

## What finite Gödel sentences actually prove

Use an ordinary proof predicate with numeralwise representation and a PA-provable code bound for all proof files of written length at most `N`. Let `G_N` be a bounded fixed point with

\[
S\vdash G_N\leftrightarrow
\neg\operatorname{Prov}_{S,\le N}(\ulcorner G_N\urcorner).
\]

Assume `S` is consistent. Then **every actual S proof of `G_N` has length greater than `N`**. Otherwise its concrete proof code gives an S proof of the bounded provability assertion by numeralwise representation, while the purported proof and fixed-point equivalence give its negation. This contradicts consistency. The argument excludes all proofs in the exact chosen system, not merely generated proofs or a fragment.

Moreover, each fixed `G_N` is provable: the absence of a short proof is a true finite check; with the stated code-bound and representation assumptions PA can verify that particular finite check, and the reverse fixed-point implication yields `G_N`. The resulting proof can be enormous. These are genuine lower bounds paired with eventual provability; no useful upper bound for the shortest reflection proof follows.

In particular the bounded equivalence does not imply a short proof of

\[
\Box_S G_N\to G_N.
\]

The antecedent quantifies over proofs of arbitrary length. Replacing it by bounded provability changes the requested reflection sentence. If compact fixed points have `|G_N|=O(log N)`, a hypothetical polylogarithmic reflection proof would have major consequences for `F`; precisely that proof is missing. Lean verification of a quotation/compiler lemma does not supply it.

The current finite-Gödel idea therefore gives a defensible direct lower bound under explicit ordinary-proof assumptions, but it has not yielded a Part 1 witness. The new transfer theorem suggests an alternative organizing target: any demonstrated superlinear lower growth of the actual `F` would automatically supply robust Part 1 witnesses, while a genuine impossibility theorem for Part 1 would force a near-linear upper shape for `F`.
