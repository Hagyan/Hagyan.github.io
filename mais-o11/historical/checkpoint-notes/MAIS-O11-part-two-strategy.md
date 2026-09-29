# MAIS-O11: choosing part 2 and connecting the two questions

## Scope

This checkpoint proves two abstract results in Lean 4.19.0. First, explicit polynomial cost certificates for three operations yield a polynomial Löb proof transformation. Second, a negative answer to part 2 implies an affirmative answer to part 1, under the finite-proof properties in the problem statement. These are reductions and accounting results, not resolutions of either open question. No novelty claim is made.

The package is standalone. It does not instantiate its proof-system interface with the PA-bin checker from the previous checkpoints. All quantitative interface assumptions are displayed in `ProofInterface` and printed by `Audit.lean`.

## Positive route: one internalization and two applications of MP

Write R_P = (Box P -> P). Given a proof pi of R_P:

1. Internalize pi to obtain a proof of Box R_P.
2. Apply a proof of the formalized Löb instance Box R_P -> Box P.
3. Apply the original proof pi of Box P -> P to conclude P.

The transformation needs only internalization of proofs with reflection conclusions. General polynomial internalization for every possible proof conclusion would suffice but is stronger than this interface requires. The hard work of constructing and bounding the formalized Löb instances is contained in a separate explicit hypothesis; it has not disappeared.

Suppose fixed nonnegative polynomials I, L, and J and a fixed natural b give these bounds:

- A supplied proof of R_P of cost k can be internalized at cost at most I(k + |P| + 1).
- There is a proof of Box R_P -> Box P of cost at most L(|P| + 1).
- Combining proofs of A and A -> B costs at most J(cost(first) + cost(second) + |B| + 1).
- |Box P| + 1 is at most b(|P| + 1).

Set x = k + |P| + 1. Then the output proof has cost at most the fixed polynomial

    Q(x) = J(J(I(x) + L(x) + b*x) + x).

`transform_bound` proves this inequality for the actual abstract proof object assembled by the two MP operations. Polynomial expressions are built solely from natural constants, the variable, addition, and multiplication. `Poly.power_bound` verifies that every such expression is bounded by C(x+1)^d for fixed C,d. `polynomial_reflection_conversion` concludes uniformly that, if k bounds the supplied reflection proof and n bounds |P|, the direct proof has cost at most C(k+n+1)^d.

Taking a maximum over the sentences admitted in F(k,n) then yields the desired type of polynomial upper bound. The harmless +1 is still a polynomial in k+n.

What remains for PA-bin: construct its actual proof objects and arithmetic box, then discharge the length bounds for reflection internalization, formalized Löb instances, and proof assembly. The previous parser/checker certificate does not do this. In particular, neither the `lob` proof constructor nor its polynomial length bound is supplied by those previous files.

## Negative route: part 2 would force part 1

Let d(P), r(P), and s(P) denote the shortest direct proof length, shortest reflection proof length, and sentence length, respectively, on the domain of provable sentences. Fix an integer toll coefficient C at least as large as the coefficient in part 1.

Assume there is no linear bound of the form

    d(P) <= M (r(P) + s(P) + 1)

valid for every provable P. This already follows from failure of every polynomial bound on F.

For any prescribed reflection budget R, only finitely many sentences have a reflection proof of length at most R: there are finitely many files of bounded length, each with one conclusion. Each such sentence has a direct proof by Löb's theorem. Therefore there is a finite bound B_R on their shortest direct proofs. Lean's `finiteBudget_from_finite_covers` proves the abstract finite-list step.

Choose M = B_R + C + 3 and then choose P satisfying

    d(P) > M (r(P) + s(P) + 1).

Since d(P) > B_R, its reflection length must exceed R. Since M is at least both 2 and C,

    d(P) >= 2 r(P) + C(s(P)+1).

Choosing one such P_i with R=i gives r(P_i)>i, so reflection lengths tend to infinity, and supplies the separation in part 1 with delta=1.

`superpolynomial_overhead_implies_speedup` connects this argument directly to an abstract F(k,n). Its attainment hypothesis states that F(k,n) is zero or is achieved by an admissible sentence, exactly the finite-maximum property used in the definition of F. The nonpolynomial hypothesis and finite-budget property remain visible inputs to the theorem; they are not asserted for PA-bin.

The contrapositive is also checked: absence of a factor-two speedup family with the stated toll would imply a global linear bound in r(P)+s(P)+1, hence a linear bound on F. A positive answer to part 2 does not decide part 1: constant-factor and polynomial speedups remain compatible with a polynomial upper bound.

## Consequence for the research plan

Focus on part 2. The positive route now has a specific compositional target, and a negative result strong enough to refute polynomial overhead would also settle part 1 affirmatively. The immediate mathematical target is a cost certificate for reflection internalization or for uniform formalized Löb instances in the fixed arithmetic representation. More parser correctness alone cannot discharge either hypothesis.

One should not infer a negative answer to part 2 merely because a particular checker or proof compiler runs slowly. That would require lower bounds on the shortest direct proofs. Likewise, an efficient external checker alone does not supply short arithmetic proofs about the designated Bew predicate.

## Verification

Run `lake build` followed by `lake env lean Audit.lean`. The build and audit succeeded under Lean 4.19.0, with no additional dependencies. The audit prints the whole proof-system interface, theorem statements, and axiom dependencies. The transformation and numerical bound use only propext and Quot.sound. The choice of an infinite speedup family additionally uses Classical.choice. There are no admitted proofs or native_decide steps.

The qualitative Löb theorem itself has independent formalizations, for example the Archive of Formal Proofs entry *Gödel's Incompleteness Theorems* (https://isa-afp.org/entries/Incompleteness.html), in hereditarily finite set theory. That work is background, not a certificate of the PA-bin character bounds assumed here.
