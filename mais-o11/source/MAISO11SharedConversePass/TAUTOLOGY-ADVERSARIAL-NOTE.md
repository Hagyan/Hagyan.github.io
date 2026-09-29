# MAIS-O11 Part 2: arbitrary tautology axioms and short internal proofs

Research note, 25 September 2026. This is a mathematical observation about one axiom family, not a PA-bin proof transformation or Lean certificate.

## A linear-size Boolean gate lemma

Take an ordinary propositional formula `F` with `n` occurrence-nodes and atoms among `p₁,...,pₘ`. Give each node `j` a fresh Boolean variable `vⱼ`; its root is `r`. Write `G_F(p,v)` as a conjunction of the following local equations: a leaf labelled `pᵢ` has `vⱼ ↔ pᵢ`; a negation node with child `k` has `vⱼ ↔ ¬vₖ`; an implication node with children `k,l` has `vⱼ ↔ (vₖ → vₗ)`. Express `↔` and `∧` through Enderton's primitive `¬,→`, if needed. Set

`H_F(p,v) := G_F(p,v) → vᵣ`.

**Lemma.** `H_F` is a propositional tautology if and only if `F` is a propositional tautology. Furthermore `H_F` has `O(n)` connective occurrences, and its fully written length is polynomial in the length of `F`, even when each variable index is charged in binary.

**Proof.** For any assignment to the leaves, the gate equations uniquely force, by induction in node order, each `vⱼ` to equal the value of its subformula. Consequently any assignment satisfying `G_F` gives `vᵣ=F(p)`. If `F` is a tautology, `G_F→vᵣ` is true on every assignment. If `F` is not, choose a falsifying leaf assignment and assign every gate its actual value. Then `G_F` is true and `vᵣ` false. Each gate contributes a bounded number of connective occurrences, and each indexed variable is written in `O(log(n+1))` characters. ∎

The same proof works for a Boolean **DAG** with backward references: visit its gates in topological order. Its gate formula is linear in the DAG node count even if the unfolded Boolean formula has exponential size. Applying this to PA-bin requires a certified compiler from the particular abbreviation grammar to a Boolean gate DAG; arbitrary string-fragment abbreviations are not automatically subformula references.

## Direct Enderton internalization of this family

Suppose the PA proof predicate's tautology test uses a coded Boolean assignment `a` and a coded table `t` of gate values. Let `Bᵢ(a)` and `Vⱼ(t)` be PA formulas saying the corresponding bit is 1. Substituting these formulas for the Boolean letters of `H_F` produces an instance `H_F(B(a),V(t))` of **Enderton's arbitrary propositional-tautology axiom group**, provided `F` is tautological. Universal closure over `a,t` is also permitted by Enderton's logical axiom convention. This axiom expresses directly that the propositional gate constraints imply a true root, for every valuation and table. Its written length is polynomial if each bit predicate and the numeral for every node index has polynomial written length.

The compiler can construct this *candidate* axiom in polynomial time from `F`. It need not decide whether `F` is tautological: the candidate is a valid PA proof line conditional on the validity of the input tautology axiom. A non-tautological `F` makes the candidate line invalid, exactly as the gate lemma predicts. This is the natural input-validity conditional in a Part 2 proof transformer.

For a particular arithmetized proof predicate, one must additionally produce polynomial-size PA derivations of the equivalence between the encoded test's `TraceValid(F,a,t)` and the local equations `G_F(B(a),V(t))`; or choose the test's defining arithmetic formula to be the corresponding gate equations. The universal closure of the substituted `H_F` then establishes the tautology branch of `Prf` once the remaining coding facts are shown. **This bridge has not been formalized here.** In particular, it does not by itself prove that the chosen *fixed* PA-bin `Bew` formula admits polynomial-size certificates: converting a specific primitive-recursive program's acceptance computation into its arithmetized test may itself have significant proof cost.

The gate argument applies to the Boolean skeleton of a first-order axiom. Treat each maximal first-order subformula that occurs as a propositional atom as a leaf; the original arithmetic content of that atom plays no role in Boolean validity. The exact skeleton extraction and handling of universal closure must follow the stipulated Enderton and file grammars.

## Why this does not imply `P = coNP`

The one-line axiom `H_F` can be validated only by an all-tautologies axiom check, which itself decides a coNP-complete condition on a simple propositional input family. Cook and Reckhow's polynomial-bound criterion concerns proof systems with **polynomial-time verifiable** proofs; this PA-bin calculus with arbitrary tautologies as primitive axioms does not meet that verification hypothesis. A polynomial-size PA derivation containing `H_F` therefore does not automatically yield a polynomially checkable proof of `F`. Likewise, a polynomial-time procedure that *prints a candidate derivation when given `F`* need not decide whether the printed derivation is valid. This distinction is the opening for the direct internalization construction.

Conversely, any purported polynomial-time *exact* checker for the full Enderton tautology family would yield a polynomial-time TAUT decision procedure. The gate lemma makes that concern explicit: `F` is tautological exactly when the constructed line `H_F` belongs to this axiom family. In a whole-file reduction, ensure other axiom groups cannot independently admit the selected candidates; one can use a disjoint sentential encoding or explicitly check and handle those finitely many other syntactic shapes. This is a complexity obstacle for a particular checker strategy, not a lower bound on Part 2's proof transformation.

## Precise remaining obligations

1. Fix the literal arithmetic formula `Bew` and Boolean-valuation predicate for the target PA-bin checker. A semantically equivalent but different arithmetization cannot silently replace that specified formula in a proof-length claim.
2. Specify whether universal generalizations of Boolean tautologies are individual axiom lines or require charged generalization records. Write and bound the actual record sequence accordingly.
3. Formalize the Boolean gate lemma in Lean, prove that substitution by PA formulas produces an allowed Enderton axiom, and certify serialization with all indices and abbreviations charged.
4. Derive the arithmetized gate constraints and the entire line-acceptance predicate from this axiom with an explicit polynomial bound in PA's actual syntax. Then compose these per-line proofs and the MP, generalization, arithmetic-axiom and abbreviation cases.

Primary references: Enderton, *A Mathematical Introduction to Logic*, second edition (2001), ch. 2 axiom groups (textbook PDF consulted in the project audit); Cook and Reckhow, [*The Relative Efficiency of Propositional Proof Systems*](https://www.cs.toronto.edu/~sacook/homepage/cook_reckhow.pdf), *Journal of Symbolic Logic* 44 (1979), 36–50. The latter supplies the polynomial-time proof verification hypothesis used in the complexity comparison.
