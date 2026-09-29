# MAIS-O11 continuation: compact modus ponens and the padding obstruction

## Status

The fixed `PA_bin` questions are open in this checkpoint. Two results below
have been checked in Lean 4.19.0: a modular bridge from compact-term equality
to formula and proof-record checking, and a numerical obstruction to the
artificial padded proof system satisfying constant-cost modus ponens. A simpler
metamathematical construction answers Part 1 under *only* the agenda's three
enumerated conditions for an efficient system, but it does not satisfy a
separate constant-cost implication-composition assertion in the agenda. This
last construction is a paper argument, not a Lean certificate of a full
arithmetized proof checker.

## 1. A compact equality interface that reaches proof checking

`CompactEquality.lean` proves `formulaEqual_iff`: any Boolean comparator for
compact terms which agrees with equality of expanded arithmetic terms extends
to a comparator for all `CFormula` syntax, including nested quantifiers.
Variable contexts are indexed by `n`, and a term reference is closed, so it
cannot acquire a free variable when comparison passes under a binder.

`mpEqual` inspects the outer implication constructor in the compact formula
and calls `formulaEqual` on the antecedent and consequent. `mpEqual_iff`
proves equivalence with the old check of fully expanded formulas. The
certified replacement covers every MP record in any `Records` value:

* `Records.checkWithTermEqual_iff` proves acceptance iff the original
  `Records.valid` relation holds;
* `Records.checkWithTermEqual_derivable` proves all accepted conclusions are
  derivable in the restricted ordinary Hilbert calculus;
* `checkWithTermEqual_agrees` instantiates the interface with an expanded-term
  reference comparator and proves equality with the existing checker on
  **all** structured proof records, not just examples.

The `graphReferenceEqual` comparator actually consults the certified graph
equality table when both compared terms are references. Its remaining cases
use the old expanded-term comparator. `graphReferenceEqual_correct` proves
that this hybrid comparator satisfies the interface for any graph whose
expanded roots are the given abbreviation dictionary. A separate induction
proves that embedding a closed term into an arithmetic term preserves syntax
equality; the graph comparison requires this injectivity.

`SharedMPDemo.lean` evaluates two MP comparisons over a 63-node graph:
one accepts syntactically equal roots, the other rejects a zero root in place
of an addition root. The common root's fully expanded term has
`2^62-1 = 4,611,686,018,427,387,903` nodes. The test evaluates the graph
table and compact formulas; it does not construct that expansion.

**Remaining scope:** the previous `readDefinitionPrelude` still creates
expanded `ClosedTerm` values, and `axiomCheck` still receives expanded
formulas. The fallback branch of `graphReferenceEqual` can also expand an
enormous term. The new bridge certifies *where* a polynomial shared-term
comparator can be substituted into MP checking. It does not yet prove a
polynomial algorithm for arbitrary proof files, much less a polynomial PA
proof that the checker accepts one.

## 2. A simpler literal padded construction

The previous padding sketch used special axioms
`Box_S Q_i -> Q_i` and a recursion theorem to make the box refer to its
own checker. That self-reference is unnecessary if one uses exactly the
three bulleted conditions in MAIS-A1, Section 2, as the definition of
"efficient". Here is a simpler, non-self-referential construction.

Let `E_i` be the binary-numeral equality `i=i`, and set
`Q_i := ¬¬E_i`. Fix a conventional Hilbert presentation of PA with binary
numerals and nested proof abbreviations. Add every formula `A -> Q_i`, where
`A` is any sentence and `i` is any natural number, as a special axiom.
Membership in this family is decidable by reading the consequent; `Q_i`
is an ordinary PA theorem, so every special axiom is already a PA theorem.
Thus this augmentation does not change PA theoremhood, and no semantic
soundness or self-reference assumption is needed for conservativity.

Modify proof files by requiring a literal trailer of at least
`(|F|+1)^2` copies of a designated padding character when their **final
expanded conclusion** `F` starts with negation. There is no terminal
padding for other conclusions. This is a primitive recursive proof predicate:
the checker expands a finite abbreviation list, tests the standard Hilbert
derivation and the special axiom shape, then checks the trailer against a
computed length. Every PA proof can be given the required finite trailer.
The same finite abbreviation grammar is available; all characters of the
trailer are charged. The checker is not claimed to run in polynomial time.

For this system `S`, write `s_i=|Q_i|`, `d_i=ell_S(Q_i)` and
`r_i=ell_S(Box_S Q_i -> Q_i)`. Every direct proof has
`d_i >= (s_i+1)^2`. Conversely, the reflection formula is **one special
axiom**, taking its antecedent `A=Box_S Q_i`. The fixed proof predicate and
binary Gödel numerals give constants `a,b` such that
`r_i <= a(s_i+1)+b`. The proof strings for the distinct reflections have
unbounded minimum lengths by the finite alphabet counting argument, and
`s_i` tends to infinity. The existing Lean theorem
`cofinal_factor_two_speedup` proves that for every fixed append toll `C_1`,
eventually `d_i >= 2*r_i+C_1(s_i+1)`. Reindexing the family beyond that
threshold meets the numerical Part 1 inequality with `delta=1`.

The append toll exists for this trailer convention: from a proof of any `P`,
remove its terminal trailer, append the usual propositional axiom
`P -> (Box_S P -> P)` and an MP record, and end with the implication
`Box_S P -> P`, which requires no trailer. With local backward line
references, the extra written size is `O(|P|+1)`. Removing the old trailer
can only reduce length.

This paper construction eliminates the recursion-theorem and Löb-proof
obligations from the **literal** padded example. It does not address the
fixed ordinary `PA_bin` presentation. A complete machine-checkable
certificate for its checker, conservativity and exact byte lengths has not
been produced.

## 3. Why the padded example fails the agenda's MP accounting

The same agenda asserts an *implication distribution* bound with a fixed
constant `c_S`: combining a proof of `A -> B` of length `a` with a proof of
`A` of length `b` yields a proof of `B` of length at most `a+b+c_S`.
Our trailer system cannot satisfy that assertion. Fix one short PA theorem
`U`, such as `0=0`. Its proof length `B` in `S` is constant. The special
axiom `U -> Q_i` has a one-line proof of length at most `a(s_i+1)+b`.
If MP composition cost a fixed `c_S`, it would yield

    d_i <= B + a(s_i+1) + b + c_S.

But every proof of `Q_i` must have
`d_i >= (s_i+1)^2`, a contradiction for large `i`.
`CompositionBarrier.lean` checks the quantified numerical contradiction
as `quadratic_fee_excludes_constant_mp`, under explicit cofinality and
length-bound assumptions. This does **not** prove a theorem about `PA_bin`.

There is consequently a difference between the agenda's three-item
definition of "efficient" and the constant-composition property it also
attributes to such systems. The padded construction is a literal Part 1
example if only those three items are imposed; it fails if the intended
class includes the displayed implication-distribution bound. I would not
advertise it as resolving the intended open problem without first settling
that convention. The ordinary `PA_bin` checker has constant MP assembly and
is unaffected by this artificial ambiguity.

## 4. Actual remaining roadblock

The earlier finite-Gödel attempt supplied short proofs of ordinary
`Box P` and sought short proofs of `Box P -> P` while proving long lower
bounds on direct `P` proofs. Appending those two short proofs yields a
short direct proof, defeating the desired lower bound. A subsequent
guarded-box construction used two *different* provability predicates; a
short bridge to ordinary `Box P` was missing. The new checker work targets a
different requirement: obtaining a quantitative internalization procedure
for the **same** ordinary `PA_bin` box.

The next concrete implementation target is a general parser that retains
abbreviation definitions as shared nodes, followed by a full term comparator
whose every branch uses those nodes. After that, compact axiom recognition
must replace `axiomCheck (f.expand δ)`. These are prerequisites for a useful
computational checker; a polynomial bound on PA proofs of its verification
and of the formalized Löb instances remains a separate arithmetic theorem.

## Verification

The project uses Lean 4.19.0 and Std. From its root, run:

    lake build
    lake env lean SharedMPDemo.lean
    lake env lean CompositionBarrier.lean

The two executable graph cases pass, as does the proof dependency audit. The
new named bridge and obstruction theorems depend only on Lean's standard
`propext` and `Quot.sound`; no `sorry`, custom axiom or `native_decide` occurs
in these files. The test is of the stated comparison algorithm, not an
instrumented time-cost theorem.
