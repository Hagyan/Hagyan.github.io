# MAIS-O11: second audit of internalization and fragment compression

25 September 2026. This is a mathematical audit and proposed certificate target. It is not a new Lean certificate or a resolution of either open question. It refers to the recovered `MAIS-A1.tex`, the `MAISO11SharedConversePass` project, and the primary sources linked below.

## 1. The constructor-DAG obstruction is real and has a precise scope

Suppose abbreviation right-hand sides may be arbitrary strings, as permitted by the agenda's phrase “fixed string.” With unary constructor notation `(D t)`, define two fragment families:

```
a_0 := (D
b_0 := )
a_(j+1) := a_j a_j
b_(j+1) := b_j b_j
```

Here spaces separate description tokens and do not become part of the expanded expression. The final word `a_n 0 b_n` is the fully parenthesized term `D^(2^n)(0)`. With charged binary names, its description uses O(n log(n+2)) characters. Its expanded term has depth 2^n+1. Every acyclic constructor DAG containing N nodes has depth at most N, because a root-to-leaf path cannot repeat a node. Hence every ordinary constructor DAG for this term has at least 2^n+1 nodes.

This independently validates the mathematical claim in `GraphDepthBarrier.lean`: arbitrary fragment abbreviations cannot uniformly be compiled to polynomial-size constructor DAGs. The Lean file currently proves the depth and graph-size statements; the bridge from the above raw-fragment program to the unary term, with its exact wire length, needs its own formal proof if that complete claim is to carry a certificate.

The obstruction does not lower-bound the size of PA proofs certifying that this string is a term or a proof line. It only lower-bounds one proposed intermediate representation. A syntax checker can operate on compressed strings without materializing the term tree or a constructor DAG. Also, in Part 2 the argument n is the expanded length of the target P: the exponential size of an example's P is already allowed in a polynomial in k+n. Exponentially long *intermediate* expressions still require care.

## 2. An exact next certificate that survives the obstruction

Use the existing arbitrary-fragment `StringQuotation.Grammar`, and compute two signed integers for every fragment w:

- d(w): number of opening parentheses minus number of closing parentheses;
- m(w): the minimum d(v) over prefixes v of w, including the empty prefix.

Other characters contribute zero. For concatenation the exact equations are

```
d(xy) = d(x) + d(y)
m(xy) = min(m(x), d(x) + m(y)).
```

They follow by splitting a prefix of xy into a prefix of x or x followed by a prefix of y. The summary of the empty string is (0,0). Summaries can therefore be computed on the grammar's backward-reference structure. Induction over definitions proves that every stored summary equals the summary of its expanded word. Balanced parentheses are then characterized exactly by d=0 and m=0. This accepts the family in Section 1 without traversing its exponentially many constructors.

The values remain small *in bits*. If g is the number of definitions plus all terminal and reference occurrences in their right-hand sides, every expanded word has length at most 2^g. To see this, maintain M as the maximum of 1 and all previous expansion lengths. Adding a right-hand side of length r changes M by a factor of at most max(1,r), which is at most 2^r. Consequently |d| and |m| are at most 2^g, and each summary component needs at most g+2 binary bits. There are O(g) concatenation operations on these O(g)-bit values. A straightforward bit implementation is polynomial; a Lean operation-count theorem and bit-cost theorem should be distinguished from one another.

This is a useful, exact milestone for the arbitrary-string layer. It is **not** a full PA grammar recognizer: lexical rules, variable identifiers, term/formula sorts, quantifier scope, and substitution conditions require additional certificates. After this milestone, substring extraction and matching-parenthesis navigation can be specified directly on compressed words. One should request the operations needed by proof checking, rather than request a complete constructor DAG.

Relevant primary research supports this direction. Ganardi, Hucke, Lohrey and Noeth, *Tree Compression Using String Grammars*, [arXiv:1504.05535v2](https://arxiv.org/pdf/1504.05535), Theorem 5, gives compressed recognition for ranked-tree preorder strings; Theorem 7 separates string and tree grammars exponentially. Theorem 19 gives polynomial evaluation specifically for SLP-compressed `{∧,∨,0,1}` trees. Its hypotheses do not cover the complete PA syntax, arbitrary `¬,→` encodings, or universal tautology checking. Fully parenthesized files need an explicit translation before the preorder results apply. These results motivate a route; they do not supply the missing PA-internal proofs.

## 3. A separate checker barrier, with the overlap loophole closed

Enderton's second edition, §2.4, printed pp.112 and 114–115, takes all propositional tautologies and their universal generalizations as logical axioms. On p.115 it explicitly distinguishes replacing this family by a polynomial-time decidable subset. His PA adds a fixed arithmetic basis and induction, described at pp.269–270. [Primary textbook PDF](https://sistemas.fciencias.unam.mx/~lokylog/images/Notas/la_aldea_de_la_logica/Libros_notas_varios/L_03_ENDERTON_A%20Mathematical%20Introduction%20to%20Logic,%20Second%202Ed.pdf).

Here is a direct reduction from ordinary propositional tautology testing to validity of a single axiom record, for that presentation. Replace each propositional letter p_i in F by the distinct closed atom `i=i`, using binary numerals; call the result F*. Distinct atomic formulas are independent letters in the *syntactic propositional skeleton*. Their arithmetic truth values are irrelevant to membership in Enderton's tautology family.

Choose a fixed, positive, even integer r exceeding the number of consecutive leading negations in any of the fixed arithmetic basis axioms. Use the single axiom record whose formula is

```
B_F := ¬^r F*.
```

This formula has no leading universal quantifier and starts with at least two negations. Thus it is not in any of Enderton's other five logical axiom groups, whose un-generalized roots are implication or equality. It is not an induction instance, whose root is implication or universal quantification. It is not one of the fixed arithmetic basis axioms by the choice of r; generalized basis axioms have a universal root. If the chosen finite basis is presented as term-substitution schemes, term substitution does not change this bounded leading-negation pattern. Therefore this record is accepted exactly when B_F is in the tautology group, which holds exactly when F is tautological. Its length and construction time are polynomial in |F|. No abbreviations occur in the reduction.

Hence a deterministic polynomial-time exact checker for this full presentation would decide TAUT in polynomial time. This is a conditional complexity obstruction to that checker strategy. It is not an unconditional impossibility theorem, and it is not a lower bound on Löb proof conversion.

In particular, it does **not** exclude a polynomial-size or polynomial-time *proof printer on promised-valid inputs*. A printer can emit another formula of the tautology axiom family whose validity follows mathematically from the validity of F, without deciding whether F is valid. The printed proof is checked by the same potentially expensive axiom recognizer. The gate construction in `TAUTOLOGY-ADVERSARIAL-NOTE.md` pursues exactly that distinction. Turning it into full PA internalization still needs a quantified evaluation/coding bridge, and its polynomial gate count currently assumes a suitably small Boolean DAG. Section 1 explains why that DAG assumption must be proved or replaced for arbitrary fragments.

## 4. The minimal conditional theorem for Part 2

One can make the required implications explicit without assuming the desired Löb transformation. Fix one syntactic calculus, one arithmetic proof predicate `Prf`, and its exact box B. Assume the following concrete proof constructors and character bounds:

1. **Small fixed points and elementary derivability instances.** For every P with |P|≤n, construct a sentence D and proofs of `D → (BD → P)` and `(BD → P) → D`. Also construct the relevant distribution and positive-introspection instances. A polynomial r(n+1) bounds their combined proof lengths and all formula lengths in the fixed construction. The distribution instances have shape `B(A→C) → (BA→BC)`; the introspection instance needed here is `BD→BBD`.
2. **External proof internalization.** From any actual proof π of A, construct an actual proof of BA of length at most I(|π|+|A|+1), for a fixed nondecreasing polynomial I. This is a theorem about proofs for the same `Prf`. It does not merely assert correctness of a different checker.
3. **Actual file assembly.** A fixed finite propositional derivation combining supplied proofs can be serialized, with valid abbreviation renaming and line references, within J(t) characters when t bounds the total supplied lengths and formulas. J is a fixed nondecreasing polynomial. It suffices that J dominates linear size; no constant-cost MP assertion is required.

The external internalization constructor in (2) does not by itself imply the internal introspection proof in (1). One sufficient way to discharge the latter is a PA proof, uniform in proof code and conclusion code, that the internalization constructor produces valid proof codes, together with its PA-provable totality. Alternatively, supply the needed introspection instances directly with their polynomial length bound. The same distinction applies to the uniform correctness of the concatenation operation behind distribution.

Here is the full unbounded Löb derivation under those assumptions. Write U=BD and V=BP. Internalizing the forward fixed-point implication gives `B(D→(U→P))`. Distribution yields `U→B(U→P)`. A second distribution instance gives `B(U→P)→(BU→V)`, and introspection gives `U→BU`. Propositional combination yields `U→V`. Combining with the input proof of `V→P` yields `U→P`. The reverse fixed-point implication now gives D. Internalize that actual proof of D to obtain U. Modus ponens with `U→P` gives P.

For an explicit polynomial ledger, enlarge r,I,J by fixed constants to cover the finite number of templates and assume each dominates its argument. Set

```
R = r(n+1)
N = J(k + R + I(2R+1) + 1)
H(k,n) = J(N + I(N+R+1) + R + 1).
```

The construction first yields D and `U→P` within N characters, then yields P within H(k,n). H is a fixed polynomial composition. For coarse bounds `r(t)=O(t^a)`, `I(t)=O(t^b)`, `J(t)=O(t^c)` with a,b,c≥1, this gives `H(k,n)=O((k+n+1)^(a*b^2*c^2))`. These exponents are deliberately loose. The assumptions are proof constructors to be built and audited; none is obtained merely by defining an efficient external data structure.

This theorem requires only two uses of unbounded external internalization and one polynomial family of unbounded introspection instances. It does not require the agenda's stronger full uniform bounded-inner-necessitation theorem or a linear one-variable expansion function E(m). Thus those stronger targets need not all be settled before Part 2 can be established.

## 5. Expanded conclusion codes: the right size parameter

For a written proof of m characters, its expanded conclusion A can have exponentially many characters. The canonical binary numeral for its ordinary string code has O(|A|) symbols. A literal computation-trace proof that writes this entire numeral therefore cannot be assumed polynomial in m alone. Compact arithmetic terms for the same integer, such as those in `StringQuotation.lean`, do not automatically have the same syntax as the canonical numeral used in the fixed box. Using them requires either a permitted compressed serialization of that numeral or an arithmetic equality proof allowing substitution into the exact `Prf` formula.

The output-sensitive hypothesis in Section 4 avoids imposing this stronger requirement: its bound depends on m+|A|. The only necessitated conclusions in the displayed Löb construction are the small fixed-point implication and D, whose lengths are already bounded by r(n+1). Its premise proof may have huge expanded intermediate lines; the internalization theorem still has to handle their compact descriptions. Thus including |A| removes one output-writing obstruction, but does not solve the arbitrary-intermediate-line verification problem.

The immediate research choice is consequently clear: preserve the full fragment grammar, certify operations directly on compressed words, and pursue promised-valid proof internalization with explicit output size and the exact fixed box. A general polynomial-time decider for Enderton proof files is an unnecessarily strong target.
