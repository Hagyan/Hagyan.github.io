# MAIS-O11: an obstruction to the current PA-bin witness

23 September 2026

**Status: neither part of MAIS-O11 is resolved for the intended PA-bin provability predicate.** This continuation proves a quantitative obstruction to the proposed transfer. It also checks a concrete proof-suffix construction in Lean. The previous quotation and arithmetic-trace certificates remain valid within their stated scope; they do not establish the missing separation.

The central distinction is between a short proof of **provability**, \(\Box P\), and a short proof of **reflection**, \(\Box P\to P\). The former can prevent the latter from being substantially shorter than a direct proof. Improving the internalization machinery does not remove that obstruction.

## 1. A necessary inequality for any candidate

Fix a sentence \(P\). Write

\[
d=\ell(P),\qquad r=\ell(\Box P\to P),\qquad s=|P|.
\]

Suppose we have a **plain**, abbreviation-free proof of \(\Box P\) containing \(b\) characters. The length \(b\) is the length of a supplied proof, not necessarily a minimum. Define

\[
L(x)=\lfloor\log_2(x+2)\rfloor+1,
\qquad a=(b+s+7)\bigl(2L(b+1)+5\bigr).
\]

For the explicit suffix-record serialization in the accompanying Lean project, appending that proof and one modus ponens record gives

\[
\boxed{d\le r+aL(r).}\tag{1}
\]

The original reflection proof stays unchanged. Only references inside the appended plain proof are shifted. The final record uses its conclusion \(\Box P\) and the original conclusion \(\Box P\to P\). A plain suffix introduces no abbreviation names that could collide with names in the original proof.

The serialization uses axiom, modus ponens, and generalization records. A line reference is `r`, followed by a unary bit-length header, a separator `0`, and the binary digits of the index plus one. Formula characters, spaces, newlines, variable indices, and both modus ponens references are charged. The constants above concern this explicitly implemented serialization. The uploaded agenda does not provide a byte-level source parser or exact line-reference encoding. Other conventional binary encodings alter these constants, while preserving the logarithmic form of (1).

**Formalization boundary:** Lean verifies relocation, acceptance in the structured Hilbert model, and the character count of its serialization. The axiom predicate and formula operations are parameters. The prefix is supplied as its expanded formula history. There is no theorem here identifying a complete parsed PA-bin file, its arithmetic `Bew` formula, and this model. Applying (1) to the intended calculus still requires that interface. No new arithmetic provability predicate has been substituted for the intended one.

Now suppose part 1's desired inequality holds with \(\delta=1/q\), where \(q\ge1\), and nonnegative toll \(t\):

\[
d\ge(1+1/q)r+t.
\]

Multiplying by \(q\) and combining with (1) gives the necessary condition

\[
\boxed{r+qt\le qaL(r).}\tag{2}
\]

This includes the agenda's toll by setting \(t=C_1(s+1)\). Considering all positive integers \(q\) suffices to exclude any fixed positive real \(\delta\): choose \(1/q\le\delta\).

Thus a proposed speedup needs the cost of independently supplying \(\Box P\) to be significant relative to the shortest reflection proof. One cannot combine an arbitrarily hard direct-proof family with cheap provability certificates and then independently declare its reflection certificates cheap.

## 2. An explicit bound, proved in Lean

The elementary inequality

\[
(m+1)^2\le4\cdot2^m
\]

implies

\[
L(r)^2\le4(r+2).
\]

If \(r\le KL(r)\) and \(r\ge2\), squaring and using \(r+2\le2r\) gives

\[
r^2\le K^2L(r)^2\le4K^2(r+2)\le8K^2r.
\]

Cancel \(r>0\). Including \(r=0,1\), we obtain

\[
r\le8K^2+1.
\]

With \(K=qa\), condition (2) therefore forces

\[
\boxed{r\le8(qa)^2+1,\qquad
d\le(a+1)\bigl(8(qa)^2+4\bigr).}\tag{3}
\]

The second inequality follows from (1), \(L(r)\le r+3\), and the first inequality. These are deliberately coarse estimates; their role is to establish an obstruction, not an optimal threshold.

For a family, suppose

\[
d_n>2^n,\qquad
d_n\le r_n+a_nL(r_n),\qquad
a_n\le A(n+1)^e.
\]

Set

\[
C=(A+1)\bigl(8(qA)^2+4\bigr).
\]

If the separation held at index \(n\), (3) would imply

\[
d_n\le C(n+1)^{3e}.
\]

Lean proves that this is impossible whenever

\[
\boxed{n>8(C+3e)^2+1.}\tag{4}
\]

In particular, **every sufficiently late member is excluded**, not just an unbounded subsequence. The theorem is `no_separation_after`. Its arguments explicitly include the direct lower bound, the assembly bound, and the polynomial coefficient bound. It does not define PA's shortest-proof lengths or assert those hypotheses for PA by fiat.

If the usual reverse inequality \(r_n\le d_n+O(s_n+1)\) is also available and \(s_n\) is polynomial in \(n\), these estimates imply \(d_n/r_n\to1\). That limit is a mathematical consequence of the estimates; the project formalizes the integer inequalities rather than a real-analysis limit theorem.

## 3. Why the original finite Gödel family has this problem

For the ordinary proof predicate, let \(G_n\) be a finite Gödel sentence satisfying

\[
\mathrm{PA}\vdash G_n\leftrightarrow\neg B_n,
\qquad B_n=\Box_{2^n}G_n.
\]

The following argument occurs **inside PA**, using the standard arithmetization and its derivability properties:

1. \(B_n\to\Box G_n\), by forgetting the length bound.
2. \(\neg B_n\to\Box\neg B_n\), by formalized \(\Sigma_1\)-completeness for a \(\Sigma_1\) presentation of this decidable bounded-checking condition.
3. Necessitate the diagonal implication \(\neg B_n\to G_n\), then use distribution to obtain \(\Box\neg B_n\to\Box G_n\).
4. The cases \(B_n\) and \(\neg B_n\) both yield \(\Box G_n\).

No consistency premise is needed in this internal argument. Consistency is used separately to establish the external lower bound on direct proofs of \(G_n\). The two facts coexist: PA can prove that these sentences have proofs without possessing short direct proofs of them.

With a uniform diagonal family, the same construction gives a uniform theorem asserting provability of its instances. Specializing that fixed theorem, and checking the instance-code calculation, is the source of the short plain provability proofs in the original proposal. The promised polynomial plain-proof bounds and their connection to the exact fixed `Bew` have not been fully certified as PA object proofs in the supplied Lean projects. **If those bounds are completed, they activate the obstruction above; they do not finish part 1.**

`finite_diagonal_box` verifies the logical argument with its three object-theory inputs explicit. Its formula type and provability relation are parameters. It is not a formalized PA diagonal lemma. Likewise, the project distinguishes a family of metatheoretic instance proofs from one PA proof containing an object-level universal quantifier.

The same test applies to many bounded comparisons of the two proof lengths. For example, a finite sentence saying that every sufficiently short direct proof has a shorter reflection proof has the following feature: falsity supplies a direct proof of the sentence, while truth supplies provability by decidable completeness. This recreates the cheap-provability mechanism. It does not by itself prove that every conceivable comparison construction fails; the quantitative obstruction applies when the displayed growth and cost hypotheses hold.

For background, Pudlák's [*The Lengths of Proofs*, §7.2](https://users.math.cas.cz/~pudlak/length.pdf) gives the classical short-provability construction for finite consistency statements. Its hypotheses and proof-system conventions must be checked before transferring numerical bounds to a compressed Enderton calculus.

## 4. What happens to the guarded-checker construction

The previous construction used two boxes: ordinary provability and guarded provability. Its short reflection proofs concerned the guarded box, while its independent short provability proofs concerned the ordinary box.

The obstruction does not identify those formulas. It explains why doing so is invalid: once the short ordinary-provability proofs are paired with ordinary reflection, they assemble into direct proofs at the cost estimated above. A uniformly cheap bridge between the two provability predicates would destroy the proposed exponential separation.

Agreement on which standard proof files are accepted does not imply a short PA proof of agreement between two arithmetic representations. The guarded construction remains a result about a different representation; it is not a separation witness for the intended ordinary PA-bin box.

## 5. A different family, and an exact remaining obstruction

Consider instead

\[
T=\mathrm{PA}+\mathrm{Con}(\mathrm{PA}),\qquad
Q_n=\mathrm{Con}(T)\restriction n.
\]

Here \(Q_n\) says that no \(T\)-proof of contradiction has at most \(n\) characters, using a fixed ordinary arithmetization. Assume \(T\) is consistent. Each standard instance \(Q_n\) is then true and has a PA proof by finite checking.

This family passes a necessary test that the earlier family fails:

\[
\mathrm{PA}\nvdash\forall n\,\Box_{\mathrm{PA}}Q_n.\tag{5}
\]

To prove (5), suppose PA proved the displayed universal statement. In \(T\) we have \(\mathrm{Con}(\mathrm{PA})\). For the fixed decidable family \(Q_n\), PA proves

\[
\neg Q_n\to\Box_{\mathrm{PA}}\neg Q_n.
\]

Combining this with \(\Box_{\mathrm{PA}}Q_n\) would yield \(\Box_{\mathrm{PA}}\bot\), contrary to \(T\)'s consistency axiom. Therefore \(T\) would prove \(\forall n Q_n\), which is \(\mathrm{Con}(T)\). This contradicts Gödel's second incompleteness theorem for the consistent theory \(T\).

This is an arithmetic argument using standard derivability and completeness facts, not a new claim to have implemented those facts in Lean. It also does **not** show that no externally established short provability proofs exist. It excludes the uniform PA theorem that powered the original construction.

The slow-consistency variant does not provide the same escape. Freund and Pakhomov's [*Short Proofs for Slow Consistency*, Corollary 2.4](https://arxiv.org/abs/1712.03251) explicitly establishes uniform PA-provability of the finite consistency statements for PA plus slow consistency. Their Proposition 3.7 shows that the corresponding uniform fast-growing-function argument cannot simply be reused for PA plus ordinary consistency.

For \(Q_n\), **a suitably short PA proof of \(\Box_{\mathrm{PA}}Q_n\to Q_n\) is still missing**, together with the matching lower bound in the exact compressed calculus. The new family therefore does not resolve part 1. Bounds from a different Hilbert presentation or from a stronger theory cannot be silently imported. In particular, a reflection proof in \(T\) about the PA box would mix the proving theory and the boxed theory, contrary to the problem's requirement.

## 6. Results of the candidate audit

| Candidate mechanism | Result of this audit |
|---|---|
| Ordinary finite Gödel sentences with exponential hardness and polynomial plain provability proofs | Excluded by (1)–(4), once the stated proof bounds and representation interface are supplied. |
| Larger PA-provably total search bounds in the same construction | They preserve the short uniform-provability mechanism; enlarging the bound alone does not repair the comparison. |
| Bounded sentences comparing direct and reflection proofs | Their falsity can itself supply a direct proof. This must be checked against the same obstruction. |
| Transferring the guarded-box witness to the ordinary box | Requires the bridge that the earlier lower-bound argument obstructs. |
| The cited slow-consistency construction | Supplies uniform provability again; it does not supply the desired ordinary-box separation. |
| Finite consistency of PA plus ordinary consistency | Avoids the uniform-provability theorem by (5); the required quantitative reflection upper bound remains unproved. |

No affirmative PA-bin witness or general negative solution to MAIS-O11 follows from this table. It records which arguments survived checking and where each attempted route stops.

## 7. Lean verification

The archive contains a Lean **4.19.0** project using **Std only**. Run:

```bash
lake build
lake env lean Audit.lean
```

The principal files are:

* `SuffixAssembly.lean`: concrete binary reference encoding; relocation preserves structured axiom, MP, and generalization records; construction of a proof suffix ending in the desired MP; bounds on its serialized characters.
* `ObstructionBounds.lean`: normalization of the logarithmic cost; necessary separation inequalities; an explicit eventual contradiction with exponential direct lower bounds.
* `FiniteDiagonalLogic.lean`: the conditional logical derivation of provability for a finite diagonal sentence. It does not conflate Lean implication with the parameterized object-language implication.
* `Audit.lean`: theorem signatures and dependency audit.

All audited dependencies are among Lean's `propext` and `Quot.sound`; the three logical interface theorems use no axioms. There are no admitted proofs, `native_decide` proofs, or user-declared axioms. `checked-output.txt` records a clean build and audit. `SHA256SUMS` identifies the delivered source files.

The certificate establishes an obstruction and a proof-assembly construction. It is not a certificate of part 1, part 2, the exact PA-bin checker, or the uniform arithmetization claims discussed in the mathematical sections.
