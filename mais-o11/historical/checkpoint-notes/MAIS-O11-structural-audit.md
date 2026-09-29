MAIS-O11: does the obstruction make part 1 impossible?

23 September 2026

The investigation does not establish impossibility for the intended PA-bin question with finite proof lengths. It establishes a defect in the literal formulation, explains a structural obstruction to our earlier candidate families, and identifies the much stronger statement needed for a general negative answer. Neither part of MAIS-O11 has been settled for the intended PA-bin predicate by the supplied work.

Fix the proving system and its own provability predicate throughout. Write

\[
d(P)=\ell_S(P),\qquad r(P)=\ell_S(\Box_S P\to P),\qquad s(P)=|P|.
\]

The sentence size here is the expanded formula size specified by the agenda, whereas proof length charges the written file with its allowed abbreviations. Fix a particular valid constant \(C_1\) for the agenda's forward weakening bound.

1. The literal formulation needs a finiteness condition.

The agenda defines proof lengths in \(\mathbb N\cup\{\infty\}\), but question 3.6(1) only says “a sequence of sentences.” It does not explicitly require that these sentences, or their reflection instances, have proofs.

Read with the usual extended-value arithmetic and meaning of tending to infinity, this admits the degenerate choice \(P_i=\bot\) for every \(i\). Consistency gives \(d(P_i)=\infty\). Löb's theorem gives \(r(P_i)=\infty\): otherwise a proof of \(\Box_S\bot\to\bot\) would yield a proof of contradiction. Consequently the reflection lengths tend to infinity and the requested inequality becomes \(\infty\ge\infty\).

This does not exhibit a saving between proofs. It is a drafting loophole, and disappears under the intended finite-proof reading. The repair is to require \(S\vdash P_i\) for every \(i\), or equivalently \(r(P_i)<\infty\), using Löb and ordinary weakening. The rest of this audit uses that repaired statement.

2. The comparison excludes the cost of compiling the rule back into PA.

A completed S-proof of P obtained through an arithmetized Löb argument cannot be shorter than d(P). That follows directly from the definition of a minimum: such a proof is one of the proofs already being minimized over.

MAIS-O11 compares d(P) with the length r(P) of a different conclusion, before paying for that conversion. One precise interpretation is a new certificate format: a certificate for P may consist of an ordinary S-proof of \(\Box_S P\to P\), accompanied by a tag permitting one application of Löb's rule. The box still denotes the original S, not the new certificate system. The checker verifies the original S-proof and its conclusion shape. Löb's theorem shows that the new certificates prove exactly S's theorems, but they can in principle have different lengths.

Thus the question concerns the quantitative cost of eliminating an admissible rule. The observation about shortest completed proofs is a tautology; it does not answer the comparison actually written in part 1. The general distinction between theoremhood and lengths in different presentations is standard in proof complexity; see Pudlák, section 2.4 [1].

3. The formal target is substantially stronger than the headline.

After the finiteness repair, part 1 asks for a fixed \(\delta>0\) and an infinite family such that

\[
r(P_i)\longrightarrow\infty,\qquad
d(P_i)\ge(1+\delta)r(P_i)+C_1(s(P_i)+1).
\tag{1}
\]

One example with \(d(P)>r(P)\) would not suffice. Even an infinite family with unbounded additive savings would not suffice without a fixed relative saving. For illustration only, a hypothetical profile \(d=r+\sqrt r\), with \(r\to\infty\), saves an unbounded number of symbols but eventually fails every fixed positive \(\delta\) in (1), even before adding its nonnegative toll. This numerical illustration is not a constructed family of PA sentences.

The constant \(C_1\) is another convention that must be fixed. A bound proved with a larger coefficient of sentence size cannot simply be substituted for the particular coefficient in (1). Such a substitution is harmless only with an additional estimate that absorbs the difference, for example along families with sentence size negligible compared with reflection length.

4. Our previous obstruction has an explicit hypothesis.

Suppose an independent proof of \(\Box_S P\) can be supplied and appended to a reflection proof, with total added cost \(e(P,r)\), including the final modus ponens. Then

\[
d(P)\le r(P)+e(P,r(P)).
\tag{2}
\]

Combining (1) and (2) forces

\[
\delta r(P)+C_1(s(P)+1)\le e(P,r(P)).
\tag{3}
\]

In particular, a family for which this added cost is \(o(r(P_i))\) cannot witness (1). This is a real structural obstruction to that family. It does not exclude a small additive saving, and it does not apply to every theorem without a bound on e.

The previous Lean project verifies a specific form of (2) in a structured Hilbert interface:

\[
d\le r+aL(r),\quad
L(r)=\lfloor\log_2(r+2)\rfloor+1,
\]

where a is explicitly controlled by a supplied plain proof of \(\Box P\) and the sentence size. It also verifies integer consequences excluding the proposed exponential-direct/polynomial-provability family. These theorems retain their numerical and proof-system hypotheses. The complete PA-bin parser and its identification with the fixed arithmetic Bew predicate are not supplied by that certificate.

For our ordinary finite Gödel family, the mechanism is logical as well as quantitative. Put \(B_n=\Box_{2^n}G_n\), with a proved fixed-point equivalence \(G_n\leftrightarrow\neg B_n\). Inside PA, the case \(B_n\) gives \(\Box G_n\) by forgetting the bound. The case \(\neg B_n\) gives provability of that decidable condition by formalized completeness, and hence \(\Box G_n\) through the fixed-point implication. Both cases yield provability. Turning a uniform version of this argument into short instance proofs activates (2); it does not produce short reflection proofs independently of the direct lower bound.

This is related to the classical finite-consistency construction in Pudlák, theorem 7.2.2 [1]: under its stated hypotheses, a sentence can have long direct proofs and short proofs of its provability. Transferring that paper's numerical bounds to the agenda's compressed calculus requires checking its assumptions. The elementary modus ponens obstruction itself explains why that familiar speedup is not a reflection speedup.

5. One proposed way to globalize the obstruction is impossible.

Here is a separate metamathematical observation. Assume standard PA and its ordinary proof predicate, and use PA's \(\Sigma_1\)-soundness. There is no total computable function g such that

\[
\ell_{\mathrm{PA}}(\Box_{\mathrm{PA}}P)\le g(|P|)
\quad\text{for every PA theorem }P.
\tag{4}
\]

Proof. Given any sentence P, compute g(|P|), and check all proof files of at most that length for a proof of \(\Box_{\mathrm{PA}}P\). There are finitely many such files and the checker terminates on each. If P is a theorem, (4) guarantees acceptance. If acceptance occurs, PA proves the \(\Sigma_1\) sentence \(\Box_{\mathrm{PA}}P\); soundness makes this true in the standard natural numbers, so an actual PA proof of P exists. This procedure would decide PA theoremhood, contradicting its undecidability. QED.

The soundness qualification matters: the argument is not asserted for every merely consistent extension of PA. The result also does not rule out a general negative answer by some other mechanism. It only blocks extending a sentence-size-only bound on independent provability proofs to all PA theorems.

6. The exact missing negative theorem can be stated cleanly.

For the fixed S, box, length conventions and \(C_1\), the negation of the repaired part 1 is

\[
\begin{split}
&\forall\varepsilon>0\ \exists K\ \forall P\in\operatorname{Th}(S),\\
&r(P)\ge K\quad\Longrightarrow\quad
d(P)<(1+\varepsilon)r(P)+C_1(s(P)+1).
\end{split}
\tag{5}
\]

To see the equivalence, a witnessing sequence for (1) eventually has reflection length above any K, contradicting (5) at \(\varepsilon=\delta\). Conversely, if (5) fails, there is one positive \(\varepsilon\) for which every integer K admits a violating theorem P. Choosing such a P with \(K=i\) constructs a sequence satisfying (1) and \(r(P_i)\ge i\).

A sufficient result would be a uniform conversion bound

\[
d(P)\le r(P)+C_1(s(P)+1)+h(r(P)),
\qquad h(r)/r\longrightarrow0.
\tag{6}
\]

For each fixed positive \(\varepsilon\), choose K so that \(h(r)<\varepsilon r\) for \(r\ge K\). Then (6) implies (5). No estimate of the form (5) or (6) has been established here for PA-bin. The word “uniform” means that the threshold depends on \(\varepsilon\) and the fixed system, not on P.

Continuation, 23 September 2026: the finite-budget argument in MAIS-O11-envelope-theorem.md now shows that (6) is also necessary for a negative answer, by taking h to be the maximum positive excess among targets below a reflection budget. The equivalence and the consequence that a negative part 1 implies a joint affine linear upper bound in part 2 have been checked in the separate envelope Lean project. This corrects the earlier description of (6) as a stronger condition. Its truth for actual PA-bin remains unresolved.

7. Part 2 does not make part 1 impossible.

A polynomial upper bound

\[
d(P)\le C(r(P)+s(P))^c
\]

allows fixed-factor separations. Even the conjectured stronger bound \(d(P)\le C(r(P)+s(P)^c)\) can allow them when \(C>1\). For example, the numerical behavior \(d=2r\), \(s=o(r)\) is compatible with such an upper bound and would satisfy (1) for suitable \(\delta<1\) eventually. Again this is a compatibility check, not a PA witness.

A generic efficient conversion establishes an upper bound; it does not establish that its leading coefficient is arbitrarily close to one. Critch explicitly treats linear expansion as an expectation about engineered proof systems [2]. Visser discusses polynomial-time transformations in the ordinary incompleteness/Löb setting [3]. Neither statement supplies the near-unit character bound (6) for the agenda's exact abbreviation grammar.

Our earlier aspiration to combine exponential direct lower bounds with polynomial reflection upper bounds and polynomial sentence size was much stronger than necessary for part 1. Such a family would also refute the polynomial alternative in part 2. Failing to obtain that stronger result should not be read as evidence against a modest fixed-factor separation.

8. The reason for the present difficulty is mathematical and representational.

The positive direction needs a lower bound on every direct proof, paired with an upper bound on reflection proofs of those same sentences. Our available finite diagonal construction produces the lower bound together with independent cheap provability, and those features obstruct the desired pairing. A negative solution requires controlling all provable sentences as in (5), beyond the scope of that construction.

Exact presentations also matter at this scale. The agenda gives substantial conventions but still leaves the full parser, some serialization choices, and the actual arithmetic formula representing its checker to implementation. Binary numerals and abbreviations alone do not prove a polynomial bound on PA proofs that certify the checker. Agreement on standard accepted files does not by itself provide a short PA proof equating two representations. A constant-factor comparison cannot be transferred merely from a polynomial simulation.

The Lean work verifies its stated conditional results. It does not discharge a missing PA-specific assumption merely by compiling successfully. More quotation infrastructure would be useful for the upper-bound project, but is not by itself evidence that the part 1 witness is close. Earlier optimism about finishing that witness by completing internalization was not justified.

The appropriate next mathematical targets are now explicit: fix the finite formulation and the concrete presentation; investigate a uniform estimate such as (5) for a negative result; or construct a family with the required direct/reflection separation whose independent provability certificates do not trigger (3). A single strict saving, or an unbounded additive saving, would be a distinct and worthwhile intermediate result, but should be labeled separately from the stronger formal part 1.

References and scope of verification

The statement audited is the uploaded MAIS-A1.tex, sections 2 and 3, together with MAIS-O11.md. The finite-length repair and the deductions (2)–(6) above are mathematical arguments presented in this note; this note does not claim a new Lean certificate. The earlier certificate is in MAIS-O11-PA-bin-obstruction.zip, with its scope documented in the accompanying obstruction note.

[1] Pavel Pudlák, *The Lengths of Proofs*, Handbook of Proof Theory (1998), especially sections 2.4, 7.1 and 7.2. https://users.math.cas.cz/~pudlak/length.pdf

[2] Andrew Critch, *Parametric Bounded Löb's Theorem and Robust Cooperation of Bounded Agents*, arXiv:1602.04184v5, especially section 5's discussion of the expansion function. https://arxiv.org/html/1602.04184v5

[3] Albert Visser, *Kripke's Reduction of Löb's Theorem to the Second Incompleteness Theorem*, Theoria, especially section 3.1. https://onlinelibrary.wiley.com/doi/full/10.1111/theo.70041
