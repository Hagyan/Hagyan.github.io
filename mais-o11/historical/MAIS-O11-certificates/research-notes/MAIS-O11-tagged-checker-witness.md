# MAIS-O11: a connective-tagged PA presentation

22 September 2026 · Research continuation for Andrew Hagy

**Status.** This note gives a mathematical construction for the explicitly permitted *chosen-system* branch of part 1, assuming PA is consistent. It also proves a quantitative obstruction to transferring this construction to an ordinary provability predicate. The construction uses a deliberately guarded verifier; it is not the prescribed PA-bin verifier. The accompanying Lean files certify concrete syntax invariants and the stated numerical implications. They do **not** yet certify the complete arithmetization, diagonal construction, or proof-length estimates below. No claim of historical novelty or independent review is made.

## 1. Result and its scope

There is a recursively presented, consistent arithmetic system \(S\), with binary numerals and nested priced abbreviations, and an effectively specified sequence \(P_n\), such that for fixed positive integers \(a,b,d\),

\[
 |P_n|+1\le b(n+1),\qquad
 \ell_S(\Box_S P_n\to P_n)\le a(n+1)^d,\qquad
 \ell_S(P_n)>2^n.
 \tag{1}
\]

The reflection formulas are distinct, and their minimum proof lengths tend to infinity. An effective subsequence therefore gives the inequality in MAIS-O11(1), with \(\delta=1\), for any fixed cheap-reflection constant \(C_1\). Moreover \(F_S\) is not bounded by any polynomial in its two arguments.

Here \(S\) has **exactly the same accepted proof files, conclusions, and written lengths** as an ordinary PA calculus \(B\), under the consistency assumption. It adds no arithmetic axiom and no new predicate symbol. It uses a different verification procedure and its corresponding arithmetical proof predicate. A redundant primitive conjunction connective, already standard in many logical languages, supplies the syntactic tags.

There are also polynomials \(q_1,q_2\) such that

\[
 \ell_B(\Box_B P_n\to P_n)+q_1(n)>2^n,
 \tag{2}
\]

\[
 \ell_B(\Box_B P_n\to\Box_S P_n)+q_2(n)>2^n.
 \tag{3}
\]

Thus the same family has short reflection proofs for the guarded box and long reflection proofs for the ordinary box. Identity translations of proof files do not supply polynomial-size proofs aligning these boxes. This is a concrete obstruction to transferring this witness to the fixed system in part 2. It does not determine \(F_{\mathsf{PA}_{\rm bin}}\).

## 2. Fixing the ordinary arithmetic calculus

Choose a finite-basis classical Hilbert calculus for PA with logical constructors

\[
 =,\quad\neg,\quad\to,\quad\forall,\quad\mathbin{\&}.
\]

The last symbol is **primitive conjunction**, with its usual introduction and elimination axiom schemes. It is not automatically expanded into negation and implication. All connectives other than these can be defined using the core connectives. Terms use the usual PA symbols and the definitional binary constructors \(b_0(t)=2t\), \(b_1(t)=2t+1\). Variables and abbreviation names have distinct reserved prefixes and self-delimiting binary indices over one fixed finite alphabet.

Proof files are lists of tagged axiom, modus ponens, generalization, and definition records. A definition names a complete term or complete formula and may refer to earlier definitions. All names, definitions, formulas, and record tags count toward written character length. The ordinary checker expands the definitions and checks the Hilbert derivation. An MP record need not contain line numbers: the checker searches earlier lines for the premises. This convention avoids an uncharged reference-size assumption when appending a fixed number of inferences. Call this presentation \(B\).

Let \(B_0\) be the core calculus, using only \(=,\neg,\to,\forall\). Its arithmetic axioms and induction schemas are written in that vocabulary. It uses the same ambient file alphabet and Gödel coding as \(B\), with the grammar restricted to core formulas. It is a presentation of PA. The extension \(B\) by primitive conjunction is conservative: translate \(A\mathbin{\&}B\) to \(\neg(A\to\neg B)\). Hence consistency of PA implies consistency of \(B\).

Use ordinary finite-string Gödel codes, with a leading marker to distinguish strings of different lengths. The bit length of a formula's code is \(O(|A|+1)\). Fix a PA-provably total elementary implementation of the ordinary checker and a core-language, PA-provably \(\Delta_1\) formula \(\operatorname{Prf}_B(p,y)\) for its accepting computation. Likewise fix the written-length function \(\operatorname{Len}\). All auxiliary arithmetic definitions in this note use the core vocabulary: a displayed mathematical conjunction inside an arithmetic definition is translated to core connectives.

Nested abbreviations do not prevent the checker from being elementary. A file of length \(m\) has an expansion bounded by \((m+1)^{m+1}\); checking the expanded finite-basis proof is polynomial in its expanded length. PA proves these elementary termination bounds. Polynomial runtime for this expanding implementation is neither asserted nor needed below.

The permitted choice of system is used here. This is not a claim that these conventions are identical to the agenda's Enderton presentation or its abbreviation grammar.

## 3. Tags that term substitution cannot manufacture

Put \(\top:=(0=0)\), and define the closed tautologies

\[
 T_0=\top,\qquad T_{n+1}=\top\mathbin{\&}T_n.
 \tag{4}
\]

A *shape* erases the terms of an atomic equality and retains every logical constructor. Decode shapes by

\[
 \operatorname{tag}(\mathrm{atom})=0,\qquad
 \operatorname{tag}(\mathrm{atom}\mathbin{\&}U)
     =1+\operatorname{tag}(U)
 \tag{5}
\]

when the right-hand side is defined; it is undefined on all other shapes. Thus \(\operatorname{tag}(T_n)=n\).

At every subformula \(A\mathbin{\&}C\), record the index \(j\) if the shape of \(A\) decodes to \(j\). The resulting finite list is the formula's **guard indices**. Duplicates do not matter. Scan the expanded formula records and expanded formula definitions of a proof in this way.

Three elementary facts will be used.

1. Every formula \(T_n\mathbin{\&}D\) has guard index \(n\).
2. Renaming variables and capture-avoiding substitution of terms preserve the entire list of guard indices. They change terms, not logical constructors.
3. Core formulas have no guard indices. The guard indices of \(A\to C\) are those of its two operands; those of \(\forall x A\) are those of \(A\).

Consequently modus ponens and generalization introduce no new guard index. The universal-instantiation axiom \((\forall x A)\to A[t/x]\) has no guard index absent from \(\forall x A\). This is the repair of the earlier arithmetic-only proposal, whose guard depended on the *value of a substituted numeral*.

These statements, including capture-avoiding substitution underneath binders, are proved in `TaggedSyntax.lean`. The implementation scans already expanded formula syntax; it does not claim to implement the proof-file expansion or PA checker.

## 4. The finite diagonal family

For a code \(e\) of a core formula with one free variable, let

\[
 f_e(n)=\#\bigl(T_n\mathbin{\&}\varphi_e(\overline n)\bigr).
\]

The parameterized diagonal lemma, carried out in \(B_0\), supplies a core formula \(D(x)\) such that, for \(d=\#D\),

\[
 B_0\vdash\forall n\,[D(n)\leftrightarrow H(n)],
 \tag{6}
\]

where

\[
 H(n)\;:\equiv\;
 \text{there is no }B\text{-proof of the formula coded by }f_d(n)
 \text{ with written length at most }2^n.
 \tag{7}
\]

Define

\[
 P_n:=T_n\mathbin{\&}D(\overline n),\qquad f(n):=f_d(n)=\#P_n.
 \tag{8}
\]

This is a diagonal construction for the **tagged** formula from the start, not the addition of a tag to an already fixed diagonal sentence. The map \(e,n\mapsto f_e(n)\) is an elementary syntactic operation. The predicate \(H\) is decidable by a finite search and is PA-provably \(\Delta_1\). Its computation may be enormous. The core formula \(D\) can also be chosen PA-provably \(\Delta_1\), since the substitution functions and the finite search are PA-provably total elementary functions.

**Finite diagonal lemma for this family.** If \(B\) is consistent, then for every standard \(n\): \(H(n)\) is true, \(B\vdash P_n\), and every \(B\)-proof of \(P_n\) has written length greater than \(2^n\).

**Proof.** Suppose a proof \(\pi\) of \(P_n\) had length at most \(2^n\). Conjunction elimination and (6) would give a \(B\)-proof of \(H(\overline n)\). Numeralwise verification of that particular proof file and its length would give a \(B_0\)-proof of \(\neg H(\overline n)\). This contradicts consistency of \(B\). Thus \(H(n)\) is true. Its terminating finite verification can be proved in \(B_0\), without any claim that this proof is short. Equation (6) then proves \(D(\overline n)\). The tautology \(T_n\), followed by conjunction introduction, proves \(P_n\). ∎

This argument quantifies over all proofs, including compressed proofs and proofs using arbitrary induction instances.

## 5. The guarded checker and its actual box

The checker for \(S\) performs these steps on a proof file \(\pi\) and a purported conclusion code \(y\):

1. Run the specified ordinary \(B\)-checker.
2. Expand the definitions, collect the guard indices just specified, and for each recorded \(j\), run the finite test \(H(j)\).
3. Accept precisely when the ordinary check and every guard test succeed.

This is a concrete primitive recursive procedure. Its finite searches concern the already fixed checker \(B\); it never recursively calls itself. With complete-expression abbreviations, the logical depth of an expanded expression is bounded by the total input length, so recorded indices are bounded by that length. Even the more generous exponential expansion bound suffices for an elementary runtime bound. PA proves totality.

Let \(V_S(p,y)\) be a core-language, PA-provably \(\Delta_1\) representation of this checker. Choose a \(\Sigma_1\) presentation, with the PA-proved equivalence to the checker retained. Define

\[
 \Box_S A:=\exists p\,V_S(p,\overline{\#A}).
 \tag{9}
\]

For example, a convenient PA-equivalent definition of \(V_S\) is ordinary proof correctness conjoined with the assertion that \(H(j)\) holds for every index in the computed guard list. This definition and the actual computation trace are equivalent in PA by induction over the finite checking procedure. Thus (9) concerns the specified verifier, not an unaligned substitute box.

By the finite diagonal lemma every standard guard test succeeds. Therefore, for every standard file and conclusion,

\[
 V_S(\pi,y)\quad\Longleftrightarrow\quad\operatorname{Prf}_B(\pi,y)
 \quad\text{in }\mathbb N.
 \tag{10}
\]

In particular the accepted files and their lengths coincide, and

\[
 \ell_S(A)=\ell_B(A)
 \tag{11}
\]

for every theorem. Thus \(S\) is a consistent recursively presented extension of PA, and it has the required binary numerals and nested priced abbreviations. Equation (10) is an external statement. A uniform PA proof of its forward-to-guarded direction will be ruled out below.

The checker also has the uniform invariant

\[
 B_0\vdash\forall n\,\bigl(\operatorname{Prov}_S(f(n))\to H(n)\bigr),
 \tag{12}
\]

where \(\operatorname{Prov}_S(y):=\exists p V_S(p,y)\). Indeed an accepted proof with conclusion \(P_n\) includes that expanded final formula; its left conjunct is \(T_n\), so the checker tested \(H(n)\). The syntactic statement \(\operatorname{tag}(T_n)=n\) is proved by induction on \(n\). Formalizing the finite expansion and scan gives (12). Neither consistency nor \(\forall n H(n)\) is used to prove (12) internally.

## 6. Derivability conditions

The box in (9) satisfies the ordinary Hilbert–Bernays–Löb conditions.

**D1.** If a particular file is accepted, its finite accepting computation is true and can be proved in \(B_0\). Thus \(S\vdash A\) implies \(S\vdash\Box_S A\).

**D2.** Concatenate two proofs, rename abbreviation identifiers to prevent collisions, and append the MP conclusion. The expanded old lines are unchanged. The new conclusion is a subformula of the old implication. Thus no new guard index appears. PA proves this syntactic property and the preservation of the successful guard tests. This gives \(\Box_S(A\to C)\to(\Box_S A\to\Box_S C)\).

**D3.** The formula \(\Box_S A\) is a core-language \(\Sigma_1\) formula. Formalized \(\Sigma_1\)-completeness for \(B_0\) gives

\[
 B_0\vdash \Box_S A\to\Box_{B_0}\Box_S A.
\]

Core proof files contain no primitive conjunction and therefore no guard indices. The inclusion of \(B_0\)-proofs into \(S\)-proofs is provable in \(B_0\), without an assumption that all guards are true. It converts the right-hand box into \(\Box_S\Box_S A\).

The diagonal lemma is available in the arithmetic theory. Thus Löb's theorem applies to this actual guarded box.

The same guard argument also preserves ordinary term instantiation. This addresses the specific uniform-instantiation defect of the earlier numeral-value guard. It does not supply numerical constants for every bounded certificate requested elsewhere in the MAIS agenda.

## 7. Why the reflection proofs are short

Only a small **syntactic graph computation**, not the computation of \(H(n)\), will be internalized efficiently.

The relation

\[
 G(n,y)\quad\Longleftrightarrow\quad y=f(n)=\#P_n
 \tag{13}
\]

is decidable in polynomial time in the combined binary lengths of \(n,y\). Decode \(y\), check its left conjunction chain and count its length, and check its right operand against the fixed formula \(D\) instantiated at the canonical numeral for \(n\). An input with an insufficiently long output string is rejected before any long construction. For the true pair \((n,f(n))\), that combined length is \(O(n+1)\).

Choose for \(G\) the usual computation representation that has polynomial-size numeralwise proofs in core Robinson arithmetic. Its agreement with the syntactic graph is provable in PA. This is the standard polynomial-numeration construction (Pudlák 1998, Theorem 6.1.4); we are free to choose this representation here. We are **not** assuming that every arbitrary \(\Delta_1\) representation has short proofs.

Consequently there is a fixed polynomial \(u\) such that the true instance

\[
 G(\overline n,\overline{\#P_n})
 \tag{14}
\]

has a core arithmetic proof of at most \(u(n+1)\) characters. These proofs can be produced effectively from the accepting computations of the graph test.

Equations (6) and (12), expressed using this graph, give a single fixed core PA proof of

\[
 \forall n\,\forall y\,
 \bigl(G(n,y)\to(\operatorname{Prov}_S(y)\to D(n))\bigr).
 \tag{15}
\]

Specialize it at the two numerals in (14), use that short graph certificate, and obtain

\[
 \Box_S P_n\to D(\overline n).
 \tag{16}
\]

There is a plain Hilbert proof of \(T_n\) of polynomial size in \(n+1\): start with \(0=0\), and at each of \(n\) steps use the conjunction-introduction schema and two MP steps. At stage \(j\), the few formulas written have size \(O(j+1)\). Summing gives \(O((n+1)^2)\) characters. Combining this proof with (16) gives a plain \(B\)-proof

\[
 r_n:\quad\Box_S P_n\to P_n
\]

of length at most \(a(n+1)^d\), for fixed integers \(a,d\ge1\). No abbreviation expansion cost is hidden: these particular proofs can be printed without abbreviations. Their formulas contain the literal target \(P_n\).

By (10), these files are also \(S\)-proofs. Their acceptance requires the true guard \(H(n)\), but a proof of the guard is **not appended to the file**. The checker performs that computation. This is the source of the separation. Internally proving that \(r_n\) is accepted need not be short.

Finally \(|T_n|=O(n+1)\) and \(|D(\overline n)|=O(\log(n+2))\), so \(|P_n|+1\le b(n+1)\) after choosing a fixed \(b\). Equations (11) and the finite diagonal lower bound establish all of (1).

## 8. An effective part 1 witness, including divergence

Fix a cheap-reflection constant \(C_1\) for \(S\). Such a constant exists with our proof-record convention: append the usual propositional instance \(P\to(\Box_S P\to P)\) and an MP line. These formulas introduce no guards outside those already in \(P\), since \(\Box_S P\) is core syntax.

Compute the plain reflection files \(r_n\) just described. Define \(n_0\) by searching for the first \(n\) such that

\[
 2^n\ge 2|r_n|+C_1(|P_n|+1).
 \tag{17}
\]

Having found \(n_i\), search for the first \(n>n_i\) satisfying (17), and call it \(n_{i+1}\). These are effective searches, and each terminates: their right-hand sides are bounded by one fixed polynomial in \(n+1\), while \(2^n\) exceeds that polynomial at arbitrarily large indices. The theorem `exponential_exceeds_polynomial_after` verifies the numerical fact used here.

Set \(Q_i=P_{n_i}\). Then

\[
 \ell_S(Q_i)>2^{n_i}
 \ge 2|r_{n_i}|+C_1(|Q_i|+1)
 \ge 2\ell_S(\Box_S Q_i\to Q_i)+C_1(|Q_i|+1).
\]

This gives \(\delta=1\), with a strict inequality stronger than the requested weak one. Numerical values for the finite template constants have not been extracted in this note; the sequence is specified by the effective proof generator and a fixed admissible \(C_1\).

The targets \(P_n\) are syntactically distinct because the left tags decode to different indices. Therefore the reflection formulas are also distinct. Over a finite alphabet there are only finitely many proof files of length at most any fixed \(M\), and each has one conclusion. Only finitely many reflection formulas can consequently have minimum proof length at most \(M\). Since \(n_i\) strictly increases, their minimum reflection lengths tend to infinity.

At \(k_n=a(n+1)^d\) and \(s_n=b(n+1)\), (1) gives

\[
 F_S(k_n,s_n)>2^n.
\]

Every polynomial in \(k_n+s_n\) is bounded by a polynomial in \(n+1\), proving that this \(F_S\) is superpolynomial. The relevant numerical implication is `no_polynomial_overhead`.

## 9. Why the ordinary box cannot be substituted

Write \(\operatorname{Prov}_B(y)=\exists p\operatorname{Prf}_B(p,y)\). We first prove a useful ordinary PA fact:

\[
 B_0\vdash\forall n\,\operatorname{Prov}_B(f(n)).
 \tag{18}
\]

Here and below notation using \(f\) is eliminable using its represented graph. Equation (18) asserts provability of each tagged instance; it does not assert the truth of all those instances.

To prove (18) inside PA, reason by cases on \(H(n)\).

* If \(\neg H(n)\), definition (7) already provides a \(B\)-proof of the formula coded by \(f(n)\).
* If \(H(n)\), its core \(\Sigma_1\) presentation and formalized \(\Sigma_1\)-completeness provide a \(B_0\)-proof of \(H(\overline n)\). The uniformly specialized proof of (6) converts this to a \(B\)-proof of \(D(\overline n)\). The simple proof generator for \(T_n\) has correctness provable in PA by induction on \(n\). Conjunction introduction combines these into a \(B\)-proof of \(P_n\).

These are operations on proof codes formalized in \(B_0\). In the second branch, they yield an existential statement about a proof; they do not yield \(H(n)\) without the case assumption. Classical case analysis proves (18), without a consistency assumption inside PA.

Specialize the fixed proof (18) and use the same short graph certificate (14). This gives **plain** \(B\)-proofs

\[
 b_n:\quad\Box_B P_n
 \tag{19}
\]

of polynomial size in \(n+1\).

Now let \(\pi\) be any \(B\)-proof of

\[
 A_n:=\Box_B P_n\to\Box_S P_n.
\]

Keep \(\pi\) intact, append the plain proof \(b_n\), then an MP line obtaining \(\Box_S P_n\); append the plain proof \(r_n\), then an MP line obtaining \(P_n\). The appended files use no abbreviation names, so they cannot collide with definitions inside \(\pi\). MP references are implicit. The total written length is

\[
 |\pi|+q_2(n)
\]

for one fixed polynomial \(q_2\), after increasing its coefficients to cover the few literal conclusion lines. The finite diagonal lower bound gives (3) **for every** \(\pi\). Taking a shortest bridge proof gives the displayed minimum-length version. Such bridge proofs do exist individually: a proof of \(P_n\) yields \(\Box_S P_n\) by D1, after which propositional reasoning yields \(A_n\).

The same argument using any ordinary reflection proof \(\Box_B P_n\to P_n\) and just \(b_n\) proves (2).

It follows from (3) that no polynomial in \(n+1\), hence no polynomial in the size of this family of bridge formulas, bounds their shortest proofs. The arithmetic implication is checked by `no_polynomial_bridges`.

There is also no \(B\)-proof of the uniform bridge

\[
 \forall n\,[\operatorname{Prov}_B(f(n))\to
                   \operatorname{Prov}_S(f(n))].
 \tag{20}
\]

Together with (18) and (12), such a proof would yield \(\forall n H(n)\). Specializing it, using (6), and adjoining the short tag proof would then give polynomial-size proofs of \(P_n\), contradicting \(\ell_B(P_n)>2^n\).

This obstruction concerns unbounded box alignment and any **uniform** bounded alignment from which (20) follows. It is not a proof of every possible formulation of the bounded-budget robustness problem. In particular, a separate proof for each fixed budget is not automatically a uniform statement over budgets.

## 10. Adversarial audit

| Potential gap | Resolution or limit |
|---|---|
| Wrong provability predicate | \(\Box_S\) is a PA representation of the explicitly specified guarded checker; its checker equivalence is part of the construction. |
| Changing the finite diagonal target after diagonalizing | The operator diagonalized in §4 already outputs the tagged formula. |
| A lower bound only against displayed proofs | The consistency argument excludes **all** ordinary \(B\)-proofs under the threshold; accepted \(S\)-files coincide with them. |
| Adding unproved reflection axioms | None are added. The short reflection files are ordinary PA derivations of (16), followed by tag introduction. |
| Guard dependence on substituted numeral values | Guards depend only on connective structure. Capture-avoiding term substitution preserves them, as Lean verifies. |
| Failure of D3 | Core arithmetic proof files have no primitive conjunction, so core \(\Sigma_1\)-completeness embeds into \(S\) internally without proving all guards. |
| Treating redundant conjunction as a macro | It is a declared primitive logical constructor. Expanding it away would change the checker and defeat the guard. |
| Hiding abbreviation expansion in a polynomial estimate | Reflection and ordinary-box certificates are printed without abbreviations. The expensive \(H(n)\) check is never assigned a polynomial proof bound. |
| Arbitrary representations assumed efficiently verifiable internally | Polynomial numeration is used only for the explicitly chosen graph relation \(G\), with the representation fixed accordingly. |
| Mistaking external equality for a provable bridge | §9 proves the required bridge proofs are long and the uniform bridge is unprovable. |
| Claiming the prescribed PA-bin problem is solved | Neither its part 1 nor its part 2 is settled by this construction. |
| Claiming a complete Lean certificate | The PA arithmetic layer remains unformalized; the certificate boundary is detailed next. |

## 11. What the Lean package proves

Lean 4.19.0, using only Core/Std, checks:

* a concrete arithmetic term and formula syntax;
* capture-avoiding simultaneous substitution with de Bruijn binders;
* preservation of connective shape and all guard indices under substitution;
* correct tag decoding, distinct tags and targets, and extraction of \(H(n)\) from the guard on \(P_n\);
* absence of guards in the core fragment;
* preservation of guard admissibility by MP, generalization, and the universal-instantiation axiom;
* equality of ordinary and guarded acceptance on **expanded traces**, under the explicit assumption that all guards hold;
* an executable Boolean guard checker for expanded traces and its equivalence to the guard specification, as well as guard-free acceptance of core traces without the all-guards assumption;
* truth of the tags and their exact formula-node count;
* the numerical factor-two and superpolynomial consequences, under the displayed length assumptions.

`ordinaryCheck`, `H`, the formula family `D`, and the numerical length bounds remain parameters where indicated. Printing foundational axiom dependencies does not remove these hypotheses. The node-count theorem is not a PA-bin character-count theorem.

An end-to-end certificate still requires an actual serialized PA checker, its arithmetization and coding theorems, the tagged diagonal instance, the internal checker invariant, the graph-certificate generator, and the character counts for the proof templates. The present package does not substitute assumed structure fields for those tasks and call the result a certified PA witness.

## References

* MAIS-A1 §2 and MAIS-O11: the chosen-system allowance and the fixed PA-bin target. Repository: <https://github.com/lionellevine/MAIS>.
* P. Pudlák, *The Lengths of Proofs*, Handbook of Proof Theory (1998), §6.1, especially Theorem 6.1.4: polynomial numeration for suitably chosen computation representations. <https://users.math.cas.cz/~pudlak/length.pdf>.
* P. Pudlák, *Incompleteness in the finite domain* (2017), §3.1: the finite-diagonal proof-length method. <https://arxiv.org/abs/1601.01487>.

The construction and transfer argument above are supplied with proofs; these references are not claims that the tagged construction itself appears in those sources.
