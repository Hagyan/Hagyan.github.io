# Returning to PA-bin: a focused upper-bound route

22 September 2026

**Status:** specification audit and proof-design note. This is not a proof of the PA-bin polynomial-overhead conjecture, and it contains no new claim of a complete Lean certificate.

## 1. Why change direction

The guarded constructions exploit the freedom to choose the verification procedure and its arithmetic representation. They therefore do not indicate that the prescribed PA-bin case is almost solved. The accompanying Lean certificates cover the stated syntax and quantitative lemmas; the complete arithmetic constructions remain human proofs.

For PA-bin, part 2's positive alternative is a better next target than transferring the exponential separation. A polynomial upper bound needs one uniformly bounded construction of a direct proof. Part 1 needs a lower bound against every direct proof, while simultaneously supplying short reflection proofs. A polynomial answer to part 2 would still permit the fixed-factor speedup requested in part 1.

No established equivalence with P versus NP, or other general impossibility barrier, has been proved here. We should not label the task intractable on the basis of unsuccessful approaches.

## 2. The exact conversion to implement

Throughout this section every box is the same prescribed PA-bin box. Put

\[
R_P:=\Box P\to P.
\]

Given a proof \(r\) of \(R_P\), construct:

1. A proof of \(\Box R_P\), by internalizing the supplied proof.
2. A proof of \(\Box R_P\to\Box P\), the internal Löb axiom instance.
3. A proof of \(\Box P\), by modus ponens.
4. A proof of \(P\), using the original \(r\).

Let \(k=|r|\), \(n=|P|\). Polynomial bounds for the first certificate in \(k+n\), the second in \(n\), and the proof-file assembly operations would establish

\[
F_{\mathsf{PA}_{\rm bin}}(k,n)\le C(k+n+1)^d.
\]

The earlier `AuditPass.lean` verifies this composition under explicitly supplied operation costs. It does not supply those costs for PA-bin. Its additive MP cost is also a hypothesis; the concrete implementation must account for abbreviation renaming and references. A polynomial assembly bound would suffice for the polynomial conclusion even if that stronger additive interface needs revision.

This construction does not search for a shortest proof of \(P\). It transforms a given reflection proof into one suitably short direct proof.

## 3. A confirmed issue: Enderton's tautology axioms

Enderton's *A Mathematical Introduction to Logic*, second edition, §2.4, pp. 114–115, allows generalizations of all propositional tautologies as logical axioms. The book explicitly distinguishes this choice from restricting to an efficiently decidable collection of axiom schemes.

Consequently, a generic argument that assumes a polynomial-time checker for a finite list of propositional schemes does not directly apply to the agenda's named calculus. Replacing Enderton's axiom group with a finite basis would require a quantitative simulation argument; equal theorem sets alone are insufficient.

However, this is **not** a proof that polynomial internalization fails. The internal proof lives in the same calculus, which can also use tautology axioms.

## 4. A way to handle an uncompressed tautology axiom

Let \(\tau(q_0,\ldots,q_{s-1})\) be the propositional skeleton of an accepted, uncompressed tautology axiom. In Enderton's terminology its propositional variables stand for distinct prime formulas: atomic formulas and universally quantified formulas treated as propositional atoms.

Let \(B_i(v)\) be an arithmetic formula asserting that the \(i\)-th bit of a coded truth assignment \(v\) is one. Uniform substitution gives

\[
\tau(B_0(v),\ldots,B_{s-1}(v)).
\]

This is itself a tautology axiom. Its universal generalization in \(v\) is also an allowed logical axiom. Thus the proof generator need not enumerate all truth assignments to obtain this statement. It reuses the tautological structure of the accepted input axiom.

For a standard compositional arithmetization of propositional evaluation, the next task is to generate a proof of

\[
\operatorname{Eval}(\ulcorner\tau\urcorner,v)=1
\quad\leftrightarrow\quad
\tau(B_0(v),\ldots,B_{s-1}(v)).
\]

Here `Eval` abbreviates an arithmetic graph, not a newly assumed primitive arithmetic function. The intended proof follows the syntax tree, using the fixed evaluation clauses at each connective. On uncompressed input there are only linearly many subformula occurrences, their codes have polynomial total length, and the relevant parsing and coding computations are polynomial in the input length. Suitable computation representations allow short arithmetic certificates for these local syntactic facts. The tautology axiom then yields the universally quantified evaluation statement.

This identifies a concrete proof-generation mechanism. It is **not yet a completed PA-bin lemma**: we still have to implement the evaluation representation, prove the equivalence, count the generated characters, and connect this certificate to the exact arithmetic predicate used by the PA-bin checker. Polynomial numeration for a suitable representation cannot simply be asserted for an arbitrary already fixed predicate.

## 5. Compression is the next quantitative boundary

Nested definitions can describe exponentially larger expressions. Expanding all intermediate formulas and then applying the preceding uncompressed construction only gives a bound in expanded size. Part 2 requires a polynomial in the written proof length and the final sentence size.

An example of the size issue is repeated definitions of the form

\[
u_0=A,\qquad u_{i+1}=(u_i\to u_i).
\]

The number of occurrences of \(A\) doubles at each expansion. The written definitions remain small, including their charged binary identifiers. A short final sentence does not bound the expanded sizes of all intermediate formulas.

The treatment of abbreviations must therefore be fixed explicitly. Complete-expression abbreviations produce a shared expression graph. Arbitrary string-fragment abbreviations can have more complicated parsing behavior. The agenda describes abbreviations for fixed strings; a proof for the narrower complete-expression grammar must not silently be claimed for the full convention.

The relevant next construction is a certificate generator operating on the compressed representation, with a PA proof that it agrees with the specified expansion-and-checking procedure. A slow expansion algorithm does not by itself prove that every arithmetic verification proof is long; an alternative symbolic verification may remain short.

## 6. What must be fixed for an end-to-end certificate

The uploaded agenda gives prose conventions and says to fix a \(\Delta_1\) predicate `Bew`. It does not give the literal arithmetic formula or a serialized executable checker to import into Lean. The public repository tree inspected at commit `a62cfe25345f3a7645128215c338d522c7755527` likewise contained no PA-bin checker implementation among its code files.

Before claiming a PA-bin certificate, the implementation must fix:

* the abbreviation grammar and expansion semantics;
* the precise Enderton axiom recognizer and inference records;
* the finite alphabet, identifiers, numerals, and Gödel code;
* the arithmetic `Bew` formula and its proved agreement with that checker;
* the certificate-generating operations and their written-character costs.

This is a formal specification obligation, not a reason to change the intended provability predicate to the guarded one.

The immediate target is polynomial internalization for the actual grammar, including Enderton's tautology axioms, followed by the polynomial-size internal Löb instance. A proof of efficient verification of individual supplied proofs would not assert PA's consistency: it yields statements about the existence of proofs, not a universal implication from provability to truth.

## Sources and scope

* Uploaded `MAIS-A1.tex`, §§2–3: PA-bin conventions and the explicitly heuristic upper-bound bookkeeping.
* H. B. Enderton, *A Mathematical Introduction to Logic*, second edition, §2.4, pp. 114–115. Primary book text inspected at <https://studylib.net/doc/25998573/herbert-enderton--herbert-b.-enderton---a-mathematical-in...>.
* P. Pudlák, *The Lengths of Proofs*, §6.1: short certificates for suitably chosen arithmetic representations. <https://users.math.cas.cz/~pudlak/length.pdf>.
* A. Critch, *Parametric Bounded Löb's Theorem and Robust Cooperation of Bounded Agents*, §5: the proof-expansion function and the expectation of a linear bound for suitable implementations. <https://arxiv.org/html/1602.04184v5>.

The Enderton substitution mechanism above is a proof-design proposal with its remaining arithmetic obligations explicitly stated. No new PA-bin upper or lower bound is asserted in this note.
