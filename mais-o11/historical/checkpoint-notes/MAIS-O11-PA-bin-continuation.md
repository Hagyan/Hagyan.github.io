# MAIS-O11: continuation toward the fixed PA-bin problem

22 September 2026

**Status: neither the PA-bin witness in part 1 nor the PA-bin polynomial
conjecture in part 2 has been proved.** This note records a checked obstruction
to carrying the earlier strategy across unchanged, a checked conditional
upper-bound construction, and the precise gaps found in attempts to finish
the requested proofs. It must not be described as a solution to those parts.

## 1. Which statements are being pursued?

The public problem was retrieved from the author's repository at commit
`a62cfe25345f3a7645128215c338d522c7755527`:

- [MAIS-O11](https://github.com/lionellevine/MAIS/blob/a62cfe25345f3a7645128215c338d522c7755527/open-problems/MAIS-O11.md).
- [MAIS-O10](https://github.com/lionellevine/MAIS/blob/a62cfe25345f3a7645128215c338d522c7755527/open-problems/MAIS-O10.md).
- [MAIS-A1, the agenda and system conventions](https://github.com/lionellevine/MAIS/blob/a62cfe25345f3a7645128215c338d522c7755527/agendas/A1/MAIS-A1.tex).

The saved-file service was unavailable during this continuation. The public
texts were retrieved directly; the previous manuscript and checked Lean
source were read from their existing working copies. The public text, rather
than an unverified assertion about the current uploaded copy, is the source
of the problem conventions used here.

For the fixed PA-bin system, part 1 asks for a sequence with divergent
minimum reflection-proof lengths and

\[
\ell(P_i)\ge (1+\delta)\ell(\Box P_i\to P_i)+C_1(|P_i|+1),\qquad \delta>0.
\]

Part 2 asks whether there is a fixed polynomial upper bound on

\[
F(k,n)=\max\{\ell(P): |P|\le n,\ \ell(\Box P\to P)\le k\}.
\]

The PA-bin presentation uses a fixed Hilbert calculus, binary numerals,
priced nested abbreviations, and a checker that expands those abbreviations.
Its arithmetized box must stay the box for that presentation. An externally
equivalent proof relation is insufficient for replacing that box inside
the formulas whose proof lengths are being compared.

## 2. The first-pass hypotheses are stronger than part 1

The first-pass interface supplies a family with

\[
n<C(\ell(P_n)+1),\qquad
\ell(\Box P_n\to P_n)\le a(\log_2 n+2),\qquad
|P_n|+1\le b(\log_2 n+2).
\]

The direct lower bound is a statement about every direct certificate.
The reflection upper bound is supplied by designated reflection certificates.

Suppose a polynomial conversion bound also held, with constants \(Q,d\):
any reflection certificate of length \(k\) for a sentence of size \(s\)
would admit a direct certificate of length at most \(Q(k+s+1)^d\).
At \(n=2^j\), the supplied reflection certificate would therefore give

\[
\ell(P_{2^j})\le Q(a+b)^d(j+2)^d.
\]

The lower bound would force

\[
2^j<C\bigl(Q(a+b)^d(j+2)^d+1\bigr),
\]

contradicting exponential growth for sufficiently large \(j\).

**This incompatibility is proved in Lean**, in
`first_pass_excludes_polynomial_overhead`. The growth argument is proved
constructively over natural-number powers; it does not rely on an informal
Big-O step or an imported asymptotic axiom.

Consequently, instantiating the old interface for PA-bin would already
**disprove** the polynomial conjecture in part 2. It is not a modest
completion of the old argument on the way to a polynomial upper bound.
The actual part 1 request is weaker and can coexist with polynomial,
even linear, overhead. For example, a factor-two gap between two growing
proof lengths need not have an exponentially large ratio. This observation
does not itself exhibit any PA-bin sentences.

## 3. A checked route to a polynomial upper bound

Write \(R_A=(\Box A\to A)\). From certificates of

\[
R_A,\qquad \Box R_A,\qquad \Box R_A\to\Box A
\]

two applications of modus ponens produce a certificate of \(A\).
In particular, the input reflection certificate can be used once as an
object of internal verification and once as a premise of the final inference.

The new Lean function `QuantitativeLobTools.convert` constructs exactly
this certificate. It does not postulate a direct proof of \(A\).
The primitive certificate-producing operations and their bounds remain
explicit inputs, and no PA-bin instance of them is supplied.

Here is the entire quantitative calculation. Suppose that, for a sentence
\(A\) of size \(n\) and a reflection certificate \(r\) of length \(k\):

1. Noticing \(r\) produces a certificate of \(\Box R_A\) of length
   at most \(u(k+n+1)^d\).
2. The internal Loeb instance \(\Box R_A\to\Box A\) has a certificate
   of length at most \(v(n+1)^e\).
3. Modus ponens on proofs of \(X\to Y\) and \(X\) costs at most
   their combined lengths plus \(m(|X|+|Y|+1)\).
4. \(|\Box X|\le b(|X|+1)\) and \(|R_X|\le r_0(|X|+1)\).

Define

\[
W=m\bigl(b(r_0+3)+2\bigr),\qquad
D=\max(d,e,1),\qquad K=1+u+v+W.
\]

The constructed proof satisfies

\[
\begin{aligned}
|\operatorname{convert}(r)|
&\le k+u(k+n+1)^d+v(n+1)^e+W(n+1)\\
&\le K(k+n+1)^D.
\end{aligned}
\]

Both inequalities, including the formula charges in the two modus-ponens
steps, are proved in Lean. `uniform_budget` also proves the version for
\(|A|\le n\) and \(|r|\le k\), which is the form needed to bound the
maximum defining \(F(k,n)\). For \(k+n\ge1\), the extra \(+1\) is
absorbed by multiplying \(K\) by \(2^D\); the zero-input case is empty
in a concrete syntax with no zero-character proofs.

If \(d\le1\), the separately checked `linear_premise_bound` gives

\[
|\operatorname{convert}(r)|
\le (u+1)k+(u+v+W)(n+1)^{\max(e,1)}.
\]

This is the shape of the strong conjecture. It is still conditional on
the primitive bounds above. In particular, item 1 is not supplied by
the existing first-pass certificate.

### The internal Loeb instance is logically derived

The qualitative theorem `internal_lob_axiom` derives
\(\Box R_A\to\Box A\) from the original Hilbert--Bernays--Loeb
conditions, a diagonal fixed point, and an explicit propositional rule.
Here is its proof, with all arrows interpreted as provable implications.

Take \(G\leftrightarrow(\Box G\to A)\). Necessitating its forward
direction and applying distribution and positive introspection yields
\(\Box G\to\Box A\). Propositional composition then gives

\[
R_A\to(\Box G\to A).
\]

Compose with the reverse fixed-point implication to obtain \(R_A\to G\).
Necessitation and distribution give \(\Box R_A\to\Box G\).
Composition with \(\Box G\to\Box A\) finishes the proof.

This establishes the logical construction. It does not by itself establish
the polynomial length of its arithmetic instantiations. `lob_bound`
records that separate obligation instead of hiding it in the logical theorem.

## 4. Why the cited polynomial-verification results do not close the gap

Pudlak's [1998 chapter, section 6.1](https://users.math.cas.cz/~pudlak/length.pdf)
develops polynomial numeration: suitable proof relations can be represented
so that true instances have short arithmetic proofs. His
[2017 article, sections 2.4--2.5](https://arxiv.org/abs/1601.01487)
states the proof-system and representation assumptions used for its
polynomial verification fact. These support an important method, but they
are not a checked polynomial internalization theorem for this particular
compressed-file checker and its specified arithmetic representation.

Two transfers still need proofs:

- The numerical facts certified by the efficient procedure must imply
  acceptance by the actual PA-bin checker, inside PA.
- The proofs of those facts, the coding equalities, and all abbreviation
  definitions must have polynomial *written* length in the original
  reflection-certificate length and the target sentence size.

Expanding first does not establish the second transfer. Definitions that
successively duplicate the preceding formula have a total written size
\(O(t\log(t+2))\), including binary identifiers, while the expanded
formula has at least \(2^t\) atom occurrences. A polynomial bound in the
expanded size therefore need not be polynomial in the written input size.

This is a failure of a proposed proof method, **not** a lower bound on
all PA proofs of acceptance. PA might reason about the compressed structure
without spelling out the expansion. Establishing that reasoning with the
required size bound remains the concrete task.

For comparison, [Critch's paper, section 5](https://arxiv.org/html/1602.04184v5)
formulates bounded necessitation and discusses efficient checking. Its
engineering estimate is not an implementation and proof-length certificate
for the agenda's checker.

## 5. Attempts at a fixed-system lower-bound witness

The following routes were challenged during this continuation.

| Route | Exact missing step or failure |
| --- | --- |
| Reuse the finite diagonal sentences | The lower bound on all direct proofs is useful, but it supplies no appropriately short proof of the ordinary PA reflection instance. |
| Translate the guarded-system construction into PA | The interpretation gives a theorem involving the guarded box. Replacing it with the ordinary PA box requires an internal provability bridge with a measured proof cost. The bridge is absent. |
| Remove the verifier's extensionally redundant guard | External equality of accepted files does not provide the internal equivalence of acceptance formulas needed by the reflection statement. |
| Use a short proof of provability from a Parikh speedup | A short proof of the reflection implication would combine with that short provability proof to make the direct proof short. A lower bound on the direct proof alone does not supply the requested gap. |
| Assert that every direct proof has a shorter reflection proof | This does not establish that the self-referential sentence is provable. A case with neither sentence provable does not meet the problem. |
| Replace unbounded reflection by bounded reflection | Finite consistency can make the bounded implication provable even when the sentence is unprovable. The hypothesis of ordinary Loeb's rule has then been changed. |

None supplies a PA-bin family meeting the factor-plus-toll inequality.
Any successful lower-bound argument must still quantify over *every*
direct PA-bin proof, including unexpected proofs using induction or
abbreviations; comparing two selected derivations is insufficient.

## 6. Formalization boundary and continuation point

The new file proves the mathematical relationships above and their
natural-number cost inequalities. It supplies no `QuantitativeLobTools`
instance for PA-bin and no `SeparationHypotheses` instance for any concrete
arithmetic checker. The incompatible combination is expressly ruled out
by `first_pass_and_polynomial_tools_incompatible`.

For the proposed polynomial direction, the next substantive theorem is a
size-controlled internalization of **reflection-premise proofs** for the
fixed compressed PA-bin syntax. The bound used here only needs this class
of premises; a uniform bound on noticing every possible theorem would
be stronger than necessary. The arithmetic Loeb-instance cost and the
assembly/renaming costs must be supplied for the same syntax as well.

For part 1, a separate witness mechanism is needed if the polynomial
conjecture is to remain true. The earlier logarithmic-reflection/linear-
direct family cannot serve that purpose. No completed mechanism is claimed.

The source package includes the exact Lean version, the actual verification
transcript, and the printed interfaces. A successful kernel check proves
these conditional theorems; it does not discharge their arithmetic hypotheses.
