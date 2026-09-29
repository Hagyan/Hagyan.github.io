MAIS-O11: the exact excess function and a relation between parts 1 and 2

23 September 2026

A general relationship between the two parts has now been proved and checked in Lean 4.19.0. If the intended finite-proof version of part 1 has no witness, the overhead in part 2 has a joint affine linear bound. Conversely, failure of every joint linear bound yields witnesses for every prescribed integer factor. These implications do not decide which behavior occurs for PA-bin.

The result uses finite proof files and the qualitative admissibility of Löb's rule. It requires no polynomial internalization estimate and does not assume that expanded sentence length is bounded by written proof length.

Fix S, its provability predicate, its proof-length convention, and a nonnegative integer constant c = C1 for the sentence-size toll. Work only with provable sentences, so all lengths below are finite. Write

\[
d(P)=\ell_S(P),\quad r(P)=\ell_S(\Box_S P\to P),\quad
s(P)=|P|,\quad t(P)=c(s(P)+1).
\]

Define the nonnegative excess

\[
e(P)=\max\{d(P)-r(P)-t(P),0\},
\]

and its finite-budget maximum

\[
H(k)=\max\bigl(\{e(P):r(P)\le k\}\cup\{0\}\bigr).
\tag{1}
\]

Each proof file has one expanded conclusion. A finite alphabet has only finitely many files of at most k symbols, so only finitely many reflection conclusions can be proved within that budget. This remains true when a short file expands to a very large formula. Löb ensures that every target of an accepted reflection proof has a direct proof. Consequently (1) is a maximum of finitely many finite natural numbers.

The function H is nondecreasing, and by definition

\[
d(P)\le r(P)+t(P)+H(r(P)).
\tag{2}
\]

The substantive question about this bound is its growth, not its existence.

1. Exact characterization of a negative answer to part 1.

The following statements are equivalent:

- There is no fixed \(\delta>0\) and sequence of provable sentences \(P_i\) with \(r(P_i)\to\infty\) and \(d(P_i)\ge(1+\delta)r(P_i)+t(P_i)\).
- \(H(k)=o(k)\).
- There is a function \(h:\mathbb N\to\mathbb N\), with \(h(k)=o(k)\), such that \(d(P)\le r(P)+t(P)+h(r(P))\) for every provable P.

Here \(h(k)=o(k)\) means that for each positive integer q there is K such that \(q h(k)<k\) whenever \(k\ge K\). This is equivalent to the usual nonnegative ratio tending to zero. Likewise, denominators \(\delta=1/q\) suffice to test part 1: given any positive real delta, choose a positive integer q with \(1/q\le\delta\).

Proof of the first implication. Suppose part 1 has no witness. Fix q > 0. Then there is a cutoff K such that

\[
q e(P)<r(P)\qquad\text{whenever }r(P)\ge K.
\tag{3}
\]

For positive reflection length, violating (3) is exactly the separation with delta = 1/q. Zero-length cases can be excluded by increasing K to at least 1. If no such cutoff existed, choosing witnesses at reflection lengths at least i would give the forbidden sequence.

Take \(k>qH(K)\). If H(k) is zero, then \(qH(k)<k\). Otherwise choose a target P attaining H(k). If \(r(P)<K\), then \(e(P)\le H(K)\), hence \(qH(k)<k\). If \(r(P)\ge K\), (3) gives \(qH(k)=q e(P)<r(P)\le k\). Thus H is sublinear. An explicit valid threshold, given K, is \(qH(K)+1\).

The second implication follows from (2) by taking h = H. For the third implication back to the first, a claimed fixed-factor separation forces \(\delta r(P_i)\le h(r(P_i))\), contradicting sublinearity. QED.

This corrects the earlier audit's description of the sublinear conversion bound as a stronger sufficient condition. With finite reflection-budget sets, it is also necessary. Defining H therefore does not make the negative result easier: one still has to prove \(H=o(k)\) for the actual system.

2. A negative part 1 forces a linear answer to part 2.

Under the equivalent negative conditions above, for every q > 0 there is a constant Bq such that

\[
q d(P)\le(q+1)r(P)+q t(P)+B_q
\quad\text{for all provable }P.
\tag{4}
\]

Indeed, choose K from (3). For targets above the cutoff, \(q e(P)<r(P)\); below it, \(q e(P)\le qH(K)\). In all cases

\[
q e(P)\le r(P)+qH(K).
\]

Combine this with \(d(P)\le r(P)+t(P)+e(P)\). One can take \(B_q=qH(K)\).

Recall the agenda's overhead function, with the empty maximum set to zero:

\[
F_S(k,n)=\max\bigl(\{d(P):r(P)\le k,\ s(P)\le n\}\cup\{0\}\bigr).
\]

Taking q = 1 in (4) gives a single finite B such that

\[
\boxed{F_S(k,n)\le 2k+c(n+1)+B\quad\text{for all }k,n.}
\tag{5}
\]

In particular,

\[
F_S(k,n)\le (2+c+B)(k+n+1).
\tag{6}
\]

Thus disproving part 1 would also settle the polynomial-overhead question affirmatively, with joint degree one. The +1 keeps the numerical theorem valid at zero budgets; for the actual syntax there is no zero-symbol sentence or proof, so the zero corner does not obstruct the agenda's formulation without that +1.

This is a relationship between the questions. It is not a proof that (5) actually holds for PA-bin, because its antecedent, the negative answer to part 1, has not been proved.

3. Failure of a linear bound gives every fixed factor.

There is a stronger contrapositive than just “superpolynomial overhead implies part 1.” Suppose

\[
\neg\exists C\ \forall k,n\quad F_S(k,n)\le C(k+n+1).
\tag{7}
\]

Then for every integer a >= 1 and every K there is a provable P satisfying

\[
\boxed{r(P)\ge K,\qquad d(P)\ge a\,r(P)+c(s(P)+1).}
\tag{8}
\]

For a >= 2, this is exactly the requested type of separation, with delta = a - 1, at arbitrarily large reflection lengths.

Proof. If (8) failed for some a and K, all targets with reflection length at least K would have \(d(P)<a r(P)+t(P)\). For the remaining targets, (2) and monotonicity give

\[
d(P)\le r(P)+t(P)+H(K)\le a r(P)+t(P)+H(K).
\]

Consequently every target satisfies the latter bound, and

\[
F_S(k,n)\le a k+c(n+1)+H(K)
\le(a+c+H(K))(k+n+1),
\]

contradicting (7). QED.

Accordingly, a joint superlinear lower bound would already be enough for part 1; an exponential-versus-polynomial construction is unnecessary. “Joint” matters: growth in k alone is not enough if the sentence-size budget n is much larger. One sufficient target is a family with \(d(P_i)/(r(P_i)+s(P_i)+1)\to\infty\).

Conversely, finding a part 1 witness would not refute a linear joint upper bound. A fixed-factor separation can fit below a larger linear coefficient. The implications proved here should not be reversed.

4. Computability and proof generation.

For the intended primitive recursive checker, H is total computable as a metamathematical fact. Enumerate all files of length at most k, keep accepted reflection proofs, and group their target conclusions. This gives each target's minimum reflection length, since a shortest such proof is among those files. For each of the finitely many targets, enumerate ordinary proofs by length until a direct proof is found. Löb guarantees termination. Compute the finite maximum in (1).

This procedure need not be fast. It supplies neither a polynomial algorithm nor a usable numerical upper bound. Similarly, searching for a shortest direct proof is a computable conversion on valid reflection proofs, but says nothing useful about running time. If H were sublinear, (2) and its monotonicity would bound that converter's output length in terms of the length of any supplied reflection proof.

The computability argument in this paragraph is given as a mathematical proof. The Lean project verifies the finite-list and numerical statements, not a formal computability theory or a PA proof-search implementation.

5. What Lean has checked.

The project uses Lean 4.19.0 and Std only. Its main declarations are:

| Declaration | Verified statement |
| --- | --- |
| `hasSpeedup_iff_witness_sequence` | Arbitrarily large witnesses yield a sequence with reflection length at least its index. |
| `noSpeedup_iff_not_hasSpeedup` | The cutoff condition is exactly absence of the integer-denominator witness. |
| `noSpeedup_iff_sublinear_envelope` | The cutoff condition is equivalent to sublinearity of H. |
| `noSpeedup_iff_sublinear_converter` | A sublinear additive bound exists exactly under the negative condition. |
| `noSpeedup_near_unit_affine` | The uniform inequality (4). |
| `noSpeedup_overhead_affine` | The two-variable bound (5). |
| `not_linear_overhead_arbitrary_factor` | The witnesses (8) under failure of every linear joint bound. |
| `FiniteFiles.mem_words` | The explicit finite list contains exactly the files of length at most k. |
| `FiniteFiles.toLengths` | Such files supply the finite-budget interface when r has its defining minimum-length property. |

The numerical model takes finite-valued d, r and s and lists containing exactly the targets below a reflection budget. The finite-file module derives those lists from a decoder over a finite alphabet. Its `minimum_spec` is the ordinary defining equivalence between “minimum reflection length <= k” and “there exists an accepted reflection file of length <= k.” It is not a polynomial-cost hypothesis.

The decoder remains a parameter. The project does not implement PA, its arithmetization, or the actual PA-bin minimum-length functions. The applicability to ordinary PA-bin uses the mathematical facts explained above. No claim is made that the negative condition, or its positive alternative, has been proved for that instance.

The final theorem audit uses only Lean's standard `propext`, `Quot.sound`, and, where classical witness selection is used, `Classical.choice`. There are no admitted proofs, custom axioms, unsafe declarations, or `native_decide` certificates in the source. The supplied transcript records a clean build and the theorem signatures and dependencies.

After extracting the archive and entering `MAISO11EnvelopePass`, run:

```bash
lake build
lake env lean Audit.lean
```

The next unresolved mathematical task is to prove a growth statement for H or F in actual PA-bin. The results above narrow the alternatives and the implications between them; they do not choose an alternative.

Source conventions: the uploaded MAIS-O11.md and MAIS-A1.tex, sections 2 and 3. For general background on proof lengths and simulations, see Pavel Pudlák, *The Lengths of Proofs*, section 2: https://users.math.cas.cz/~pudlak/length.pdf. The deductions in this note follow directly from the specified finite-budget definitions; no claim of historical novelty is intended.
