# Symbolic expansion and polynomial-bit table coding

26 September 2026. MAIS-O11 remains unresolved. This note supplies a
mathematical uniform-induction argument for an explicitly chosen auxiliary
coding, together with coding implementations and pending Lean source. It does
not claim a newly kernel-checked PA derivation or fixed-Bew equivalence.

## 1. The useful theorem

The table of local Join proofs can be used without printing the enormous
expanded word codes. The intended uniform arithmetic statement is

    ValidGrammar(g) AND LocalJoinTable(g,t)
      -> exists e, Expanded(g,e) AND
           forall i < productions(g), NF(e[i],t[i]).

Here e stores expanded words as pairs (length, raw base-b payload); NF compares
their actual digit scan with the supplied summaries. The proof is two nested
inductions, on productions and positions within each RHS. It remains uniform
in the codes g,t, rather than a separate argument for each standard grammar.

`UNIFORM-SCAN-AUDIT.md` gives the proof in detail. The conclusion is a fixed
theorem provable in PA after defining the indicated elementary operations and
finite-sequence coding. This is a mathematical PA-provability argument by
effective formalization, **not a printed Enderton proof or a Lean certificate**.
The distinction applies to every claim of PA provability in this note.

An instance names only g and t. The expansion table e stays existentially
quantified. Applying existential elimination later requires a statement
uniform in e; one cannot extract its value, print its enormous numeral, and
retain the same size claim.

## 2. The scan means decoded characters, not certificate acceptance

Fix b>=2 and distinct digits op,cl<b. A word is (L,c) with c<b^L, retaining
leading zeros through L. Concatenation is

    (L,c) * (K,d) = (L+K, c*b^K+d).

Define T_d on unmatched-close/open pairs (R,O): an opening digit increments O;
a closing digit decrements O when O>0, otherwise increments R; a neutral digit
does nothing. The arithmetic Scan reads the L base-b digits of c from left
to right and iterates T.

Writing J for the uniquely determined result of Join, the elementary identity

    T_d(J(s,t)) = J(s,T_d(t))

has an exhaustive proof by cases on the digit and the relevant unmatched
counts. This yields, by induction on K,

    Scan(L+K,c*b^K+d) = J(Scan(L,c),Scan(K,d))  when d<b^K.

Crucially, NF is defined using this actual arithmetic digit scan. Defining NF
merely as 'there exists an accepted local table' would make the proposed
bridge circular. No axiom about arbitrary semantic truth is used.

The displayed Scan recurrence changes the payload parameter. To specify a
literal primitive recursion, use the digit-fold H(L,c,i) in the audit note,
then prove the recurrence by induction. This fixes a definability detail that
could otherwise be hidden by the phrase 'primitive recursive'.

## 3. Explicit sequence coding with polynomial bit length

The audit called for a concrete finite-sequence encoding. Use

    Pair(a,b) = (a+b)^2+a+1.

This is injective: if s=a+b, then Pair(a,b)-1 lies between s^2 and s^2+s,
and these intervals are disjoint for different s. Thus s is determined, then
a is determined by subtraction, then b=s-a. PA proves this argument using
elementary inequalities. The arithmetic inverse can be defined by bounded
search; the executable implementation uses integer square root.

For a sequence x_0,...,x_(n-1), choose w>=1 with every x_i<2^w and put

    p = sum_(i<n) x_i * 2^(w*i),
    SeqCode = Pair(n,Pair(w,p)).

A valid sequence representation has w>=1 and p<2^(n*w). Entry i<n is

    (p div 2^(w*i)) mod 2^w.

These formulas specify a concrete arithmetical sequence predicate after the
graphs of exponentiation and division are expanded. The representation need
not have minimal w: admitting larger widths simplifies the append lemma.
The generator chooses max(1,max_i bitlength(x_i)) deterministically.

**Size.** If a,b<2^B, Pair(a,b)<2^(2B+3). There are only two pairing layers in
SeqCode, so its bit length is O(n*w+log(n+2)+log(w+2)). Encode a summary triple
by Pair(L,Pair(R,O)); if its coordinates have B bits, it has O(B) bits.
For O(M) table and accumulator entries with O(M)-bit coordinates, the complete
local-table code has O(M^2) bits. This avoids repeatedly nesting Pair once per
entry, which would give a much worse bit-length recurrence.

Grammar RHSs are sequences of tagged atoms. For a literal digit d use 2d;
for a reference index j use 2j+1. Encode the list of RHS codes by the same
scheme. For a fixed alphabet and grammar mass M, an RHS code has at most
O(M log(M+2)) bits, and the outer code has O(M^2 log(M+2)) bits. This loose
bound suffices; no uncharged identifiers are being assumed. Backward-reference
checks remain part of ValidGrammar.

The local-table code contains both the root summary table and every RHS
intermediate accumulator, in production/atom order. Thus the single arithmetic
predicate LocalJoinTable can quantify over a bounded set of locations and
check Join between each adjacent accumulator and the correct literal or
earlier-reference entry. Empty RHSs have the zero summary.

To append an entry when proving sequence existence in PA, first increase the
width if needed, recode the finitely many old entries, and append the new
digit block. Induction on sequence length proves the recoding preserves all
lookups. These are elementary finite-recursion lemmas, so the outer grammar
induction can construct e without assuming an infinite sequence or a choice
principle. Their explicit PA derivations are still to be emitted.

## 4. What this removes, and what it does not

The expansion table can contain numbers with exponentially many bits. That
does not prevent the *uniform theorem* above or a short instance naming only
g,t. PA proves existence by finite induction; the proof does not need to
evaluate the existential witness as a literal numeral.

The two named input codes g,t now also have explicit polynomial bit bounds.
Consequently, if a polynomial-size PA proof of the single antecedent
ValidGrammar(g) AND LocalJoinTable(g,t) is supplied, applying the fixed theorem
preserves polynomial size under polynomial proof assembly. No term depending
on the printed size of e enters this conditional size argument.

**The remaining antecedent obligation is real.** The 407 local arithmetic
proofs from the previous milestone are not yet one PA proof about the packed
table code. We still must prove lookup equations, tags and bounds for that
code, and combine local assertions under the bounded index quantifiers.
Polynomial payload size does not, by itself, prove a polynomial PA proof-size
bound. This note does not import an unverified general efficient-computation
theorem to skip that work.

The auxiliary coding is explicit. It has not silently replaced the problem's
fixed proof predicate. A PA-provable equivalence to the intended decoder and
Bew remains necessary. Also, delimiter summaries handle only one syntactic
service: full term/formula recognition, substitution, and the tautology axiom
family remain separate issues.

## 5. Artifacts and evidence

`CodedScan.lean` specifies numerical decoding and scanning against the existing
`rawCode`. Its source includes decoder length, both inversion directions for
valid codes, concatenation, and

    cachedGrammarSummary ... = scanCode ... length rawPayload.

The concat theorem in that file assumes both payload bounds. Actual grammar
words have these bounds by the existing raw-code theorem. Its scan is a
semantic specification that recurses over expanded length, not the compressed
polynomial-time implementation. The file remains **pending kernel verification**;
it is also not an object-language PA derivation even if Lean verifies it.

`packed_summary_tables.py` implements the sequence coding and checks round trips
against the saved arithmetic-certificate example. The measured code sizes are:

| Code | Bits |
|---|---:|
| Grammar | 120,766 |
| Root summary table | 326,421 |
| Intermediate accumulator table | 652,033 |
| Combined local table | 1,304,065 |

These are auxiliary numeric codes for the grammar and local data, not the
expanded word code. The example's expanded word has 2^101+1 characters, and
its payload is never computed. The coding audit passed; it is not a proof of
the coding lemmas in PA or Lean.

`SummaryFiniteCheck.lean` is now generated for this fixed grammar. Its source
defines Lean functions to recompute the table and 407 merge inputs, and
contains theorem statements and explicit witness proof terms for every
concrete Join relation and the balanced final summary. If it passes the
pending Lean kernel run, that will close the finite semantic check for this
sample. It does not establish `LocalJoinTable(g,t)` as a PA theorem for
variable codes, nor connect the auxiliary code to the fixed `Bew` predicate.

From the project directory:

```bash
python3 packed_summary_tables.py summary-arithmetic-demo.json
lake build CodedScan
```

The first command reproduces the completed executable audit. The second is
an outstanding formal check. This workspace currently has no `lake` or `lean`
executable, so no successful run of the second command is reported.
