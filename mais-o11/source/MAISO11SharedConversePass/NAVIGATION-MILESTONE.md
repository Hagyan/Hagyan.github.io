# Compressed matching delimiters: construction, audit, and PA obligation

26 September 2026. MAIS-O11 remains unresolved. The mathematical arguments below
are separate from their Lean status: `FragmentPrefix.lean` and
`FragmentRange.lean` still await a successful kernel run. The Python audit is
executable evidence, not a formal certificate. No novelty claim is made for
compressed-string navigation as an algorithmic result.

## 1. A precise failure in the previous shortcut

Let S(w)=(d(w),m(w)), where d is net opening-minus-closing count and m is the
minimum over all prefix counts, including the empty prefix. Then

    S(xy) = (d(x)+d(y), min(m(x), d(x)+m(y))).

Although d(y) can be recovered by subtracting d(x) from d(xy), m(y) cannot in
general be recovered from these two summaries. Both `()(` and `(()` have
summary (1,0), and both first-character prefixes have summary (1,0). Their
remaining suffixes `)(` and `()` have different summaries: (0,-1) and (0,0).
Thus no function of just S(x) and S(xy) computes S(y) for every x,y. This is
an information-loss obstruction, not an implementation inconvenience.

`FragmentRange` directly traverses the compressed representation to obtain
the missing information. Its intended exact Lean theorem is

    rangeSummary op cl g i p q =
      wordSummary op cl (((g.words i).drop p).take q).

The source contains proofs with no placeholders, but elaboration and kernel
verification are pending. The companion `RANGE-NOTE.md` audits the recurrence.

## 2. Matching theorem and a short witness check

Fix two distinct characters `(` and `)`, with weights +1 and -1; all other
characters have weight zero. Let w have length L, and suppose w[a]='('. Define
the matching close locally as the first position j>a at which the running
height, started at 1 just after position a, returns to zero. No assumption
that the entire word is well formed is necessary for this local definition.

**Theorem.** For 0<=a<j<L, j is the matching close for a if and only if

1. w[a]='(';
2. w[j]=')';
3. S(w[a+1:j])=(0,0), with the right endpoint excluded.

**Proof.** If these three conditions hold, the height remains at least 1
throughout the interior and equals 1 at its end. The final closing character
then makes the height zero for the first time. Conversely, before a first
return to zero, integer heights are at least 1. Each character changes height
by at most one, so the returning character must have weight -1, the preceding
height must be 1, and the interior must have net weight zero and no negative
prefix. Its minimum is exactly zero because the empty prefix is included. QED.

This gives a **three-query witness check**: query the two endpoint characters
and the interior. In particular, a later PA acceptance proof need not contain
or verify the binary search used to discover j. It can check the proposed
position using this equivalence. The theorem concerns a single delimiter pair,
not term/formula sorting, variable binding, or the validity of a proof line.

## 3. Finding the witness without expansion

For 0<=t<=L-a-1 put

    C(t) := minimum-prefix-weight(w[a+1:a+1+t]) <= -1.

C is monotone: extending a word only adds candidate prefixes to its minimum.
C(0) is false. If C(L-a-1) is false there is no matching close. Otherwise
binary search finds the least t with C(t); the answer is j=a+t.

To justify the last assertion, minimality implies every earlier prefix has
weight at least zero. At t the weight crosses below zero, and a one-character
step can decrease it by at most one, so this prefix has weight exactly -1.
Its last character is a close, and the preceding interior has summary (0,0).
The theorem above applies. Conversely, the first matching close gives this
least t. The binary search maintains a false lower endpoint and a true upper
endpoint and halves their distance each time, so it terminates.

## 4. Explicit size and cost scope

Let M be the number of definitions plus all atom occurrences in an acyclic
fragment grammar. Each reference points to an earlier definition. With a
cached length/summary table and random access to definitions, an interval
query skips atoms before its start, uses cached summaries for whole selected
atoms, and descends only into partially selected atoms.

In the expanded derivation, a partially selected occurrence must contain
one of the two boundaries strictly inside it. At each depth there are at most
two such occurrences, lying on the two boundary paths. Along either path,
definition indices strictly decrease. Hence any definition is scanned at most
twice. Each scan examines at most its written RHS length: the query visits at
most 2M definitions-plus-atoms. Empty expansions cannot be partial and are
skipped; repeated references do not invalidate the two-path argument. An
out-of-bounds request is equivalent to its intersection with [0,L), and follows
the same bound. The root can be treated as the initial scan.

The existing expanded-length bound gives L<2^M, so in-range positions, lengths,
net weights, and minima have O(M) bits. Under an ordinary array representation
with O(M)-bit addition, subtraction, comparison and minimum, preprocessing and
one interval query take O(M^2) bit operations. Matching uses O(M) queries, for
O(M^3) bit operations and O(M^2) bits of stored numeric data. These are
mathematical bounds for the specified implementation model, **not certified
Lean runtime bounds**. The persistent-vector implementation in the Lean source
requires separate accounting for copying. Arbitrarily oversized input
coordinates also have their own bit-length cost; matching in-range positions
does not introduce that issue.

The three-query witness check uses O(M) arithmetic/branch steps, each on O(M)
bits, in this model. Recording those steps and their referenced positions
would give O(M^2) bits of numerical trace. We have not yet supplied a complete
serialized trace language, trace checker, or PA proof printer for that trace.

## 5. What would actually bridge this result to PA?

The useful next internal theorem is not a PA proof of the search algorithm's
optimality. It is a fixed PA theorem of the following schematic form:

    ValidGrammar(g) and NavigationCertificate(g,i,a,j,c)
      imply forall y, Expansion(g,i,y) -> MatchingClose(y,a,j).

All predicates here must be explicitly defined arithmetic formulas for the
chosen coding, and the implication must be derived in the actual PA-bin
calculus. This displayed schema is an obligation, **not a theorem already
proved in PA**. One then needs polynomial-size PA proofs of certificate
acceptance for the produced c, and a proved connection between Expansion and
the syntax relations used by the fixed Bew predicate. For a concrete formula
code, that connection also needs the appropriate quotation/equality proofs.
Semantic equality of two external checkers does not supply those proofs.

This separates three targets that had been too easy to conflate:

- computing a correct delimiter position externally;
- verifying its finite numerical witness externally;
- producing a short PA proof about the fixed arithmetized syntax predicate.

Only the first target and the mathematical specification of the second are
established in this note. Further, even polynomial local navigation does not
make a full parser polynomial if it calls navigation once per expanded node.
The exponential-depth example still rules out that traversal strategy.

## 6. Evidence and literature boundary

`check_fragment_navigation.py` is an independent tuple/array model. Its recorded
run compared 99,824 interval answers, 27,108 matching answers, and 47,020
candidate-match checks with explicit-string reference computations. It includes
every word of length at most six over `(`, `)`, and a neutral character, empty
definitions, and 500 deterministic randomized grammars. On a mass-608 grammar
with 2^101+1 expanded characters, four matches were found without expansion,
using 102 or 103 queries each. Finite tests cannot prove the universal claims.

Ganardi, Hucke, Lohrey and Noeth, *Tree Compression Using String Grammars*,
arXiv:1504.05535v2, provide compressed navigation results. Their paper also
warns against extending such local algorithms indiscriminately: general
context-free compressed membership can be PSPACE-complete, and a fixed tree
automaton can have PSPACE-complete evaluation on SLP-compressed preorder
traversals. These results do not show that PA syntax checking is PSPACE-hard;
the input representation and particular language matter.

Source: https://arxiv.org/pdf/1504.05535 (introduction and Section 3).

## 7. Verification status and local commands

The server's stock Lean 4.19 executable cannot discover its application path:
its numeric `/proc/<pid>/exe` lookup is denied before source loading. This
diagnoses the environment failure; it says nothing about whether the new proof
scripts elaborate. The runtime was not modified to bypass the restriction.

On the working local installation, from the project directory:

```bash
lake build FragmentPrefix FragmentRange
python3 check_fragment_navigation.py
```

The first command is the outstanding formal check. The second repeats the
independent executable audit. Neither command, even if successful, certifies
a solution of either part of MAIS-O11 or polynomial PA internalization.
