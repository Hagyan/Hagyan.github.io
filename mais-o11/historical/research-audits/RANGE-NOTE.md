# Compressed interval summaries: source proof and audit

Status: **new source has NOT been checked by the Lean kernel**. On this pass,
invoking the available `lake env lean FragmentRange.lean` exited before loading
source with `error: could not detect the configuration of the Lake installation`.
The file contains proof scripts with no placeholders, but this is not a claim
that those scripts elaborate. Its imported prefix module likewise requires the
pending environment verification described in the checkpoint.

## Exact target and algorithm

For every grammar `g`, root `i`, start `p`, and requested length `q`, the target is

```
rangeSummary op cl g i p q =
  wordSummary op cl (((g.words i).drop p).take q)
```

The runtime path computes the existing cached table of `(length, summary)`
entries and visits the written grammar. No expanded word, `g.words`, or
`expandFragment` occurs on that runtime path. Expansion occurs only in theorem
statements and proofs. Callers with many queries can reuse `rangeWithTable` and
one table; `rangeSummary` itself rebuilds the table on each call.

At an atom of expanded length `L`:

1. If the requested length is zero, return the empty summary immediately.
2. If `L ≤ p`, skip the atom and continue at start `p-L`, length `q`.
3. Otherwise, if `p=0` and `L≤q`, use the stored atom summary. For a partial
   atom, recursively query it with the original `p,q`.
4. Join the atom answer with the rest-fragment answer at start zero and length
   `q-(L-p)`.

This handles empty referenced strings because they always satisfy step 2;
termination follows the finite fragment list, not positive expanded length.
Oversized requests are clipped without an endpoint addition that might obscure
the subtraction cases. Natural numbers are unbounded Lean `Nat` values.

## Mathematical correctness audit

The proof uses induction on fragment lists, and then induction on the acyclic
grammar. In the skip case, `drop p (x++y)=drop (p-|x|) y` when `|x|≤p`.
In the intersecting case, `p<|x|` and therefore

```
take q (drop p (x++y))
 = take q (drop p x) ++ take (q-(|x|-p)) y.
```

The summary of concatenation is `Summary.join`. Complete atoms are correct by
the table invariant and `take q x=x` when `|x|≤q`; partial atoms are correct by
the induction hypothesis. These cases cover all natural `p,q`, including zero
and starts past the word end. The implementation uses exactly these identities.

The query includes a smoke test on the grammar for `()` repeated `2^60` times:
an interior `)(` interval, a final unmatched `)`, an out-of-bounds start, and
zero length. This test is **also unexecuted** while Lean startup remains broken.

## Why two prefix summaries cannot replace this operation

Net weights subtract, but prefix minima cannot be subtracted. The words `()(`
and `(()` both have full summary `(1,0)`, and their first character `(` has
summary `(1,0)` in both cases. Yet removing that first character leaves `)(`
with summary `(0,-1)` and `()` with summary `(0,0)`. Thus a function of just the
full and removed-prefix summaries cannot compute the desired interval summary.
The new direct interval traversal supplies information absent from those two
summaries.

## Complexity and limits

Complete referenced atoms are handled by table lookup. Only partial atoms are
recursively expanded into their written definitions. A contiguous selected
interval has at most two boundary paths through its expanded derivation; each
path moves to earlier definitions. This gives a route to a polynomial traversal
bound, but **this module contains no certified visit or bit-operation bound**.
In particular table copying and arbitrary-precision arithmetic require explicit
accounting before asserting a machine-time or PA proof-length bound.

More precisely, when both endpoints lie in one atom there is one recursive
partial-atom call. When they lie in different atoms there are two calls, each
carrying only one boundary; thereafter neither can split into two nonempty
partial intervals. Repeated references to the same earlier definition can
therefore be visited along both paths, but do not create a third boundary path.
Empty atoms cause no recursive calls: the inequality `0 ≤ p` always skips them.
Whole atoms cause no recursive calls. Scanning intervening RHS atoms and
descending past unselected grammar definitions must still be charged, as must
the constant-time return for an empty remaining interval. This combinatorial
argument supports a linear *navigation count* in written grammar mass, before
charging vector operations and bit arithmetic; no exact numerical bound is
asserted or formalized here. A bit-cost statement must also include the binary
lengths of the externally supplied `p,q`, which need not be bounded by grammar
mass for an oversized request.

The result would permit local balance tests on substrings selected by binary
positions, once kernel-checked. It is not a parser, a proof checker, or a proof
of polynomial PA internalization. MAIS-O11 remains unresolved.
