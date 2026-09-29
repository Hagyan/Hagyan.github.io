# MAIS-O11: third audit and the next compressed-string certificate

25 September 2026. Source audit of `FragmentBalance.lean` and the current project. This note proposes the next theorem; it is not a certificate of PA internalization.

**Implementation follow-up.** The cache issue identified below has now been
addressed by `cachedGrammarSummary` in `FragmentBalance.lean`, with a successful
Lean correctness check recorded earlier in the session. `GrammarLengthBound.lean`
also bounds its numeric payload. `FragmentPrefix.lean` now contains a combined
length/summary table, prefix-query code, a correctness proof, and an instrumented
visit bound. An independent source audit found no semantic counterexample;
its fresh kernel run is pending because the restored local Lean executable
fails at startup with `failed to locate application`. The recommendations below
record the reasoning that led to these implementations, rather than claiming
they are all still absent.

## What the new theorem establishes

`grammarSummary_correct` proves exact agreement between the summary computed on every definition of `StringQuotation.Grammar` and the net/minimum-prefix parenthesis balance of its expanded word. `grammarBalanced_iff` gives the corresponding acceptance criterion. These theorems cover arbitrary fragments, including fragments that are neither terms nor balanced strings.

They do not yet connect a raw agenda proof file to `StringQuotation.Grammar`, recognize the full PA syntax, or produce a PA derivation of the arithmetic proof predicate. The alphabet map also takes arbitrary `op` and `cl`: their distinctness must be required when interpreting the result as actual opening and closing delimiters. If `op=cl`, `charWeight` classifies that character as opening because its first branch wins. The existing theorem remains true for that map, but would not express ordinary parenthesis balance.

## A computational caveat before the next parser theorem

The present `grammarSummary` and `FragmentGraph.compute` return recursively defined environments `Fin n → Summary`. They do not explicitly materialize a cache with one entry per grammar definition. In the `snoc` equation, the recursive environment is supplied separately to the new-fragment calculation and to `Fin.lastCases`; implementations can recompute earlier summaries. Multiple references can therefore lose the intended sharing. Correctness of the returned value alone supplies no polynomial running-time bound. `Fin.lastCases` also has the same operational caveat identified earlier in `DagEquality`.

This is a risk in the source computation, not a claimed benchmark or a proved compiled-runtime lower bound: compiler optimization and evaluation strategy matter. A clean certificate should avoid depending on them. Build a materialized vector/array of entries, with one entry per definition, and compute each new entry exactly once from prior entries. An entry contains both expanded length and balance summary. Prove a lookup invariant:

```
table[g][i].length  = (g.words i).length
table[g][i].summary = wordSummary op cl (g.words i).
```

The actual array implementation and an operation counter can then justify the intended bottom-up schedule. The integer bit-length bound from the preceding audit is a separate obligation.

## Smallest next semantic target: compressed prefix summaries

After that table, I recommend **prefix queries**, rather than a complete lexer or first-order parser. This needs no unresolved choice about the agenda's self-delimiting integer code and works at its actual character-fragment layer.

Given a definition index i and binary position q, compute the summary of the first q expanded characters. Let the operation clamp q to the expansion length, matching Lean's `List.take`. The exact specification is

```
prefixSummary g i q
  = wordSummary op cl ((g.words i).take q).
```

Scan the right-hand side of definition i. For a whole character or whole referenced fragment lying before q, use its stored length and summary. When q lies inside a reference, recurse into that earlier definition with the residual q. Only one reference can contain the boundary. Stop when q reaches zero; empty referenced words consume no position but scanning still advances to the next written atom. Termination follows from strictly decreasing definition indices for recursive calls and decreasing right-hand-side lists for scanning.

This directly answers a syntactic question about an exponentially long expansion without constructing it. A query follows one chain of strictly earlier definitions; the total number of scanned right-hand-side atoms along that chain is at most the grammar's total written atom count. With cached table entries and O(g)-bit positions/summaries, it admits a direct polynomial bit-cost bound. This count must refer to the implemented traversal, not to evaluation of `g.words` in the specification.

For the certificate, use the same pattern as `grammarSummary_correct`: a local theorem for a right-hand-side list, a theorem for an atom/reference, and induction over the grammar. Required string facts are `take` across concatenation and the existing `wordSummary_append` theorem. The local concatenation rule is

```
prefixSummary(xy,q) =
  prefixSummary(x,q)                            if q <= |x|;
  summary(x).join(prefixSummary(y,q-|x|))        otherwise.
```

This is a smaller, more reviewable target than full delimiter matching, while supplying its essential operation.

## Matching delimiters follows, but requires a range operation

For an opening parenthesis at position p, let z be the suffix after it. A closing match exists exactly when a prefix of z first brings the relative depth from 1 to 0. Since character weights are in {-1,0,1}, this is the least t≥1 satisfying

```
floor(summary(z.take t)) <= -1.
```

The predicate is monotone in t, so binary search can find the least crossing using O(log(|z|+1)) range-summary queries. The character at that first crossing is the matching closing delimiter. Specify `none` when no crossing occurs; correctness should include minimality and the positive depth of every earlier prefix.

A range summary cannot be obtained merely by subtracting two prefix summaries: net balances subtract, minimum-prefix balances do not. Thus the next dependent lemma is

```
rangeSummary g i p t
  = wordSummary op cl (((g.words i).drop p).take t).
```

Implement it by scanning the two boundary paths while using cached summaries for whole interior fragments. Alternatively, construct a small grammar for the substring and invoke the existing summary operation, with its own size proof. Ordinary whole-file delimiter balance does not supply this missing range information.

These operations remain syntactic services. Balanced delimiters plus a matching position do not establish term arity, variable scope, or any axiom instance.

## The exact PA proof-predicate bridge

There are three distinct equalities/implications still to connect:

1. **Bytes to the declared grammar.** Specify a parser for the full raw-fragment proof-file syntax, including interleaved definitions, fresh names, identifier code, record boundaries, and reference interpretation. Prove agreement with literal expansion. The existing full-file equivalence theorem is for the restricted closed-term prelude, while the new balance theorem starts with an already resolved `StringQuotation.Grammar`; those inputs cannot silently be identified.
2. **Compressed specification to arithmetic formulas.** Fix an object-language arithmetic predicate `PrfCompact(p,a)` and the intended canonical `Bew(p,a)`. Produce a PA proof of their uniform equivalence, or at least `PrfCompact(p,a) → Bew(p,a)` for the direction used in internalization. A Lean equality of external Boolean programs does not establish that object-language theorem. Conversely, once one *fixed* PA proof of the uniform bridge has been built, its length is a system constant; it does not require a fresh large equivalence proof for each input.
3. **Valid file to a short PA proof of its acceptance.** Construct actual serialized PA derivations of `PrfCompact(⌜π⌝,⌜A⌝)` for every valid input π ending in A, and bound their characters polynomially in |π|+|A|. Instantiating the fixed bridge then gives `Bew(⌜π⌝,⌜A⌝)`, followed by existential introduction for the same ordinary box. The target numeral syntax and the passage from compact arithmetic code terms to canonical code numerals must be accounted for.

The project still has no full PA arithmetic axiom system or literal full `Bew` formula. `ArithmeticTrace.lean` explicitly provides an external arithmetic encoding/checker, while `CompactProof.IsAxiom` retains four logical families. Therefore the earliest honest arithmetic certificate should target one explicitly declared local arithmetic predicate and an actual PA derivation of its summary equations. Its extension to `Bew` should remain an identified theorem obligation until the full calculus and bridge exist.

Polynomial-time recognition of arbitrary Enderton tautology axioms remains unnecessary for the final proof-printer theorem: promised-valid input permits an output proof using tautology axioms whose validity is inherited mathematically. Prefix and range services improve the compressed syntax layer without assuming that stronger decision procedure.

## Recommended next implementation order

1. Materialized `(length, summary)` table, correctness invariant, and operation count; require distinct delimiter characters at the user-facing balance specification.
2. `prefixSummary_correct` for the actual `StringQuotation.Grammar`, together with a scanned-atom bound.
3. `rangeSummary_correct` and first-matching-delimiter soundness, completeness, and minimality.
4. Use those operations in a separately specified raw-file grammar and then connect its arithmetic verification predicates to the chosen `Bew`.

The first two items are a concrete next certificate. They make progress on the full fragment setting while keeping the unproved object-arithmetic bridge explicit.
