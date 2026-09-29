# MAIS-O11: compact parsing and shared-graph equality

## The verified result

This checkpoint extends the previous compact-parser equivalence result in two
directions. First, `SharedConverse.lean` proves that the compact definition
reader and the original expanding reader accept exactly the same definition
preludes on every input string. Second, `GraphCompiler.lean` compiles any
accepted compact definition list to a shared DAG whose roots have exactly the
same expanded syntax as the definitions.

The compiler theorem `compileDefs_refines` states that graph expansion at a
compiled definition root is the same arithmetic syntax tree as expansion of
the compact definition. `compileTerm_root` gives the corresponding result for
an arbitrary closed compact term, while `compileTerm_preserves` shows that
previous graph roots retain their meanings when a term is appended.
`compiledDefs_table_iff` connects the graph's equality table to exact equality
of expanded syntax trees. This is syntactic equality, not equality of the
natural numbers denoted by terms.

The graph has one node per non-reference constructor: references reuse an
existing root. The bounds `compileDefs_size_le_wire` and
`compiledPrelude_size_le_input` show that its number of nodes is at most the
written syntax size (and, for a parsed prelude, at most its input character
count). `DagEquality.lean` bounds equality-table writes by the cube of the
number of graph nodes. These are bounds on this graph representation and table
construction; they are not an end-to-end complexity result for full PA-bin
proof checking.

`SharedOracle.lean` uses this graph for closed-term comparison, and
`OpenGraph.lean` provides the variable-labelled extension used at positive
binder depths. The theorems `sharedClosedEqual_correct` and
`sharedOpenEqual_correct` prove exact agreement with expanded syntax. In
`SharedOracleDemo.lean`, the graph for the 61 written doubling definitions has
61 nodes. It compares `u_60` with `u_59 + u_59` using the compiled roots and a
graph equality table. The expanded tree has `2^61 - 1` syntax nodes. Lean's
executable demo reports that the roots compare equal without materializing
that tree.

`OpenGraph.lean` removes the earlier binder-depth fallback. Its `OpenNode`
adds de Bruijn-variable leaves to the same backward-reference DAG structure;
`OpenGraph.table_iff` proves that the resulting table decides exact syntax
equality of expanded open terms. `compileOpenTerm_correct` certifies roots and
preservation of prior roots, and `compileOpenTerm_size` gives the exact node
count: variables and explicit constructors allocate one node, while compact
abbreviation references allocate none. `openTermNodes_le_weight` bounds that
count by the compact written term weight. `sharedOpenEqual_correct` proves
that two compact terms, at any binder depth, compare equal in the graph table
exactly when their expanded open syntax trees are identical.

The demo now also compares `x + u_60` with `x + (u_59 + u_59)` at binder depth
1. This exercises the case that defeated a simple structural comparator: the
large closed abbreviation is compared with its differently written closed
definition beneath an open constructor. The theorem `compiledTermEqual_correct`
connects this variable-labelled comparator to the exact expansion semantics.

`SharedOracle.lean` has graph shortcuts for contraposition,
conjunction-introduction, and instances of `∀x, x=x` whose two compact
conclusion terms expand to identical syntax. `compiledAxiomCheck_eq_reference`
proves that these shortcuts preserve the old four-family axiom relation
exactly. Successful shortcuts bypass expansion. Other universal-instantiation
cases and failed shortcuts still use the expanding reference checker. A demo
record instantiates reflexivity with `u_60` on one side and its explicit
definition `u_59+u_59` on the other; the graph accepts it without constructing
the large expansion.

`GraphFileChecker.lean` joins compact definition parsing to graph-based MP
comparison and those successful axiom shortcuts. The theorem
`checkWholeSharedGraph_eq_old_accept` proves exact agreement with the earlier
expanding checker on every input within the implemented file grammar;
`checkWholeSharedGraph_sound` transfers accepted records to the existing
derivability theorem. The checker returns a Boolean; it does not produce a PA
proof of its own correctness or a proof-length bound.

## What the compact whole-file demo does and does not exercise

`SharedConverseDemo.lean` parses a file containing the 61 definitions and a
reflexivity axiom record without expanding its final abbreviation. The
reflexivity record itself does not mention the large abbreviation. The
separate graph-comparison demo is what compares the 61st abbreviation with
its explicit written definition.

Modus-ponens comparisons now use graph equality at every binder depth. Three
axiom shapes have successful graph shortcuts. The 61-definition whole-file
example still uses a small reflexivity axiom; the separate record demos
exercise all three shortcuts with huge abbreviations. The checker can still
expand exponentially large abbreviations for other universal instantiations
and unsuccessful shortcut candidates.
Thus successful cases are more compact, but the restricted whole-file
checker is not compact on every input.

`InstantiationGraph.lean` now solves universal-instantiation recognition for
the restricted closed-term abbreviation grammar. Its search checks every
internal graph node, every written target subterm, and zero for a vacuous
quantified variable. `GraphSubterms.lean` proves that a term buried inside an
abbreviation occurs at a graph node. The binder-aware substitution theorem
handles arbitrary nested quantifiers, and `compiledInstCandidates_iff`
proves search completeness. `compiledInstCandidate_count_bound` bounds the
number of candidate checks by graph nodes plus written target weight plus one.

`GraphFileCheckerInst.lean` integrates this search into the restricted
whole-file checker. Its `checkWholeGraphWithInst_eq_old_accept` theorem proves
agreement with the original expanding checker for every file in that grammar.
A certified example accepts the witness `E 0` hidden inside `u_0 := (E 0)+0`.
Remaining axiom families retain the old expanding fallback; neither this
theorem nor the candidate-count bound is a polynomial PA internalization.

The full agenda permits arbitrary *string fragments* in definitions, not just
complete closed terms. `GraphDepthBarrier.lean` proves a unary spine of length
`m` needs at least `m+1` ordinary constructor-graph nodes. The separate
`SHARED-COMPILER-AUDIT.md` gives polynomial-length fragment-macro files with
an expanded unary spine of length `2^m`. Thus the ordinary term-DAG compiler
cannot polynomially normalize the full fragment grammar. This is a limitation
of that representation, not an overhead lower bound for PA.

`FragmentBalance.lean` certifies the next representation: a pair of integers
tracks net and minimum-prefix parenthesis balance under concatenation.
`FragmentGraph.compute_correct` establishes the generic string-DAG case.
More importantly, `grammarSummary_correct` computes these summaries over the
project's actual arbitrary-fragment `StringQuotation.Grammar` and proves exact
agreement with expanded strings; `grammarBalanced_iff` checks parentheses
without expansion. This covers one syntactic property of the raw fragment
grammar, not complete first-order parsing or the PA proof checker. A bound
on the bit complexity of this implementation remains mathematical rather
than formally verified. `SpecTransfer.lean` proves an abstract
conditional link between superlinear overhead growth and arbitrarily strong
Part 1 witnesses; `SPEC-SECOND-AUDIT.md` supplies the finite-alphabet and
Löb assumptions mathematically, not as a PA-bin Lean implementation.

## Materialized summaries and the next prefix certificate

The functional environment `grammarSummary` is a semantic specification;
references can recompute earlier results when it is evaluated directly.
`cachedGrammarSummary` now constructs a materialized vector, storing one
summary per definition. `cachedGrammarSummary_correct` proves the same exact
expanded-string specification and was checked successfully with Lean 4.19.0.

`GrammarLengthBound.lean` proves that each expanded definition has length
less than `2^g.mass`. Each signed balance component needs at most `g.mass+1`
bits; all cached numeric balance payloads together need at most
`2*g.mass*(g.mass+1)` bits. This excludes vector metadata and is a storage
bound, not a compiled-machine runtime theorem. The mass-to-file-length step
is an explicit assumption that every atom and definition costs a character.

`FragmentFamily.lean` now supplies the raw-fragment construction behind the
DAG obstruction: its grammar has mass `4+6*m`, and its expanded final word
is the stipulated unary rendering of depth `2^m`. Combined with
`GraphDepthBarrier.lean`, every ordinary graph for that unary term has at
least `2^m+1` nodes. These theorems were checked successfully. This is an
abstract alphabet and rendering, not a full PA-bin parser or axiom certificate.

`FragmentPrefix.lean` contains the next implementation: a cached table of
expanded lengths and balance summaries, then a query for the summary of
`(g.words i).take q`. The source includes `prefixSummary_correct` and a bound
of `g.mass` on visited definitions and written atoms. Each scan follows only
one partially consumed reference. It handles empty references and oversized
requests. The instrumented bound excludes table preparation, vector copying,
and integer bit costs. External cost analysis must include the bit length of
the supplied `q` as well as grammar mass.

**Verification status:** a fresh kernel run of `FragmentPrefix.lean` is pending.
The restored toolchain currently exits before elaboration with
`failed to locate application` (Lake reports that it cannot detect its
installation configuration). An independent source audit found no semantic
counterexample. This is not a successful Lean transcript for that new module.
The earlier successful checks of the cached summary, length bounds, and
fragment-family modules remain separately recorded.

The new `PA-BIN-THIRD-AUDIT.md` gives a short file with exponentially large
intermediate tautology lines and a fixed small conclusion. It defeats a
compiler that expands every intermediate formula, but its redundant lines
give no lower bound on shortest proofs or on F. Compact intermediate-code
certificates remain necessary for the proposed general internalization route.

`QUOTATION-HOMOMORPHISM-AUDIT.md` supplies a conditional mathematical way
to write exact canonical numeral syntax compactly: when the coding alphabet
has size `2^r`, fixed-width digit replacement, reversal, and leading-zero
trimming preserve linear grammar mass (for fixed r). This has not been
formalized in Lean, and the agenda does not fix a power-of-two alphabet or
the required formula-numbering convention. It therefore supplies a possible
component, not a theorem about the fixed Bew predicate. It also corrects a
potentially misleading output-size argument: a huge *expanded* numeral does
not by itself force a huge proof *file* when fragment abbreviations are allowed.

## Scope against the uploaded agenda

The agenda names PA in Enderton's Hilbert calculus, generalization records,
abbreviations for previously defined strings, and written-character proof
length. The current serialized checker supports only a restricted fragment:
four logical axiom families, axiom and modus-ponens records, closed-term
abbreviation definitions, and definitions placed before proof records. It
does not implement all logical and arithmetic PA axiom schemes, induction,
generalization records, open proof lines, arbitrary string abbreviations, or
the agenda's complete arithmetized proof predicate.

The separate [specification audit](SPEC-AUDIT.md) gives the detailed
comparison. One strategic issue it identifies is that literal Enderton axiom
recognition includes arbitrary propositional tautologies. This obstructs a
naive polynomial-time checker: exact polynomial-time recognition of all
tautologies would imply `P = coNP`. That observation does not rule out short
PA proofs or a polynomial-size compiler producing internal proofs conditional
on valid input; those are distinct claims and require a separate construction.

## Verification and limits

The earlier modules have recorded Lean 4.19.0 checks. The prefix and range
modules added subsequently remain pending verification. From this directory:

```bash
lake build
lake build GraphFileCheckerInst FragmentBalance GraphDepthBarrier SpecTransfer
lake build GrammarLengthBound FragmentFamily
# New modules: local verification requested; current server run blocked.
lake build FragmentPrefix FragmentRange
lake env lean SharedConverseDemo.lean
lake env lean SharedOracleDemo.lean
```

The earlier demos printed `PASS` for compact parsing, graph size, closed and
binder-depth graph equality, three huge-abbreviation axiom records, and
restricted whole-file acceptance. The `#print axioms` audit of the new
principal theorems, including the quantified example and the axiom record
examples, reports `[propext, Quot.sound]`; the
parser/compiler/checker modules introduce no custom axioms, `sorry`, `admit`,
or `native_decide`. The previously checked main theorems use standard logical dependencies
`[propext, Quot.sound]` (with `Classical.choice` for one abstract balance
predicate lemma).

This checkpoint establishes neither a Part 1 proof-length witness nor a
negative result. It also does not establish MAIS-O11 Part 2's PA-bin overhead
bound. The full audit-compatible fragment grammar and PA-internal
correctness/length construction remain. The
agenda's arbitrary-tautology axiom family must remain explicit; the two
shortcut shapes do not implement or recognize arbitrary tautologies, and
replacing the family with a fixed Frege basis would change the specified
system.

## 26 September update: compressed interval navigation

The new `FragmentRange.lean` supplies source proofs for direct interval summaries;
like `FragmentPrefix.lean`, it is still awaiting a successful kernel run.
`NAVIGATION-MILESTONE.md` gives a mathematical matching-delimiter construction,
a three-query witness check, a two-boundary traversal bound, and the exact
remaining PA proof obligation. `check_fragment_navigation.py` independently
audits these claims on small explicit words and a word of length 2^101+1.
The tests passed; they are not a Lean or PA certificate.

The old shortcut of subtracting prefix minima is impossible: the summaries
lose information. Direct interval traversal repairs that local obstacle.
Polynomial PA internalization and both parts of MAIS-O11 remain unresolved.

## 26 September arithmetic update

`PA-ARITHMETIC-MILESTONE.md` records explicit binary-addition and existential
Join derivations in a PA-admissible object calculus, extending beyond the
earlier reflexivity-only local certificates. The saved JSON demonstration
contains 407 local proofs for a summary table of a word of length 2^101+1.
Fresh replay passed. The exact Enderton serializer, uniform PA decoded-string
correctness theorem, fixed-Bew connection, and Lean verification remain open.

## 26 September symbolic-expansion update

`SYMBOLIC-EXPANSION-MILESTONE.md` and `UNIFORM-SCAN-AUDIT.md` give the
mathematical uniform PA scan/grammar induction argument for an explicit
auxiliary coding. Keeping expanded words existential avoids printing their
huge payload numerals. A fixed-width finite-sequence coding gives polynomial
bit length for the named grammar and local-table codes; its executable
round-trip audit passed. `CodedScan.lean` supplies pending source for the
arithmetic decoder bridge. No new successful Lean or emitted PA verification
is claimed. Polynomial PA proofs of the packed-table antecedent, the exact
Bew bridge, and both MAIS-O11 parts remain unresolved.
