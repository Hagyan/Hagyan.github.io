# MAIS-O11 shared-graph certificate

## Latest status — 28 September 2026

The fixed PA-bin branch of Part 1 and Part 2 remain unresolved. A separate
slow-verifier argument is a credible conditional candidate for Part 1's
“any efficient system” branch, but is not yet formalized end to end. Its
repaired size ledger handles arbitrary string-fragment abbreviations by
combining a `2^(O(m^2))` expansion/translation bound with a `2^n` diagonal
cutoff, yielding a `sqrt(n)` direct-proof lower bound. Start with
`CURRENT-STATUS.md`, `CHOSEN-SYSTEM-PART1-AUDIT.md`,
`CHOSEN-SYSTEM-PART1-ROBUST-LEDGER.md`,
`ChosenSystemExpansion.lean`, `ChosenSystemSerialization.lean`,
`ChosenSystemInterleaving.lean`,
`LOB-INTERNALIZATION-REDIRECT.md`, `PA-FINITE-ASSEMBLY-MILESTONE.md`, and
`SYMBOLIC-EXPANSION-MILESTONE.md`. The Python arithmetic proof objects are
checked in a PA-admissible calculus; they are not exact Enderton/Bew or Lean
certificates. Separate Lean proof source has been generated for the 407 summary
joins in `SummaryFiniteCheck.lean`. On 28 September 2026, the current
`ChosenSystemExpansion.lean` completed `lake build ChosenSystemExpansion` with
Lean 4.19.0. Its four axiom reports list only `propext` and `Quot.sound`, with
no `sorryAx`. The bundled Linux toolchain in this workspace needed a local
rebuild of its corrupted `Init.Data.List.MinMax.olean` from matching Lean
4.19.0 source before Lake could finish. The decoder references are fully
qualified as `MAISO11.Quotation.readIdentifier`. The user's later error log
does not match this checked source: it reports axiom checks at lines 266–269
and `sorryAx`, while this file reports at lines 268–271 without `sorryAx`.
`ChosenSystemSerialization.lean` also builds with Lean 4.19.0 and proves
round trips for identifiers, tagged atoms and fragments, definitions, a
topologically ordered grammar, and its root stream; its six axiom reports list
only `propext` and `Quot.sound`. This is the grammar-plus-root model. Parsing
the actual AX/MP/GEN proof-file protocol with definitions interleaved, and
proving that every accepted file satisfies the model's size hypotheses, remain
open. The earlier `sorryAx` log came from a different or earlier source copy;
`ChosenSystemInterleaving.lean` additionally verifies compilation and the
`2^(2*m)` size bound for abstract output/definition directives in interleaved
order; its four checked theorems have no `sorryAx`. All three targets build
without `sorryAx`.
`FragmentPrefix`, `FragmentRange`,
and `CodedScan` also remain pending Lean checks.
The earlier verified modules are distinguished in the status table.

This Lean 4.19.0 project certifies compact parsing, compilation of compact
abbreviation definitions into a shared term graph, and exact comparison of
closed and open terms through that graph. The examples compare the 61st
doubling abbreviation with its written addition definition, both by itself
and beneath a quantifier binder, without building the exponentially large
expanded syntax tree.

Read [CONVERSE-NOTE.md](CONVERSE-NOTE.md) for theorem names, scope, and the
remaining gaps. [SPEC-AUDIT.md](SPEC-AUDIT.md) compares the implemented
fragment with the uploaded MAIS-O11 agenda.
`COMPRESSED-TAUTOLOGY-CIRCUIT-ROUTE.md` gives a literature-guided route for
arbitrary tautology records while preserving string-grammar compression; it
is not a PA-bin or Lean certificate.

From this directory, with Lean 4.19.0 and Std:

```bash
lake build
lake build ChosenSystemExpansion ChosenSystemSerialization ChosenSystemInterleaving
lake env lean SharedConverseDemo.lean
lake env lean SharedOracleDemo.lean
```

The modules `SharedConverseDemo` and `SharedOracleDemo` print executable
`PASS` checks. Modus-ponens comparisons use the graph at every binder depth,
and successful contraposition, conjunction-introduction, and reflexivity
instantiation axiom shapes use graph shortcuts. Other axiom checks can still
expand terms; the proof grammar
remains restricted as detailed in the research note. These results do not
prove a MAIS-O11 Part 1 witness or settle Part 2's PA-bin proof-length
question.

To independently check the concrete 204-rule summary instance on Lean 4.19.0:

```bash
python3 emit_summary_lean.py summary-arithmetic-demo.json SummaryFiniteCheck.lean
lake env lean SummaryFiniteCheck.lean
```

This checks the fixed grammar, all 407 local Join relations, and its balanced
root summary of length `2^101 + 1`. It does not verify the PA-bin proof printer
or the fixed `Bew` predicate.
