# Current certificate status — 28 September 2026

Part 1 now has a credible conditional construction for its permissive
“any efficient system” branch, based on a slow guarded verifier. A new robust
ledger removes the draft's linear-translation dependency: with the arbitrary
string-fragment abbreviation rule, full expansion costs at most
`2^(O(m^2))`, and a diagonal cutoff of `2^n` yields a direct-proof lower bound
of order `sqrt(n)`. This is still not an end-to-end Lean certificate; the exact
checker arithmetization, derivability-condition proofs, and translation ledger
need one fixed implementation. The fixed PA-bin branch of Part 1 and Part 2
remain unresolved.

The audit is `CHOSEN-SYSTEM-PART1-AUDIT.md`; the repaired quantitative
argument is `CHOSEN-SYSTEM-PART1-ROBUST-LEDGER.md`. They separate this
candidate from the active PA-bin work and record the remaining formalization
gaps. The connective-tag Lean project is related but distinct from the
nullary-predicate construction; its syntax module does not formalize the PA
proof-length claim.

The newest strategic correction is recorded in `LOB-INTERNALIZATION-REDIRECT.md`:
the immediate Part 2 target is polynomial internalization of the specific
Löb-assembled proof, not a global compiler for every valid PA-bin proof file.
The latter is stronger and has an unresolved arbitrary-tautology-axiom case.
`COMPRESSED-TAUTOLOGY-CIRCUIT-ROUTE.md` narrows that case further: preserve the
input's string-grammar compression and build a succinct Boolean evaluation
description, compressed gate-constraint formula, and polynomial PA proof of
correctness. Polynomial-time evaluation on string-compressed Boolean trees is
known, but the required symbolic circuit, PA-bin derivation, and exact `Bew`
bridge are not built. This is a route, not a Part 2 result.
The finite summary-table work is a proof-of-concept for compressed arithmetic
certificates; it is not itself a step in the Löb derivation or an O11 witness.

| Component | Status |
|---|---|
| Restricted whole-file checker and compact universal instantiation | Successful Lean 4.19.0 checks recorded earlier in this session |
| Cached arbitrary-fragment balance summary | Successful Lean 4.19.0 check recorded earlier in this session |
| Expanded-length and numeric-storage bounds (`GrammarLengthBound`) | Successful Lean 4.19.0 check reported in the preceding agent run |
| Tagged serializer model and parser round trips (`ChosenSystemExpansion`, `ChosenSystemSerialization`) | Both Lake targets build locally; the expansion theorem and six parser/serializer round-trip theorems report only `propext` and `Quot.sound`, no `sorryAx`. The model uses a definition prelude and one root stream. |
| Interleaved fragment expansion (`ChosenSystemInterleaving`) | Lean verifies that a script with definitions between emitted fragments compiles to a grammar-plus-root stream without changing its expansion, and has the `2^(2m)` size bound from the serialized directive length. The concrete AX/MP/GEN parser remains open. |
| Explicit fragment family and ordinary-DAG size obstruction | Successful Lean 4.19.0 check recorded earlier in this session |
| Prefix query correctness and instrumented visits (`FragmentPrefix`) | Source complete and independently audited; successful kernel run still pending |
| Interval query correctness (`FragmentRange`) | Source complete and mathematically audited; successful kernel run still pending |
| Matching delimiters, three-query witness check, two-boundary traversal bound | Mathematical argument and independent Python audit; not a Lean or PA certificate |
| Binary addition and local existential summary proofs | Explicit PA-admissible proof objects checked by the new Python calculus; not an exact Enderton or Lean certificate |
| Saved arithmetic proof object for an exponential-word summary table | Fresh JSON replay passed; 407 local Join roots; assembly currently checked externally |
| Concrete summary theorem in Lean | Generated source independently recomputes the 204-rule grammar and proves 407 Join relations by explicit witnesses; pending Lean kernel run |
| Uniform scan and existential expansion-table theorem | Mathematical induction argument for explicit auxiliary coding; PA derivation not emitted |
| Polynomial-bit sequence/table coding | Explicit coding and mathematical size bound; executable round trips passed |
| Arithmetic decoder bridge (`CodedScan`) | Source written; kernel verification pending; semantic Lean theorem, not a PA derivation |
| Exact numeral grammar for power-of-two coding | Mathematical construction only; conditional on coding choices |
| Full PA-bin parser, fixed Bew bridge, polynomial PA acceptance proofs | Not established |
| Compressed Boolean circuit route for arbitrary tautology records | Research specification; no uniform circuit/PA proof yet |

The current workspace has neither `lake` nor `lean` on `PATH`, so the generated
`SummaryFiniteCheck.lean` was not run here. Its source is not yet a Lean
verification. Earlier Lean checks listed above are preserved from their
recorded runs.

From this directory on a working Lean installation:

```bash
lake build GraphFileCheckerInst FragmentBalance GraphDepthBarrier SpecTransfer GrammarLengthBound FragmentFamily
lake build FragmentPrefix FragmentRange
python3 check_fragment_navigation.py
```

The project pins Lean 4.19.0. The second command is the outstanding formal check.
The third runs an independent executable audit, not a kernel certificate.
The prefix file includes executable examples, but no passing output from those
examples is asserted for the current workspace.

See `CONVERSE-NOTE.md` for scope and the audit files for assumptions and gaps.
See `NAVIGATION-MILESTONE.md` for the exact matching theorem and the remaining
PA obligation. The numerical audit output is in `NAVIGATION-AUDIT-OUTPUT.txt`.

The arithmetic step is `PA-ARITHMETIC-MILESTONE.md`: the proof generator now derives
numerical additions and closed existential Join assertions from arithmetic
axioms. This extends beyond the earlier reflexivity-only local certificates.
It does not supply the uniform PA theorem about decoded grammar semantics.

```bash
python3 pa_eq_kernel.py
python3 pa_summary_certificate.py
python3 pa_summary_replay.py --verify summary-arithmetic-demo.json
python3 emit_summary_lean.py summary-arithmetic-demo.json SummaryFiniteCheck.lean
lake env lean SummaryFiniteCheck.lean
```

The first three commands use the experimental PA-admissible calculus, not
Lean. The last command is an independent Lean proof of the finite example; it
does not establish fixed-Bew acceptance. Recorded replay output is in
`PA-AGGREGATE-REPLAY-OUTPUT.txt`.

The latest step is `SYMBOLIC-EXPANSION-MILESTONE.md`, with the detailed
`UNIFORM-SCAN-AUDIT.md`. Expanded codes can remain existential in a fixed
uniform PA theorem for the auxiliary encoding; the named grammar/local-table
codes have polynomial bit length. The single packed-table antecedent still
needs a polynomial PA proof, and the fixed-Bew bridge remains open.

```bash
python3 packed_summary_tables.py summary-arithmetic-demo.json
lake build CodedScan
```

The coding audit passed. The Lean command remains outstanding.
