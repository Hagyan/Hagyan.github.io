# One checked conjunction for the local summary table

27 September 2026. This step combines every certified local arithmetic result
into one closed theorem of the PA-admissible object calculus. It is progress
toward a single coded table assertion, but it does not establish that coded
assertion, the fixed Enderton/Bew bridge, or either part of MAIS-O11.

## Result

For each atom occurrence in the compressed grammar, the existing generator
produces a closed proof of its existential Join equation. The grammar, summary
table, and gate positions independently determine the formula expected at
each root. `pa_summary_replay.py` checks all of those root/formula pairs, then
checks that `aggregate_root` proves the conjunction of the 407 individual
Join sentences in production and RHS order.

The proof uses 407 local roots and 406 conjunction introductions, plus the
existing arithmetic and existential introduction records. It is one closed
sentence in the object calculus: the conjunction of the complete finite list
of certificate equations. Its semantics follows from the soundness of each
accepted arithmetic and logical rule; no disjunction or existential witness is
inferred from a Python numeric equality alone.

The logical formulas are now serialized as a shared DAG. The new example
contains 24,012 formula nodes, 6,511 introduction records, 912 arithmetic
records, and 494 term nodes; the replay file is 864,778 bytes. The previous
tree-shaped JSON duplicated each longer prefix conjunction and occupied about
16.9 MB. Formula-DAG references encode the sharing actually used by the proof.
The definition DAG, grammar, binary identifiers, and derivation records all
have polynomial size in the grammar mass. This is a size audit of the object
calculus representation; no exact PA-bin character count has been certified.

## Independent Lean statement for the concrete instance

`emit_summary_lean.py` reads the replay-checked JSON and emits
`SummaryFiniteCheck.lean`. The source defines the 204-rule grammar and Lean
functions for recomputing its summary table and intermediate gate list. It
states the backward-reference check, table equality, final summary
`(2^101 + 1, 0, 0)`, and `computed_gates_valid`; the 407 local Join proofs use
explicit natural number witnesses. No expanded word is constructed.

If successfully elaborated, these Lean theorems check the finite mathematical
instance by computation and explicit witnesses. They do not replay the Python equational proof graph,
derive the local facts in PA's Hilbert calculus, encode the compressed table as
a PA formula, or check the fixed PA-bin `Bew` predicate. The current workspace
has no `lake` or `lean` executable, so the generated source is pending a local
Lean 4.19.0 kernel run. The replay and exporter themselves were run here.

## Finite assembly lemma

Let D_i prove A_i for i<r in a calculus with a fixed conjunction-introduction
template. Define C_0=A_0 and C_(i+1)=C_i AND A_(i+1). One application of the
fixed template gives C_(i+1) from C_i,A_(i+1), so the proof DAG has r-1 new
inference nodes, in addition to the union of the input proof DAGs. If formulas
and terms are shared by an acyclic abbreviation DAG, each new conjunction
definition refers to the previous C_i and next A_i by a binary identifier.
Charging each identifier O(log(r+2)) symbols gives the elementary bound

    size(assembled proof) <= sum_i size(D_i)
                            + O(r log(r+2) + formula-DAG definitions).

For the actual Enderton propositional-axiom presentation, each introduction
can be expanded using the fixed tautology A -> (B -> A AND B) and two MP
applications. This adds a constant number of proof records per join, plus the
charged record references and shared formula definitions. It is a concrete
assembly route for a *finite list* of already supplied PA proofs. It does not
prove the PA derivation of the computational predicate saying the packed
table decodes to that list.

In the demonstrated auxiliary code, the named grammar, root table, and
intermediate accumulator table are separately packed. Round-trip lookup tests
passed for all table rows. Those executable checks do not supply PA proofs of
the decoding equations. The next exact obligation is a short PA proof of

    DecodeGrammar(g,G) AND DecodeSummaryTable(t,T)
      AND PackedArithmeticProofs(c, A_0,...,A_(r-1))
      -> AndList(A_0,...,A_(r-1)),

or an equivalent uniform local-table theorem. In particular, one must show
that each binary lookup from the packed table selects the very operands used
at the corresponding Join root. The outer existential expansion theorem can
then consume the resulting uniformly coded table assertion. No expanded word
code needs to be written.

This is still an auxiliary syntax and proof calculus. To reach MAIS-O11's
fixed proof predicate, the definitions of the numerical terms, formulas,
record tags, and abbreviation references must be tied to the exact PA-bin
grammar and checker. The uploaded draft does not print every decoder detail.

## Reproduction

```bash
python3 pa_summary_replay.py --verify summary-arithmetic-demo.json
python3 packed_summary_tables.py summary-arithmetic-demo.json
python3 emit_summary_lean.py summary-arithmetic-demo.json SummaryFiniteCheck.lean
lake env lean SummaryFiniteCheck.lean
```

The replay rejects mutations to a gate claim, individual proof root,
aggregate root, packed grammar cycle, and arithmetic proof conclusion. Its
acceptance is an executable check of the specified object calculus, not a
Lean kernel certificate or a derivation in the fixed PA-bin file format. The
last command is a separate Lean check of the concrete grammar instance; it
remains pending until run under Lean 4.19.0.
