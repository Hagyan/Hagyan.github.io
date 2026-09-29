# MAIS-O11: certified equality for shared arithmetic terms

## Result

`DagEquality.lean` implements a table-based comparison of acyclic, shared closed arithmetic terms. `Graph.table_iff` proves that its Boolean entry for any two roots is true exactly when their fully expanded terms are syntactically identical. Expansion occurs in the mathematical specification, not in the table-building algorithm.

The graph supports the exact closed-term constructors used in our preceding arithmetic syntax: zero, binary doubling D, binary doubling-plus-one E, addition, and multiplication. A node can refer only to earlier nodes, enforced by its `Fin n` reference type. Graphs can contain duplicate nodes and arbitrary sharing; no canonicalization assumption is needed.

This is standard dynamic programming formalized for the present syntax. It does not decide the open problem or establish a PA internalization bound.

## Algorithm and correctness

When a graph has n nodes, its materialized Boolean table records expanded syntactic equality for all n by n pairs. To append a node:

1. Copy the existing comparisons.
2. Compare the new node with every old node in each orientation. Different outer constructors compare false. Matching unary or binary constructors consult one or two entries of the old table.
3. Set the new diagonal entry to true.

`Node.same_iff` proves the local constructor comparison correct given a correct child table. `Graph.node_expand` identifies the term defined by a node retrieved from the graph. Induction over graph extensions then proves `Graph.table_iff`.

The algorithm checks syntax, not numerical equality. In particular it correctly distinguishes zero from a syntactically nontrivial sum of zeros, even though both terms denote zero.

## Construction schedule and implementation correction

The number of scheduled calls to the constructor comparator is given by c(0)=0 and c(n+1)=c(n)+2n. Lean proves `comparisonCalls n + n = n*n`. The matrix-entry write schedule is w(0)=0 and w(n+1)=w(n)+(n+1)^2; Lean proves `tableWrites n <= n*n*n`.

These are exact/upper bounds for the stated construction schedules. They are not an instrumented operational-semantics theorem for the compiled program, a bit-complexity theorem, or a PA proof-length theorem. Looking up a node also traverses its graph prefix; the direct implementation follows at most one recursive branch at each level.

Testing exposed a problem in the first executable version: Lean's logical eliminator `Fin.lastCases` is defined using reverse induction. It was inappropriate for an inexpensive runtime index branch, and the large test did not finish promptly. The final executable `Graph.node` and `Graph.table` use the new `splitLast`, with a direct index test and a delayed last branch. This avoids evaluating unused comparisons. `Fin.lastCases` remains in the semantic expansion specification and proofs, where it is not evaluated by the comparator.

The corrected build and all four tests pass. The failure of the first implementation is a useful distinction between a logical correctness theorem and an efficiency claim.

## Connection to the actual abbreviation family

`doublingGraph_matches_definitions` proves that the graph representation of the doubling family has precisely the expanded root previously certified for `doublingProgram` in the actual serialized definition grammar.

`duplicateRoot_expanded_nodes` proves that the two equal roots tested at parameter n describe expanded terms with 2^(n+2)-1 nodes. The executable tests evaluate only their shared graphs and comparison tables:

| Parameter n | Graph nodes | Scheduled constructor comparisons | Expanded root nodes |
|---|---:|---:|---:|
| 0 | 3 | 6 | 3 |
| 4 | 7 | 42 | 63 |
| 20 | 23 | 506 | 4,194,303 |
| 60 | 63 | 3,906 | 4,611,686,018,427,387,903 |

Every test also rejects a comparison between the zero root and the large addition root. The expanded-node counts in the test report are computed from the proved formula, not by expanding the trees.

## What remains

The table theorem applies to arbitrary well-formed graphs, but the connection to the preceding definition compiler is currently established only for the doubling family. A general compiler/parser that retains sharing still needs a correctness and size proof. Formula substitution under binders is not handled by this closed-term module. General axiom recognition, arithmetization of the comparison procedure, short PA proofs of verification, and the uniform quantitative Löb transformation remain to be connected.

Thus literal expansion is no longer required for this particular syntactic equality operation. This does not rule out a negative answer to MAIS-O11 part 2. The conditional theorem from the previous checkpoint still has unproved PA-bin cost hypotheses.

## Verification

In `MAISO11DagPass`, run `lake build` and `lake env lean DagDemo.lean`. Both passed with Lean 4.19.0. The principal new theorems depend only on `propext` and `Quot.sound`; there are no admitted proofs, custom axiom declarations, or native_decide proofs. `CHECKED-OUTPUT.txt` records the executable tests and dependency audit.
