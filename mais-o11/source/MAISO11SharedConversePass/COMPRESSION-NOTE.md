# MAIS-O11: audit of the remaining gap and an expansion barrier

## What the problem still requires

The uploaded MAIS-O11 statement asks in part 1 for a fixed positive delta and sentences P_i such that the shortest direct proofs exceed the shortest reflection proofs by a fixed factor plus the specified formula-length toll. It also requires the shortest reflection-proof lengths to tend to infinity. A long proof we happen to construct is not a lower bound on the shortest proof. Any successful lower-bound argument must cover every proof in the selected full system.

Our current Lean certificates establish particular proof constructions, their serialized lengths, and the correctness of an executable checker for the emitted fragment. They supply upper bounds, not the lower bound required by part 1. The fragment contains fewer axiom schemes and rules than full PA-bin; a lower bound proved only for this fragment would not automatically apply to PA-bin.

Part 2 asks for a uniform polynomial bound on the conversion from proofs of Box P -> P to proofs of P, or a refutation of that bound. The existing trace theorem is not such a conversion. The published agenda's proposed ledger still needs quantitative diagonalization and internalization results for the stipulated arithmetic and proof encoding, and those results must be assembled into a complete proof transformation.

In particular, a Lean theorem about a checker is a theorem in the surrounding formalization. It is not itself a short proof written in PA-bin that its own arithmetized proof predicate accepts a given encoded file. A polynomial-time external verifier, if obtained, would be helpful but would still need an explicit arithmetic simulation and length accounting. It is not logically necessary to prove every desired PA length bound via a polynomial-time verifier; another direct PA construction might work.

## New certified obstruction to literal expansion

`CompressionBarrier.lean` builds a family in the existing `PackingProgram` grammar, with no source registers. Start with a definition of zero, and repeatedly define a fresh register to be the sum of two references to the previous register. All identifiers use the project's actual self-delimiting binary encoding and every written character is charged.

For n doubling steps, Lean proves:

- The actual definition reader accepts the emitted file and reconstructs its environment.
- Written length is at most `(2*n + 22)*(4*n + 2)` characters.
- The final expanded term has exactly `2^(n+1)-1` syntax-tree nodes.

The main theorem is `MAISO11.Quotation.parsed_expansion_barrier`. The induction uses the recurrence `T(0)=1`, `T(n+1)=1+2*T(n)` for the expanded tree. The written bound follows from the existing certified serializer estimate and the exact definition-expression weight `1+3*n`.

Actual executable examples (n, written characters, expanded tree nodes):

| n | Characters | Expanded nodes |
|---|---:|---:|
| 0 | 14 | 1 |
| 1 | 40 | 3 |
| 4 | 138 | 31 |
| 8 | 290 | 511 |
| 12 | 458 | 8191 |

Consequently, an approach that physically writes the entire expanded tree cannot have a polynomial output-size bound in the compressed file length. This is a concrete reason the parser/checker correctness results do not provide the desired complexity bound automatically.

**Scope:** this is a syntax-size theorem. It is not a lower bound on the actual compiled Lean program's runtime: an implementation can share heap objects and reuse computations. It is not a shortest-proof lower bound or an impossibility result for polynomial PA internalization. The terms all evaluate to zero, but syntactic proof checking must still respect their structure; numerical equality is not a substitute for syntactic identity.

## Next research gate

We should distinguish two research tracks explicitly. Part 1 needs a candidate sequence and a genuine proof-length lower-bound mechanism in the full chosen system. The current files do not supply that mechanism. Part 2's constructive route needs a uniform proof transformation with internalization and diagonalization costs fully accounted for.

For the current implementation route, the next concrete step is explicit syntax sharing with certified structural equality and substitution. Its connection to the existing expansion semantics must be proved. Any improved checker must then be connected inside PA to the stipulated proof predicate with controlled proof length. Incidental speedups observed in compiled code are not a substitute for those theorems.

Neither part of MAIS-O11 is resolved. This checkpoint gives a verified diagnosis of one failed shortcut; it does not establish that the problem is impossible or that the remaining work is routine.

## Verification

Run `lake build` and `lake env lean BarrierDemo.lean` in the project directory. Both succeeded under Lean 4.19.0. The main new theorem's axiom dependencies are `[propext, Quot.sound]`, with no `sorry`, additional axiom, or `native_decide` dependency. The previous checker certificate is retained, with its scope described in `CHECKER-NOTE.md`.
