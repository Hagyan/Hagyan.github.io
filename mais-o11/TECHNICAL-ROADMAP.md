# Technical roadmap from the current state

**No PA-bin Part 1 or Part 2 proof is claimed here.** This is a dependency map, not a progress percentage. The shortest plausible positive Part 2 route is to cost the particular Löb construction; a negative result would instead require a new shortest-proof lower bound.

## First fix the target that the cost theorem quantifies over

1. Write the exact ordinary PA-bin record and formula specification. Preserve the agenda's arbitrary string-fragment abbreviations, all Enderton logical axiom groups including arbitrary tautologies, arithmetic axioms, induction, MP, and the intended generalization records. Choose and disclose missing details of the finite alphabet, identifier syntax, formula numbering, line references, expansion order, and exact arithmetical Bew. The uploaded agenda constrains these but does not supply a complete executable checker.
2. Implement one serializer, parser, and checker and prove a soundness/completeness theorem for its exact expanded Hilbert relation. Give an explicit map from accepted files to the abstract expansion model and charge every written character. The current chosen-system tagged serializer, interleaving model, and restricted compact checker are useful components with different inputs. They have not yet been identified.
3. Freeze this source and record reproducible builds, theorem statements, dependency audits, and checksums. Do not switch to a different proof predicate midway through a proof-length comparison.

## Positive route for Part 2: cost the Löb assembly

For each sentence P of expanded length n and actual PA-bin proof π of □P → P of written length k, build the diagonal sentence D_P and the usual Löb proof ρ(P,π) of D_P, with polynomial written budgets. The decisive missing constructor should output a **PA-bin proof file** q of the fixed arithmetic statement Bew(code(ρ(P,π)), code(D_P)) with |q| bounded by one polynomial in k+n. Prove that q passes the fixed checker. Complete the constant number of subsequent MP/implication steps and derive a polynomial upper bound on F_PA-bin(k,n).

This is narrower than a global compiler internalizing every PA-bin proof; a global compiler would be sufficient but is not demanded by this route. The construction still must process every arbitrary tautology record that may occur inside the input π. The [compressed tautology route](source/MAISO11SharedConversePass/COMPRESSED-TAUTOLOGY-CIRCUIT-ROUTE.md) proposes a symbolic evaluator and object-PA correctness proof for a string grammar. Its essential unsolved lemma is a polynomially written PA-bin acceptance proof for every promised-valid compressed tautology axiom. A polynomial evaluator for one Boolean assignment and an ordinary constructor DAG do not give that lemma.

The arithmetic side needs quantified, uniform derivations, not only finite replay. The JSON 407-join certificate, prefix/range balance, compact quotation and PA-admissible local proofs identify useful algorithms; one must emit exact Enderton proof files for the packed antecedent, the coding lemmas, and the fixed Bew bridge. Keep code numerals, expanded formula lengths, and written file lengths separate.

## Negative route for Part 2 and direct Part 1 route

A negative answer requires a family (k_i,n_i) on which F_PA-bin exceeds every fixed polynomial. That entails lower bounds against **all** ordinary direct proofs, not against one printer or one representation. With the fixed standard Löb predicate and finite maxima assumptions, [SpecTransfer](source/MAISO11SharedConversePass/SpecTransfer.lean) would then give a Part 1 witness in the same system. A merely superlinear lower bound already suffices for that Part 1 transfer; no such actual PA-bin bound has been shown.

A standalone Part 1 attack may prove short □P_i → P_i certificates plus an independent all-proofs direct lower bound and r(P_i) → ∞. The bounded Gödel candidate does not supply its short reflection proofs. Any candidate must survive short MP composition and check for alternate derivations, including compressed ones.

## Separate alternative-system branch

The guarded slow-verifier [robust ledger](source/MAISO11SharedConversePass/CHOSEN-SYSTEM-PART1-ROBUST-LEDGER.md) is a candidate for the permissive alternative-system wording of Part 1. To close it, emit the checker source and fixed indices, object-PA diagonal/guard/D1–D3 proofs, exact accepted-file expansion and translation theorems, and the final character inequality. It does not transfer to ordinary PA-bin Part 1 or Part 2. This branch can be pursued independently after the current archival pause.

## Stop conditions for claims

- A Lean theorem about an abstract grammar proves only that theorem, even if its file builds and reports no sorryAx.
- A Python replay in a PA-admissible calculus is not acceptance by the fixed Enderton/Bew checker.
- A claimed Part 2 bound must quantify over **every** accepted reflection proof in the fixed system and account for its arbitrary tautology records.
- A claimed Part 1 witness must prove the lower bound for **every** direct proof and the reflection-length divergence.
