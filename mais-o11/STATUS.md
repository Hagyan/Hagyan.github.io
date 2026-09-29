# Theorem and verification status

**Snapshot: 2026-09-28.** This page supersedes status sentences in older snapshots. The target is the ordinary PA-bin system described in the [uploaded agenda](source/spec/MAIS-A1.tex), including binary numerals, fully charged string-fragment abbreviations, tagged axiom/MP/generalization/definition records, a fixed proof-file coding, and a fixed arithmetical proof predicate.

Let d(P) be the least written length of a direct proof of P, r(P) the least written length of a proof of □P → P, and s(P) the sentence length. Part 1 seeks a sequence with r(P_i) → ∞ and d(P_i) ≥ (1+δ)r(P_i)+C₁(s(P_i)+1) for some δ>0. Part 2 asks whether F_PA-bin(k,n) = max{d(P): r(P)≤k, s(P)≤n} has a fixed polynomial upper bound, or grows faster than every polynomial along a sequence.

## Headline decisions

| Question | Current answer |
| --- | --- |
| Part 1 for intended ordinary PA-bin | **Open.** No verified family with a lower bound on *all* direct proofs and a short ordinary reflection proof. |
| Part 1 for an alternative efficient system | **Conditional candidate.** The guarded slow-verifier ledger gives a mathematical size argument assuming a fixed PA base and consistency. Exact checker, recursion-theorem index, uniform guard and D1–D3 derivations, and translation proof objects remain absent. Do not report a completed witness. |
| Part 2 for intended ordinary PA-bin | **Open.** No polynomial conversion theorem and no superpolynomial lower-bound family. |
| Shared syntax, parser/trace, compact equality, padding/composition | **Infrastructure and diagnosis.** They do not constitute a substantive PA-bin Part 2 result. |

## Proved and Lean-verified within their stated models

**Fresh evidence:** [all six historical projects](historical/MAIS-O11-certificates/archive-six-projects-build-2026-09-28.txt) passed their build and warning-as-error Audit.lean scripts; [all 40 registered current libraries](source/MAISO11SharedConversePass/archive-build-audit-2026-09-28.txt) built with Lean 4.19.0. The current source scan found no sorry, admit, custom axiom declaration, or native_decide. Selected theorem dependency reports list Lean's standard propext and Quot.sound, and sometimes Classical.choice; the build transcript is not a proof that every declaration has the same axiom set. The [finite example](source/MAISO11SharedConversePass/archive-finite-check-2026-09-28.txt) also elaborated. A build checks precisely the theorem statement and assumptions encoded in a file.

| Layer | Representative declarations or result | Scope |
| --- | --- | --- |
| FirstPass / AuditPass / TaggedPass | conditional_main; internal_lob_axiom under interfaces; guarded tag syntax and numerical gaps | Abstract hypotheses or tagged auxiliary system, not PA-bin. The earlier blanket guard-preservation claim was corrected. |
| QuotationPass | compile_correct, checked local certificates and traces, packedWitness_checked, character bounds | Raw-fragment quotation and restricted local calculus. |
| ObstructionPass / EnvelopePass | suffix-assembly inequalities, separation obstruction, noSpeedup_iff_sublinear_envelope | Numerical and abstract proof-system implications, no witness for the target. |
| Compact parser and trace | CompactParser, CompactChecker, SharedConverse; decodeWholeShared_iff_old, checkWholeSharedReference_sound | Restricted calculus: four logical axiom families, closed-term abbreviations, definition prelude, AX/MP records. |
| Shared equality and instantiation | DagEquality, SharedOracle, GraphFileCheckerInst; compiledInstCandidates_iff, checkWholeGraphWithInst_eq_old_accept | Exact equivalence to the restricted expanding checker, including hidden graph subterms. Other axiom cases may expand. |
| Arbitrary string fragments | FragmentBalance, GrammarLengthBound, FragmentPrefix, FragmentRange, FragmentFamily | Correct cached balance/length and prefix/range queries; a source-language graph depth obstruction. Prefix/range were previously listed as pending; their libraries built in this audit. No full compressed first-order parser or PA internal proof. |
| Abstract transfer | SpecTransfer.unboundedOverheadGivesWitness and reflectionLengthsTendToInfinity | If the *same system* has superlinear overhead and the stipulated finite maxima/fiber hypotheses, strong Part 1 witnesses follow. The needed lower bound on actual F is unknown. |
| Chosen-system expansion | ChosenSystemExpansion, ChosenSystemSerialization, ChosenSystemInterleaving | Tagged grammar-plus-root round trips, abstract interleaving, and a 2^(2m) expansion bound from that model's serialized directive cost. No concrete AX/MP/GEN proof-file parser or accepted-file bridge. |
| Arithmetic bridge and finite instance | CodedScan library builds; SummaryFiniteCheck.lean elaborates one 204-rule grammar and 407 local joins | Lean semantic statements and one finite check, not a uniform PA derivation or fixed Bew acceptance theorem. |

The Python programs replayed finite local arithmetic proof objects in an experimental PA-admissible calculus, including a 407-join JSON example. This is executable checking by that program. It is not the agenda's exact Enderton PA-bin proof predicate, and the Lean finite example does not replay that Python proof graph.

## Conditional, exploratory, and obstructed routes

- **Chosen guarded verifier.** The repaired ledger replaces a withdrawn linear expansion/translation claim by a coarse bound 2^(C(m+1)^2), using arbitrary fragments and cutoff 2^n. It derives a proposed Ω(√n) direct-proof bound versus logarithmic reflection-file size. Its mathematical outline still requires a concrete fixed-point checker and object-PA proofs. [Ledger](source/MAISO11SharedConversePass/CHOSEN-SYSTEM-PART1-ROBUST-LEDGER.md).
- **Padded shortcuts.** The numerical inequality is Lean-checked. A quadratic terminal trailer violates the agenda's constant-cost MP composition property, so this weak-definition example cannot be promoted to the intended result. [Continuation](source/MAISO11SharedConversePass/CONTINUATION-NOTE.md).
- **Finite Gödel sentences.** A bounded diagonal lower bound does not produce a short proof of the unbounded reflection premise. Combining a short proof of □P with a short □P → P gives a short direct proof. [Part 1 audit](source/MAISO11SharedConversePass/PART1-ADVERSARIAL-NOTE.md).
- **Ordinary term DAGs.** Raw string fragments can encode an exponentially deep unary term; any constructor DAG for it has exponentially many nodes. This blocks that representation, not every compact parser or a PA proof. [Compiler audit](source/MAISO11SharedConversePass/SHARED-COMPILER-AUDIT.md).
- **Tautology records.** Literal Enderton axioms include arbitrary propositional tautologies. A general exact polynomial-time recognizer would decide TAUT in polynomial time; this conditional complexity obstacle does not rule out a polynomial proof printer on promised-valid inputs. The proposed compressed Boolean-circuit route has no uniform symbolic compiler or PA correctness derivation. [Route](source/MAISO11SharedConversePass/COMPRESSED-TAUTOLOGY-CIRCUIT-ROUTE.md).
- **Provability predicate.** An extensionally correct Δ₁ formula can fail Löb's derivability conditions. The actual fixed Bew and uniform PA bridge matter; standard-instance agreement alone is insufficient. [Audit](source/MAISO11SharedConversePass/PART2-ADVERSARIAL-NOTE.md).
- **Other local repairs.** Prefix-minimum summaries cannot be subtracted to recover interval minima; direct range traversal repairs that local issue. A power-of-two-alphabet numeral homomorphism is conditional on coding choices absent from the uploaded agenda.

## Exact outstanding obligations

1. Fix a complete executable PA-bin contract compatible with the agenda: alphabet, complete Enderton logical and arithmetic axiom families including all tautologies and induction, generalization, open lines, arbitrary fresh identifiers and interleaved string-fragment definitions, counts, Gödel codes, and a canonical arithmetic Bew formula. Record every choice where the prose is underspecified.
2. Prove the concrete proof-file decoder/serializer and checker agree with the stated PA-bin relation for **all** accepted files. Current Lean equivalences apply to a restricted calculus, and the chosen-system serializer applies to a different abstract stream.
3. For a positive Part 2 answer, construct a PA-bin proof of the diagonal lemma and the necessary D1–D3/introspection instances with polynomial **written character** budgets, then internalize the particular Löb-assembled proof from any reflection proof. Handle arbitrary compressed tautology records without assuming a polynomial tautology decider or silently changing the calculus. Prove the output is accepted by the fixed Bew predicate and the resulting bound on F.
4. For a negative Part 2 answer, exhibit and prove a superpolynomial family of shortest direct-proof lower bounds against **all** PA-bin proofs while bounding the corresponding reflection lengths. No such lower bound is present.
5. For ordinary PA-bin Part 1, give a family with the exact δ, C₁, and divergence conditions above and exclude all alternate short proofs. The conditional SpecTransfer theorem applies only after an actual superlinear lower bound is supplied.
6. For the alternative chosen system, implement and certify its exact guarded checker and self-reference, the PA guard lemma, consistency/derivability conditions, the accepted-file-to-abstract-expansion bridge, and the quantitative translation of every accepted proof. Until then the proposed Part 1 inequality is a draft.

See [TECHNICAL-ROADMAP.md](TECHNICAL-ROADMAP.md) for an order of attack and [ARTIFACTS.md](ARTIFACTS.md) for source locations.
