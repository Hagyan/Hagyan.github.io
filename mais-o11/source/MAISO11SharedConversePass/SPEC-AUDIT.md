# MAIS-O11: specification and calculus audit

Audit date: 25 September 2026. This is a source audit, not a solution of either part of MAIS-O11 and not a new Lean theorem.

Sources: the uploaded `MAIS-A1.tex` (736 lines; Library identity `libfile_a497ff9c172081918f70362f54b738a5`), uploaded `MAIS-O11.md` (Library identity `libfile_285f0722c7f48191b35173f96d5022c6`), and the recovered project `MAISO11SharedConversePass`. Line numbers below refer to those versions. Enderton's *A Mathematical Introduction to Logic*, second edition (2001), is the primary source for the referenced calculus; the agenda identifies this edition at A1 lines 642–645. The book text was checked at printed pages 112, 117–118, 122, and 269–270, through [this PDF of the book](https://daiwz.net/course/logic/books/AMIL2edn.pdf). [Publisher bibliographic page](https://www.sciencedirect.com/book/9780122384523/a-mathematical-introduction-to-logic).

## Main finding

The agenda supplies meaningful constraints on PA-bin, but not a complete executable specification. More seriously for the proposed proof strategy, literal Enderton axiom recognition includes arbitrary propositional tautologies. Compact parsing and expansion equality therefore do not establish a polynomial-time checker for the full calculus. The current certificate is an exact implementation of its own restricted syntax and four axiom families; it is not yet an exact implementation of all agenda PA-bin proofs.

Neither finding shows that MAIS-O11 is false or unanswerable. They show which additional premises and constructions a solution must make explicit.

## What the uploaded agenda fixes

At A1 line 86, proofs are strings over a finite alphabet and must be “checkable by a primitive recursive predicate.” Polynomial-time checking is not required there. Lines 90 and 99 require written-symbol accounting and logarithmic-size numerals. Line 100 permits a fresh abbreviation for a “fixed string,” including earlier abbreviations.

A1 line 104 specifies the following:

- “Peano arithmetic in Enderton's Hilbert calculus,” in fully parenthesized prefix notation.
- Binary constructors with meanings `2x` and `2x+1`.
- Tagged records for axioms, modus ponens, generalization, and abbreviation definitions.
- `def u := τ`, with a fresh name, earlier references permitted, and scope the remainder of the file.
- Names consisting of `u` and a self-delimiting binary integer, with all characters charged.
- Expansion in definition order; the last expanded formula is the conclusion.
- Base-alphabet codes of proof files and written-character proof length.

The same paragraph says these choices fix the checker and coding. That assertion goes beyond the supplied implementation detail: no exact integer code, alphabet enumeration, complete grammar, or checker algorithm appears in that paragraph. A1 line 109 additionally fixes a Delta-1 proof predicate abstractly, without giving its arithmetic formula.

O11 line 11 repeats the claim of complete specification. Lines 15–20 make the distinction relevant: part 1 permits another efficient system, while part 2 names PA-bin specifically. A formalization should not silently replace that system to obtain easier verification.

## Enderton and the existing four axiom families

Enderton p.112 uses all universal generalizations of six logical axiom groups, including every propositional tautology, universal instantiation, quantifier distribution, vacuous quantification, variable reflexivity, and atomic equality replacement. At pp.117–118 generalization is a derived metatheorem; p.122 distinguishes abbreviated derivations using it from literal deductions. His PA presentation uses the arithmetic axioms AE and induction (pp.269–270).

This makes the four constructors in `CompactProof.lean:8–15` legitimate instances of the book's logical axioms:

| Current family | Formula | Status relative to Enderton |
| --- | --- | --- |
| `universalRefl` | `∀x, x=x` | Universal generalization of variable reflexivity |
| `inst` | `(∀x A) → A[t/x]` | Universal-instantiation instance; current record checker restricts to closed `t` |
| `contrap` | `(A→¬B)→(B→¬A)` | Propositional tautology |
| `conjIntro` | `A→(B→¬(A→¬B))` | Propositional tautology |

Thus these four were not erroneously promoted from multi-step derived rules. In contrast, term reflexivity and existential introduction really are derived in `PAFormula.lean:144–156`.

The agenda's generalization record is an explicit choice beyond literal MP-only Enderton deductions. It may be intended as a primitive admissible-rule extension or as a macro whose expansion is charged. The prose does not distinguish these choices; their proof-length measures need not coincide. Calling this a variant is justified; calling the agenda inconsistent is not.

## Exact implementation gaps

| Issue | Current implementation | Consequence |
| --- | --- | --- |
| Logical axioms | Exactly four families in `CompactProof.lean:8–15`; `CompactChecker.lean:143–146` recognizes those four | No arbitrary tautologies, quantifier distribution, vacuous-quantifier scheme, general atomic equality replacement, or general universal closure of axiom instances |
| Arithmetic axioms | None in `PAFormula.lean:122–129` or `CompactProof.lean:8–15` | No object-language PA arithmetic or induction has been added. Lean's semantic interpretation of `+`, `*`, `D`, `E` does not provide arithmetic axioms to the object calculus |
| Generalization rule | `Record` has only `axiom` and `mp`, at `CompactWire.lean:361–363` | No agenda generalization record, parser, or checker |
| Open proof lines | Every serialized proof formula is `CFormula r 0`; `CompactParser.lean:244,252` parses at variable context zero | Open intermediate formulas and ordinary nonvacuous generalization cannot be represented in proof files |
| Variable spelling | De Bruijn variables internally; canonical depth levels on the wire, `CompactWire.lean:135–185` | `CompactParser.lean:173–178` requires the next binder name to be exactly its depth. Other legal named-variable spellings and shadowing are excluded unless translated |
| Abbreviation type | `CTerm.ref` expands to `ClosedTerm`; definition RHS has no variables or formulas (`CompactParser.lean:403–445`, `SharedPrelude.lean`) | These are closed-term abbreviations only. A1 does not impose that restriction on its “fixed string” abbreviations |
| Abbreviation placement | All definitions precede all logical records (`CompactParser.lean:893–898`) | Interleaved definitions, permitted by the agenda's record sequence, require a translation or an extended parser |
| Fresh names | Next definition must have index `env.length` (`CompactParser.lean:442`) | The agenda only says fresh. Arbitrary fresh indices are not handled without renaming |
| Counts | Register and record counts are external parameters; `CheckFile.lean:5–24` | The certified callable checker is not yet a single-input proof-file predicate with no auxiliary count inputs. Counts are inferable from tags, but that inference and its agreement need certification |
| Expansion costs | Shared parsing avoids materializing definition expansions. Modus-ponens comparisons use the variable-labelled DAG at every binder depth; successful contraposition, conjunction introduction, and reflexivity instantiation axiom shapes use graph shortcuts (`OpenGraph.lean`, `SharedOracle.lean`). Other instantiations and failed shortcut candidates still call the expansion-based checker (`CompactChecker.lean:200`) | Some successful axiom instances avoid expansion, but many candidates can still trigger exponential expansion; this is not a full polynomial-time checker |
| Arithmetic proof predicate | No literal full PA-bin `Bew` formula and polynomial internalization compiler | Lean-level parser/checker correctness alone is not a short PA proof of its own accepting computation |

`PAFormula.lean:12–19` has `0`, `D`, `E`, `+`, and `*`, and `Formula` has equality, negation, implication, and universal quantification. Successor, order, and the precise definitional status of `D/E` require explicit choices for a complete PA presentation. All nonlogical arithmetic axioms are missing; the agenda does not spell out a literal list that could be copied unchanged into this syntax. Choosing a conventional list is possible, but must be documented as completing the specification.

The earlier `StringQuotation.lean:61–89` does handle arbitrary string-fragment grammars for quotation. This does not mean the proof-file decoder accepts arbitrary string-fragment definitions: the quotation compiler and the decoder's closed-term grammar are different layers. They need a formal connection.

## The newly identified complexity obstacle

The often-used implication

> compact syntax + easy local proof rules → polynomial proof verification

cannot be applied to the literal all-tautologies axiom group without another argument. An arbitrary propositional formula, regarded as an axiom candidate, already presents a tautology decision problem. An exact polynomial-time recognizer for that group would give a polynomial-time algorithm for TAUT. This obstruction is independent of exponential abbreviation expansion and is not cured by shared term equality.

It is essential to distinguish three claims:

1. There is a polynomial-time decision procedure for all valid proof files.
2. Every valid proof file has a short PA proof of its validity.
3. There is a polynomial-size compiler producing those internal proofs, conditional on input validity.

The first is obstructed by the tautology family under the usual complexity assumptions. The first is not a necessary condition for the other two. A compiler might reuse an input tautology as a tautology axiom after replacing its atoms by suitable arithmetic evaluation formulas. It could then prove a compositional evaluation statement without enumerating a truth table. That is a possible new route, not a completed internalization theorem. It still requires exact arithmetization, short compositional correctness proofs, quantified valuation handling, and actual serialized PA derivations.

Replacing the tautology group by a fixed Frege basis or adding extra certificates changes the admitted proof files and possibly their lengths. Such a change is legitimate as an explicitly named comparison system, but it is not automatically a resolution of part 2 for the stated default.

## Prioritized next formal targets

1. **Make the target contract explicit.** Record which details are agenda requirements and which are choices completing it. Preserve the all-tautologies group if using literal Enderton. State how generalization records are charged; name the PA language, arithmetic axioms, induction, integer code, and arithmetic `Bew` presentation.
2. **Formalize the full logical axiom relation before extending the parser piecemeal.** Include all six families, universal generalizations, and the agreed rule treatment. Prove that the current four-family calculus embeds into it with an explicit character-cost map. This pins down what current certificates establish in the target.
3. **Attack arbitrary-tautology internalization separately.** The current graph shortcuts handle two fixed propositional axiom shapes but not Enderton's full tautology family. First prove the finite-syntax evaluation-substitution lemma for propositional skeletons and arbitrary replacements. Then build and bound object-language derivations certifying the evaluation equation. State the desired compiler theorem for a supplied tautology without claiming an efficient tautology decider.
4. **Extend proof-file scope and abbreviation support with explicit translations.** Variable-labelled DAG equality now handles open terms at every binder depth for modus-ponens comparisons. The Lean-checked `hiddenWitness_is_instance` example shows that a general compact instantiation checker must search subterms inside definition graphs: the only compact conclusion reference names the entire larger term, while the substitution witness is an internal subterm. Still certify variable renaming, permitted abstraction/capture behavior, and movement of interleaved definitions if using a prelude normal form. For arbitrary string fragments, prove their parsing and binding consequences rather than assuming every fragment is a term subtree.
5. **Only then claim a PA-bin checker or polynomial internalization result.** Add all nonlogical arithmetic axioms, induction checking, full proof-file coding, and a uniform internalization theorem in the specified object calculus. Existing exponential-expansion examples remain valuable regression cases but do not settle these obligations.

The substantial correction from this audit is therefore strategic: the target was being treated as though finishing a compact parser would finish an ordinary polynomial-time Hilbert checker. The uploaded default names an axiom system with a separate tautology-verification issue, and its remaining syntactic choices must be fixed explicitly. This narrows the missing theorem rather than supplying a negative answer to MAIS-O11.
