# Artifact inventory

**Inventory cut: 2026-09-28.** This is a file inventory, not a proof claim. Links point to the public snapshot when bytes are included. The original ChatGPT Library also has checkpoint ZIPs by the exact filenames below; those historical ZIPs are catalogued, while the six-project sources and the final current-project source are expanded in this repository. No unrelated user images or personal files are part of this archive. See [STATUS.md](STATUS.md) for mathematical scope.

## Primary specifications, manuscripts, PDF and TeX

| Artifact | Purpose | Verification/status |
| --- | --- | --- |
| [MAIS-O11.md](source/spec/MAIS-O11.md) | Uploaded problem statement | Primary target, not our theorem; SHA-256 30a8828c7311bbca… |
| [MAIS-A1.tex](source/spec/MAIS-A1.tex) | Uploaded agenda including PA-bin grammar and question | Primary specification; underdetermined executable details; SHA-256 ba7379dece208f8e… |
| [MAIS-O11-slow-verifier-construction.tex](historical/MAIS-O11-certificates/research-notes/MAIS-O11-slow-verifier-construction.tex) | Original guarded slow-verifier manuscript | Historical draft; use corrected robust ledger; SHA-256 2d36f4142edf2486… |
| [MAIS-O11-slow-verifier-construction.pdf](historical/MAIS-O11-certificates/research-notes/MAIS-O11-slow-verifier-construction.pdf) | Rendered original manuscript | Historical PDF, same scope as TeX; SHA-256 e98b1c56cae9eea0… |
| [MAIS-O11-progress-report.tex](historical/MAIS-O11-certificates/research-notes/MAIS-O11-progress-report.tex) | Earlier research report source | Historical; claims audited by current STATUS; SHA-256 91e124d3c68a0db9… |
| [MAIS-O11-progress-report.pdf](historical/MAIS-O11-certificates/research-notes/MAIS-O11-progress-report.pdf) | Rendered earlier report | Historical PDF, same scope as TeX; SHA-256 5c12a2add2078d87… |

The two PDFs and their TeX sources are preserved together in the historical certificate tree; the TeX sources allow regeneration.

## Six historical Lean 4.19.0 projects

The [cumulative tree](historical/MAIS-O11-certificates/README.md) contains each project’s Lean source, Audit.lean, README.md, lakefile.toml, lake-manifest.json, lean-toolchain, SHA256SUMS, and checked-output.txt, plus the files named below. [verify.sh](historical/MAIS-O11-certificates/verify.sh) passed for all six in a fresh run. The original root [SHA256SUMS](historical/MAIS-O11-certificates/SHA256SUMS) verified all 85 files in the unpacked bundle before the new audit transcript was added.

| Project | All Lean source in that project | Certified purpose and limit |
| --- | --- | --- |
| [MAISO11FirstPass](historical/MAIS-O11-certificates/projects/MAISO11FirstPass/README.md) | [FirstPass.lean](historical/MAIS-O11-certificates/projects/MAISO11FirstPass/FirstPass.lean), [Audit.lean](historical/MAIS-O11-certificates/projects/MAISO11FirstPass/Audit.lean) | Abstract finite diagonal, Löb, and conditional separation. Fresh build/Audit.lean pass; exact source assumptions apply. |
| [MAISO11AuditPass](historical/MAIS-O11-certificates/projects/MAISO11AuditPass/README.md) | [FirstPass.lean](historical/MAIS-O11-certificates/projects/MAISO11AuditPass/FirstPass.lean), [AuditPass.lean](historical/MAIS-O11-certificates/projects/MAISO11AuditPass/AuditPass.lean), [Audit.lean](historical/MAIS-O11-certificates/projects/MAISO11AuditPass/Audit.lean) | Internal Löb logic and quantitative conditional conversion. Fresh build/Audit.lean pass; exact source assumptions apply. |
| [MAISO11TaggedPass](historical/MAIS-O11-certificates/projects/MAISO11TaggedPass/README.md) | [TaggedSyntax.lean](historical/MAIS-O11-certificates/projects/MAISO11TaggedPass/TaggedSyntax.lean), [TaggedBounds.lean](historical/MAIS-O11-certificates/projects/MAISO11TaggedPass/TaggedBounds.lean), [Audit.lean](historical/MAIS-O11-certificates/projects/MAISO11TaggedPass/Audit.lean) | Tagged syntax, guard fragments, and numerical gaps; corrected guard transfer. Fresh build/Audit.lean pass; exact source assumptions apply. |
| [MAISO11QuotationPass](historical/MAIS-O11-certificates/projects/MAISO11QuotationPass/README.md) | [StringQuotation.lean](historical/MAIS-O11-certificates/projects/MAISO11QuotationPass/StringQuotation.lean), [QuotationWire.lean](historical/MAIS-O11-certificates/projects/MAISO11QuotationPass/QuotationWire.lean), [LocalCertificates.lean](historical/MAIS-O11-certificates/projects/MAISO11QuotationPass/LocalCertificates.lean), [ArithmeticTrace.lean](historical/MAIS-O11-certificates/projects/MAISO11QuotationPass/ArithmeticTrace.lean), [TracePacking.lean](historical/MAIS-O11-certificates/projects/MAISO11QuotationPass/TracePacking.lean), [Examples.lean](historical/MAIS-O11-certificates/projects/MAISO11QuotationPass/Examples.lean), [Demo.lean](historical/MAIS-O11-certificates/projects/MAISO11QuotationPass/Demo.lean), [Audit.lean](historical/MAIS-O11-certificates/projects/MAISO11QuotationPass/Audit.lean) | Raw-fragment quotation, restricted local certificates, packed traces. Fresh build/Audit.lean pass; exact source assumptions apply. |
| [MAISO11ObstructionPass](historical/MAIS-O11-certificates/projects/MAISO11ObstructionPass/README.md) | [SuffixAssembly.lean](historical/MAIS-O11-certificates/projects/MAISO11ObstructionPass/SuffixAssembly.lean), [ObstructionBounds.lean](historical/MAIS-O11-certificates/projects/MAISO11ObstructionPass/ObstructionBounds.lean), [FiniteDiagonalLogic.lean](historical/MAIS-O11-certificates/projects/MAISO11ObstructionPass/FiniteDiagonalLogic.lean), [Audit.lean](historical/MAIS-O11-certificates/projects/MAISO11ObstructionPass/Audit.lean) | Suffix assembly and abstract separation obstruction. Fresh build/Audit.lean pass; exact source assumptions apply. |
| [MAISO11EnvelopePass](historical/MAIS-O11-certificates/projects/MAISO11EnvelopePass/README.md) | [Envelope.lean](historical/MAIS-O11-certificates/projects/MAISO11EnvelopePass/Envelope.lean), [FiniteFiles.lean](historical/MAIS-O11-certificates/projects/MAISO11EnvelopePass/FiniteFiles.lean), [Audit.lean](historical/MAIS-O11-certificates/projects/MAISO11EnvelopePass/Audit.lean) | Sublinear envelope and affine consequences. Fresh build/Audit.lean pass; exact source assumptions apply. |

Each project also has its own [README.md](historical/MAIS-O11-certificates/projects/MAISO11FirstPass/README.md) pattern, SHA256SUMS and checked-output.txt under its project directory. The root [verified-build.txt](historical/MAIS-O11-certificates/verified-build.txt) is the original cumulative transcript; the fresh transcript is below. The bundle also contains its historical research-notes files: [MAIS-O11-PA-bin-continuation.md](historical/MAIS-O11-certificates/research-notes/MAIS-O11-PA-bin-continuation.md), [MAIS-O11-PA-bin-obstruction.md](historical/MAIS-O11-certificates/research-notes/MAIS-O11-PA-bin-obstruction.md), [MAIS-O11-PA-bin-quotation-milestone.md](historical/MAIS-O11-certificates/research-notes/MAIS-O11-PA-bin-quotation-milestone.md), [MAIS-O11-PA-bin-upper-bound-route.md](historical/MAIS-O11-certificates/research-notes/MAIS-O11-PA-bin-upper-bound-route.md), [MAIS-O11-envelope-theorem.md](historical/MAIS-O11-certificates/research-notes/MAIS-O11-envelope-theorem.md), [MAIS-O11-structural-audit.md](historical/MAIS-O11-certificates/research-notes/MAIS-O11-structural-audit.md), [MAIS-O11-tagged-checker-witness.md](historical/MAIS-O11-certificates/research-notes/MAIS-O11-tagged-checker-witness.md), [open-problems__MAIS-O10.md](historical/MAIS-O11-certificates/research-notes/open-problems__MAIS-O10.md), [open-problems__MAIS-O11.md](historical/MAIS-O11-certificates/research-notes/open-problems__MAIS-O11.md).

## Current Lean 4.19.0 source files

There are 49 .lean files. Forty are registered library targets and built together; two are executable roots and built separately; six standalone demo modules elaborated separately; SummaryFiniteCheck.lean elaborated separately. “Checked” means Lean accepted the encoded statements, not that ordinary PA-bin has been formalized. [Build evidence](#build-transcripts-and-checksums).

| File | Purpose | Fresh check |
| --- | --- | --- |
| [ArithmeticTrace.lean](source/MAISO11SharedConversePass/ArithmeticTrace.lean) | typed local arithmetic recurrence checker | Library built; scope limited to file model. |
| [BarrierDemo.lean](source/MAISO11SharedConversePass/BarrierDemo.lean) | executable expansion-size examples | Standalone elaborated; scope limited to file model. |
| [CheckFile.lean](source/MAISO11SharedConversePass/CheckFile.lean) | restricted proof-file command-line checker | Executable built; scope limited to file model. |
| [CheckerDemo.lean](source/MAISO11SharedConversePass/CheckerDemo.lean) | restricted checker examples and dependency audit | Standalone elaborated; scope limited to file model. |
| [ChosenSystemExpansion.lean](source/MAISO11SharedConversePass/ChosenSystemExpansion.lean) | tagged alphabet, identifiers, serialized expansion bound | Library built; scope limited to file model. |
| [ChosenSystemInterleaving.lean](source/MAISO11SharedConversePass/ChosenSystemInterleaving.lean) | abstract interleaved definitions/output and cost bound | Library built; scope limited to file model. |
| [ChosenSystemSerialization.lean](source/MAISO11SharedConversePass/ChosenSystemSerialization.lean) | tagged grammar-plus-root parser round trips | Library built; scope limited to file model. |
| [CodedScan.lean](source/MAISO11SharedConversePass/CodedScan.lean) | semantic arithmetic decoder bridge for auxiliary coding | Library built; scope limited to file model. |
| [CompactChecker.lean](source/MAISO11SharedConversePass/CompactChecker.lean) | restricted axiom and MP checker | Library built; scope limited to file model. |
| [CompactEquality.lean](source/MAISO11SharedConversePass/CompactEquality.lean) | formula and MP equality interface | Library built; scope limited to file model. |
| [CompactParser.lean](source/MAISO11SharedConversePass/CompactParser.lean) | compact syntax and record parser with round trips | Library built; scope limited to file model. |
| [CompactProof.lean](source/MAISO11SharedConversePass/CompactProof.lean) | restricted Hilbert proof relation and soundness | Library built; scope limited to file model. |
| [CompactWire.lean](source/MAISO11SharedConversePass/CompactWire.lean) | closed-term references and wire record grammar | Library built; scope limited to file model. |
| [CompositionBarrier.lean](source/MAISO11SharedConversePass/CompositionBarrier.lean) | quadratic trailer versus constant MP numerical obstruction | Library built; scope limited to file model. |
| [CompressionBarrier.lean](source/MAISO11SharedConversePass/CompressionBarrier.lean) | expanded-tree size accounting | Library built; scope limited to file model. |
| [DagDemo.lean](source/MAISO11SharedConversePass/DagDemo.lean) | shared graph equality examples | Standalone elaborated; scope limited to file model. |
| [DagEquality.lean](source/MAISO11SharedConversePass/DagEquality.lean) | acyclic graph equality table | Library built; scope limited to file model. |
| [Demo.lean](source/MAISO11SharedConversePass/Demo.lean) | quotation executable | Executable built; scope limited to file model. |
| [Examples.lean](source/MAISO11SharedConversePass/Examples.lean) | cross-boundary raw-fragment examples | Library built; scope limited to file model. |
| [ExportExamples.lean](source/MAISO11SharedConversePass/ExportExamples.lean) | example proof-file exporter | Standalone elaborated; scope limited to file model. |
| [FragmentBalance.lean](source/MAISO11SharedConversePass/FragmentBalance.lean) | compositional and cached parenthesis summaries | Library built; scope limited to file model. |
| [FragmentFamily.lean](source/MAISO11SharedConversePass/FragmentFamily.lean) | short fragment grammar for exponential-depth unary word | Library built; scope limited to file model. |
| [FragmentPrefix.lean](source/MAISO11SharedConversePass/FragmentPrefix.lean) | cached prefix summary queries and visit counts | Library built; scope limited to file model. |
| [FragmentRange.lean](source/MAISO11SharedConversePass/FragmentRange.lean) | direct interval summaries | Library built; scope limited to file model. |
| [GrammarLengthBound.lean](source/MAISO11SharedConversePass/GrammarLengthBound.lean) | expansion length and cached numeric payload bounds | Library built; scope limited to file model. |
| [GraphCompiler.lean](source/MAISO11SharedConversePass/GraphCompiler.lean) | compile restricted shared term definitions to graph | Library built; scope limited to file model. |
| [GraphDepthBarrier.lean](source/MAISO11SharedConversePass/GraphDepthBarrier.lean) | ordinary constructor graph depth lower bound | Library built; scope limited to file model. |
| [GraphFileChecker.lean](source/MAISO11SharedConversePass/GraphFileChecker.lean) | shared graph checks in restricted file checker | Library built; scope limited to file model. |
| [GraphFileCheckerInst.lean](source/MAISO11SharedConversePass/GraphFileCheckerInst.lean) | hidden-witness instantiation integration | Library built; scope limited to file model. |
| [GraphSubterms.lean](source/MAISO11SharedConversePass/GraphSubterms.lean) | subterm enumeration within shared graph | Library built; scope limited to file model. |
| [InstantiationGraph.lean](source/MAISO11SharedConversePass/InstantiationGraph.lean) | binder-aware compact instantiation candidates | Library built; scope limited to file model. |
| [LocalCertificates.lean](source/MAISO11SharedConversePass/LocalCertificates.lean) | restricted local equality proof certificates | Library built; scope limited to file model. |
| [OpenGraph.lean](source/MAISO11SharedConversePass/OpenGraph.lean) | binder-depth graph comparison infrastructure | Library built; scope limited to file model. |
| [PAFormula.lean](source/MAISO11SharedConversePass/PAFormula.lean) | first-order arithmetic syntax and small Hilbert fragment | Library built; scope limited to file model. |
| [PadBounds.lean](source/MAISO11SharedConversePass/PadBounds.lean) | quadratic padding asymptotic inequality | Library built; scope limited to file model. |
| [PairingGraph.lean](source/MAISO11SharedConversePass/PairingGraph.lean) | pairing/coding lemmas for graph representation | Library built; scope limited to file model. |
| [ParserDemo.lean](source/MAISO11SharedConversePass/ParserDemo.lean) | parser executable examples | Standalone elaborated; scope limited to file model. |
| [QuotationWire.lean](source/MAISO11SharedConversePass/QuotationWire.lean) | finite-alphabet quotation and character bounds | Library built; scope limited to file model. |
| [SharedConverse.lean](source/MAISO11SharedConversePass/SharedConverse.lean) | reference/shared parser equivalence | Library built; scope limited to file model. |
| [SharedConverseDemo.lean](source/MAISO11SharedConversePass/SharedConverseDemo.lean) | whole-file agreement examples and axiom audit | Library built; scope limited to file model. |
| [SharedMPDemo.lean](source/MAISO11SharedConversePass/SharedMPDemo.lean) | compact MP comparison examples | Standalone elaborated; scope limited to file model. |
| [SharedOracle.lean](source/MAISO11SharedConversePass/SharedOracle.lean) | shared equality and selected axiom shortcuts | Library built; scope limited to file model. |
| [SharedOracleDemo.lean](source/MAISO11SharedConversePass/SharedOracleDemo.lean) | graph/axiom examples and dependency reports | Library built; scope limited to file model. |
| [SharedPrelude.lean](source/MAISO11SharedConversePass/SharedPrelude.lean) | closed-term definition-prelude parser | Library built; scope limited to file model. |
| [SharedPreludeDemo.lean](source/MAISO11SharedConversePass/SharedPreludeDemo.lean) | prelude agreement and character examples | Library built; scope limited to file model. |
| [SpecTransfer.lean](source/MAISO11SharedConversePass/SpecTransfer.lean) | abstract superlinear-overhead to Part 1 transfer | Library built; scope limited to file model. |
| [StringQuotation.lean](source/MAISO11SharedConversePass/StringQuotation.lean) | arbitrary string-fragment grammar and arithmetic quotation | Library built; scope limited to file model. |
| [SummaryFiniteCheck.lean](source/MAISO11SharedConversePass/SummaryFiniteCheck.lean) | one generated 204-rule, 407-join finite example | Finite instance elaborated; scope limited to file model. |
| [TracePacking.lean](source/MAISO11SharedConversePass/TracePacking.lean) | compact encoding of witness traces | Library built; scope limited to file model. |

## Current research notes and audit files

Every note below is research prose, not a new Lean theorem. Several preserve earlier “pending” status; current checks are in STATUS.md.

| Note | Purpose |
| --- | --- |
| [CHECKER-NOTE.md](source/MAISO11SharedConversePass/CHECKER-NOTE.md) | restricted executable checker and scope |
| [CHOSEN-SYSTEM-PART1-AUDIT.md](source/MAISO11SharedConversePass/CHOSEN-SYSTEM-PART1-AUDIT.md) | chosen-system caveats and withdrawn transfer |
| [CHOSEN-SYSTEM-PART1-ROBUST-LEDGER.md](source/MAISO11SharedConversePass/CHOSEN-SYSTEM-PART1-ROBUST-LEDGER.md) | conditional guarded-verifier size ledger and formal gaps |
| [COMPRESSED-TAUTOLOGY-CIRCUIT-ROUTE.md](source/MAISO11SharedConversePass/COMPRESSED-TAUTOLOGY-CIRCUIT-ROUTE.md) | unproved symbolic evaluator and PA certificate route |
| [COMPRESSION-NOTE.md](source/MAISO11SharedConversePass/COMPRESSION-NOTE.md) | compression barrier and remaining target |
| [CONTINUATION-NOTE.md](source/MAISO11SharedConversePass/CONTINUATION-NOTE.md) | compact MP, padding loophole, composition failure |
| [CONVERSE-NOTE.md](source/MAISO11SharedConversePass/CONVERSE-NOTE.md) | parser/shared graph milestone and limitations |
| [CURRENT-STATUS.md](source/MAISO11SharedConversePass/CURRENT-STATUS.md) | old status snapshot; fresh build statements supersede it |
| [INTERNALIZATION-SECOND-AUDIT.md](source/MAISO11SharedConversePass/INTERNALIZATION-SECOND-AUDIT.md) | DAG obstruction and full-axiom checker issue |
| [INTERNALIZATION-THIRD-AUDIT.md](source/MAISO11SharedConversePass/INTERNALIZATION-THIRD-AUDIT.md) | cache/prefix/PA internalization audit |
| [LOB-INTERNALIZATION-REDIRECT.md](source/MAISO11SharedConversePass/LOB-INTERNALIZATION-REDIRECT.md) | specific Löb proof rather than global compiler |
| [NAVIGATION-MILESTONE.md](source/MAISO11SharedConversePass/NAVIGATION-MILESTONE.md) | mathematical matching-delimiter plan and Python audit |
| [PA-ARITHMETIC-MILESTONE.md](source/MAISO11SharedConversePass/PA-ARITHMETIC-MILESTONE.md) | experimental local arithmetic proof objects |
| [PA-BIN-THIRD-AUDIT.md](source/MAISO11SharedConversePass/PA-BIN-THIRD-AUDIT.md) | compressed intermediate tautology counterexample to expansion approach |
| [PA-FINITE-ASSEMBLY-MILESTONE.md](source/MAISO11SharedConversePass/PA-FINITE-ASSEMBLY-MILESTONE.md) | one finite conjunction of local summary claims |
| [PART1-ADVERSARIAL-NOTE.md](source/MAISO11SharedConversePass/PART1-ADVERSARIAL-NOTE.md) | padding and finite-Gödel candidate objections |
| [PART2-ADVERSARIAL-NOTE.md](source/MAISO11SharedConversePass/PART2-ADVERSARIAL-NOTE.md) | extensional Δ₁ Bew failure of Löb |
| [PRELUDE-NOTE.md](source/MAISO11SharedConversePass/PRELUDE-NOTE.md) | restricted definition-prelude parser |
| [QUOTATION-HOMOMORPHISM-AUDIT.md](source/MAISO11SharedConversePass/QUOTATION-HOMOMORPHISM-AUDIT.md) | conditional exact numeral grammar under 2-power alphabet |
| [RANGE-NOTE.md](source/MAISO11SharedConversePass/RANGE-NOTE.md) | interval summary source proof; older pending-build note |
| [README.md](source/MAISO11SharedConversePass/README.md) | old current-project overview and commands |
| [RESEARCH-NOTE.md](source/MAISO11SharedConversePass/RESEARCH-NOTE.md) | shared arithmetic term equality result |
| [RESTORE-DATA.md](source/MAISO11SharedConversePass/RESTORE-DATA.md) | reconstruct saved finite JSON proof object from gzip |
| [SHARED-COMPILER-AUDIT.md](source/MAISO11SharedConversePass/SHARED-COMPILER-AUDIT.md) | raw fragment to tree-DAG size obstruction |
| [SPEC-AUDIT.md](source/MAISO11SharedConversePass/SPEC-AUDIT.md) | comparison of restricted implementation and agenda |
| [SPEC-SECOND-AUDIT.md](source/MAISO11SharedConversePass/SPEC-SECOND-AUDIT.md) | conditional overhead-to-witness transfer |
| [SYMBOLIC-EXPANSION-MILESTONE.md](source/MAISO11SharedConversePass/SYMBOLIC-EXPANSION-MILESTONE.md) | mathematical existential expansion-table coding |
| [TAUTOLOGY-ADVERSARIAL-NOTE.md](source/MAISO11SharedConversePass/TAUTOLOGY-ADVERSARIAL-NOTE.md) | valid tautology axiom and gate lemma |
| [UNIFORM-SCAN-AUDIT.md](source/MAISO11SharedConversePass/UNIFORM-SCAN-AUDIT.md) | mathematical scan induction; no PA derivation |

Additional independent/duplicate audit snapshots were created at research root:

| File | Purpose/status |
| --- | --- |
| [INTERNALIZATION-SECOND-AUDIT.md](historical/research-audits/INTERNALIZATION-SECOND-AUDIT.md) | Separate research or independent audit; prose, not a Lean certificate. |
| [INTERNALIZATION-THIRD-AUDIT.md](historical/research-audits/INTERNALIZATION-THIRD-AUDIT.md) | Separate research or independent audit; prose, not a Lean certificate. |
| [PA-BIN-THIRD-AUDIT.md](historical/research-audits/PA-BIN-THIRD-AUDIT.md) | Separate research or independent audit; prose, not a Lean certificate. |
| [PART1-ADVERSARIAL-NOTE.md](historical/research-audits/PART1-ADVERSARIAL-NOTE.md) | Separate research or independent audit; prose, not a Lean certificate. |
| [PART2-ADVERSARIAL-NOTE.md](historical/research-audits/PART2-ADVERSARIAL-NOTE.md) | Separate research or independent audit; prose, not a Lean certificate. |
| [QUOTATION-HOMOMORPHISM-AUDIT.md](historical/research-audits/QUOTATION-HOMOMORPHISM-AUDIT.md) | Separate research or independent audit; prose, not a Lean certificate. |
| [RANGE-NOTE.md](historical/research-audits/RANGE-NOTE.md) | Separate research or independent audit; prose, not a Lean certificate. |
| [SHARED-COMPILER-AUDIT.md](historical/research-audits/SHARED-COMPILER-AUDIT.md) | Separate research or independent audit; prose, not a Lean certificate. |
| [SPEC-AUDIT.md](historical/research-audits/SPEC-AUDIT.md) | Separate research or independent audit; prose, not a Lean certificate. |
| [SPEC-SECOND-AUDIT.md](historical/research-audits/SPEC-SECOND-AUDIT.md) | Separate research or independent audit; prose, not a Lean certificate. |
| [TAUTOLOGY-ADVERSARIAL-NOTE.md](historical/research-audits/TAUTOLOGY-ADVERSARIAL-NOTE.md) | Separate research or independent audit; prose, not a Lean certificate. |
| [UNIFORM-SCAN-AUDIT.md](historical/research-audits/UNIFORM-SCAN-AUDIT.md) | Separate research or independent audit; prose, not a Lean certificate. |
| [UNIFORM-SCAN-INDEPENDENT-AUDIT.md](historical/research-audits/UNIFORM-SCAN-INDEPENDENT-AUDIT.md) | Separate research or independent audit; prose, not a Lean certificate. |

Workspace aggregate outputs preserved: [MAIS-O11-chosen-system-structural-audit.md](historical/workspace-output/MAIS-O11-chosen-system-structural-audit.md), [MAIS-O11-shared-graph-checkpoint.md](historical/workspace-output/MAIS-O11-shared-graph-checkpoint.md). They duplicate and aggregate older notes; current STATUS.md prevails.

## Supporting files, proof objects, build transcripts, and checksums

| File | Purpose / evidence |
| --- | --- |
| [NAVIGATION-AUDIT-OUTPUT.txt](source/MAISO11SharedConversePass/NAVIGATION-AUDIT-OUTPUT.txt) | Python navigation transcript. |
| [PA-AGGREGATE-REPLAY-OUTPUT.txt](source/MAISO11SharedConversePass/PA-AGGREGATE-REPLAY-OUTPUT.txt) | Python finite aggregate replay transcript. |
| [PA-ARITHMETIC-AUDIT-OUTPUT.txt](source/MAISO11SharedConversePass/PA-ARITHMETIC-AUDIT-OUTPUT.txt) | local arithmetic audit transcript. |
| [PACKED-TABLE-AUDIT-OUTPUT.txt](source/MAISO11SharedConversePass/PACKED-TABLE-AUDIT-OUTPUT.txt) | Python packed-table transcript. |
| [SHA256SUMS](source/MAISO11SharedConversePass/SHA256SUMS) | fresh hash manifest for this source snapshot. |
| [SHA256SUMS.legacy](source/MAISO11SharedConversePass/SHA256SUMS.legacy) | prior manifest; six mismatches after later edits. |
| [SUMMARY-LEAN-EXPORT-OUTPUT.txt](source/MAISO11SharedConversePass/SUMMARY-LEAN-EXPORT-OUTPUT.txt) | finite Lean exporter transcript. |
| [VERIFIED-OUTPUT.txt](source/MAISO11SharedConversePass/VERIFIED-OUTPUT.txt) | older recorded certificate output. |
| [archive-build-audit-2026-09-28.txt](source/MAISO11SharedConversePass/archive-build-audit-2026-09-28.txt) | fresh build of 40 registered libraries. |
| [archive-exe-build-2026-09-28.txt](source/MAISO11SharedConversePass/archive-exe-build-2026-09-28.txt) | fresh build of two executable targets. |
| [archive-finite-check-2026-09-28.txt](source/MAISO11SharedConversePass/archive-finite-check-2026-09-28.txt) | fresh elaboration of generated finite instance. |
| [archive-standalone-audit-2026-09-28.txt](source/MAISO11SharedConversePass/archive-standalone-audit-2026-09-28.txt) | fresh elaboration of six other demo modules. |
| [boundary-quotation-with-trace.pabin](source/MAISO11SharedConversePass/boundary-quotation-with-trace.pabin) | example with trace. |
| [boundary-quotation.pabin](source/MAISO11SharedConversePass/boundary-quotation.pabin) | example restricted proof file. |
| [check_fragment_navigation.py](source/MAISO11SharedConversePass/check_fragment_navigation.py) | independent prefix/range/matching examples. |
| [check_local_file.py](source/MAISO11SharedConversePass/check_local_file.py) | restricted proof-file example checker. |
| [emit_summary_lean.py](source/MAISO11SharedConversePass/emit_summary_lean.py) | generate one finite Lean summary instance. |
| [examples/invalid-mp.pabin](source/MAISO11SharedConversePass/examples/invalid-mp.pabin) | invalid restricted checker example. |
| [examples/reflexivity.pabin](source/MAISO11SharedConversePass/examples/reflexivity.pabin) | valid restricted checker example. |
| [lake-manifest.json](source/MAISO11SharedConversePass/lake-manifest.json) | Lake dependency manifest. |
| [lakefile.toml](source/MAISO11SharedConversePass/lakefile.toml) | Lean project targets and build configuration. |
| [lean-toolchain](source/MAISO11SharedConversePass/lean-toolchain) | Lean 4.19.0 pin. |
| [pa_eq_kernel.py](source/MAISO11SharedConversePass/pa_eq_kernel.py) | experimental PA-admissible equality calculus. |
| [pa_summary_certificate.py](source/MAISO11SharedConversePass/pa_summary_certificate.py) | create local summary proof objects. |
| [pa_summary_replay.py](source/MAISO11SharedConversePass/pa_summary_replay.py) | replay saved local proof-object JSON. |
| [packed_summary_tables.py](source/MAISO11SharedConversePass/packed_summary_tables.py) | finite-sequence coding and round-trip audit. |
| [summary-arithmetic-demo.json.gz](source/MAISO11SharedConversePass/summary-arithmetic-demo.json.gz) | compressed saved 204-rule/407-join local certificate; see RESTORE-DATA.md. |
| [verify_boundary.py](source/MAISO11SharedConversePass/verify_boundary.py) | quotation boundary examples. |

### Build transcripts and checksums

- [Fresh six-project verification](historical/MAIS-O11-certificates/archive-six-projects-build-2026-09-28.txt): exit 0; all six build and Audit.lean passes. Original [verified-build.txt](historical/MAIS-O11-certificates/verified-build.txt) and six project-specific checked-output.txt files are preserved above.
- [Current 40-library audit](source/MAISO11SharedConversePass/archive-build-audit-2026-09-28.txt): exit 0. This contains selected #print axioms reports, including chosen-system, fragment, and graph theorems.
- [Two executable targets](source/MAISO11SharedConversePass/archive-exe-build-2026-09-28.txt): exit 0.
- [Six standalone demos](source/MAISO11SharedConversePass/archive-standalone-audit-2026-09-28.txt): exit 0 for each.
- [Generated finite example](source/MAISO11SharedConversePass/archive-finite-check-2026-09-28.txt): exit 0 with no diagnostic output; this is one instance.
- [Historical cumulative SHA256SUMS](historical/MAIS-O11-certificates/SHA256SUMS) passed a fresh sha256sum -c against the original extracted bundle. Each of its six project folders has its own SHA256SUMS.
- [Current source SHA256SUMS](source/MAISO11SharedConversePass/SHA256SUMS) is regenerated for this snapshot. [SHA256SUMS.legacy](source/MAISO11SharedConversePass/SHA256SUMS.legacy) is the old current-project manifest; six entries failed after subsequent edits (CHOSEN-SYSTEM-PART1-AUDIT.md, CHOSEN-SYSTEM-PART1-ROBUST-LEDGER.md, CURRENT-STATUS.md, ChosenSystemExpansion.lean, README.md, lakefile.toml).
- [Whole archive ARCHIVE-SHA256SUMS](ARCHIVE-SHA256SUMS) covers this published snapshot. Hashes identify bytes, not mathematical truth.

## Dated historical checkpoint notes

The following 20 exact historical note versions were copied into [historical/checkpoint-notes](historical/checkpoint-notes/). Their timestamps are artifact creation dates, not measured work hours. Some overlap the six-project research-notes or current project.

| Date (UTC) | Note | Purpose/status |
| --- | --- | --- |
| 2026-09-27 | [CHOSEN-SYSTEM-PART1-ROBUST-LEDGER-2026-09-27.md](historical/checkpoint-notes/CHOSEN-SYSTEM-PART1-ROBUST-LEDGER-2026-09-27.md) | MAIS-O11 Part 1: robust size ledger for the chosen-system branch; historical scope. |
| 2026-09-24 | [RESEARCH-NOTE-2026-09-24.md](historical/checkpoint-notes/RESEARCH-NOTE-2026-09-24.md) | MAIS-O11 PA-bin parser checkpoint (24 September 2026); historical scope. |
| 2026-09-22 | [MAIS-O11-PA-bin-continuation.md](historical/checkpoint-notes/MAIS-O11-PA-bin-continuation.md) | MAIS-O11: continuation toward the fixed PA-bin problem; historical scope. |
| 2026-09-22 | [MAIS-O11-PA-bin-quotation-milestone.md](historical/checkpoint-notes/MAIS-O11-PA-bin-quotation-milestone.md) | PA-bin: polynomial quotation and a checked arithmetic trace; historical scope. |
| 2026-09-22 | [MAIS-O11-PA-bin-upper-bound-route.md](historical/checkpoint-notes/MAIS-O11-PA-bin-upper-bound-route.md) | Returning to PA-bin: a focused upper-bound route; historical scope. |
| 2026-09-22 | [MAIS-O11-tagged-checker-witness.md](historical/checkpoint-notes/MAIS-O11-tagged-checker-witness.md) | MAIS-O11: a connective-tagged PA presentation; historical scope. |
| 2026-09-23 | [MAIS-O11-PA-bin-arithmetic-access.md](historical/checkpoint-notes/MAIS-O11-PA-bin-arithmetic-access.md) | MAIS-O11: object-language trace access; historical scope. |
| 2026-09-23 | [MAIS-O11-PA-bin-compact-wire.md](historical/checkpoint-notes/MAIS-O11-PA-bin-compact-wire.md) | MAIS-O11: compact trace conclusions and proof-record accounting; historical scope. |
| 2026-09-23 | [MAIS-O11-PA-bin-complete-trace-proof.md](historical/checkpoint-notes/MAIS-O11-PA-bin-complete-trace-proof.md) | MAIS-O11: complete compact trace proofs with polynomial character bounds; historical scope. |
| 2026-09-23 | [MAIS-O11-PA-bin-obstruction.md](historical/checkpoint-notes/MAIS-O11-PA-bin-obstruction.md) | MAIS-O11: an obstruction to the current PA-bin witness; historical scope. |
| 2026-09-23 | [MAIS-O11-envelope-theorem.md](historical/checkpoint-notes/MAIS-O11-envelope-theorem.md) | Checkpoint; historical scope. |
| 2026-09-23 | [MAIS-O11-structural-audit.md](historical/checkpoint-notes/MAIS-O11-structural-audit.md) | Checkpoint; historical scope. |
| 2026-09-24 | [MAIS-O11-PA-bin-checker-note.md](historical/checkpoint-notes/MAIS-O11-PA-bin-checker-note.md) | MAIS-O11: executable checker milestone; historical scope. |
| 2026-09-24 | [MAIS-O11-expansion-audit.md](historical/checkpoint-notes/MAIS-O11-expansion-audit.md) | MAIS-O11: audit of the remaining gap and an expansion barrier; historical scope. |
| 2026-09-24 | [MAIS-O11-part-two-strategy.md](historical/checkpoint-notes/MAIS-O11-part-two-strategy.md) | MAIS-O11: choosing part 2 and connecting the two questions; historical scope. |
| 2026-09-24 | [MAIS-O11-shared-equality-note.md](historical/checkpoint-notes/MAIS-O11-shared-equality-note.md) | MAIS-O11: certified equality for shared arithmetic terms; historical scope. |
| 2026-09-25 | [MAIS-O11-compact-MP-and-padding-audit.md](historical/checkpoint-notes/MAIS-O11-compact-MP-and-padding-audit.md) | MAIS-O11 continuation: compact modus ponens and the padding obstruction; historical scope. |
| 2026-09-25 | [MAIS-O11-compact-decoder-equivalence.md](historical/checkpoint-notes/MAIS-O11-compact-decoder-equivalence.md) | MAIS-O11: exact equivalence of compact and expanding file decoders; historical scope. |
| 2026-09-25 | [MAIS-O11-shared-graph-checkpoint.md](historical/checkpoint-notes/MAIS-O11-shared-graph-checkpoint.md) | Current certificate status — 27 September 2026; historical scope. |
| 2026-09-25 | [MAIS-O11-shared-prelude-checkpoint.md](historical/checkpoint-notes/MAIS-O11-shared-prelude-checkpoint.md) | MAIS-O11: shared parsing of the PA-bin definition prelude; historical scope. |

## ZIP archives and other historical deliverables

The following exact filenames are in the user’s ChatGPT Library. The newest expanded source and six early projects are mirrored in this repository. The other ZIPs are incremental snapshots; their existence does not add a current proof claim. Their Library files may need separate access in a future session. Local copies of three checkpoint ZIPs were also observed in the scratch workspace, with distinct SHA-256 values listed below.

| Created (UTC) | Library artifact | Purpose / status |
| --- | --- | --- |
| 2026-09-22 | MAIS-O11-first-pass.zip | FirstPass source snapshot; conditional; original Library artifact, not a final PA-bin certificate. |
| 2026-09-22 | MAIS-O11-PA-bin-audit.zip | abstract PA-bin audit snapshot; original Library artifact, not a final PA-bin certificate. |
| 2026-09-22 | MAIS-O11-tagged-checker.zip | tagged variant; guard transfer later corrected; original Library artifact, not a final PA-bin certificate. |
| 2026-09-22 | MAIS-O11-PA-bin-quotation.zip | quotation checkpoint; original Library artifact, not a final PA-bin certificate. |
| 2026-09-23 | MAIS-O11-PA-bin-obstruction.zip | obstruction checkpoint; original Library artifact, not a final PA-bin certificate. |
| 2026-09-23 | MAIS-O11-envelope-certificate.zip | envelope checkpoint; original Library artifact, not a final PA-bin certificate. |
| 2026-09-23 | MAIS-O11-certificates.zip | cumulative six-project tree, expanded here; original Library artifact, not a final PA-bin certificate. |
| 2026-09-23 | MAIS-O11-PA-bin-arithmetic-access.zip | arithmetic syntax checkpoint; original Library artifact, not a final PA-bin certificate. |
| 2026-09-23 | MAIS-O11-PA-bin-compact-wire.zip | compact wire checkpoint; original Library artifact, not a final PA-bin certificate. |
| 2026-09-23 | MAIS-O11-PA-bin-complete-trace-proof.zip | restricted complete-trace checker checkpoint; original Library artifact, not a final PA-bin certificate. |
| 2026-09-24 | MAIS-O11-PA-bin-parser-checkpoint.zip | parser checkpoint; original Library artifact, not a final PA-bin certificate. |
| 2026-09-24 | MAIS-O11-PA-bin-checker-checkpoint.zip | checker checkpoint; original Library artifact, not a final PA-bin certificate. |
| 2026-09-24 | MAIS-O11-compression-audit.zip | compression audit snapshot; original Library artifact, not a final PA-bin certificate. |
| 2026-09-24 | MAIS-O11-lob-interface.zip | abstract Löb interface snapshot; original Library artifact, not a final PA-bin certificate. |
| 2026-09-24 | MAIS-O11-shared-equality.zip | shared equality snapshot; original Library artifact, not a final PA-bin certificate. |
| 2026-09-25 | MAISO11PaddingLoophole.zip | artificial padded system numerical example; original Library artifact, not a final PA-bin certificate. |
| 2026-09-25 | MAIS-O11-shared-MP-and-composition-certificate.zip | MP interface and padding obstruction; original Library artifact, not a final PA-bin certificate. |
| 2026-09-25 | MAIS-O11-shared-prelude-certificate.zip | restricted prelude parser; original Library artifact, not a final PA-bin certificate. |
| 2026-09-25 | MAIS-O11-compact-decoder-equivalence.zip | restricted decoder equivalence; original Library artifact, not a final PA-bin certificate. |
| 2026-09-25 | MAIS-O11-shared-graph-certificate.zip | shared graph snapshot from 25 September; original Library artifact, not a final PA-bin certificate. |

The following local copies were separately recovered and are not byte-identical just because their names are similar:
- cumulative six projects: recovered/library_artifacts/MAIS-O11-certificates.zip; SHA-256 0cda3be8fa541c3788d85efd63785391a2f4eabd27f9ba1fcfaaa8b1c8eeb552.
- shared graph, workspace output: output/MAIS-O11-shared-graph-certificate.zip; SHA-256 35b862786494bd54303eb15b37477498fb86450f240b5a35645689d4158ff499.
- shared graph, later download: downloads_latest/MAIS-O11-shared-graph-certificate.zip; SHA-256 33e5d4c86a244cd495dca279b18da56a93947b4ca5acd1b92fb42286cf3f14b8.
- compact decoder, recovered: recovered/MAIS-O11-compact-decoder-equivalence.zip; SHA-256 24e92c5c730472bc60c04d09460ff2ceb12c60f26662a582d2127c689478e9b5.

Other original Library items include [MAIS-O11-first-pass.sh](historical/MAIS-O11-first-pass.sh) (self-extracting early project), the dated RESEARCH-NOTE and robust-ledger versions in the checkpoint table, and the PDF/TeX pair already indexed above. The related uploaded MAIS-O1.md, MAIS-O10.md, MAIS-O12.md, MAIS-O13.md, MAIS-O14.md, MAIS-O15.md, MAIS-O18.md, and MAIS-O19.md are background agenda files, not results generated by this project; the primary O11/A1 copies are present under source/spec.

## Limits of completeness

This inventory covers all recoverable artifacts in the present workspace and the 2026-09-22–28 Library project inventory. It cannot reconstruct unrecorded private prompts, expired attachments beyond the recovered original specification, or undocumented earlier runs. The preserved source and build records make every affirmative verification claim above independently checkable; they do not close either ordinary PA-bin question.
