# MAIS-O11 research log

**Status: open as of 2026-09-28.** Neither Part 1 nor Part 2 is settled for the intended ordinary PA-bin proof predicate. A separate guarded, slow-verifier proof system offers a **conditional** Part 1 candidate under the agenda's permissive “any efficient system” wording; its checker, fixed points, and PA derivations have not been certified end to end.

MAIS-O11 asks whether a proof of the reflection premise □P → P can be genuinely shorter than every proof of P, and whether the associated overhead function for ordinary PA-bin has a fixed polynomial bound. The original [problem statement](source/spec/MAIS-O11.md) and [agenda specification](source/spec/MAIS-A1.tex) are included here.

## Read the record

- [Project log](PROJECT-LOG.md): dated routes, corrections, and reconstructed prompt milestones.
- [Status](STATUS.md): checked theorems, conditional claims, obstructions, and exact open obligations.
- [Technical roadmap](TECHNICAL-ROADMAP.md): shortest current routes to a genuine result.
- [Artifacts](ARTIFACTS.md): every recoverable source, note, archive, manuscript, checksum, and transcript.
- [Handoff](HANDOFF.md): compact instructions for a future conversation.
- [Telemetry](telemetry.json): manually maintained fields; unknown quantities stay unknown.
- [Historical six-project certificates](historical/MAIS-O11-certificates/README.md) and [current Lean project](source/MAISO11SharedConversePass/README.md).

A fresh 2026-09-28 audit rebuilt all six historical Lean 4.19.0 projects and all 40 registered libraries in the current project. It also elaborated the one generated finite summary example. These checks establish the exact statements in their files, with their stated assumptions; they do **not** establish a PA-bin proof-length theorem. See the [build transcripts](ARTIFACTS.md#build-transcripts-and-checksums).

## How to use this archive

The [source directory](source/) is a research snapshot. Some older notes say a module is “pending” because they predate the fresh build. [STATUS.md](STATUS.md) is the current status authority. Historical drafts are preserved to show how claims were corrected; their existence does not endorse their earlier conclusions.

The [site landing page](index.html) reads the static [telemetry.json](telemetry.json) at load time and links to this log. On GitHub Pages it has the stable path /mais-o11/. The Markdown files remain directly readable in GitHub. Future updates should be dated in PROJECT-LOG.md, reflected in STATUS.md and telemetry.json, and accompanied by a new build record when a verification claim changes.

This repository is external project continuity. It does not extend ChatGPT's private memory automatically; a future assistant needs this URL or the files and must read the handoff.
