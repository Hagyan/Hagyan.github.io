# MAIS-O11 — cumulative Lean certificates

Consolidated 23 September 2026. All six projects are pinned to Lean 4.19.0 and
use Core/Std only. No Mathlib or third-party Lean libraries are needed.

From this directory, run:

```bash
bash verify.sh
```

The script builds each project and executes its `Audit.lean`, with warnings
treated as errors. It exits at the first failure and prints the final success
message only if all six projects pass. Elan may download Lean 4.19.0 if that
toolchain is not yet installed. The script also looks for Lake in the standard
`$HOME/.elan/bin` directory when it is absent from PATH.

If the ZIP is in Downloads on a Mac, these commands extract to a fresh folder
and run the same verification without overwriting an earlier project:

```bash
mais_check_dir="$(mktemp -d "${TMPDIR:-/tmp}/mais-o11.XXXXXX")"
unzip -q "$HOME/Downloads/MAIS-O11-certificates.zip" -d "$mais_check_dir"
cd "$mais_check_dir/MAIS-O11-certificates"
bash verify.sh
```

## Projects and scope

| Project | Certified content |
|---|---|
| `MAISO11FirstPass` | Conditional finite-diagonal lower bound, abstract Löb rule, proof translation, separation subsequence, and divergence. The PA/checker hypotheses have not been instantiated. |
| `MAISO11AuditPass` | Internal Löb logic and a polynomial conversion from explicitly supplied quantitative operations; incompatibility with the first-pass gap hypotheses. |
| `MAISO11TaggedPass` | Concrete connective-tag syntax, substitution and guard invariants, expanded-trace checker facts, and conditional numerical consequences. Not the whole guarded PA construction. |
| `MAISO11QuotationPass` | Raw-string quotation, binary identifiers, local equality certificates, arithmetic traces, compact trace packing, and written-character bounds. Not full PA internalization. |
| `MAISO11ObstructionPass` | Serialized plain-suffix assembly, reference cost, explicit separation obstruction, and parameterized finite-diagonal logic. |
| `MAISO11EnvelopePass` | The exact sublinear-envelope characterization of absence of part 1 witnesses; affine overhead consequences; arbitrary-factor witnesses from failure of all joint linear bounds. |

Neither requested part is resolved for the intended ordinary PA-bin checker.
The report's structural implications do not assert their positive or negative
hypothesis for PA-bin.

The audited dependencies are among `propext`, `Quot.sound`, and
`Classical.choice`. An axiom audit is not a list of theorem hypotheses: inspect
the theorem type and the supplied interface structures. The `.lean` sources
contain no admitted proofs, custom axiom declarations, `native_decide`, or
unsafe declarations.

`verified-build.txt` records a fresh cumulative build with this runner. Each
project also retains its earlier `checked-output.txt`. The archive contains
source, not prebuilt `.olean` files, so your run performs a fresh kernel check.

## Optional quotation demo

From the archive root:

```bash
cd projects/MAISO11QuotationPass
lake exe quotationdemo
```

This generates small example files and reports the size of the large syntax
example. It does not evaluate the enormous expanded large code. See that
project's README for optional Python diagnostics, which are separate tests
and are not kernel proofs of the complete PA-bin checker.

## Research record

`research-notes/` preserves the milestone notes, uploaded problem conventions,
and the earlier slow-verifier PDF/TeX. The current companion
`MAIS-O11-progress-report.pdf` / `.tex` consolidate the status through the
envelope theorem. Earlier affirmative constructions concern a different
chosen presentation and were not fully formalized; the cumulative report
states that scope explicitly.

`SHA256SUMS` identifies every included file except the checksum list itself.
On macOS, it can be checked from this directory with:

```bash
shasum -a 256 -c SHA256SUMS
```
