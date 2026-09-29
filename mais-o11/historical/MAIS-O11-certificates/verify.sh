#!/usr/bin/env bash
set -euo pipefail

bundle_root="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
if command -v lake >/dev/null 2>&1; then
  lake_bin="$(command -v lake)"
elif [[ -x "$HOME/.elan/bin/lake" ]]; then
  lake_bin="$HOME/.elan/bin/lake"
else
  printf '%s\n' 'Lake was not found. Install Lean through the VS Code Lean extension / Elan, then rerun this script.' >&2
  exit 1
fi

projects=(
  MAISO11FirstPass
  MAISO11AuditPass
  MAISO11TaggedPass
  MAISO11QuotationPass
  MAISO11ObstructionPass
  MAISO11EnvelopePass
)

for project in "${projects[@]}"; do
  printf '\nVerifying %s\n' "$project"
  (
    cd "$bundle_root/projects/$project"
    "$lake_bin" env lean --version
    "$lake_bin" build
    "$lake_bin" env lean -DwarningAsError=true Audit.lean
  )
done

printf '\n%s\n' 'All six Lean certificate projects passed.'
printf '%s\n' 'These checks certify the statements and hypotheses in the source; they do not resolve either PA-bin part of MAIS-O11.'
