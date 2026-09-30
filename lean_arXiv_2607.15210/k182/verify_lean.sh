#!/usr/bin/env bash
# Run from any directory. Dependencies must first be fetched with lake update
# and lake exe cache get, using the pinned toolchain in the parent project.
set -euo pipefail
project_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_dir"
# Compile this certificate and its one project dependency from source.
# Mathlib is loaded from the pinned cache; unrelated paper modules are not built.
mkdir -p .lake/build/lib/lean
for module in PreliminariesLegendre K182Dual K182Numerics K182Entropy; do
  printf 'Checking %s.lean\n' "$module"
  lake env lean -o ".lake/build/lib/lean/$module.olean" "$module.lean"
done
lake env lean K182Audit.lean
