#!/usr/bin/env bash
set -euo pipefail
proof_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
repo_root="$(cd -- "$proof_dir/../.." && pwd -P)"
# Build outside the arXiv-labelled source folder: ':' separates LEAN_PATH entries.
build_dir="${ADDER_BUILD_DIR:-$repo_root/build/arxiv-2609.26743/adder-trace}"
build_dir="$(python3 -c 'from pathlib import Path; import sys; print(Path(sys.argv[1]).resolve())' "$build_dir")"
if [[ "$build_dir" == *:* ]]; then
  echo "ADDER_BUILD_DIR must resolve to a path without ':' for Lean's search path." >&2
  exit 1
fi
mkdir -p -- "$build_dir" "$proof_dir/verification"
cp -- "$proof_dir/"*.lean "$proof_dir/lakefile.toml" \
  "$proof_dir/lake-manifest.json" "$proof_dir/lean-toolchain" "$build_dir/"
cd -- "$build_dir"
exec > >(tee "$proof_dir/verification/current-build.log") 2>&1
trap 'proof_status=$?; printf "%s\n" "$proof_status" > "$proof_dir/verification/current-exit-code.txt"' EXIT
lake env lean --version
mapfile -t adder_imports < <(python3 - <<'PY'
from pathlib import Path
import re
imports = set()
for source in Path('.').glob('*.lean'):
    imports.update(re.findall(r'^import (Mathlib\.[A-Za-z0-9_.]+)', source.read_text(), re.M))
print('\n'.join(sorted(imports)))
PY
)
lake exe cache get "${adder_imports[@]}"
test "$(git -C .lake/packages/mathlib rev-parse HEAD)" = f897ebcf72cd16f89ab4577d0c826cd14afaafc7
# Recompile the local proof modules; dependency caches remain reusable.
lake clean addertrace
lake build
lake env lean Audit.lean | tee "$proof_dir/verification/current-audit.log"
echo "Adder trace verification completed."
