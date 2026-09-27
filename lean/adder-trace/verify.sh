#!/usr/bin/env bash
set -euo pipefail
proof_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
cd -- "$proof_dir"
mkdir -p verification
exec > >(tee verification/current-build.log) 2>&1
trap 'proof_status=$?; printf "%s\n" "$proof_status" > verification/current-exit-code.txt' EXIT
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
lake env lean Audit.lean | tee verification/current-audit.log
echo "Adder trace verification completed."
