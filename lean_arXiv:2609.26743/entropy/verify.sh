#!/usr/bin/env bash
# Rebuild every local proof from source, then audit all of its declarations.
set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
repo_root="$(cd -- "$script_dir/../.." && pwd -P)"
physlib_commit=c76e3ccab04eacb69a126ca5c021b0788d513292
mathlib_commit=db584cd6d46c92f209a44c0f1c829460d327499d
# Lake puts absolute package paths in colon-separated LEAN_PATH on POSIX.
physlib_dir="${PHYSLIB_DIR:-$repo_root/build/arxiv-2609.26743/physlib}"
verification_dir="${VERIFICATION_DIR:-$script_dir/verification}"

for executable in git lake python3; do
  command -v "$executable" >/dev/null || {
    echo "Required executable not found: $executable" >&2
    exit 1
  }
done

physlib_dir="$(python3 -c 'from pathlib import Path; import sys; print(Path(sys.argv[1]).resolve())' "$physlib_dir")"
if [[ "$physlib_dir" == *:* ]]; then
  echo "PHYSLIB_DIR must resolve to a path without ':' for Lean's search path." >&2
  exit 1
fi
verification_dir="$(python3 -c 'from pathlib import Path; import sys; print(Path(sys.argv[1]).resolve())' "$verification_dir")"
mkdir -p -- "$verification_dir/generated"
exec > >(tee "$verification_dir/verification.log") 2>&1
trap 'verification_status=$?; printf "%s\n" "$verification_status" > "$verification_dir/exit_code.txt"' EXIT
rm -f -- "$verification_dir/verification_status.json" "$verification_dir/axiom_audit.log" \
  "$verification_dir/exit_code.txt"

# An inherited search path must not supply unrelated compiled proof modules.
unset LEAN_PATH LEAN_SRC_PATH
export ELAN_TOOLCHAIN="$(cat "$script_dir/lean-toolchain")"

python3 "$script_dir/scripts/proof_plan.py" plan "$script_dir" "$verification_dir/generated"
mapfile -t modules < "$verification_dir/generated/proof_modules.txt"
mapfile -t physlib_targets < "$verification_dir/generated/physlib_targets.txt"
if [[ ${#modules[@]} -eq 0 ]]; then
  echo "No proof modules selected." >&2
  exit 1
fi

if [[ ! -e "$physlib_dir" ]]; then
  mkdir -p -- "$(dirname -- "$physlib_dir")"
  git clone --no-checkout https://github.com/leanprover-community/physlib.git "$physlib_dir"
  git -C "$physlib_dir" checkout --detach "$physlib_commit"
fi

actual_commit="$(git -C "$physlib_dir" rev-parse HEAD)"
if [[ "$actual_commit" != "$physlib_commit" ]]; then
  echo "Expected Physlib $physlib_commit; found $actual_commit." >&2
  exit 1
fi
cmp -- "$script_dir/lean-toolchain" "$physlib_dir/lean-toolchain"

if git -C "$physlib_dir" apply --check "$script_dir/upstream.patch" >/dev/null 2>&1; then
  git -C "$physlib_dir" apply "$script_dir/upstream.patch"
elif git -C "$physlib_dir" apply --reverse --check "$script_dir/upstream.patch" >/dev/null 2>&1; then
  echo "The pinned dependency patch is already applied."
else
  echo "The dependency patch does not apply cleanly to this checkout." >&2
  exit 1
fi

# Require the pinned source tree plus precisely the published patch. Git may
# choose different abbreviated object-name lengths, so ignore only index lines.
git -C "$physlib_dir" diff --no-ext-diff --no-textconv --binary -U3 \
  --src-prefix=a/ --dst-prefix=b/ HEAD -- > "$verification_dir/physlib.patch"
python3 - "$script_dir/upstream.patch" "$verification_dir/physlib.patch" <<'PY_PATCH'
from pathlib import Path
import sys
def normalized(path):
    return [line for line in Path(path).read_text().splitlines() if not line.startswith('index ')]
if normalized(sys.argv[1]) != normalized(sys.argv[2]):
    raise SystemExit('The Physlib checkout has tracked changes beyond upstream.patch.')
PY_PATCH

cd -- "$physlib_dir"
lean_version="$(lake env lean --version)"
if [[ "$lean_version" != "Lean (version 4.33.0,"* ]]; then
  echo "Expected Lean 4.33.0; found: $lean_version" >&2
  exit 1
fi
actual_mathlib_commit="$(git -C .lake/packages/mathlib rev-parse HEAD)"
if [[ "$actual_mathlib_commit" != "$mathlib_commit" ]]; then
  echo "Expected Mathlib $mathlib_commit; found $actual_mathlib_commit." >&2
  exit 1
fi
if ! git -C .lake/packages/mathlib diff --quiet HEAD --; then
  echo "The pinned Mathlib checkout has tracked source changes." >&2
  exit 1
fi
printf '%s\n' "$lean_version" "Physlib: $actual_commit" "Mathlib: $actual_mathlib_commit" \
  "Local proof modules: ${#modules[@]} (all rebuilt from source)" \
  > "$verification_dir/environment.txt"
cat "$verification_dir/environment.txt"

python3 "$script_dir/scripts/proof_plan.py" cache "$script_dir" "$physlib_dir" \
  > "$verification_dir/generated/cache_imports.txt"
if ! cmp -s "$script_dir/cache_imports.txt" "$verification_dir/generated/cache_imports.txt"; then
  echo "cache_imports.txt is stale. Regenerate it with:" >&2
  echo "python3 scripts/proof_plan.py cache . PATH_TO_PINNED_PHYSLIB > cache_imports.txt" >&2
  exit 1
fi
if [[ "${SKIP_CACHE_DOWNLOAD:-0}" == 1 ]]; then
  echo "Using existing standard dependency artifacts; every local proof is still rebuilt."
else
  mapfile -t cache_imports < "$script_dir/cache_imports.txt"
  lake --no-cache exe cache get "${cache_imports[@]}"
fi

# Physlib itself is built locally; its optional package artifact downloads are
# disabled. Only the explicit standard Mathlib cache download above is allowed.
if [[ ${#physlib_targets[@]} -gt 0 ]]; then
  lake --no-cache build "${physlib_targets[@]}"
fi

artifact_dir="$physlib_dir/.lake/build/lib/lean"
mkdir -p -- "$artifact_dir"
for module in "${modules[@]}"; do
  cp -- "$script_dir/$module.lean" "$physlib_dir/$module.lean"
  # Remove all previous local proof artifacts, including optional Lean sidecars.
  rm -f -- "$artifact_dir/$module.olean" "$artifact_dir/$module.olean.private" \
    "$artifact_dir/$module.olean.server" "$artifact_dir/$module.ilean"
done

for module in "${modules[@]}"; do
  echo "Checking $module.lean"
  proof_temp="$(mktemp -d "$artifact_dir/.verify-$module.XXXXXX")"
  if lake env lean -Dwarn.sorry=true -o "$proof_temp/$module.olean" "$module.lean"; then
    # Install the main import artifact last, only after a successful kernel check.
    for suffix in .olean.private .olean.server .ilean; do
      if [[ -f "$proof_temp/$module$suffix" ]]; then
        mv -- "$proof_temp/$module$suffix" "$artifact_dir/$module$suffix"
      fi
    done
    mv -- "$proof_temp/$module.olean" "$artifact_dir/$module.olean"
    rmdir -- "$proof_temp"
  else
    compile_status=$?
    rm -rf -- "$proof_temp"
    exit "$compile_status"
  fi
done

cp -- "$verification_dir/generated/SupplementAxiomAudit.lean" "$physlib_dir/SupplementAxiomAudit.lean"
lake env lean SupplementAxiomAudit.lean | tee "$verification_dir/axiom_audit.log"
python3 - "$verification_dir/axiom_audit.log" "$verification_dir/generated/source_manifest.json" \
  "$verification_dir/verification_status.json" "$script_dir" <<'PY_AUDIT'
from pathlib import Path
import hashlib
import json
import re
import sys
text = Path(sys.argv[1]).read_text()
matches = re.findall(r'^AXIOM_AUDIT_OK declarations=(\d+) modules=(\d+)$', text, re.M)
manifest = json.loads(Path(sys.argv[2]).read_text())
for filename, expected in manifest['sha256'].items():
    actual = hashlib.sha256((Path(sys.argv[4]) / filename).read_bytes()).hexdigest()
    if actual != expected:
        raise SystemExit(f'Proof source changed during verification: {filename}')
if len(matches) != 1 or int(matches[0][1]) != len(manifest['modules']):
    raise SystemExit('Missing or inconsistent aggregate axiom audit result.')
declarations, modules = map(int, matches[0])
if declarations < 1:
    raise SystemExit('The aggregate axiom audit contains no declarations.')
result = {
    'status': 'passed',
    'lean_version': '4.33.0',
    'physlib_commit': 'c76e3ccab04eacb69a126ca5c021b0788d513292',
    'mathlib_commit': 'db584cd6d46c92f209a44c0f1c829460d327499d',
    'all_local_modules_recompiled': True,
    'audited_declarations': declarations,
    'audited_modules': modules,
    'allowed_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
    'source_manifest': manifest,
}
Path(sys.argv[3]).write_text(json.dumps(result, indent=2) + '\n')
print(f'Aggregate audit passed: {declarations} declarations in {modules} modules; standard axioms only.')
PY_AUDIT

echo "Verification completed. Results: $verification_dir"
