#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"

# Normal usage performs setup. --no-setup reuses installed pinned dependencies.
setup=1
require_complete=1
require_unconditional=0
for arg in "$@"; do
  case "$arg" in
    --no-setup) setup=0 ;;
    --require-complete) require_complete=1 ;;
    --require-unconditional) require_unconditional=1 ;;
    *) echo "Usage: $0 [--no-setup] [--require-complete] [--require-unconditional]" >&2; exit 2 ;;
  esac
done
command -v lake >/dev/null || { echo 'Install elan and add lake to PATH; see README.md.' >&2; exit 1; }
command -v python3 >/dev/null
if [[ "$setup" == 1 ]]; then
  lake update
  lake exe cache get
  python3 -m venv .venv
  .venv/bin/python -m pip install -r scripts/requirements.txt
fi
python=python3
if [[ -x .venv/bin/python ]]; then python=.venv/bin/python; fi
mkdir -p verification
printf 'running\n' > verification/exit_code.txt
trap 'code=$?; printf "%s\n" "$code" > verification/exit_code.txt' EXIT
"$python" scripts/verify_lean.py
"$python" scripts/verify_python.py
"$python" scripts/result_index.py --check
if [[ "$require_unconditional" == 1 ]]; then
  "$python" scripts/check_coverage.py --require-unconditional
elif [[ "$require_complete" == 1 ]]; then
  "$python" scripts/check_coverage.py --require-complete
else
  "$python" scripts/check_coverage.py
fi
echo 'Verification completed for the checked source files.'
