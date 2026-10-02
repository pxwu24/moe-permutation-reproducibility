#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
# Prerequisites: Lean 4.19.0, `lake update`, `lake exe cache get`, and
# `python3 -m pip install -r final_draft_audit/requirements.txt`.
python3 final_draft_audit/verify_lean_project.py
python3 final_draft_audit/verify_python.py
