#!/usr/bin/env bash
# Verify the unified project; optionally replay the preserved Lean 4.24 project.
set -euo pipefail
proof_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
bash "$proof_root/entropy/verify.sh"
if [[ "${VERIFY_LEGACY_ADDER:-0}" == 1 ]]; then
  ELAN_TOOLCHAIN="$(cat "$proof_root/adder-trace/lean-toolchain")" \
    bash "$proof_root/adder-trace/verify.sh"
fi
