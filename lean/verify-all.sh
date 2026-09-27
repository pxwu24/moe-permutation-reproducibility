#!/usr/bin/env bash
set -euo pipefail
proof_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
bash "$proof_root/entropy/verify.sh"
bash "$proof_root/adder-trace/verify.sh"
