#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p .lake/build/lib/lean/Entropy validation
for module in Defs Analysis Combinatorics BellBounds BellOne BellGeneral Bell BellFiniteDifference BellLimitCoefficients BellLimitTransfer BellMatrixIdentities Localization SpikeArithmetic Spike Single Infimum MainCoefficient MainSpectral Minimum OutputSpace OutputSpaceBody; do
  echo "Checking Entropy.$module"
  lake env lean -o ".lake/build/lib/lean/Entropy/$module.olean" "Entropy/$module.lean" > "validation/$module.log" 2>&1 || { cat "validation/$module.log"; exit 1; }
done
lake env lean -o .lake/build/lib/lean/Entropy.olean Entropy.lean > validation/Entropy.log 2>&1
lake env lean -o .lake/build/lib/lean/AppendixB.olean AppendixB.lean > validation/AppendixB.log 2>&1
lake env lean Audit.lean > validation/axioms.log 2>&1
lake env lean AuditAll.lean > validation/all_axioms.log 2>&1
if grep -Eq 'sorryAx|declaration uses .sorry.|error:' validation/*.log; then
  echo 'Verification failed: error or incomplete proof detected.'
  exit 1
fi
python3 check_axioms.py
python3 verify_statements.py
echo 'Lean verification and axiom audit passed.'
