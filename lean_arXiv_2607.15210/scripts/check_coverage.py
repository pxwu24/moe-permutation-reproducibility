#!/usr/bin/env python3
"""Report paper completion separately from successful source compilation."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument('--require-complete', action='store_true')
args = parser.parse_args()
data = json.loads((ROOT / 'RESULTS.json').read_text())
remaining = [r['number'] for r in data['results']
             if r['status'] not in {'complete', 'complete_under_permitted_black_box'}]
result = {'all_requested_paper_results_complete': not remaining,
          'unfinished_paper_results': remaining,
          'only_permitted_external_assumption': data['only_permitted_external_assumption'],
          'note': 'Successful compilation does not discharge explicit theorem hypotheses.'}
(ROOT / 'verification/paper_coverage.json').write_text(json.dumps(result, indent=2) + '\n')
if remaining:
    print('Full paper formalization is incomplete. Unfinished statements:', ', '.join(remaining))
    if args.require_complete:
        raise SystemExit(2)
else:
    print('All indexed paper results are complete under the documented assumption policy.')
