#!/usr/bin/env python3
"""Distinguish checked deductions from unconditional paper verification."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument('--require-complete', action='store_true',
                    help='Require all indexed deductions to be checked under their stated hypotheses')
parser.add_argument('--require-unconditional', action='store_true',
                    help='Fail while any indexed result still depends on an unverified input')
args = parser.parse_args()
data = json.loads((ROOT / 'results/RESULTS.json').read_text())
remaining = [r['number'] for r in data['results']
             if r['status'] not in {'complete', 'complete_under_permitted_black_box'}]
conditional = [r['number'] for r in data['results']
               if r['status'] == 'complete_under_permitted_black_box']
progress = json.loads((ROOT / 'partial_progress/status.json').read_text())
input_removed = progress['paper_convergence_hypothesis_removed']
unconditional = not remaining and (not conditional or input_removed)
result = {
    'all_indexed_deductions_verified_under_stated_hypotheses': not remaining,
    'all_requested_paper_results_complete': unconditional,
    'unconditional_paper_verification_complete': unconditional,
    'unfinished_deductions': remaining,
    'results_depending_on_unverified_convergence_input': conditional,
    'remaining_input': None if input_removed else progress['remaining_hypothesis'],
    'input_statement_and_partial_progress': '../partial_progress/README.md',
    'only_permitted_external_assumption': data['only_permitted_external_assumption'],
    'note': 'Compilation and checked deductions do not discharge the strong-convergence hypothesis.'}
(ROOT / 'verification/paper_coverage.json').write_text(json.dumps(result, indent=2) + '\n')
if remaining:
    print('Unfinished indexed deductions:', ', '.join(remaining))
    if args.require_complete or args.require_unconditional:
        raise SystemExit(2)
else:
    print('All indexed deductions are checked under their stated hypotheses.')
if not unconditional:
    print('Unconditional paper verification is incomplete: block-modified strong convergence remains an input.')
    if args.require_unconditional:
        raise SystemExit(2)
