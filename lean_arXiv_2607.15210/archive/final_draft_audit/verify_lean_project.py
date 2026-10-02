#!/usr/bin/env python3
"""Compile the actual project sources, then run the transitive kernel audit.

Use after `lake update; lake exe cache get`. Every included source is rebuilt;
the archive of the supplied uncorrected AppendixB is intentionally excluded.
No installation, network mutation, or source modification is performed here.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess
import time
import hashlib

ROOT = Path(__file__).resolve().parents[1]


def verify(direct=False):
    modules = {p.stem: p for p in ROOT.glob('*.lean') if p.name != 'lakefile.lean'}
    modules.update({'Entropy.'+p.stem: p for p in (ROOT/'entropy/Entropy').glob('*.lean')})
    modules['Entropy'] = ROOT/'entropy/Entropy.lean'
    ordered, visiting = [], set()

    def visit(name):
        if name in ordered:
            return
        if name in visiting:
            raise RuntimeError('Import cycle: '+name)
        visiting.add(name)
        for dep in re.findall(r'^import ([\w.]+)$', modules[name].read_text(), re.M):
            if dep in modules:
                visit(dep)
        visiting.remove(name)
        ordered.append(name)

    for name in sorted(modules):
        visit(name)
    logs = ROOT/'final_draft_audit/lean_logs'
    logs.mkdir(exist_ok=True)
    records = []
    prefix = ['lean'] if direct else ['lake', 'env', 'lean']
    for name in ordered:
        file = modules[name]
        out = ROOT/'.lake/build/lib/lean'/Path(*name.split('.')).with_suffix('.olean')
        out.parent.mkdir(parents=True, exist_ok=True)
        log = logs/(name+'.log')
        start = time.monotonic()
        with log.open('w') as handle:
            result = subprocess.run(prefix+['-o', str(out), str(file.relative_to(ROOT))],
                                    cwd=ROOT, stdout=handle, stderr=subprocess.STDOUT)
        text = log.read_text()
        if result.returncode or 'sorryAx' in text or 'declaration uses \'sorry\'' in text:
            raise RuntimeError(f'{name} failed ({result.returncode}):\n{text}')
        records.append({'module': name, 'path': str(file.relative_to(ROOT)),
                        'exit_code': result.returncode,
                        'sha256': hashlib.sha256(file.read_bytes()).hexdigest(),
                        'seconds': round(time.monotonic()-start, 3)})
        print('Checked', name, flush=True)
    audit = (logs/'FinalAudit.log').read_text()
    match = re.search(r'TOTAL audited theorem declarations: (\d+)', audit)
    if not match or 'PROJECT LOGICAL AXIOM DECLARATIONS: []' not in audit:
        raise RuntimeError('Missing successful project axiom audit')
    status = {'status': 'pass', 'lean_version': '4.19.0',
              'mathlib_commit': 'c44e0c8ee63ca166450922a373c7409c5d26b00b',
              'compiled_modules': len(records),
              'audited_theorem_declarations_including_generated': int(match[1]),
              'allowed_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
              'scope': 'See README.md; this does not assert full paper formalization.',
              'modules': records}
    (ROOT/'final_draft_audit/lean_verification.json').write_text(json.dumps(status, indent=2)+'\n')
    subprocess.run(['python3', 'verify_statements.py'], cwd=ROOT/'entropy', check=True)
    return status


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--direct', action='store_true',
                        help='Use an already configured Lean executable and LEAN_PATH.')
    args = parser.parse_args()
    result = verify(args.direct)
    print('Verified', result['compiled_modules'], 'modules and',
          result['audited_theorem_declarations_including_generated'], 'theorem declarations.')
