#!/usr/bin/env python3
"""Run the seven-part numerical checks and the exact k182 certificate."""
import json
from pathlib import Path
import subprocess
import sys
import time
import hashlib

ROOT = Path(__file__).resolve().parents[1]
A = ROOT/'final_draft_audit'


def run():
    logs = ROOT/'verification/python_logs'
    logs.mkdir(exist_ok=True)
    status_file = ROOT/'verification/python_verification.json'
    status_file.write_text(json.dumps({'status': 'running'})+'\n')
    cases = [
        ('compression', A, ['random_compression_check.py', '--output', 'random_compression_results.json']),
        ('entropy', ROOT/'entropy', ['verify_entropy.py', '--output', 'python_results.json']),
        ('tensor', ROOT/'entropy', ['verify_tensor_spectra.py', '--output', 'tensor_spectra_results.json']),
        ('bell', A, ['verify_bell_limit.py']),
        ('main', A, ['verify_main_coefficient.py']),
        ('k182', A, ['certify_k182_exact.py', '--json', 'certificate_results.json']),
        ('k182_optimized_python', A, ['-O', 'certify_k182_exact.py'])]
    records = []
    for name, cwd, args in cases:
        start = time.monotonic()
        with (logs/(name+'.log')).open('w') as handle:
            result = subprocess.run([sys.executable]+args, cwd=cwd,
                                    stdout=handle, stderr=subprocess.STDOUT)
        if result.returncode:
            status_file.write_text(json.dumps({'status': 'failed', 'check': name})+'\n')
            raise RuntimeError(f'{name} failed; see {logs/(name+".log")}')
        print('Passed', name, flush=True)
        records.append({'check': name, 'exit_code': result.returncode,
                        'source': str((cwd/next(a for a in args if a.endswith('.py'))).relative_to(ROOT)),
                        'source_sha256': hashlib.sha256((cwd/next(a for a in args if a.endswith('.py'))).read_bytes()).hexdigest(),
                        'seconds': round(time.monotonic()-start, 3)})
    summary = {'status': 'pass', 'checks': records,
               'scope': 'Exact k182 scalar certificate; other numerical checks are not universal proofs.'}
    status_file.write_text(json.dumps(summary, indent=2)+'\n')


if __name__ == '__main__':
    run()
