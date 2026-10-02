#!/usr/bin/env python3
"""High-precision diagnostics for the main coefficient gap.

The universal p>0 proof is in entropy/Entropy/MainCoefficient.lean.
This script checks a finite grid and the integral identity independently;
it does not turn a grid of orders into a universal certificate.
"""
import argparse
import json
from pathlib import Path
import mpmath as mp


def check():
    mp.mp.dps = 90
    orders = [mp.mpf(s) for s in (
        '1e-12', '.001', '.01', '.1', '.25', '.5', '.75',
        '.99999999999999999999', '1', '1.00000000000000000001',
        '1.5', '2', '4', '8', '20')]
    rows = []
    log16 = mp.log(16)
    for p in orders:
        B = (400 * log16 - 375 if p == 1 else
             25 * (mp.expm1(p * log16) - 15*p) / (p-1))
        ratio = B / (375*p)
        integral = mp.quad(lambda s: (16-s)*s**(p-2), [1, 2, 4, 8, 16])/15
        bound = 1-log16/15
        err = abs(ratio-integral)/max(1, abs(integral))
        if not (err < mp.mpf('1e-60') and ratio >= bound-mp.mpf('1e-70')
                and ratio > mp.mpf(4)/5 and B > 300*p):
            raise ArithmeticError(f'Coefficient check failed for p={p}')
        rows.append({'p': str(p), 'B': mp.nstr(B, 32),
                     'normalized_gap': mp.nstr(ratio-mp.mpf(4)/5, 32),
                     'relative_integral_error': mp.nstr(err, 8)})
    return {'status': 'pass', 'precision_decimal_digits': mp.mp.dps,
            'scope': 'Finite-grid numerical diagnostics; universal inequality is Lean-proved.',
            'uniform_ratio_lower_bound': mp.nstr(1-log16/15, 32), 'cases': rows}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = check()
    text = json.dumps(result, indent=2)+'\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')
