#!/usr/bin/env python3
"""Independent 100-digit checks of the all-p coefficient gap.

The universal theorem is kernel checked in Entropy/MainCoefficient.lean.
These finite samples are regression checks, not a proof for all real p.
The Taylor certificate exp(3)>16 at the end uses exact rational arithmetic.
"""
import json
from fractions import Fraction
from math import factorial
from pathlib import Path
import mpmath as mp

if not __debug__:
    raise RuntimeError('Run without -O: assertions are verification gates.')
mp.mp.dps = 100
L = mp.log(16)

def coefficient(p):
    if p == 1:
        return 400 * L - 375
    return 25 * (mp.expm1(p * L) - 15 * p) / (p - 1)

def integral_coefficient(p):
    return 25 * p * mp.quad(lambda s: (16-s) * mp.power(s, p-2), [1, 2, 4, 8, 16])

orders = [mp.mpf(s) for s in ['1e-40', '1e-12', '0.01', '0.1', '0.25',
    '0.5', '0.75', '0.99', '1', '1.01', '1.5', '2', '5', '10', '100']]
orders.extend([1-mp.mpf('1e-30'), 1+mp.mpf('1e-30')])
rows = []
for p in sorted(orders):
    b = coefficient(p)
    bi = integral_coefficient(p)
    lower = 25 * p * (3-L)
    gap = b-300*p
    assert abs(b-bi) <= mp.mpf('1e-58') * max(abs(b), mp.mpf(1)), (p,b,bi)
    assert gap >= lower > 0, (p,gap,lower)
    rows.append({'p': mp.nstr(p, 45), 'B': mp.nstr(b, 45),
        'gap': mp.nstr(gap, 45), 'proved_lower_bound': mp.nstr(lower, 45)})

# Exact certificate used by the Lean proof of log(16)<3.
taylor = sum((Fraction(3)**j / factorial(j) for j in range(6)), Fraction(0))
assert taylor > 16
result = {'status':'PASS', 'precision_digits':mp.mp.dps,
    'mpmath_version':mp.__version__, 'tested_orders':len(rows),
    'exact_exp3_partial_sum':str(taylor), 'samples':rows,
    'scope':'Finite high-precision regression checks; the all-real-p theorem is in Lean.'}
Path('main_coefficient_results.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k != 'samples'}, indent=2))
