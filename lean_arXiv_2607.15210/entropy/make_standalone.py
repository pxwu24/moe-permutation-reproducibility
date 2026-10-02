#!/usr/bin/env python3
"""Generate the standalone Lean file from the maintained modular source."""
from pathlib import Path
root = Path(__file__).parent
modules = ['Defs', 'Analysis', 'Combinatorics', 'Localization', 'SpikeArithmetic', 'Spike',
           'Single', 'BellBounds', 'BellOne', 'BellGeneral', 'Infimum']
imports = '\n'.join(l for l in (root / 'Entropy/Defs.lean').read_text().splitlines() if l.startswith('import '))
header = '''/-
Entropy appendix: standalone spectral formalization.
Generated from Entropy/*.lean by make_standalone.py.
Lean 4.19.0 / mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b.
See LEAN_SCOPE.md for the operator-to-spectrum boundary and infimum convention.
Compile in a pinned Mathlib project: lake env lean AppendixB_verified.lean
-/
'''
parts = []
for name in modules:
    source = (root / f'Entropy/{name}.lean').read_text()
    body = '\n'.join(l for l in source.splitlines() if not l.startswith('import '))
    parts.append(f'\n/- Source module: Entropy.{name} -/\n'+body)
audit = '\n'.join(l for l in (root / 'Audit.lean').read_text().splitlines() if not l.startswith('import '))
(root / 'AppendixB_verified.lean').write_text(header + imports + '\n' + '\n'.join(parts) + '\n' + audit + '\n')
