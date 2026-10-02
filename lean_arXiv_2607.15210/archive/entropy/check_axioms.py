#!/usr/bin/env python3
"""Reject incomplete proofs and nonstandard axioms in the compiler audit."""
import re
from pathlib import Path
text = Path('validation/axioms.log').read_text()
entries = re.findall(r"'(.+)' depends on axioms: \[([^]]*)\]", text)
assert entries, 'No axiom audit results found.'
expected = sum(line.startswith('#print axioms ') for line in Path('Audit.lean').read_text().splitlines())
assert len(entries) == expected, (len(entries), expected)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name, raw in entries:
    axioms = {v.strip() for v in raw.split(',') if v.strip()}
    assert axioms <= allowed, (name, axioms - allowed)
assert 'sorryAx' not in text and 'error:' not in text
print(f'{len(entries)} declarations audited: only standard Lean axioms.')
