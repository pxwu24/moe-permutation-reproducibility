# Third-party source notices

## Physlib / QuantumInfo

Source: https://github.com/leanprover-community/physlib

Pinned commit: `c76e3ccab04eacb69a126ca5c021b0788d513292`.

Physlib is distributed under the Apache License, Version 2.0. The dependency
checkout retains its original copyright and author notices. In particular,
the files modified by `upstream.patch` carry these notices:

- `QuantumInfo/ForMathlib/Filter.lean`: Copyright (c) 2025 Alex Meiburg. All
  rights reserved. Authors: Alex Meiburg.
- `QuantumInfo/ForMathlib/Majorization.lean`: Copyright (c) 2026 Alex Meiburg.
  All rights reserved. Authors: Alex Meiburg.
- `QuantumInfo/ForMathlib/HermitianMat/Rpow.lean`: Copyright (c) 2026 Alex
  Meiburg. All rights reserved. Authors: Alex Meiburg.
- `QuantumInfo/Channels/Unbundled.lean`: Copyright (c) 2025 Alex Meiburg. All
  rights reserved. Authors: Alex Meiburg.

The patch narrows imports, explicitly imports required integral and matrix-map
results, and supplies an existing subtype equality to a simplifier call. It
changes no mathematical statements or assumptions.

## QICLean / TNLean

Source: https://github.com/LionSR/QICLean

Pinned commit: `cdaa636d1f41560f7caca7077c11068229cb9727`.

Parts of the AM–GM and determinant arguments in `FilterTrace.lean` are adapted
from the following Apache 2.0 sources:

- `QICLean/Analysis/MatrixTraceInequalities.lean`: Copyright (c) 2026 Sirui Lu
  and TNLean contributors. All rights reserved. Authors: Sirui Lu.
- `QICLean/Analysis/DeterminantTraceBound.lean`: Copyright (c) 2026 TNLean
  contributors. All rights reserved. Authors: TNLean contributors.

The adapted arguments use Mathlib's weighted AM–GM and finite matrix
determinant identities, and are specialized and extended here to prove the
suppressor estimate. QICLean itself is not required as a build dependency.

The applicable Apache License, Version 2.0 text is reproduced in
`LICENSE-APACHE-2.0.txt`.
