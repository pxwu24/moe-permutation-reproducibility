> Historical material. See the [current verification summary](../../README.md) for maintained commands and results.

> Historical scope/report. The current numbered results and complete Lean dependencies are listed in [the project README](../README.md). Statements below about missing proofs describe the earlier snapshot.

# Output dimension 182: certificate and Lean checks

For the projection-induced ensemble in arXiv:2607.15210, the rational choice

\[
k=182,\qquad t=\frac{27}{100000}
\]

gives the strict limiting Bell-witness gap

\[
2\min_{\sigma\in\mathscr K_{182,t}}S_1(\sigma)
-S_1(\lambda^{\mathrm{Bell}}_{182,t})>\frac{477}{10^6}.
\]

Thus **the certified upper bound is `k_high(1) <= 182`**. Neither this
certificate nor the Lean files exclude all smaller dimensions. The
manuscript's output-set and Bell-output convergence theorems turn this
positive limiting gap into finite-dimensional channel violations for
sufficiently large input dimension; no explicit finite input dimension
is supplied here.

The Python certificate and the accompanying analytic proof establish the
global entropy comparison. **The Lean verification is partial:** it proves
the scalar eigenvalue bound and the numerical entropy gap, and derives the
global conclusion under an explicit minimizer-shape hypothesis. The
minimizer-shape theorem itself is proved in the LaTeX supplement, but is
not yet formalized in Lean. The random-matrix limit theorems are also
outside these new Lean modules.

## Reproduce the Python certificate

From this directory:

```sh
python -m pip install -r requirements.txt
python certify_k182.py
```

The script uses Arb ball arithmetic through `python-flint==0.9.0`.
All inputs are exact rationals. No numerical optimizer or sampling is
used. A check fails if its intervals do not separate strictly.
The script checks

\[
L=\frac{162513}{10^6},\qquad z=\frac{2077}{2000},
\]

and obtains a lower bound on the gap of approximately
`0.00047756110230383259375` nats. This number is a lower bound, not a
numerical claim of the exact global minimum.

## What the Lean files prove

The new modules are in the parent Lean project:

| Module | Coverage |
| --- | --- |
| `K182Dual.lean` | The exact scalar dual inequality, its rational square-root certificate, and the bound `u_i / sum u <= L` for every feasible vector. |
| `K182Numerics.lean` | Rigorous bounds for actual real logarithms and the inequality `2 * entropyLower - bellEntropy > 477/1000000`. This is proved within Lean, independently of Arb's numerical output. |
| `K182Entropy.lean` | Entropy of a spectrum with one larger eigenvalue, its monotonicity, and the conclusion under an explicitly stated minimizer-shape hypothesis. |
| `K182Audit.lean` | Transitive axiom audit of all theorem declarations in the new modules. |

Read the hypotheses of the entropy-reduction theorem carefully: a bound
on the largest eigenvalue alone is not a proof of the global Shannon
entropy lower bound. The LaTeX proof excludes zero coordinates and uses
the multiplier rule and second variation to establish the missing
minimizer-shape statement.

## Reproduce the Lean checks

From the parent directory `lean_arXiv_2607.15210`:

```sh
lake update
lake exe cache get
bash k182/verify_lean.sh
```

The project pins Lean 4.19.0 and mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`.
The verification directory contains the build and axiom-audit output
from the checked source snapshot.

The recorded run compiled the four required project source files and
audited 58 theorem declarations, including generated helpers. The only
transitive axioms were `propext`, `Classical.choice`, and `Quot.sound`;
there were no added logical axioms or admitted proofs. This audit checks
the statements actually proved, including their explicit hypotheses.

## Manuscript text

`k182_revision.tex` contains the replacement subsection and the two
supporting lemmas for the appendix. It states the upper bound rather
than the unproved equality `k_high(1) = 182`.

The comparison is with the random-Stinespring/Bell-state criterion in
Belinschi, Collins, and Nechita, *Almost one bit violation for the
additivity of the minimum output entropy*, Communications in Mathematical
Physics 341 (2016), 885–909. That ensemble's threshold is 183; it is a
different ensemble from the locally normalized projection construction.

