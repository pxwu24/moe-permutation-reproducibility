# Lean verification for arXiv:2607.15210

This Lean 4.19.0 project formalizes results from the preliminaries, the deterministic Bernoulli convex-duality argument, and the scalar certificate for output dimension 182.

**Verification is partial.** The full Haar local-support lemma, the Choi characterization and normalization, and the deterministic support/infimum duality are proved. The random-compression limit, the free-convolution law, and its actual spectral-edge identification remain unproved.

## Output dimension 182

The [certificate and proof](k182/README.md) establish `k_high(1) <= 182`
at the exact parameter `t = 27/100000`, with limiting Bell-witness gap
greater than `477/1000000` nats. They do not prove minimality of 182.

`k182/certify_k182.py` uses rigorous Arb interval arithmetic.
`K182Dual.lean` and `K182Numerics.lean` independently prove the scalar
eigenvalue certificate and the actual real-logarithm gap in Lean.
`K182Entropy.lean` derives the entropy comparison under an explicit
minimizer-shape hypothesis. The proof of that hypothesis is supplied in
`k182/k182_revision.tex`; its Lean formalization remains unfinished.
This upload therefore does not claim a complete Lean proof of the
global entropy-minimization theorem or the finite-channel existence result.

```sh
python -m pip install -r k182/requirements.txt
python k182/certify_k182.py
bash k182/verify_lean.sh
```

## Verified results

- Full Haar local support: `HaarFullLocalSupport.lean`.
- Quantum channels and generalized Choi operators: `CompletePositivity.lean`.
- Bernoulli convex duality and critical-point classification: `BernoulliDuality.lean`, `BernoulliCriticalPoint.lean`.
- Gaussian/Haar, matrix, Cauchy-transform, and convergence-extension intermediates: the accompanying modules.

In the original preliminaries snapshot, all 30 mathematical modules were rebuilt from source. `FullAudit.lean` audited 421 theorem declarations, including generated helpers: only `propext`, `Classical.choice`, and `Quot.sound` occur as transitive axiom dependencies. There are no added logical axioms or admitted proofs. The new `K182Audit.lean` separately audits the output-dimension certificate; its build and audit logs are in `k182/verification/`.

`UnprovedTargets.lean` only defines the remaining random-compression proposition; it does not prove it and is not imported by the verified-results aggregate.

## Build

```sh
lake update
lake exe cache get
lake build
lake env lean FullAudit.lean
```

Mathlib is pinned to `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Start with `Preliminaries.lean`. See `formalization_scope_map.md` for exact coverage and `full_axiom_audit.log` for the recorded audit.
