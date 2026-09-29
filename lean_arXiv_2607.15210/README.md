# Lean verification for arXiv:2607.15210

This Lean 4.19.0 project formalizes results from the preliminaries and the deterministic Bernoulli convex-duality argument.

**Verification is partial.** The full Haar local-support lemma, the Choi characterization and normalization, and the deterministic support/infimum duality are proved. The random-compression limit, the free-convolution law, and its actual spectral-edge identification remain unproved.

## Verified results

- Full Haar local support: `HaarFullLocalSupport.lean`.
- Quantum channels and generalized Choi operators: `CompletePositivity.lean`.
- Bernoulli convex duality and critical-point classification: `BernoulliDuality.lean`, `BernoulliCriticalPoint.lean`.
- Gaussian/Haar, matrix, Cauchy-transform, and convergence-extension intermediates: the accompanying modules.

All 30 mathematical modules were rebuilt from source. `FullAudit.lean` audited 421 theorem declarations, including generated helpers: only `propext`, `Classical.choice`, and `Quot.sound` occur as transitive axiom dependencies. There are no added logical axioms or admitted proofs.

`UnprovedTargets.lean` only defines the remaining random-compression proposition; it does not prove it and is not imported by the verified-results aggregate.

## Build

```sh
lake update
lake exe cache get
lake build
lake env lean FullAudit.lean
```

Mathlib is pinned to `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Start with `Preliminaries.lean`. See `formalization_scope_map.md` for exact coverage and `full_axiom_audit.log` for the recorded audit.
