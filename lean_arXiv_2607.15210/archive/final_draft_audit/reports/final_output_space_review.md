> Historical scope/report. The current numbered results and complete Lean dependencies are listed in [the project README](../../README.md). Statements below about missing proofs describe the earlier snapshot.

# Output-state-space audit

The theorem and entropy corollary are mathematically correct conditional on the random compression formula and the preceding channel construction. The final draft's strict-sign bracketing correctly repairs the earlier unjustified interchange of an infimum and a pointwise limit.

Two small manuscript repairs are needed:

1. Define `m_{k,t}` before its first use (it is used twice but never defined in the supplied final draft). Set it equal to the minimum total coordinate sum on the compact body. Its positivity follows because the body lies in the nonnegative orthant and excludes zero when `k²t>1`.
2. Say **nonempty compact sets** in the Hausdorff definition and **nonempty compact convex sets** in the support-duality lemma. The output sets to which the lemma is applied are nonempty, so this does not change the theorem.

The cone normalization argument for convexity is valid. The trace spectral function is convex because its scalar function is convex; operator convexity of the scalar function is not needed. The marginal threshold is strict and sufficient. The unitary conjugation argument is applied separately to each fixed matrix and only then to a countable dense family, so it uses no uncountable intersection of events.

## New kernel-checked results

`Entropy/OutputSpace.lean` proves:

- The signs on either side of the normalized ratio maximum, with quantitative bounds `± εm`.
- Convergence of the generalized eigenvalue threshold from pointwise convergence at two strict brackets.
- Their composition as `normalized_support_tendsto`.
- Extension of convergence from a dense set under common Lipschitz bounds.
- The finite-net uniform convergence argument on compact sets.
- Convergence of attained minima under Hausdorff convergence and a common uniformly continuous objective.
- The same theorem for infimum values, deriving minimum attainment from compactness and continuity.
- The countable almost-sure intersection followed by dense extension and compact uniformization.
- Convergence of a support-distance supremum from uniform convergence.
- The combined almost-sure support-distance convergence theorem, with the norm-dual geometric identity explicit.

`Entropy/OutputSpaceBody.lean` uses the actual `AppendixB.Dset` definition and proves:

- Continuity of the Bernoulli cost, nonemptiness and compactness of the body.
- Positive total mass at each feasible point and a uniform strictly positive mass lower bound under `k²t>1`.
- Existence/attainment of the ordinary and normalized linear support maxima.
- `concrete_normalized_support_tendsto`: the scalar support convergence step for the concrete manuscript body, assuming only the compression limit and the channel's threshold identity.

There are 18 new theorem/lemma declarations in the two files, plus two definitions. `OutputSpaceAudit.lean` prints their complete axiom closures. All use only `propext`, `Classical.choice`, and `Quot.sound`; there are no `sorry` or new axioms.

## Exact scope boundary

These files do not themselves formalize matrices, partial traces, the variational characterization of the largest eigenvalue, unitary-invariance transport of the Haar law, trace/operator norm duality, the separating/minimax argument giving the support-Hausdorff identity, or continuity of matrix Rényi entropy. They formalize the analytic mechanism applied after those mathematical identifications. The standalone entropy files expose `hcut`/`hthreshold`, compression convergence, and `hdual` as explicit inputs. The additional matrix modules below now discharge the threshold identity for actual block compressions. The density-matrix variational support identification and the support/Hausdorff duality still remain outside the combined formalization. A claim that the complete random-channel Hausdorff theorem is kernel-verified would therefore be too strong.

## Reproduction

With the pinned Lean/mathlib environment used by the entropy project:

```sh
lake env lean -o .lake/build/lib/lean/Entropy/OutputSpace.olean Entropy/OutputSpace.lean
lake env lean -o .lake/build/lib/lean/Entropy/OutputSpaceBody.olean Entropy/OutputSpaceBody.lean
lake env lean OutputSpaceAudit.lean
```

The existing `Entropy.Defs` module must have been compiled first. The logs are `validation/OutputSpace.log`, `validation/OutputSpaceBody.log`, and `validation/OutputSpaceAudit.log`. `output_space_repairs.tex` gives the small manuscript repairs and an optional shorter theorem proof.

## Additional actual matrix verification

`lean_arXiv_2607.15210/OutputSpaceMatrix.lean` proves ten further results about genuine complex matrices:

- Congruence by an invertible Hermitian matrix reflects and preserves positive semidefiniteness.
- The largest-eigenvalue threshold before and after normalization is equivalent.
- Positive definiteness of the marginal proves invertibility of its positive square root and the exact inverse-square-root normalization identity.
- Consequently `λmax(A^(-1/2) H A^(-1/2)) ≤ z` if and only if `λmax(H-zA) ≤ 0`.
- The block pencil identity `S(a-z1)=S(a)-zS(1)` is proved directly from finite sums.
- The same threshold equivalence is specialized to actual diagonal block compressions.

`OutputSpaceCompressionBridge.lean` imports `OutputSpaceMatrix` and `Entropy.OutputSpaceBody`. Its theorem `normalized_compression_convergence` applies the proved matrix threshold to matrices of growing dimension `Fin (N+1)` and derives convergence of normalized largest eigenvalues from the unnormalized compression formula. The concrete body compactness, positivity of total mass, ratio support formula and root-limit argument are all used internally. The marginal is assumed positive definite at every index; in the paper this applies after discarding the finite initial exceptional segment. The sole spectral convergence input is convergence of the actual unnormalized top eigenvalues to `bodySupport` for every coefficient vector.

The ten matrix results and one bridge theorem also pass axiom audits with only the standard three axioms. The new audits are `OutputSpaceMatrixAudit.lean` and `OutputSpaceCompressionBridgeAudit.lean`; logs are in `validation/OutputSpaceMatrix{,Audit}.log` and `validation/OutputSpaceCompressionBridge{,Audit}.log`.
