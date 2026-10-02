# Lemma II.3: Random compression formula

**Status: Complete under the permitted block-modified strong-convergence input.**

For an actual projection sequence, affine operator-norm convergence from the permitted amplified block-modified strong-convergence input implies largest-eigenvalue convergence to the stated body support, simultaneously for all real coefficient vectors on one probability-one event. The spectral edge is proved through Lemma A.1.

## Check this result

First run `bash lean_arXiv_2607.15210/verify-all.sh` from the repository root. Then, from `lean_arXiv_2607.15210/`, run:

```sh
cat > InspectResult.lean <<'LEAN'
import AllProofs

#check ProjectionChannels.random_compression_from_amplified_block_strong
#print axioms ProjectionChannels.random_compression_from_amplified_block_strong
#check ProjectionChannels.fixed_random_compression_from_block_strong
#print axioms ProjectionChannels.fixed_random_compression_from_block_strong
#check ProjectionStrongConvergence.projections_strongly_converge_to_bernoulli
#print axioms ProjectionStrongConvergence.projections_strongly_converge_to_bernoulli
#check ProjectionChannels.amplified_diagonalTrace
#print axioms ProjectionChannels.amplified_diagonalTrace
#check ProjectionChannels.FullBlockModifiedStrongInput.to_amplified
#print axioms ProjectionChannels.FullBlockModifiedStrongInput.to_amplified
LEAN
lake env lean InspectResult.lean
rm InspectResult.lean
```

The displayed hypotheses are part of the checked statement. A theorem conditional on an intermediate assertion does not verify that assertion.

## Entry files

- [RevisionBernoulliCompression](../RevisionBernoulliCompression.lean)
- [ProjectionStrongConvergence](../ProjectionStrongConvergence.lean)
- [BlockModification](../BlockModification.lean)
- [RevisionFullBlockInput](../RevisionFullBlockInput.lean)

## All related Lean files

This is the complete transitive local import closure of the entry files. Mathlib dependencies are pinned in `lake-manifest.json`.

- [BernoulliCalculus.lean](../BernoulliCalculus.lean)
- [BernoulliCriticalPoint.lean](../BernoulliCriticalPoint.lean)
- [BernoulliDuality.lean](../BernoulliDuality.lean)
- [BernoulliEdgeCalculus.lean](../BernoulliEdgeCalculus.lean)
- [BlockModification.lean](../BlockModification.lean)
- [CauchyBernoulli.lean](../CauchyBernoulli.lean)
- [CauchyHolomorphic.lean](../CauchyHolomorphic.lean)
- [CauchyHolomorphy.lean](../CauchyHolomorphy.lean)
- [CauchyLocalInverse.lean](../CauchyLocalInverse.lean)
- [CompletePositivity.lean](../CompletePositivity.lean)
- [CompressionEndpointGlue.lean](../CompressionEndpointGlue.lean)
- [CompressionExtension.lean](../CompressionExtension.lean)
- [CompressionSpectral.lean](../CompressionSpectral.lean)
- [entropy/Entropy/Defs.lean](../entropy/Entropy/Defs.lean)
- [entropy/Entropy/OutputSpace.lean](../entropy/Entropy/OutputSpace.lean)
- [entropy/Entropy/OutputSpaceBody.lean](../entropy/Entropy/OutputSpaceBody.lean)
- [HaarMeasure.lean](../HaarMeasure.lean)
- [HaarProjection.lean](../HaarProjection.lean)
- [OutputSpaceCompressionBridge.lean](../OutputSpaceCompressionBridge.lean)
- [OutputSpaceMatrix.lean](../OutputSpaceMatrix.lean)
- [PreliminariesAnalysis.lean](../PreliminariesAnalysis.lean)
- [PreliminariesChoi.lean](../PreliminariesChoi.lean)
- [PreliminariesLegendre.lean](../PreliminariesLegendre.lean)
- [PreliminariesMatrix.lean](../PreliminariesMatrix.lean)
- [ProjectionStrongConvergence.lean](../ProjectionStrongConvergence.lean)
- [RevisionBernoulliCauchy.lean](../RevisionBernoulliCauchy.lean)
- [RevisionBernoulliCompression.lean](../RevisionBernoulliCompression.lean)
- [RevisionBernoulliEdge.lean](../RevisionBernoulliEdge.lean)
- [RevisionBernoulliHolomorphic.lean](../RevisionBernoulliHolomorphic.lean)
- [RevisionBernoulliLaw.lean](../RevisionBernoulliLaw.lean)
- [RevisionBernoulliTensor.lean](../RevisionBernoulliTensor.lean)
- [RevisionFullBlockInput.lean](../RevisionFullBlockInput.lean)
- [RevisionOutputChannel.lean](../RevisionOutputChannel.lean)
- [RevisionOutputConvergence.lean](../RevisionOutputConvergence.lean)
- [RevisionOutputDuality.lean](../RevisionOutputDuality.lean)
- [RevisionOutputUnitary.lean](../RevisionOutputUnitary.lean)
- [SpectralEdge.lean](../SpectralEdge.lean)

## Assumptions and dependencies

- Fixed positive integer k, t in (0,1), rank densities d_n/(n*k)->t, Haar projection sequence.
- The source statement incorrectly starts with fixed n,d,P before using d_n,P_n; write a sequence explicitly.
- AmplifiedBlockModifiedStrongInput is the permitted block-modified strong-convergence theorem specialized to affine polynomial norm tests on the actual amplified map (id tensor phi_a)(P_n). Tensor operator-norm equality, norm-to-edge conversion, and the edge identity are proved.

Paper dependencies: A.1.

## Python checks

- [random_compression_check.py](../final_draft_audit/random_compression_check.py)

The exact rational certificate is a certificate of its scalar inequalities; the other numerical checks are cross-checks, not universal proofs.
