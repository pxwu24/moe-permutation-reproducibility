# Lemma II.3: Random compression formula

Deduction verified; the block-modified strong-convergence theorem remains an input.

For an actual projection sequence, affine operator-norm convergence from the permitted amplified block-modified strong-convergence input implies largest-eigenvalue convergence to the stated body support, simultaneously for all real coefficient vectors on one probability-one event. The spectral edge is proved through Lemma A.1.

The full unverified input and the Lean progress are stated in [partial_progress/](../partial_progress/README.md).

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

- [RandomCompression.RevisionBernoulliCompression](../lean/RandomCompression/RevisionBernoulliCompression.lean)
- [RandomCompression.ProjectionStrongConvergence](../lean/RandomCompression/ProjectionStrongConvergence.lean)
- [RandomCompression.BlockModification](../lean/RandomCompression/BlockModification.lean)
- [RandomCompression.RevisionFullBlockInput](../lean/RandomCompression/RevisionFullBlockInput.lean)

## All related Lean files

This is the complete transitive local import closure of the entry files. Mathlib dependencies are pinned in `lake-manifest.json`.

- [lean/Entropy/Defs.lean](../lean/Entropy/Defs.lean)
- [lean/Entropy/OutputSpace.lean](../lean/Entropy/OutputSpace.lean)
- [lean/Entropy/OutputSpaceBody.lean](../lean/Entropy/OutputSpaceBody.lean)
- [lean/HaarProjections/HaarMeasure.lean](../lean/HaarProjections/HaarMeasure.lean)
- [lean/HaarProjections/HaarProjection.lean](../lean/HaarProjections/HaarProjection.lean)
- [lean/OutputStates/OutputSpaceCompressionBridge.lean](../lean/OutputStates/OutputSpaceCompressionBridge.lean)
- [lean/OutputStates/OutputSpaceMatrix.lean](../lean/OutputStates/OutputSpaceMatrix.lean)
- [lean/OutputStates/RevisionOutputChannel.lean](../lean/OutputStates/RevisionOutputChannel.lean)
- [lean/OutputStates/RevisionOutputConvergence.lean](../lean/OutputStates/RevisionOutputConvergence.lean)
- [lean/OutputStates/RevisionOutputDuality.lean](../lean/OutputStates/RevisionOutputDuality.lean)
- [lean/OutputStates/RevisionOutputUnitary.lean](../lean/OutputStates/RevisionOutputUnitary.lean)
- [lean/Preliminaries/CompletePositivity.lean](../lean/Preliminaries/CompletePositivity.lean)
- [lean/Preliminaries/PreliminariesAnalysis.lean](../lean/Preliminaries/PreliminariesAnalysis.lean)
- [lean/Preliminaries/PreliminariesChoi.lean](../lean/Preliminaries/PreliminariesChoi.lean)
- [lean/Preliminaries/PreliminariesLegendre.lean](../lean/Preliminaries/PreliminariesLegendre.lean)
- [lean/Preliminaries/PreliminariesMatrix.lean](../lean/Preliminaries/PreliminariesMatrix.lean)
- [lean/RandomCompression/BernoulliCalculus.lean](../lean/RandomCompression/BernoulliCalculus.lean)
- [lean/RandomCompression/BernoulliCriticalPoint.lean](../lean/RandomCompression/BernoulliCriticalPoint.lean)
- [lean/RandomCompression/BernoulliDuality.lean](../lean/RandomCompression/BernoulliDuality.lean)
- [lean/RandomCompression/BernoulliEdgeCalculus.lean](../lean/RandomCompression/BernoulliEdgeCalculus.lean)
- [lean/RandomCompression/BlockModification.lean](../lean/RandomCompression/BlockModification.lean)
- [lean/RandomCompression/CauchyBernoulli.lean](../lean/RandomCompression/CauchyBernoulli.lean)
- [lean/RandomCompression/CauchyHolomorphic.lean](../lean/RandomCompression/CauchyHolomorphic.lean)
- [lean/RandomCompression/CauchyHolomorphy.lean](../lean/RandomCompression/CauchyHolomorphy.lean)
- [lean/RandomCompression/CauchyLocalInverse.lean](../lean/RandomCompression/CauchyLocalInverse.lean)
- [lean/RandomCompression/CompressionEndpointGlue.lean](../lean/RandomCompression/CompressionEndpointGlue.lean)
- [lean/RandomCompression/CompressionExtension.lean](../lean/RandomCompression/CompressionExtension.lean)
- [lean/RandomCompression/CompressionSpectral.lean](../lean/RandomCompression/CompressionSpectral.lean)
- [lean/RandomCompression/ProjectionStrongConvergence.lean](../lean/RandomCompression/ProjectionStrongConvergence.lean)
- [lean/RandomCompression/RevisionBernoulliCauchy.lean](../lean/RandomCompression/RevisionBernoulliCauchy.lean)
- [lean/RandomCompression/RevisionBernoulliCompression.lean](../lean/RandomCompression/RevisionBernoulliCompression.lean)
- [lean/RandomCompression/RevisionBernoulliEdge.lean](../lean/RandomCompression/RevisionBernoulliEdge.lean)
- [lean/RandomCompression/RevisionBernoulliHolomorphic.lean](../lean/RandomCompression/RevisionBernoulliHolomorphic.lean)
- [lean/RandomCompression/RevisionBernoulliLaw.lean](../lean/RandomCompression/RevisionBernoulliLaw.lean)
- [lean/RandomCompression/RevisionBernoulliTensor.lean](../lean/RandomCompression/RevisionBernoulliTensor.lean)
- [lean/RandomCompression/RevisionFullBlockInput.lean](../lean/RandomCompression/RevisionFullBlockInput.lean)
- [lean/RandomCompression/SpectralEdge.lean](../lean/RandomCompression/SpectralEdge.lean)

## Assumptions and dependencies

- Fixed positive integer k, t in (0,1), rank densities d_n/(n*k)->t, Haar projection sequence.
- The source statement incorrectly starts with fixed n,d,P before using d_n,P_n; write a sequence explicitly.
- AmplifiedBlockModifiedStrongInput is the permitted block-modified strong-convergence theorem specialized to affine polynomial norm tests on the actual amplified map (id tensor phi_a)(P_n). Tensor operator-norm equality, norm-to-edge conversion, and the edge identity are proved.

Paper dependencies: A.1.

## Python checks

- [random_compression_check.py](../python/random_compression/random_compression_check.py)

The exact rational certificate is a certificate of its scalar inequalities; the other numerical checks are cross-checks, not universal proofs.
