# Theorem III.1: Hausdorff limit of output state spaces

Deduction verified; the block-modified strong-convergence theorem remains an input.

Almost-sure convergence of the actual locally normalized channel output image to the actual unitarily invariant density-matrix body in the genuine trace-norm Hausdorff distance. Compactness, convexity, support identification, general Hermitian tests, common probability-one events, and eventual marginal invertibility including the finite-prefix argument are proved.

The full unverified input and the Lean progress are stated in [partial_progress/](../partial_progress/README.md).

## Check this result

First run `bash lean_arXiv_2607.15210/verify-all.sh` from the repository root. Then, from `lean_arXiv_2607.15210/`, run:

```sh
cat > InspectResult.lean <<'LEAN'
import AllProofs

#check RevisionOutput.output_space_limit
#print axioms RevisionOutput.output_space_limit
#check RevisionOutput.trace_distance_density_formula
#print axioms RevisionOutput.trace_distance_density_formula
#check RevisionOutput.raw_normalizedOutput_posSemidef
#print axioms RevisionOutput.raw_normalizedOutput_posSemidef
LEAN
lake env lean InspectResult.lean
rm InspectResult.lean
```

The displayed hypotheses are part of the checked statement. A theorem conditional on an intermediate assertion does not verify that assertion.

## Entry files

- [OutputStates.RevisionOutputTheorem](../lean/OutputStates/RevisionOutputTheorem.lean)

## All related Lean files

This is the complete transitive local import closure of the entry files. Mathlib dependencies are pinned in `lake-manifest.json`.

- [lean/Entropy/Analysis.lean](../lean/Entropy/Analysis.lean)
- [lean/Entropy/Combinatorics.lean](../lean/Entropy/Combinatorics.lean)
- [lean/Entropy/Defs.lean](../lean/Entropy/Defs.lean)
- [lean/Entropy/Infimum.lean](../lean/Entropy/Infimum.lean)
- [lean/Entropy/Localization.lean](../lean/Entropy/Localization.lean)
- [lean/Entropy/Minimum.lean](../lean/Entropy/Minimum.lean)
- [lean/Entropy/OutputSpace.lean](../lean/Entropy/OutputSpace.lean)
- [lean/Entropy/OutputSpaceBody.lean](../lean/Entropy/OutputSpaceBody.lean)
- [lean/Entropy/Single.lean](../lean/Entropy/Single.lean)
- [lean/Entropy/Spike.lean](../lean/Entropy/Spike.lean)
- [lean/Entropy/SpikeArithmetic.lean](../lean/Entropy/SpikeArithmetic.lean)
- [lean/HaarProjections/HaarMeasure.lean](../lean/HaarProjections/HaarMeasure.lean)
- [lean/HaarProjections/HaarProjection.lean](../lean/HaarProjections/HaarProjection.lean)
- [lean/OutputStates/OutputSpaceCompressionBridge.lean](../lean/OutputStates/OutputSpaceCompressionBridge.lean)
- [lean/OutputStates/OutputSpaceMatrix.lean](../lean/OutputStates/OutputSpaceMatrix.lean)
- [lean/OutputStates/RevisionOutputBody.lean](../lean/OutputStates/RevisionOutputBody.lean)
- [lean/OutputStates/RevisionOutputChannel.lean](../lean/OutputStates/RevisionOutputChannel.lean)
- [lean/OutputStates/RevisionOutputConvergence.lean](../lean/OutputStates/RevisionOutputConvergence.lean)
- [lean/OutputStates/RevisionOutputDuality.lean](../lean/OutputStates/RevisionOutputDuality.lean)
- [lean/OutputStates/RevisionOutputEventual.lean](../lean/OutputStates/RevisionOutputEventual.lean)
- [lean/OutputStates/RevisionOutputFunctionals.lean](../lean/OutputStates/RevisionOutputFunctionals.lean)
- [lean/OutputStates/RevisionOutputGeometry.lean](../lean/OutputStates/RevisionOutputGeometry.lean)
- [lean/OutputStates/RevisionOutputLimit.lean](../lean/OutputStates/RevisionOutputLimit.lean)
- [lean/OutputStates/RevisionOutputProbability.lean](../lean/OutputStates/RevisionOutputProbability.lean)
- [lean/OutputStates/RevisionOutputStates.lean](../lean/OutputStates/RevisionOutputStates.lean)
- [lean/OutputStates/RevisionOutputTheorem.lean](../lean/OutputStates/RevisionOutputTheorem.lean)
- [lean/OutputStates/RevisionOutputTraceDistance.lean](../lean/OutputStates/RevisionOutputTraceDistance.lean)
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

- Fixed k>=2, t in (1/k^2,1), independent Haar projections with d_n/(n*k)->t; channels defined eventually when marginals positive.
- FullBlockModifiedStrongInput is the sole external theorem parameter; it contains the norm and weak-trace parts of the permitted block-modified strong-convergence theorem for the same law.

Paper dependencies: II.2, II.3, III.3, III.4, A.1.
