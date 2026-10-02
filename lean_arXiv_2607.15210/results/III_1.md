# Theorem III.1: Hausdorff limit of output state spaces

**Status: Complete under the permitted block-modified strong-convergence input.**

Almost-sure convergence of the actual locally normalized channel output image to the actual unitarily invariant density-matrix body in the genuine trace-norm Hausdorff distance. Compactness, convexity, support identification, general Hermitian tests, common probability-one events, and eventual marginal invertibility including the finite-prefix argument are proved.

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

- [RevisionOutputTheorem](../RevisionOutputTheorem.lean)

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
- [entropy/Entropy/Analysis.lean](../entropy/Entropy/Analysis.lean)
- [entropy/Entropy/Combinatorics.lean](../entropy/Entropy/Combinatorics.lean)
- [entropy/Entropy/Defs.lean](../entropy/Entropy/Defs.lean)
- [entropy/Entropy/Infimum.lean](../entropy/Entropy/Infimum.lean)
- [entropy/Entropy/Localization.lean](../entropy/Entropy/Localization.lean)
- [entropy/Entropy/Minimum.lean](../entropy/Entropy/Minimum.lean)
- [entropy/Entropy/OutputSpace.lean](../entropy/Entropy/OutputSpace.lean)
- [entropy/Entropy/OutputSpaceBody.lean](../entropy/Entropy/OutputSpaceBody.lean)
- [entropy/Entropy/Single.lean](../entropy/Entropy/Single.lean)
- [entropy/Entropy/Spike.lean](../entropy/Entropy/Spike.lean)
- [entropy/Entropy/SpikeArithmetic.lean](../entropy/Entropy/SpikeArithmetic.lean)
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
- [RevisionOutputBody.lean](../RevisionOutputBody.lean)
- [RevisionOutputChannel.lean](../RevisionOutputChannel.lean)
- [RevisionOutputConvergence.lean](../RevisionOutputConvergence.lean)
- [RevisionOutputDuality.lean](../RevisionOutputDuality.lean)
- [RevisionOutputEventual.lean](../RevisionOutputEventual.lean)
- [RevisionOutputFunctionals.lean](../RevisionOutputFunctionals.lean)
- [RevisionOutputGeometry.lean](../RevisionOutputGeometry.lean)
- [RevisionOutputLimit.lean](../RevisionOutputLimit.lean)
- [RevisionOutputProbability.lean](../RevisionOutputProbability.lean)
- [RevisionOutputStates.lean](../RevisionOutputStates.lean)
- [RevisionOutputTheorem.lean](../RevisionOutputTheorem.lean)
- [RevisionOutputTraceDistance.lean](../RevisionOutputTraceDistance.lean)
- [RevisionOutputUnitary.lean](../RevisionOutputUnitary.lean)
- [SpectralEdge.lean](../SpectralEdge.lean)

## Assumptions and dependencies

- Fixed k>=2, t in (1/k^2,1), independent Haar projections with d_n/(n*k)->t; channels defined eventually when marginals positive.
- FullBlockModifiedStrongInput is the sole external theorem parameter; it contains the norm and weak-trace parts of the permitted block-modified strong-convergence theorem for the same law.

Paper dependencies: II.2, II.3, III.3, III.4, A.1.
