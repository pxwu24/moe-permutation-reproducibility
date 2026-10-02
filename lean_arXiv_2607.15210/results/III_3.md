# Lemma III.3: Support-function formula for trace-norm Hausdorff distance

**Status: Complete.**

Exact trace-norm Hausdorff distance equals the supremum of support-function differences over the Hermitian operator-norm unit ball. Trace/operator duality is attained by explicit spectral witnesses; compact trace balls and the separation argument are proved.

## Check this result

First run `bash lean_arXiv_2607.15210/verify-all.sh` from the repository root. Then, from `lean_arXiv_2607.15210/`, run:

```sh
cat > InspectResult.lean <<'LEAN'
import AllProofs

#check RevisionOutput.traceHausdorff_eq_matrixSupportDistance
#print axioms RevisionOutput.traceHausdorff_eq_matrixSupportDistance
#check RevisionOutput.trace_operator_duality_named
#print axioms RevisionOutput.trace_operator_duality_named
#check RevisionOutput.density_opNorm_witness
#print axioms RevisionOutput.density_opNorm_witness
LEAN
lake env lean InspectResult.lean
rm InspectResult.lean
```

The displayed hypotheses are part of the checked statement. A theorem conditional on an intermediate assertion does not verify that assertion.

## Entry files

- [RevisionOutputHausdorff](../RevisionOutputHausdorff.lean)

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
- [RevisionBellContraction.lean](../RevisionBellContraction.lean)
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
- [RevisionOutputHausdorff.lean](../RevisionOutputHausdorff.lean)
- [RevisionOutputLimit.lean](../RevisionOutputLimit.lean)
- [RevisionOutputMetricComparison.lean](../RevisionOutputMetricComparison.lean)
- [RevisionOutputProbability.lean](../RevisionOutputProbability.lean)
- [RevisionOutputStates.lean](../RevisionOutputStates.lean)
- [RevisionOutputTheorem.lean](../RevisionOutputTheorem.lean)
- [RevisionOutputTraceBalls.lean](../RevisionOutputTraceBalls.lean)
- [RevisionOutputTraceDistance.lean](../RevisionOutputTraceDistance.lean)
- [RevisionOutputTraceGeometry.lean](../RevisionOutputTraceGeometry.lean)
- [RevisionOutputUnitary.lean](../RevisionOutputUnitary.lean)
- [RevisionTraceDuality.lean](../RevisionTraceDuality.lean)
- [SpectralEdge.lean](../SpectralEdge.lean)

## Assumptions and dependencies

- Nonempty compact convex sets C,K of Hermitian k-by-k matrices. The PDF omits nonemptiness and should add it.
