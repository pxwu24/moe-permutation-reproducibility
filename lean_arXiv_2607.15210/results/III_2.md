# Corollary III.2: One-copy entropy limit and asymptotics

**Status: Complete under the permitted block-modified strong-convergence input.**

The actual channel minimum Rényi entropy tends almost surely to the attained minimum on the actual output body. Matrix-entropy continuity, the spectral-body image equality, and the large-k expansion (with stronger O(k^-5/2) error) are proved for every fixed p>0, including p=1.

## Check this result

First run `bash lean_arXiv_2607.15210/verify-all.sh` from the repository root. Then, from `lean_arXiv_2607.15210/`, run:

```sh
cat > InspectResult.lean <<'LEAN'
import AllProofs

#check RevisionMatrixEntropy.actual_minimum_output_entropy_limit
#print axioms RevisionMatrixEntropy.actual_minimum_output_entropy_limit
#check RevisionMatrixEntropy.spectralBody_entropy_image
#print axioms RevisionMatrixEntropy.spectralBody_entropy_image
#check AppendixB.single_output_r1_minimum
#print axioms AppendixB.single_output_r1_minimum
LEAN
lake env lean InspectResult.lean
rm InspectResult.lean
```

The displayed hypotheses are part of the checked statement. A theorem conditional on an intermediate assertion does not verify that assertion.

## Entry files

- [RevisionMatrixEntropyBody](../RevisionMatrixEntropyBody.lean)
- [Entropy.Minimum](../entropy/Entropy/Minimum.lean)

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
- [K182Dual.lean](../K182Dual.lean)
- [K182Entropy.lean](../K182Entropy.lean)
- [K182Numerics.lean](../K182Numerics.lean)
- [K182SecondVariation.lean](../K182SecondVariation.lean)
- [K182ShapeCalculus.lean](../K182ShapeCalculus.lean)
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
- [RevisionCoordinateCap.lean](../RevisionCoordinateCap.lean)
- [RevisionEntropyHausdorff.lean](../RevisionEntropyHausdorff.lean)
- [RevisionFullBlockInput.lean](../RevisionFullBlockInput.lean)
- [RevisionK182BirthCurve.lean](../RevisionK182BirthCurve.lean)
- [RevisionK182BoundaryEqual.lean](../RevisionK182BoundaryEqual.lean)
- [RevisionK182BoundaryExclusion.lean](../RevisionK182BoundaryExclusion.lean)
- [RevisionK182BoundaryTools.lean](../RevisionK182BoundaryTools.lean)
- [RevisionK182Compact.lean](../RevisionK182Compact.lean)
- [RevisionK182Curve.lean](../RevisionK182Curve.lean)
- [RevisionK182Descent.lean](../RevisionK182Descent.lean)
- [RevisionK182EntropyMaximum.lean](../RevisionK182EntropyMaximum.lean)
- [RevisionK182Minimizer.lean](../RevisionK182Minimizer.lean)
- [RevisionK182Multiplier.lean](../RevisionK182Multiplier.lean)
- [RevisionK182Nonuniform.lean](../RevisionK182Nonuniform.lean)
- [RevisionK182Normalization.lean](../RevisionK182Normalization.lean)
- [RevisionK182RepeatedHigh.lean](../RevisionK182RepeatedHigh.lean)
- [RevisionK182Stationarity.lean](../RevisionK182Stationarity.lean)
- [RevisionLemmaC1.lean](../RevisionLemmaC1.lean)
- [RevisionMatrixEntropy.lean](../RevisionMatrixEntropy.lean)
- [RevisionMatrixEntropyBody.lean](../RevisionMatrixEntropyBody.lean)
- [RevisionOutputBody.lean](../RevisionOutputBody.lean)
- [RevisionOutputChannel.lean](../RevisionOutputChannel.lean)
- [RevisionOutputContinuousMinimum.lean](../RevisionOutputContinuousMinimum.lean)
- [RevisionOutputConvergence.lean](../RevisionOutputConvergence.lean)
- [RevisionOutputDuality.lean](../RevisionOutputDuality.lean)
- [RevisionOutputEventual.lean](../RevisionOutputEventual.lean)
- [RevisionOutputFunctionals.lean](../RevisionOutputFunctionals.lean)
- [RevisionOutputGeometry.lean](../RevisionOutputGeometry.lean)
- [RevisionOutputLimit.lean](../RevisionOutputLimit.lean)
- [RevisionOutputMetricComparison.lean](../RevisionOutputMetricComparison.lean)
- [RevisionOutputProbability.lean](../RevisionOutputProbability.lean)
- [RevisionOutputStates.lean](../RevisionOutputStates.lean)
- [RevisionOutputTheorem.lean](../RevisionOutputTheorem.lean)
- [RevisionOutputTraceDistance.lean](../RevisionOutputTraceDistance.lean)
- [RevisionOutputTraceGeometry.lean](../RevisionOutputTraceGeometry.lean)
- [RevisionOutputUnitary.lean](../RevisionOutputUnitary.lean)
- [SpectralEdge.lean](../SpectralEdge.lean)

## Assumptions and dependencies

- For fixed k, p>0 and assumptions of III.1; for large k, fixed t in (0,1), p>0.

Paper dependencies: III.1, B.1.

## Python checks

- [verify_entropy.py](../entropy/verify_entropy.py)

The exact rational certificate is a certificate of its scalar inequalities; the other numerical checks are cross-checks, not universal proofs.
