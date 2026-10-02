# Corollary III.2: One-copy entropy limit and asymptotics

Deduction verified; the block-modified strong-convergence theorem remains an input.

The actual channel minimum Rényi entropy tends almost surely to the attained minimum on the actual output body. Matrix-entropy continuity, the spectral-body image equality, and the large-k expansion (with stronger O(k^-5/2) error) are proved for every fixed p>0, including p=1.

The full unverified input and the Lean progress are stated in [partial_progress/](../partial_progress/README.md).

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

- [Entropy.RevisionMatrixEntropyBody](../lean/Entropy/RevisionMatrixEntropyBody.lean)
- [Entropy.Minimum](../lean/Entropy/Minimum.lean)

## All related Lean files

This is the complete transitive local import closure of the entry files. Mathlib dependencies are pinned in `lake-manifest.json`.

- [lean/Dimension182/K182Dual.lean](../lean/Dimension182/K182Dual.lean)
- [lean/Dimension182/K182Entropy.lean](../lean/Dimension182/K182Entropy.lean)
- [lean/Dimension182/K182Numerics.lean](../lean/Dimension182/K182Numerics.lean)
- [lean/Dimension182/K182SecondVariation.lean](../lean/Dimension182/K182SecondVariation.lean)
- [lean/Dimension182/K182ShapeCalculus.lean](../lean/Dimension182/K182ShapeCalculus.lean)
- [lean/Dimension182/RevisionCoordinateCap.lean](../lean/Dimension182/RevisionCoordinateCap.lean)
- [lean/Dimension182/RevisionK182BirthCurve.lean](../lean/Dimension182/RevisionK182BirthCurve.lean)
- [lean/Dimension182/RevisionK182BoundaryEqual.lean](../lean/Dimension182/RevisionK182BoundaryEqual.lean)
- [lean/Dimension182/RevisionK182BoundaryExclusion.lean](../lean/Dimension182/RevisionK182BoundaryExclusion.lean)
- [lean/Dimension182/RevisionK182BoundaryTools.lean](../lean/Dimension182/RevisionK182BoundaryTools.lean)
- [lean/Dimension182/RevisionK182Compact.lean](../lean/Dimension182/RevisionK182Compact.lean)
- [lean/Dimension182/RevisionK182Curve.lean](../lean/Dimension182/RevisionK182Curve.lean)
- [lean/Dimension182/RevisionK182Descent.lean](../lean/Dimension182/RevisionK182Descent.lean)
- [lean/Dimension182/RevisionK182EntropyMaximum.lean](../lean/Dimension182/RevisionK182EntropyMaximum.lean)
- [lean/Dimension182/RevisionK182Minimizer.lean](../lean/Dimension182/RevisionK182Minimizer.lean)
- [lean/Dimension182/RevisionK182Multiplier.lean](../lean/Dimension182/RevisionK182Multiplier.lean)
- [lean/Dimension182/RevisionK182Nonuniform.lean](../lean/Dimension182/RevisionK182Nonuniform.lean)
- [lean/Dimension182/RevisionK182Normalization.lean](../lean/Dimension182/RevisionK182Normalization.lean)
- [lean/Dimension182/RevisionK182RepeatedHigh.lean](../lean/Dimension182/RevisionK182RepeatedHigh.lean)
- [lean/Dimension182/RevisionK182Stationarity.lean](../lean/Dimension182/RevisionK182Stationarity.lean)
- [lean/Dimension182/RevisionLemmaC1.lean](../lean/Dimension182/RevisionLemmaC1.lean)
- [lean/Entropy/Analysis.lean](../lean/Entropy/Analysis.lean)
- [lean/Entropy/Combinatorics.lean](../lean/Entropy/Combinatorics.lean)
- [lean/Entropy/Defs.lean](../lean/Entropy/Defs.lean)
- [lean/Entropy/Infimum.lean](../lean/Entropy/Infimum.lean)
- [lean/Entropy/Localization.lean](../lean/Entropy/Localization.lean)
- [lean/Entropy/Minimum.lean](../lean/Entropy/Minimum.lean)
- [lean/Entropy/OutputSpace.lean](../lean/Entropy/OutputSpace.lean)
- [lean/Entropy/OutputSpaceBody.lean](../lean/Entropy/OutputSpaceBody.lean)
- [lean/Entropy/RevisionMatrixEntropy.lean](../lean/Entropy/RevisionMatrixEntropy.lean)
- [lean/Entropy/RevisionMatrixEntropyBody.lean](../lean/Entropy/RevisionMatrixEntropyBody.lean)
- [lean/Entropy/Single.lean](../lean/Entropy/Single.lean)
- [lean/Entropy/Spike.lean](../lean/Entropy/Spike.lean)
- [lean/Entropy/SpikeArithmetic.lean](../lean/Entropy/SpikeArithmetic.lean)
- [lean/HaarProjections/HaarMeasure.lean](../lean/HaarProjections/HaarMeasure.lean)
- [lean/HaarProjections/HaarProjection.lean](../lean/HaarProjections/HaarProjection.lean)
- [lean/OutputStates/OutputSpaceCompressionBridge.lean](../lean/OutputStates/OutputSpaceCompressionBridge.lean)
- [lean/OutputStates/OutputSpaceMatrix.lean](../lean/OutputStates/OutputSpaceMatrix.lean)
- [lean/OutputStates/RevisionEntropyHausdorff.lean](../lean/OutputStates/RevisionEntropyHausdorff.lean)
- [lean/OutputStates/RevisionOutputBody.lean](../lean/OutputStates/RevisionOutputBody.lean)
- [lean/OutputStates/RevisionOutputChannel.lean](../lean/OutputStates/RevisionOutputChannel.lean)
- [lean/OutputStates/RevisionOutputContinuousMinimum.lean](../lean/OutputStates/RevisionOutputContinuousMinimum.lean)
- [lean/OutputStates/RevisionOutputConvergence.lean](../lean/OutputStates/RevisionOutputConvergence.lean)
- [lean/OutputStates/RevisionOutputDuality.lean](../lean/OutputStates/RevisionOutputDuality.lean)
- [lean/OutputStates/RevisionOutputEventual.lean](../lean/OutputStates/RevisionOutputEventual.lean)
- [lean/OutputStates/RevisionOutputFunctionals.lean](../lean/OutputStates/RevisionOutputFunctionals.lean)
- [lean/OutputStates/RevisionOutputGeometry.lean](../lean/OutputStates/RevisionOutputGeometry.lean)
- [lean/OutputStates/RevisionOutputLimit.lean](../lean/OutputStates/RevisionOutputLimit.lean)
- [lean/OutputStates/RevisionOutputMetricComparison.lean](../lean/OutputStates/RevisionOutputMetricComparison.lean)
- [lean/OutputStates/RevisionOutputProbability.lean](../lean/OutputStates/RevisionOutputProbability.lean)
- [lean/OutputStates/RevisionOutputStates.lean](../lean/OutputStates/RevisionOutputStates.lean)
- [lean/OutputStates/RevisionOutputTheorem.lean](../lean/OutputStates/RevisionOutputTheorem.lean)
- [lean/OutputStates/RevisionOutputTraceDistance.lean](../lean/OutputStates/RevisionOutputTraceDistance.lean)
- [lean/OutputStates/RevisionOutputTraceGeometry.lean](../lean/OutputStates/RevisionOutputTraceGeometry.lean)
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

- For fixed k, p>0 and assumptions of III.1; for large k, fixed t in (0,1), p>0.

Paper dependencies: III.1, B.1.

## Python checks

- [verify_entropy.py](../python/entropy/verify_entropy.py)

The exact rational certificate is a certificate of its scalar inequalities; the other numerical checks are cross-checks, not universal proofs.
