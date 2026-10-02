# Proposition VI.1: Certified output dimension 182

Deduction verified; the block-modified strong-convergence theorem remains an input.

The exact paper inequality 477/10^6 < 2 min_{rho in K_182,t} S1(rho) − S1(Bell spectrum) is proved for the actual matrix output body, with attained minimum. All shape and numerical premises are discharged. It certifies k_high(1)<=182 and does not assert minimality. The accompanying finite-channel theorem derives eventual nonadditivity for the actual product/conjugate channels from the same permitted convergence input.

The full unverified input and the Lean progress are stated in [partial_progress/](../partial_progress/README.md).

## Check this result

First run `bash lean_arXiv_2607.15210/verify-all.sh` from the repository root. Then, from `lean_arXiv_2607.15210/`, run:

```sh
cat > InspectResult.lean <<'LEAN'
import AllProofs

#check RevisionMatrixEntropy.proposition_VI_1
#print axioms RevisionMatrixEntropy.proposition_VI_1
#check RevisionMatrixEntropy.proposition_VI_1_body
#print axioms RevisionMatrixEntropy.proposition_VI_1_body
#check RevisionMatrixEntropy.eventual_nonadditivity_182
#print axioms RevisionMatrixEntropy.eventual_nonadditivity_182
#check ProjectionChannels.RevisionK182.certified_entropy_gap_182
#print axioms ProjectionChannels.RevisionK182.certified_entropy_gap_182
#check ProjectionChannels.K182.certified_entropy_gap
#print axioms ProjectionChannels.K182.certified_entropy_gap
LEAN
lake env lean InspectResult.lean
rm InspectResult.lean
```

The displayed hypotheses are part of the checked statement. A theorem conditional on an intermediate assertion does not verify that assertion.

## Entry files

- [Dimension182.RevisionPropositionVI](../lean/Dimension182/RevisionPropositionVI.lean)
- [Entropy.RevisionMatrixEntropyBody](../lean/Entropy/RevisionMatrixEntropyBody.lean)
- [Dimension182.RevisionK182Minimizer](../lean/Dimension182/RevisionK182Minimizer.lean)
- [Dimension182.K182Numerics](../lean/Dimension182/K182Numerics.lean)

## All related Lean files

This is the complete transitive local import closure of the entry files. Mathlib dependencies are pinned in `lake-manifest.json`.

- [lean/BellOutput/RevisionBellAEPPolarization.lean](../lean/BellOutput/RevisionBellAEPPolarization.lean)
- [lean/BellOutput/RevisionBellCentralDerivative.lean](../lean/BellOutput/RevisionBellCentralDerivative.lean)
- [lean/BellOutput/RevisionBellChannel.lean](../lean/BellOutput/RevisionBellChannel.lean)
- [lean/BellOutput/RevisionBellContraction.lean](../lean/BellOutput/RevisionBellContraction.lean)
- [lean/BellOutput/RevisionBellEntropyTransport.lean](../lean/BellOutput/RevisionBellEntropyTransport.lean)
- [lean/BellOutput/RevisionBellFiniteMoments.lean](../lean/BellOutput/RevisionBellFiniteMoments.lean)
- [lean/BellOutput/RevisionBellHessian.lean](../lean/BellOutput/RevisionBellHessian.lean)
- [lean/BellOutput/RevisionBellHessianResult.lean](../lean/BellOutput/RevisionBellHessianResult.lean)
- [lean/BellOutput/RevisionBellImplicit.lean](../lean/BellOutput/RevisionBellImplicit.lean)
- [lean/BellOutput/RevisionBellLimitFromMoments.lean](../lean/BellOutput/RevisionBellLimitFromMoments.lean)
- [lean/BellOutput/RevisionBellLogConvergence.lean](../lean/BellOutput/RevisionBellLogConvergence.lean)
- [lean/BellOutput/RevisionBellLogIdentity.lean](../lean/BellOutput/RevisionBellLogIdentity.lean)
- [lean/BellOutput/RevisionBellLogPotential.lean](../lean/BellOutput/RevisionBellLogPotential.lean)
- [lean/BellOutput/RevisionBellMatrixLog.lean](../lean/BellOutput/RevisionBellMatrixLog.lean)
- [lean/BellOutput/RevisionBellNegativeBranch.lean](../lean/BellOutput/RevisionBellNegativeBranch.lean)
- [lean/BellOutput/RevisionBellNormalizedChoi.lean](../lean/BellOutput/RevisionBellNormalizedChoi.lean)
- [lean/BellOutput/RevisionBellPolarization.lean](../lean/BellOutput/RevisionBellPolarization.lean)
- [lean/BellOutput/RevisionBellPositiveLaw.lean](../lean/BellOutput/RevisionBellPositiveLaw.lean)
- [lean/BellOutput/RevisionBellPrimitive.lean](../lean/BellOutput/RevisionBellPrimitive.lean)
- [lean/BellOutput/RevisionBellQuadraticLimit.lean](../lean/BellOutput/RevisionBellQuadraticLimit.lean)
- [lean/BellOutput/RevisionBellSpectralGap.lean](../lean/BellOutput/RevisionBellSpectralGap.lean)
- [lean/BellOutput/RevisionBellTheorem.lean](../lean/BellOutput/RevisionBellTheorem.lean)
- [lean/BellOutput/RevisionBellTraceConvergence.lean](../lean/BellOutput/RevisionBellTraceConvergence.lean)
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
- [lean/Dimension182/RevisionPropositionVI.lean](../lean/Dimension182/RevisionPropositionVI.lean)
- [lean/Entropy/Analysis.lean](../lean/Entropy/Analysis.lean)
- [lean/Entropy/BellFiniteDifference.lean](../lean/Entropy/BellFiniteDifference.lean)
- [lean/Entropy/BellLimitCoefficients.lean](../lean/Entropy/BellLimitCoefficients.lean)
- [lean/Entropy/BellLimitTransfer.lean](../lean/Entropy/BellLimitTransfer.lean)
- [lean/Entropy/BellMatrixIdentities.lean](../lean/Entropy/BellMatrixIdentities.lean)
- [lean/Entropy/Combinatorics.lean](../lean/Entropy/Combinatorics.lean)
- [lean/Entropy/Defs.lean](../lean/Entropy/Defs.lean)
- [lean/Entropy/Infimum.lean](../lean/Entropy/Infimum.lean)
- [lean/Entropy/Localization.lean](../lean/Entropy/Localization.lean)
- [lean/Entropy/Minimum.lean](../lean/Entropy/Minimum.lean)
- [lean/Entropy/OutputSpace.lean](../lean/Entropy/OutputSpace.lean)
- [lean/Entropy/OutputSpaceBody.lean](../lean/Entropy/OutputSpaceBody.lean)
- [lean/Entropy/RevisionMatrixEntropy.lean](../lean/Entropy/RevisionMatrixEntropy.lean)
- [lean/Entropy/RevisionMatrixEntropyBell.lean](../lean/Entropy/RevisionMatrixEntropyBell.lean)
- [lean/Entropy/RevisionMatrixEntropyBody.lean](../lean/Entropy/RevisionMatrixEntropyBody.lean)
- [lean/Entropy/RevisionMatrixEntropyConjugate.lean](../lean/Entropy/RevisionMatrixEntropyConjugate.lean)
- [lean/Entropy/RevisionMatrixEntropyProjection.lean](../lean/Entropy/RevisionMatrixEntropyProjection.lean)
- [lean/Entropy/RevisionMatrixEntropyWitness.lean](../lean/Entropy/RevisionMatrixEntropyWitness.lean)
- [lean/Entropy/Single.lean](../lean/Entropy/Single.lean)
- [lean/Entropy/Spike.lean](../lean/Entropy/Spike.lean)
- [lean/Entropy/SpikeArithmetic.lean](../lean/Entropy/SpikeArithmetic.lean)
- [lean/HaarProjections/HaarMeasure.lean](../lean/HaarProjections/HaarMeasure.lean)
- [lean/HaarProjections/HaarProjection.lean](../lean/HaarProjections/HaarProjection.lean)
- [lean/HaarProjections/ProjectionOrbit.lean](../lean/HaarProjections/ProjectionOrbit.lean)
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
- [lean/Preliminaries/RevisionTensorChannels.lean](../lean/Preliminaries/RevisionTensorChannels.lean)
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

- k=182, t=27/100000; L=162513/1000000, z=2077/2000 exact rationals.

Paper dependencies: C.1, C.2, IV.1.

## Python checks

- [certify_k182_exact.py](../python/dimension_182/certify_k182_exact.py)

The exact rational certificate is a certificate of its scalar inequalities; the other numerical checks are cross-checks, not universal proofs.
