# Proposition VI.1: Certified output dimension 182

**Status: Complete.**

The exact paper inequality 477/10^6 < 2 min_{rho in K_182,t} S1(rho) − S1(Bell spectrum) is proved for the actual matrix output body, with attained minimum. All shape and numerical premises are discharged. It certifies k_high(1)<=182 and does not assert minimality. The accompanying finite-channel theorem derives eventual nonadditivity for the actual product/conjugate channels from the same permitted convergence input.

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

- [RevisionPropositionVI](../RevisionPropositionVI.lean)
- [RevisionMatrixEntropyBody](../RevisionMatrixEntropyBody.lean)
- [RevisionK182Minimizer](../RevisionK182Minimizer.lean)
- [K182Numerics](../K182Numerics.lean)

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
- [entropy/Entropy/BellFiniteDifference.lean](../entropy/Entropy/BellFiniteDifference.lean)
- [entropy/Entropy/BellLimitCoefficients.lean](../entropy/Entropy/BellLimitCoefficients.lean)
- [entropy/Entropy/BellLimitTransfer.lean](../entropy/Entropy/BellLimitTransfer.lean)
- [entropy/Entropy/BellMatrixIdentities.lean](../entropy/Entropy/BellMatrixIdentities.lean)
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
- [ProjectionOrbit.lean](../ProjectionOrbit.lean)
- [ProjectionStrongConvergence.lean](../ProjectionStrongConvergence.lean)
- [RevisionBellAEPPolarization.lean](../RevisionBellAEPPolarization.lean)
- [RevisionBellCentralDerivative.lean](../RevisionBellCentralDerivative.lean)
- [RevisionBellChannel.lean](../RevisionBellChannel.lean)
- [RevisionBellContraction.lean](../RevisionBellContraction.lean)
- [RevisionBellEntropyTransport.lean](../RevisionBellEntropyTransport.lean)
- [RevisionBellFiniteMoments.lean](../RevisionBellFiniteMoments.lean)
- [RevisionBellHessian.lean](../RevisionBellHessian.lean)
- [RevisionBellHessianResult.lean](../RevisionBellHessianResult.lean)
- [RevisionBellImplicit.lean](../RevisionBellImplicit.lean)
- [RevisionBellLimitFromMoments.lean](../RevisionBellLimitFromMoments.lean)
- [RevisionBellLogConvergence.lean](../RevisionBellLogConvergence.lean)
- [RevisionBellLogIdentity.lean](../RevisionBellLogIdentity.lean)
- [RevisionBellLogPotential.lean](../RevisionBellLogPotential.lean)
- [RevisionBellMatrixLog.lean](../RevisionBellMatrixLog.lean)
- [RevisionBellNegativeBranch.lean](../RevisionBellNegativeBranch.lean)
- [RevisionBellNormalizedChoi.lean](../RevisionBellNormalizedChoi.lean)
- [RevisionBellPolarization.lean](../RevisionBellPolarization.lean)
- [RevisionBellPositiveLaw.lean](../RevisionBellPositiveLaw.lean)
- [RevisionBellPrimitive.lean](../RevisionBellPrimitive.lean)
- [RevisionBellQuadraticLimit.lean](../RevisionBellQuadraticLimit.lean)
- [RevisionBellSpectralGap.lean](../RevisionBellSpectralGap.lean)
- [RevisionBellTheorem.lean](../RevisionBellTheorem.lean)
- [RevisionBellTraceConvergence.lean](../RevisionBellTraceConvergence.lean)
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
- [RevisionMatrixEntropyBell.lean](../RevisionMatrixEntropyBell.lean)
- [RevisionMatrixEntropyBody.lean](../RevisionMatrixEntropyBody.lean)
- [RevisionMatrixEntropyConjugate.lean](../RevisionMatrixEntropyConjugate.lean)
- [RevisionMatrixEntropyProjection.lean](../RevisionMatrixEntropyProjection.lean)
- [RevisionMatrixEntropyWitness.lean](../RevisionMatrixEntropyWitness.lean)
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
- [RevisionPropositionVI.lean](../RevisionPropositionVI.lean)
- [RevisionTensorChannels.lean](../RevisionTensorChannels.lean)
- [SpectralEdge.lean](../SpectralEdge.lean)

## Assumptions and dependencies

- k=182, t=27/100000; L=162513/1000000, z=2077/2000 exact rationals.

Paper dependencies: C.1, C.2, IV.1.

## Python checks

- [certify_k182_exact.py](../final_draft_audit/certify_k182_exact.py)

The exact rational certificate is a certificate of its scalar inequalities; the other numerical checks are cross-checks, not universal proofs.
