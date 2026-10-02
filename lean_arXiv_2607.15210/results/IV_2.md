# Corollary IV.2: Product-channel bound and Bell entropy expansion

**Status: Complete under the permitted block-modified strong-convergence input.**

The actual tensor-product/conjugate-channel minimum entropy has limsup at most the explicit Bell-spectrum entropy. The Bell input is proved to be a density matrix, the witness bound and matrix-entropy continuity are proved, and the actual isotropic entropy has the stated expansion with stronger O(k^-4) error, for every p>0 including p=1.

## Check this result

First run `bash lean_arXiv_2607.15210/verify-all.sh` from the repository root. Then, from `lean_arXiv_2607.15210/`, run:

```sh
cat > InspectResult.lean <<'LEAN'
import AllProofs

#check RevisionMatrixEntropy.corollary_IV_2_fixed_k
#print axioms RevisionMatrixEntropy.corollary_IV_2_fixed_k
#check RevisionMatrixEntropy.isotropic_entropy_eq_bell_spectrum
#print axioms RevisionMatrixEntropy.isotropic_entropy_eq_bell_spectrum
#check RevisionMatrixEntropy.corollary_IV_2_asymptotics
#print axioms RevisionMatrixEntropy.corollary_IV_2_asymptotics
LEAN
lake env lean InspectResult.lean
rm InspectResult.lean
```

The displayed hypotheses are part of the checked statement. A theorem conditional on an intermediate assertion does not verify that assertion.

## Entry files

- [RevisionCorollaryIV](../RevisionCorollaryIV.lean)

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
- [entropy/Entropy/BellBounds.lean](../entropy/Entropy/BellBounds.lean)
- [entropy/Entropy/BellFiniteDifference.lean](../entropy/Entropy/BellFiniteDifference.lean)
- [entropy/Entropy/BellLimitCoefficients.lean](../entropy/Entropy/BellLimitCoefficients.lean)
- [entropy/Entropy/BellLimitTransfer.lean](../entropy/Entropy/BellLimitTransfer.lean)
- [entropy/Entropy/BellMatrixIdentities.lean](../entropy/Entropy/BellMatrixIdentities.lean)
- [entropy/Entropy/BellOne.lean](../entropy/Entropy/BellOne.lean)
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
- [RevisionCorollaryIV.lean](../RevisionCorollaryIV.lean)
- [RevisionFullBlockInput.lean](../RevisionFullBlockInput.lean)
- [RevisionMatrixEntropy.lean](../RevisionMatrixEntropy.lean)
- [RevisionMatrixEntropyBell.lean](../RevisionMatrixEntropyBell.lean)
- [RevisionMatrixEntropyConjugate.lean](../RevisionMatrixEntropyConjugate.lean)
- [RevisionMatrixEntropyProjection.lean](../RevisionMatrixEntropyProjection.lean)
- [RevisionMatrixEntropyWitness.lean](../RevisionMatrixEntropyWitness.lean)
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
- [RevisionTensorChannels.lean](../RevisionTensorChannels.lean)
- [SpectralEdge.lean](../SpectralEdge.lean)

## Assumptions and dependencies

- For fixed k, assumptions of IV.1 and p>0; asymptotic expansion fixed t in (0,1),p>0.

Paper dependencies: IV.1, B.2.

## Python checks

- [verify_entropy.py](../entropy/verify_entropy.py)

The exact rational certificate is a certificate of its scalar inequalities; the other numerical checks are cross-checks, not universal proofs.
