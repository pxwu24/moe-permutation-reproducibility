# Theorem IV.1: Limit of the Bell output

**Status: Complete under the permitted block-modified strong-convergence input.**

The genuine tensor-product/conjugate-channel Bell output converges almost surely in the matrix operator norm to the explicit isotropic density matrix. Every actual Choi entry, logarithmic potential, second-moment transfer, and polarization step is proved, and the local normalizer is the actual inverse marginal square root with eventual invertibility derived.

## Check this result

First run `bash lean_arXiv_2607.15210/verify-all.sh` from the repository root. Then, from `lean_arXiv_2607.15210/`, run:

```sh
cat > InspectResult.lean <<'LEAN'
import AllProofs

#check RevisionBell.bell_output_limit
#print axioms RevisionBell.bell_output_limit
#check RevisionBell.bell_output_and_purity_limit
#print axioms RevisionBell.bell_output_and_purity_limit
#check RevisionBell.tensor_conjugate_bell_entry
#print axioms RevisionBell.tensor_conjugate_bell_entry
#check BellLimitVerification.bell_spectrum_identities
#print axioms BellLimitVerification.bell_spectrum_identities
#check BellLimitVerification.bell_spectrum_positive
#print axioms BellLimitVerification.bell_spectrum_positive
LEAN
lake env lean InspectResult.lean
rm InspectResult.lean
```

The displayed hypotheses are part of the checked statement. A theorem conditional on an intermediate assertion does not verify that assertion.

## Entry files

- [RevisionBellTheorem](../RevisionBellTheorem.lean)

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
- [OutputSpaceCompressionBridge.lean](../OutputSpaceCompressionBridge.lean)
- [OutputSpaceMatrix.lean](../OutputSpaceMatrix.lean)
- [PreliminariesAnalysis.lean](../PreliminariesAnalysis.lean)
- [PreliminariesChoi.lean](../PreliminariesChoi.lean)
- [PreliminariesLegendre.lean](../PreliminariesLegendre.lean)
- [PreliminariesMatrix.lean](../PreliminariesMatrix.lean)
- [ProjectionStrongConvergence.lean](../ProjectionStrongConvergence.lean)
- [RevisionBellAEPPolarization.lean](../RevisionBellAEPPolarization.lean)
- [RevisionBellCentralDerivative.lean](../RevisionBellCentralDerivative.lean)
- [RevisionBellChannel.lean](../RevisionBellChannel.lean)
- [RevisionBellContraction.lean](../RevisionBellContraction.lean)
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

- Fixed k>=2, t in (1/k^2,1), Haar projections with rank density tending to t.

Paper dependencies: A.3.

## Python checks

- [verify_bell_limit.py](../final_draft_audit/verify_bell_limit.py)

The exact rational certificate is a certificate of its scalar inequalities; the other numerical checks are cross-checks, not universal proofs.
