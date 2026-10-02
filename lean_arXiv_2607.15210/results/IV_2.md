# Corollary IV.2: Product-channel bound and Bell entropy expansion

Deduction verified; the block-modified strong-convergence theorem remains an input.

The actual tensor-product/conjugate-channel minimum entropy has limsup at most the explicit Bell-spectrum entropy. The Bell input is proved to be a density matrix, the witness bound and matrix-entropy continuity are proved, and the actual isotropic entropy has the stated expansion with stronger O(k^-4) error, for every p>0 including p=1.

The full unverified input and the Lean progress are stated in [partial_progress/](../partial_progress/README.md).

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

- [BellOutput.RevisionCorollaryIV](../lean/BellOutput/RevisionCorollaryIV.lean)

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
- [lean/BellOutput/RevisionCorollaryIV.lean](../lean/BellOutput/RevisionCorollaryIV.lean)
- [lean/Entropy/Analysis.lean](../lean/Entropy/Analysis.lean)
- [lean/Entropy/BellBounds.lean](../lean/Entropy/BellBounds.lean)
- [lean/Entropy/BellFiniteDifference.lean](../lean/Entropy/BellFiniteDifference.lean)
- [lean/Entropy/BellLimitCoefficients.lean](../lean/Entropy/BellLimitCoefficients.lean)
- [lean/Entropy/BellLimitTransfer.lean](../lean/Entropy/BellLimitTransfer.lean)
- [lean/Entropy/BellMatrixIdentities.lean](../lean/Entropy/BellMatrixIdentities.lean)
- [lean/Entropy/BellOne.lean](../lean/Entropy/BellOne.lean)
- [lean/Entropy/Combinatorics.lean](../lean/Entropy/Combinatorics.lean)
- [lean/Entropy/Defs.lean](../lean/Entropy/Defs.lean)
- [lean/Entropy/Infimum.lean](../lean/Entropy/Infimum.lean)
- [lean/Entropy/Localization.lean](../lean/Entropy/Localization.lean)
- [lean/Entropy/Minimum.lean](../lean/Entropy/Minimum.lean)
- [lean/Entropy/OutputSpace.lean](../lean/Entropy/OutputSpace.lean)
- [lean/Entropy/OutputSpaceBody.lean](../lean/Entropy/OutputSpaceBody.lean)
- [lean/Entropy/RevisionMatrixEntropy.lean](../lean/Entropy/RevisionMatrixEntropy.lean)
- [lean/Entropy/RevisionMatrixEntropyBell.lean](../lean/Entropy/RevisionMatrixEntropyBell.lean)
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

- For fixed k, assumptions of IV.1 and p>0; asymptotic expansion fixed t in (0,1),p>0.

Paper dependencies: IV.1, B.2.

## Python checks

- [verify_entropy.py](../python/entropy/verify_entropy.py)

The exact rational certificate is a certificate of its scalar inequalities; the other numerical checks are cross-checks, not universal proofs.
