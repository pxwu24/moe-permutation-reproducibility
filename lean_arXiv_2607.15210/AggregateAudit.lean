import AllProofs
import BernoulliCalculus
import BernoulliCriticalPoint
import BernoulliDuality
import BernoulliEdgeCalculus
import BlockModification
import CauchyBernoulli
import CauchyHolomorphic
import CauchyHolomorphy
import CauchyLocalInverse
import CompletePositivity
import CompressionEndpointAudit
import CompressionEndpointGlue
import CompressionExtension
import CompressionSpectral
import Entropy
import Entropy.Analysis
import Entropy.Bell
import Entropy.BellBounds
import Entropy.BellFiniteDifference
import Entropy.BellGeneral
import Entropy.BellLimitCoefficients
import Entropy.BellLimitTransfer
import Entropy.BellMatrixIdentities
import Entropy.BellOne
import Entropy.Combinatorics
import Entropy.Defs
import Entropy.Infimum
import Entropy.Localization
import Entropy.MainCoefficient
import Entropy.MainSpectral
import Entropy.Minimum
import Entropy.OutputSpace
import Entropy.OutputSpaceBody
import Entropy.Single
import Entropy.Spike
import Entropy.SpikeArithmetic
import FinalAudit
import FullAudit
import GaussianMatrixLaw
import GaussianRadial
import GaussianRank
import GaussianUnitary
import GaussianWhitening
import HaarFullLocalSupport
import HaarLocalSupport
import HaarMeasure
import HaarOrbitUnique
import HaarProjection
import K182Audit
import K182Dual
import K182Entropy
import K182Numerics
import K182SecondVariation
import K182ShapeCalculus
import MatrixRankMeasurable
import OutputSpaceCompressionBridge
import OutputSpaceCompressionBridgeAudit
import OutputSpaceMatrix
import OutputSpaceMatrixAudit
import PaperFormalization
import Preliminaries
import PreliminariesAnalysis
import PreliminariesChoi
import PreliminariesLegendre
import PreliminariesMatrix
import ProjectionOrbit
import ProjectionStrongConvergence
import ResultChecks
import RevisionAntisymmetric
import RevisionAntisymmetricAudit
import RevisionAntisymmetricBasis
import RevisionAntisymmetricBellBridge
import RevisionAntisymmetricBellEntropy
import RevisionAntisymmetricBellOperators
import RevisionAntisymmetricChannel
import RevisionAntisymmetricCoordinates
import RevisionAntisymmetricEntropy
import RevisionAntisymmetricEntropyAudit
import RevisionAntisymmetricLadder
import RevisionAntisymmetricLegMatrix
import RevisionAntisymmetricMatrixRecursion
import RevisionAntisymmetricNesting
import RevisionAntisymmetricOrthonormal
import RevisionAntisymmetricPartialTrace
import RevisionAntisymmetricProjection
import RevisionAntisymmetricRecursion
import RevisionAntisymmetricShuffling
import RevisionAntisymmetricSwap
import RevisionAntisymmetricTransport
import RevisionAntisymmetricUnitary
import RevisionAntisymmetricWeightedBell
import RevisionBellAEPPolarization
import RevisionBellAudit
import RevisionBellCentralDerivative
import RevisionBellChannel
import RevisionBellContraction
import RevisionBellEntropyTransport
import RevisionBellFiniteMoments
import RevisionBellHessian
import RevisionBellHessianAudit
import RevisionBellHessianResult
import RevisionBellImplicit
import RevisionBellLimitFromMoments
import RevisionBellLogConvergence
import RevisionBellLogIdentity
import RevisionBellLogPotential
import RevisionBellMatrixLog
import RevisionBellNegativeBranch
import RevisionBellNormalizedChoi
import RevisionBellPolarization
import RevisionBellPositiveLaw
import RevisionBellPrimitive
import RevisionBellQuadraticLimit
import RevisionBellSpectralGap
import RevisionBellTheorem
import RevisionBellTraceConvergence
import RevisionBernoulliAudit
import RevisionBernoulliCauchy
import RevisionBernoulliCompression
import RevisionBernoulliEdge
import RevisionBernoulliHolomorphic
import RevisionBernoulliLaw
import RevisionBernoulliTensor
import RevisionCanonicalEnsemble
import RevisionCoordinateCap
import RevisionCorollaryIV
import RevisionEntropyHausdorff
import RevisionEntropyTheoremV
import RevisionFullBlockInput
import RevisionGramLadder
import RevisionGramSpectrum
import RevisionHermitianMultiplicity
import RevisionK182BirthCurve
import RevisionK182BoundaryEqual
import RevisionK182BoundaryExclusion
import RevisionK182BoundaryTools
import RevisionK182Compact
import RevisionK182Curve
import RevisionK182Descent
import RevisionK182EntropyMaximum
import RevisionK182Minimizer
import RevisionK182Multiplier
import RevisionK182Nonuniform
import RevisionK182Normalization
import RevisionK182RepeatedHigh
import RevisionK182Stationarity
import RevisionKrausVectorization
import RevisionLemmaC1
import RevisionMainAudit
import RevisionMainExistence
import RevisionMainNonadditivity
import RevisionMainTheorem
import RevisionMatrixEntropy
import RevisionMatrixEntropyAudit
import RevisionMatrixEntropyBell
import RevisionMatrixEntropyBody
import RevisionMatrixEntropyConjugate
import RevisionMatrixEntropyProjection
import RevisionMatrixEntropyWitness
import RevisionOutputAudit
import RevisionOutputBody
import RevisionOutputChannel
import RevisionOutputContinuousMinimum
import RevisionOutputConvergence
import RevisionOutputDuality
import RevisionOutputEventual
import RevisionOutputFunctionals
import RevisionOutputGeometry
import RevisionOutputHausdorff
import RevisionOutputLimit
import RevisionOutputMetricComparison
import RevisionOutputProbability
import RevisionOutputStates
import RevisionOutputTheorem
import RevisionOutputTraceBalls
import RevisionOutputTraceDistance
import RevisionOutputTraceGeometry
import RevisionOutputUnitary
import RevisionPostprocessTensor
import RevisionPostprocessedBellLimit
import RevisionPostprocessingTransport
import RevisionPropositionVI
import RevisionScalarCertificate
import RevisionSlaterGramCoordinates
import RevisionSlaterLadderCoordinates
import RevisionSlaterReduction
import RevisionSlaterSpectrum
import RevisionSlaterWeightedLadder
import RevisionTensorChannels
import RevisionTensorComposition
import RevisionTraceDuality
import SpectralEdge
import SuppliedBernoulliEdge
import UnprovedTargets
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0

open Lean in
run_elab do
  let projectModules : Array Name := #[`AllProofs, `BernoulliCalculus, `BernoulliCriticalPoint, `BernoulliDuality, `BernoulliEdgeCalculus, `BlockModification, `CauchyBernoulli, `CauchyHolomorphic, `CauchyHolomorphy, `CauchyLocalInverse, `CompletePositivity, `CompressionEndpointAudit, `CompressionEndpointGlue, `CompressionExtension, `CompressionSpectral, `Entropy, `Entropy.Analysis, `Entropy.Bell, `Entropy.BellBounds, `Entropy.BellFiniteDifference, `Entropy.BellGeneral, `Entropy.BellLimitCoefficients, `Entropy.BellLimitTransfer, `Entropy.BellMatrixIdentities, `Entropy.BellOne, `Entropy.Combinatorics, `Entropy.Defs, `Entropy.Infimum, `Entropy.Localization, `Entropy.MainCoefficient, `Entropy.MainSpectral, `Entropy.Minimum, `Entropy.OutputSpace, `Entropy.OutputSpaceBody, `Entropy.Single, `Entropy.Spike, `Entropy.SpikeArithmetic, `FinalAudit, `FullAudit, `GaussianMatrixLaw, `GaussianRadial, `GaussianRank, `GaussianUnitary, `GaussianWhitening, `HaarFullLocalSupport, `HaarLocalSupport, `HaarMeasure, `HaarOrbitUnique, `HaarProjection, `K182Audit, `K182Dual, `K182Entropy, `K182Numerics, `K182SecondVariation, `K182ShapeCalculus, `MatrixRankMeasurable, `OutputSpaceCompressionBridge, `OutputSpaceCompressionBridgeAudit, `OutputSpaceMatrix, `OutputSpaceMatrixAudit, `PaperFormalization, `Preliminaries, `PreliminariesAnalysis, `PreliminariesChoi, `PreliminariesLegendre, `PreliminariesMatrix, `ProjectionOrbit, `ProjectionStrongConvergence, `ResultChecks, `RevisionAntisymmetric, `RevisionAntisymmetricAudit, `RevisionAntisymmetricBasis, `RevisionAntisymmetricBellBridge, `RevisionAntisymmetricBellEntropy, `RevisionAntisymmetricBellOperators, `RevisionAntisymmetricChannel, `RevisionAntisymmetricCoordinates, `RevisionAntisymmetricEntropy, `RevisionAntisymmetricEntropyAudit, `RevisionAntisymmetricLadder, `RevisionAntisymmetricLegMatrix, `RevisionAntisymmetricMatrixRecursion, `RevisionAntisymmetricNesting, `RevisionAntisymmetricOrthonormal, `RevisionAntisymmetricPartialTrace, `RevisionAntisymmetricProjection, `RevisionAntisymmetricRecursion, `RevisionAntisymmetricShuffling, `RevisionAntisymmetricSwap, `RevisionAntisymmetricTransport, `RevisionAntisymmetricUnitary, `RevisionAntisymmetricWeightedBell, `RevisionBellAEPPolarization, `RevisionBellAudit, `RevisionBellCentralDerivative, `RevisionBellChannel, `RevisionBellContraction, `RevisionBellEntropyTransport, `RevisionBellFiniteMoments, `RevisionBellHessian, `RevisionBellHessianAudit, `RevisionBellHessianResult, `RevisionBellImplicit, `RevisionBellLimitFromMoments, `RevisionBellLogConvergence, `RevisionBellLogIdentity, `RevisionBellLogPotential, `RevisionBellMatrixLog, `RevisionBellNegativeBranch, `RevisionBellNormalizedChoi, `RevisionBellPolarization, `RevisionBellPositiveLaw, `RevisionBellPrimitive, `RevisionBellQuadraticLimit, `RevisionBellSpectralGap, `RevisionBellTheorem, `RevisionBellTraceConvergence, `RevisionBernoulliAudit, `RevisionBernoulliCauchy, `RevisionBernoulliCompression, `RevisionBernoulliEdge, `RevisionBernoulliHolomorphic, `RevisionBernoulliLaw, `RevisionBernoulliTensor, `RevisionCanonicalEnsemble, `RevisionCoordinateCap, `RevisionCorollaryIV, `RevisionEntropyHausdorff, `RevisionEntropyTheoremV, `RevisionFullBlockInput, `RevisionGramLadder, `RevisionGramSpectrum, `RevisionHermitianMultiplicity, `RevisionK182BirthCurve, `RevisionK182BoundaryEqual, `RevisionK182BoundaryExclusion, `RevisionK182BoundaryTools, `RevisionK182Compact, `RevisionK182Curve, `RevisionK182Descent, `RevisionK182EntropyMaximum, `RevisionK182Minimizer, `RevisionK182Multiplier, `RevisionK182Nonuniform, `RevisionK182Normalization, `RevisionK182RepeatedHigh, `RevisionK182Stationarity, `RevisionKrausVectorization, `RevisionLemmaC1, `RevisionMainAudit, `RevisionMainExistence, `RevisionMainNonadditivity, `RevisionMainTheorem, `RevisionMatrixEntropy, `RevisionMatrixEntropyAudit, `RevisionMatrixEntropyBell, `RevisionMatrixEntropyBody, `RevisionMatrixEntropyConjugate, `RevisionMatrixEntropyProjection, `RevisionMatrixEntropyWitness, `RevisionOutputAudit, `RevisionOutputBody, `RevisionOutputChannel, `RevisionOutputContinuousMinimum, `RevisionOutputConvergence, `RevisionOutputDuality, `RevisionOutputEventual, `RevisionOutputFunctionals, `RevisionOutputGeometry, `RevisionOutputHausdorff, `RevisionOutputLimit, `RevisionOutputMetricComparison, `RevisionOutputProbability, `RevisionOutputStates, `RevisionOutputTheorem, `RevisionOutputTraceBalls, `RevisionOutputTraceDistance, `RevisionOutputTraceGeometry, `RevisionOutputUnitary, `RevisionPostprocessTensor, `RevisionPostprocessedBellLimit, `RevisionPostprocessingTransport, `RevisionPropositionVI, `RevisionScalarCertificate, `RevisionSlaterGramCoordinates, `RevisionSlaterLadderCoordinates, `RevisionSlaterReduction, `RevisionSlaterSpectrum, `RevisionSlaterWeightedLadder, `RevisionTensorChannels, `RevisionTensorComposition, `RevisionTraceDuality, `SpectralEdge, `SuppliedBernoulliEdge, `UnprovedTargets]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let mut names : Array Name := #[]
  let mut logicalAxioms : Array Name := #[]
  let mut theorems : Nat := 0
  for (name, ci) in env.constants.toList do
    if let some mi := env.getModuleIdxFor? name then
      if projectModules.contains env.allImportedModuleNames[mi.toNat]! then
        if ci.isTheorem then
          theorems := theorems + 1
        if let .axiomInfo v := ci then
          if !v.isUnsafe then
            logicalAxioms := logicalAxioms.push name
        if !ci.isUnsafe then
          names := names.push name
  names := names.qsort Name.lt
  for name in names do
    logInfo m!"AUDIT_DECLARATION {name}"
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  let axioms := state.axioms.qsort Name.lt
  logInfo m!"TRANSITIVE AXIOMS: {axioms.toList}"
  logInfo m!"PROJECT LOGICAL AXIOMS: {logicalAxioms.toList}"
  logInfo m!"AUDITED DECLARATIONS: {names.size}"
  logInfo m!"AUDITED THEOREMS: {theorems}"
  if !logicalAxioms.isEmpty || axioms.any (fun a => !allowed.contains a) then
    throwError "Aggregate axiom audit failed"
  logInfo "Aggregate audit passed"
