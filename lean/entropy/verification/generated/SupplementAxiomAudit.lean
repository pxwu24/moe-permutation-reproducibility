import Lean
import BellAlgebra
import FilterTrace
import JointBound
import JointProjection
import JointEntropy
import SingleEntropy
import TensorBridge
import JointChannel
import TensorMarginalEntropy
import ActualTensorTuple
import ActualCoordinateMarginal
import FiniteFilterSupport
import SignFilterLower
import GaussianSignCoefficient
import GridNet
import GridCardinality
import GaussianSignGrid
import ActualGridFilterLower
import ActualGridSupport
import ActualGridFilterProperties
import ActualTensorBasis
import AdderTrace
import MainHolevo
import MainHolevoTensor
import MainCapacity
import MainAdderTuple
import MainChannel
import MainReal
import SingleChannel
import GapObstruction
import GapRemainder
import GapAsymptotics
import TensorAmplification
import SymbolicAmplification
import TensorCalibration
import SupplementEntropy
import SupplementSingle
import MainBasic
import MainFilterParameters
import MainGridBridge
import MainParameters
import MainConcreteBasic
import MainRandomizer
import MainPauli
import MainConcreteRandomizer
import MainSmoothing
import MainSmoothedChannel
import MainConcreteSmoothed
import MainDimensions
import MainFlaggedEntropy
import MainPauliTensor
import MainPauliHolevo
import MainTheorem
import MainCapacityCorollary
import MainParameterGrowth
import SupplementAdder
import AllProofs

open Lean Elab Command

-- Enumerate the complete imported environment, independently of its size.
set_option maxHeartbeats 0

/- This command audits every declaration from the selected proof modules,
including auxiliary definitions and private lemmas. `collectAxioms` follows
dependencies transitively; an unexpected axiom is a compilation error. -/
run_cmd do
  let selected : Array Name := #[Name.mkSimple "BellAlgebra", Name.mkSimple "FilterTrace", Name.mkSimple "JointBound", Name.mkSimple "JointProjection", Name.mkSimple "JointEntropy", Name.mkSimple "SingleEntropy", Name.mkSimple "TensorBridge", Name.mkSimple "JointChannel", Name.mkSimple "TensorMarginalEntropy", Name.mkSimple "ActualTensorTuple", Name.mkSimple "ActualCoordinateMarginal", Name.mkSimple "FiniteFilterSupport", Name.mkSimple "SignFilterLower", Name.mkSimple "GaussianSignCoefficient", Name.mkSimple "GridNet", Name.mkSimple "GridCardinality", Name.mkSimple "GaussianSignGrid", Name.mkSimple "ActualGridFilterLower", Name.mkSimple "ActualGridSupport", Name.mkSimple "ActualGridFilterProperties", Name.mkSimple "ActualTensorBasis", Name.mkSimple "AdderTrace", Name.mkSimple "MainHolevo", Name.mkSimple "MainHolevoTensor", Name.mkSimple "MainCapacity", Name.mkSimple "MainAdderTuple", Name.mkSimple "MainChannel", Name.mkSimple "MainReal", Name.mkSimple "SingleChannel", Name.mkSimple "GapObstruction", Name.mkSimple "GapRemainder", Name.mkSimple "GapAsymptotics", Name.mkSimple "TensorAmplification", Name.mkSimple "SymbolicAmplification", Name.mkSimple "TensorCalibration", Name.mkSimple "SupplementEntropy", Name.mkSimple "SupplementSingle", Name.mkSimple "MainBasic", Name.mkSimple "MainFilterParameters", Name.mkSimple "MainGridBridge", Name.mkSimple "MainParameters", Name.mkSimple "MainConcreteBasic", Name.mkSimple "MainRandomizer", Name.mkSimple "MainPauli", Name.mkSimple "MainConcreteRandomizer", Name.mkSimple "MainSmoothing", Name.mkSimple "MainSmoothedChannel", Name.mkSimple "MainConcreteSmoothed", Name.mkSimple "MainDimensions", Name.mkSimple "MainFlaggedEntropy", Name.mkSimple "MainPauliTensor", Name.mkSimple "MainPauliHolevo", Name.mkSimple "MainTheorem", Name.mkSimple "MainCapacityCorollary", Name.mkSimple "MainParameterGrowth", Name.mkSimple "SupplementAdder", Name.mkSimple "AllProofs"]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← getEnv
  for moduleName in selected do
    unless env.allImportedModuleNames.contains moduleName do
      throwError "Audit module was not imported: {moduleName}"
  let declarations := env.constants.toList.filterMap fun (name, _) => do
    let moduleIdx ← env.getModuleIdxFor? name
    let moduleName ← env.allImportedModuleNames[moduleIdx.toNat]?
    if selected.contains moduleName then some name else none
  let declarations := declarations.toArray.qsort Name.lt
  if declarations.isEmpty then
    throwError "The axiom audit selected no declarations."
  for name in declarations do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Unsupported axiom dependency: {name} uses {axiomName}"
    logInfo m!"AUDIT_DECL {name}: {axioms}"
  logInfo m!"AXIOM_AUDIT_OK declarations={declarations.size} modules={selected.size}"
