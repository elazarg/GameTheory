module

import all GameTheoryComplexity.SampleTest
import all GameTheoryComplexity.Backend.CompiledSampleTest
import all GameTheoryComplexity.Tests.BinaryRatioExtraction
import all GameTheoryComplexity.Tests.BimatrixProgramEmission
import all GameTheoryComplexity.Tests.BimatrixRawGateMachine
import all GameTheoryComplexity.Tests.SpernerCoordinateColor
import all GameTheoryComplexity.Tests.BimatrixProgramPayoffs
import all GameTheoryComplexity.Tests.GeneralBimatrixPayoffEmission
import all GameTheoryComplexity.Tests.BimatrixRawGate
import all GameTheoryComplexity
import all GameTheoryComplexity.LintAll
import all GameTheoryComplexity.Backend.Negligible
import all GameTheoryComplexity.Tests.RandomTape
import all GameTheoryComplexity.Tests.Facade
import all GameTheoryComplexity.Tests.Serializer
import all GameTheoryComplexity.Tests.Composition
import all GameTheoryComplexity.Tests.SATReduction
import all GameTheoryComplexity.Tests.NashCertificate
import all GameTheoryComplexity.Tests.SearchReduction
import all GameTheoryComplexity.Tests.EndOfLine
import all GameTheoryComplexity.Tests.RawEndOfLine
import all GameTheoryComplexity.Tests.PPAD
import all GameTheoryComplexity.Tests.CircuitPrefixCompiler
import all GameTheoryComplexity.Tests.NormalizedEndOfLine
import all GameTheoryComplexity.Tests.SpernerGridWords
import all GameTheoryComplexity.Tests.SpernerPointerMachine
import all GameTheoryComplexity.Tests.Sperner
import all GameTheoryComplexity.Tests.GridRouting
import all GameTheoryComplexity.Tests.GridRoutingGeometry
import all GameTheoryComplexity.Tests.GridRoutingNodes
import all GameTheoryComplexity.Tests.SpernerHardness
import all GameTheoryComplexity.Tests.Brouwer
import all GameTheoryComplexity.Tests.GeneralBimatrix
import all GameTheoryComplexity.Tests.GeneralBimatrixCodec
import all GameTheoryComplexity.Tests.GeneralBimatrixTotality
import all GameTheoryComplexity.Tests.GeneralBimatrixEndpoint
import all GameTheoryComplexity.Tests.BinarySignedArithmetic
import all GameTheoryComplexity.Tests.BinarySignedRowComparison
import all GameTheoryComplexity.Tests.BinarySignedMatrixMachine
import all GameTheoryComplexity.Tests.BinarySignedRowSelection
import all GameTheoryComplexity.Tests.BinarySubsetMachine
import all GameTheoryComplexity.Tests.BinaryUnaryArithmetic
import all GameTheoryComplexity.Tests.BinaryBirdDeterminantMachine
import all GameTheoryComplexity.Tests.BinaryCramerMachine
import all GameTheoryComplexity.Tests.BinaryDictionaryMachine
import all GameTheoryComplexity.Tests.BinaryBirdDeterminantCorrectness
import all GameTheoryComplexity.Tests.BimatrixNodeWord
import all GameTheoryComplexity.Tests.GeneralBimatrixMatrixWord
import all GameTheoryComplexity.Tests.BinaryDictionaryCorrectness
import all GameTheoryComplexity.Tests.BinaryDictionaryFeasibility
import all GameTheoryComplexity.Tests.GeneralBimatrixEndpointMachine
import all GameTheoryComplexity.Tests.BimatrixNodeOperations
import all GameTheoryComplexity.Tests.BimatrixNodeColor
import all GameTheoryComplexity.Tests.GeneralBimatrixNodeOperations
import all GameTheoryComplexity.Tests.GeneralBimatrixCircuitMachine
import all GameTheoryComplexity.Tests.GeneralBimatrixReduction
import all GameTheoryComplexity.Tests.GeneralBimatrixDictionary
import all GameTheoryComplexity.Tests.GeneralBimatrixNodeValidation
import all GameTheoryComplexity.Tests.GeneralBimatrixEndpointCapacity
import all GameTheoryComplexity.Tests.GeneralBimatrixPathEndpoint
meta import Lean.Util.CollectAxioms

@[expose] public section

/-! Reject placeholders and nonstandard axioms in every public extension
declaration, including axioms reached through upstream dependencies. -/

open Lean in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : ℕ := 0
  for (name, _) in env.constants.toList do
    let owned := match env.getModuleIdxFor? name with
      | some idx => (`GameTheoryComplexity).isPrefixOf env.header.moduleNames[idx.toNat]!
      | none => false
    if owned then
      checked := checked + 1
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "{name} depends on forbidden axiom {axiomName}"
  if checked == 0 then
    throwError "Complexity axiom audit found no declarations"
