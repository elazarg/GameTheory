import GameTheoryComplexity
import GameTheoryComplexity.LintAll
import GameTheoryComplexity.Backend.Negligible
import GameTheoryComplexity.Tests.RandomTape
import GameTheoryComplexity.Tests.Facade
import GameTheoryComplexity.Tests.Serializer
import GameTheoryComplexity.Tests.Composition
import GameTheoryComplexity.Tests.SATReduction
import GameTheoryComplexity.Tests.NashCertificate
import GameTheoryComplexity.Tests.SearchReduction
import GameTheoryComplexity.Tests.EndOfLine
import GameTheoryComplexity.Tests.RawEndOfLine
import GameTheoryComplexity.Tests.PPAD
import GameTheoryComplexity.Tests.CircuitPrefixCompiler
import GameTheoryComplexity.Tests.NormalizedEndOfLine
import GameTheoryComplexity.Tests.SpernerGridWords
import GameTheoryComplexity.Tests.SpernerPointerMachine
import GameTheoryComplexity.Tests.Sperner
import GameTheoryComplexity.Tests.GridRouting
import GameTheoryComplexity.Tests.GridRoutingGeometry
import GameTheoryComplexity.Tests.GridRoutingNodes
import GameTheoryComplexity.Tests.SpernerHardness
import GameTheoryComplexity.Tests.Brouwer
import GameTheoryComplexity.Tests.GeneralBimatrix
import GameTheoryComplexity.Tests.GeneralBimatrixCodec
import GameTheoryComplexity.Tests.GeneralBimatrixTotality
import Lean.Util.CollectAxioms

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
  logInfo m!"Audited {checked} complexity declarations"
