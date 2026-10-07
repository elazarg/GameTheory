import GameTheoryComplexity
import GameTheoryComplexity.Backend.Negligible
import GameTheoryComplexity.Tests.RandomTape
import GameTheoryComplexity.Tests.Facade
import GameTheoryComplexity.Tests.Serializer
import GameTheoryComplexity.Tests.Composition
import Lean.Util.CollectAxioms

/-! Reject placeholders and nonstandard axioms in every public extension
declaration, including axioms reached through upstream dependencies. -/

open Lean in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : ℕ := 0
  for (name, _) in env.constants.toList do
    if (`GameTheory.Complexity).isPrefixOf name then
      checked := checked + 1
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "{name} depends on forbidden axiom {axiomName}"
  if checked == 0 then
    throwError "Complexity axiom audit found no declarations"
  logInfo m!"Audited {checked} complexity declarations"
