import GameTheory.Core

/-! The default Core surface carries direct utility transfer. Uniform utility
certificates and their mixture bridge require an explicit additional import. -/

run_cmd do
  let env ← Lean.getEnv
  unless env.contains `GameTheory.GameForm.isεNash_of_deviation_bounds do
    throwError "Core must export direct utility transfer"
  if env.contains `GameTheory.GameForm.UtilitySimulation then
    throwError "UtilitySimulation must remain an explicit import"
  if env.contains `GameTheory.GameForm.MixtureSimulationOn.toUtilitySimulation then
    throwError "The utility certificate bridge must remain an explicit import"
