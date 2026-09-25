/-
# The pure embedding as a PMF-mixture simulation

Every mixed deviation is already a PMF over pure deviations. Integration of
each actual randomized deviation remains the separate numerical condition.
-/

import GameTheory.Core.Mixed
import GameTheory.Core.MixtureSimulation

noncomputable section

namespace GameTheory.GameForm

open GameTheory.Math.Probability

universe uι us uo

variable {Player : Type uι} [Fintype Player] [DecidableEq Player]

/-- Pure profiles embed into the canonical mixed extension, with the
replacement PMF itself as the source-deviation mixture. -/
def mixedSimulation (source : GameForm.{uι, us, uo} Player) :
    MixtureSimulationOn source source.mixed id id (fun _ _ => True) where
  compileStrategy _ := PMF.pure
  honest_law profile := by
    have hprofile : Profile.map (fun _ => PMF.pure) profile =
        source.purify profile := by
      funext who
      rfl
    rw [hprofile, PMF.map_id, PMF.map_id]
    exact source.mixed_play_purify profile
  compiled_considered _ _ := trivial
  deviation_mixture profile who replacement _ := by
    refine ⟨replacement, ?_⟩
    have hfull : source.mixed.play
        (Profile.update (source.purify profile) who replacement) =
        replacement.bind fun alternative =>
          source.play (Profile.update profile who alternative) := by
      rw [mixed_play_update]
      congr 1
      funext alternative
      rw [purify_update, mixed_play_purify]
    exact (congrArg (fun law => law.map id) hfull).trans (PMF.map_bind _ _ _)

/-- The pure embedding has the exact guarded approximate-Nash
characterization, with no finite strategy-carrier premise. -/
theorem isεNash_purify_iff (source : GameForm.{uι, us, uo} Player)
    (utility : source.sig.Outcome → Player → ℝ) (ε : ℝ)
    (profile : Profile source.sig) :
    IsεNash source.mixed utility ε (source.purify profile) ↔
      IsεNash source utility ε profile ∧
        ∀ (who : Player) (replacement : PMF (source.sig.Strategy who)),
          UtilityIntegrable utility who
            (source.mixed.play (Profile.update
              (source.purify profile) who replacement)) := by
  have hprofile : (source.mixedSimulation).compileProfile profile =
      source.purify profile := by
    funext who
    rfl
  have h := (source.mixedSimulation).isεNash_compileProfile_iff utility ε profile
    (fun _ _ => trivial)
  simpa only [id_eq, hprofile] using h

end GameTheory.GameForm
