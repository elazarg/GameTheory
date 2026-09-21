/-
# The pure embedding as a finite-mixture simulation

The mixed extension supplies a native consumer of the finite-mixture transfer
API: every mixed deviation is already a finite law over pure deviations.
-/

import GameTheory.Core.Mixed
import GameTheory.Core.MixtureSimulation

noncomputable section

namespace GameTheory.GameForm

open GameTheory.Math.Probability

universe uι us uo

variable {Player : Type uι} [Fintype Player] [DecidableEq Player]

/-- Pure profiles embed into the canonical mixed extension, with the deviator's
replacement law itself as the mixture witness. -/
def mixedSimulation (source : GameForm.{uι, us, uo} Player) :
    MixtureSimulationOn source source.mixed id id (fun _ _ => True) where
  compileStrategy _ := FinDist.pure
  honest_law profile := by
    simp only [FinDist.map_id, FinDist.pi_pure, FinDist.pure_bind]
  compiled_considered _ _ := trivial
  deviation_mixture profile who replacement _ := by
    refine ⟨replacement, ?_⟩
    have hfull : source.mixed.play (Profile.update (source.purify profile) who replacement) =
        replacement.bind
          (fun alternative => source.play (Profile.update profile who alternative)) := by
      rw [mixed_play_update]
      apply FinDist.bind_congr
      intro alternative _
      rw [purify_update, mixed_play_purify]
    unfold GameForm.purify at hfull
    exact (congrArg (fun law => law.map id) hfull).trans (FinDist.map_bind _ _ _)

/-- The pure embedding preserves and reflects the same real epsilon. -/
theorem isεNash_purify_iff (source : GameForm.{uι, us, uo} Player)
    (utility : source.sig.Outcome → Player → ℝ) (ε : ℝ) (profile : Profile source.sig) :
    IsεNash source.mixed utility ε (source.purify profile) ↔
      IsεNash source utility ε profile :=
  (source.mixedSimulation).isεNash_compileProfile_iff utility ε profile (fun _ _ => trivial)

end GameTheory.GameForm
