/-
# EXP-120: direct hypotheses versus a narrow mixture record

Both consumers below use the same native mixed-extension laws, compile the
same coordinatewise pure embedding, and prove the same epsilon-Nash theorem.
The separate namespaces permit identical-import elaboration measurements.
-/

import GameTheory.Core.Mixed
import GameTheory.Core.MixtureSimulation

noncomputable section

namespace GameTheory.Experimental.MixtureSimulationComparison

open GameTheory.Math.Probability GameTheory.GameForm

universe uι us uo

variable {Player : Type uι} [Fintype Player] [DecidableEq Player]
variable (source : GameForm.{uι, us, uo} Player)

omit [DecidableEq Player] in
theorem honestLaw (profile : Profile source.sig) :
    (source.mixed.play (Profile.map (fun _ => PMF.pure) profile)).map id =
      (source.play profile).map id := by
  have hp : Profile.map (fun _ => PMF.pure) profile = source.purify profile := rfl
  rw [hp, source.mixed_play_purify]

theorem deviationLaw (profile : Profile source.sig) (who : Player)
    (replacement : source.mixed.sig.Strategy who) :
    ∃ alternatives : PMF (source.sig.Strategy who),
      (source.mixed.play (Profile.update
          (Profile.map (fun _ => PMF.pure) profile) who replacement)).map id =
        alternatives.bind fun alternative =>
          (source.play (Profile.update profile who alternative)).map id := by
  refine ⟨replacement, ?_⟩
  have hfull : source.mixed.play (Profile.update (source.purify profile) who replacement) =
      replacement.bind fun alternative => source.play (Profile.update profile who alternative) := by
    rw [GameForm.mixed_play_update]
    apply bind_congr_on_support
    intro alternative _
    rw [purify_update, GameForm.mixed_play_purify]
  have hp : Profile.map (fun _ => PMF.pure) profile = source.purify profile := rfl
  rw [hp, PMF.map_id]
  simpa only [PMF.map_id] using hfull

namespace Direct

theorem transfer (utility : source.sig.Outcome → Player → ℝ) (ε : ℝ)
    (profile : Profile source.sig) :
    IsεNash source.mixed utility ε (source.purify profile) ↔
      IsεNash source utility ε profile ∧
        ∀ who replacement,
          UtilityIntegrable utility who
            (source.mixed.play
              (Profile.update (source.purify profile) who replacement)) := by
  constructor
  · intro htarget
    constructor
    · exact isεNash_of_honest_law (source := source) (target := source.mixed)
        (sourceObserve := id) (targetObserve := id) (fun _ => PMF.pure)
        (honestLaw source) utility ε profile htarget
    · intro who replacement
      exact ((GameTheory.isεNash_iff _ _).mp htarget who replacement).2.1
  · rintro ⟨hsource, hdev⟩
    rw [GameTheory.isεNash_iff]
    intro who replacement
    exact considered_deviations_of_isεNash_of_mixtures
      (source := source) (target := source.mixed)
      (sourceObserve := id) (targetObserve := id) profile
      (Profile.map (fun _ => PMF.pure) profile) (fun _ _ => True)
      (honestLaw source profile) (fun who replacement _ =>
        deviationLaw source profile who replacement) utility ε
      (fun who replacement _ => hdev who replacement) hsource who replacement trivial

end Direct

namespace Bundled

def simulation : MixtureSimulationOn source source.mixed id id (fun _ _ => True) where
  compileStrategy _ := PMF.pure
  honest_law := honestLaw source
  compiled_considered _ _ := trivial
  deviation_mixture profile who replacement _ := deviationLaw source profile who replacement

theorem transfer (utility : source.sig.Outcome → Player → ℝ) (ε : ℝ)
    (profile : Profile source.sig) :
    IsεNash source.mixed utility ε (source.purify profile) ↔
      IsεNash source utility ε profile ∧
        ∀ who replacement,
          UtilityIntegrable utility who
            (source.mixed.play
              (Profile.update (source.purify profile) who replacement)) :=
  (simulation source).isεNash_compileProfile_iff utility ε profile (fun _ _ => trivial)

end Bundled

end GameTheory.Experimental.MixtureSimulationComparison
