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
    (source.mixed.play (Profile.map (fun _ => FinDist.pure) profile)).map id =
      (source.play profile).map id := by
  unfold Profile.map
  simp only [FinDist.map_id, FinDist.pi_pure, FinDist.pure_bind]

theorem deviationLaw (profile : Profile source.sig) (who : Player)
    (replacement : source.mixed.sig.Strategy who) :
    ∃ alternatives : FinDist (source.sig.Strategy who),
      (source.mixed.play (Profile.update
          (Profile.map (fun _ => FinDist.pure) profile) who replacement)).map id =
        alternatives.bind fun alternative =>
          (source.play (Profile.update profile who alternative)).map id := by
  refine ⟨replacement, ?_⟩
  have hfull : source.mixed.play (Profile.update (source.purify profile) who replacement) =
      replacement.bind fun alternative => source.play (Profile.update profile who alternative) := by
    rw [mixed_play_update]
    apply FinDist.bind_congr
    intro alternative _
    rw [purify_update, mixed_play_purify]
  unfold GameForm.purify at hfull
  unfold Profile.map
  exact (congrArg (fun law => law.map id) hfull).trans (FinDist.map_bind _ _ _)

namespace Direct

theorem transfer (utility : source.sig.Outcome → Player → ℝ) (ε : ℝ)
    (profile : Profile source.sig) :
    IsεNash source.mixed utility ε (source.purify profile) ↔
      IsεNash source utility ε profile := by
  constructor
  · exact isεNash_of_honest_law (source := source) (target := source.mixed)
      (sourceObserve := id) (targetObserve := id) (fun _ => FinDist.pure)
      (honestLaw source) utility ε profile
  · intro hsource
    rw [GameTheory.isεNash_iff]
    intro who replacement
    exact considered_deviations_of_isεNash_of_mixtures
      (source := source) (target := source.mixed) (sourceObserve := id) (targetObserve := id) profile
      (Profile.map (fun _ => FinDist.pure) profile) (fun _ _ => True)
      (honestLaw source profile) (fun who replacement _ =>
        deviationLaw source profile who replacement) utility ε hsource who replacement trivial

end Direct

namespace Bundled

def simulation : MixtureSimulationOn source source.mixed id id (fun _ _ => True) where
  compileStrategy _ := FinDist.pure
  honest_law := honestLaw source
  compiled_considered _ _ := trivial
  deviation_mixture profile who replacement _ := deviationLaw source profile who replacement

theorem transfer (utility : source.sig.Outcome → Player → ℝ) (ε : ℝ)
    (profile : Profile source.sig) :
    IsεNash source.mixed utility ε (source.purify profile) ↔
      IsεNash source utility ε profile :=
  (simulation source).isεNash_compileProfile_iff utility ε profile (fun _ _ => trivial)

end Bundled

end GameTheory.Experimental.MixtureSimulationComparison
