/-
EXP-134: finite-average play samples one stage and its actual outcome. An
unrelated profile may have an undefined geometric payoff while stationary
all-false play remains uniform. A unilateral deviation into that undefined
law is rejected, and the empty horizon pays zero.
-/

import GameTheory.Repeated.Uniform
import GameTheory.Experimental.PostArchitecture.PMFStaticGate

noncomputable section

namespace GameTheory.Experimental.PMFUniformGate

open GameTheory GameTheory.Math.Probability
open GameTheory.Experimental.PMFRestoration
open GameTheory.Experimental.PMFStaticGate

@[reducible]
def form : GameForm (Fin 2) where
  sig :=
    { Strategy := fun _ => Bool
      Outcome := ℕ }
  play profile :=
    if profile 0 = true ∧ profile 1 = true then geometric else PMF.pure 0

@[reducible]
def game : UtilityGame (Fin 2) where
  form := form
  utility outcome _ := exploding outcome

def allFalse : Profile game.form.sig := fun _ => false

def falseTrue : Profile game.form.sig := fun i => i = 1

theorem allFalse_play : game.form.play allFalse = PMF.pure 0 := by
  simp [game, form, allFalse]

theorem allFalse_update_play (who : Fin 2) (own : Bool) :
    game.form.play (Profile.update allFalse who own) = PMF.pure 0 := by
  fin_cases who <;> cases own <;>
    simp [game, form, allFalse, Profile.update]

/-- All-false is guarded stage Nash despite an unrelated divergent profile. -/
theorem allFalse_stageNash :
    IsNash game.form (euPreference game.utility) allFalse := by
  rw [isNash_iff]
  intro who own
  rw [euPreference_apply]
  have hinc := allFalse_play
  have hdev := allFalse_update_play who own
  rw [hinc, hdev]
  refine ⟨payoffIntegrable_pure 0 _, payoffIntegrable_pure 0 _, ?_⟩
  simp

/-- The stationary profile satisfies the canonical uniform property without
any certificate for the unrelated all-true profile. -/
theorem allFalse_uniform :
    game.IsUniformEquilibrium (game.stationaryRepeatedProfile allFalse) :=
  game.stationaryRepeatedProfile_isUniformEquilibrium_of_isNash
    allFalse_stageNash

theorem allTrue_play :
    game.form.play (fun _ => true) = geometric := by
  simp [game, form]

/-- The all-true stage payoff is genuinely nonintegrable. -/
theorem allTrue_not_integrable :
    ¬ UtilityIntegrable game.utility (0 : Fin 2)
      (game.form.play (fun _ => true)) := by
  rw [allTrue_play]
  exact explodingUtility_not_integrable

theorem falseTrue_update_true :
    Profile.update falseTrue 0 true = (fun _ => true) := by
  funext i
  fin_cases i <;> simp [falseTrue, Profile.update]

theorem falseTrue_deviation_not_integrable :
    ¬ UtilityIntegrable game.utility (0 : Fin 2)
      (game.form.play (Profile.update falseTrue 0 true)) := by
  rw [falseTrue_update_true]
  exact allTrue_not_integrable

def deviatesTrue : game.RepeatedStrategy 0 := fun _ => true

/-- An undefined unilateral stage law invalidates approximate Nash at every
positive horizon, independent of the numerical epsilon. -/
theorem falseTrue_not_approximate (horizon : ℕ) (hpositive : 0 < horizon)
    (epsilon : ℝ) :
    ¬ game.IsεFiniteRepeatedNash horizon epsilon
      (game.stationaryRepeatedProfile falseTrue) := by
  intro happrox
  obtain ⟨_, hdev, _⟩ :=
    (game.isεFiniteRepeatedNash_iff).1 happrox 0 deviatesTrue
  have hpath :
      game.repeatedPlay
          (Profile.update (game.stationaryRepeatedProfile falseTrue)
            0 deviatesTrue) 0 =
        Profile.update falseTrue 0 true := by
    rw [game.repeatedPlay_update_stationaryRepeatedProfile]
    rfl
  apply falseTrue_deviation_not_integrable
  simpa only [hpath] using hdev 0 hpositive

/-- The zero-horizon form uses its explicit zero-payoff outcome. -/
theorem zeroHorizon_play (profile : game.RepeatedProfile) :
    (game.finiteAverageForm 0).play profile = PMF.pure none :=
  by simp [UtilityGame.finiteAverageForm]

theorem zeroHorizon_expectedUtility (profile : game.RepeatedProfile)
    (who : Fin 2) :
    expectedUtility game.finiteAverageOutcomeUtility who
      ((game.finiteAverageForm 0).play profile)
      (payoffIntegrable_pure none _) = 0 := by
  exact expectedUtility_pure game.finiteAverageOutcomeUtility who
    (none : Option ℕ)

/-- Every profile is zero-horizon approximate Nash precisely when the
nonnegative slack makes the two zero values comparable. -/
theorem zeroHorizon_approximate (profile : game.RepeatedProfile)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    game.IsεFiniteRepeatedNash 0 epsilon profile := by
  rw [game.isεFiniteRepeatedNash_iff]
  intro who deviation
  refine ⟨fun t ht => (Nat.not_lt_zero t ht).elim,
    fun t ht => (Nat.not_lt_zero t ht).elim, ?_⟩
  simpa [UtilityGame.finiteAveragePayoff] using hepsilon

end GameTheory.Experimental.PMFUniformGate
