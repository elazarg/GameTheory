/-
EXP-134: finite-average play samples one stage and its actual outcome. An
unrelated profile may have a nonintegrable geometric payoff while stationary
all-false play remains uniform. A unilateral deviation into that law is
rejected, and the empty horizon pays zero.

Under EXP-147's extended expectation the geometric payoff is worth `⊤`, so the
deviation is rejected because it is infinitely profitable rather than because
its value is undefined.
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
  rw [allFalse_play, allFalse_update_play who own]
  exact (euPreference_pure_iff _ _ _ _).2 le_rfl

/-- The stationary profile satisfies the canonical uniform property without
any certificate for the unrelated all-true profile. -/
theorem allFalse_uniform :
    game.IsUniformEquilibrium (game.stationaryRepeatedProfile allFalse) :=
  game.stationaryRepeatedProfile_isUniformEquilibrium_of_isNash
    allFalse_stageNash fun who own => by
      rw [allFalse_update_play]
      exact payoffIntegrable_pure _ _

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

/-- A unilateral deviation into the geometric stage law is worth `⊤` in the
finite-average form, so it invalidates approximate Nash at every positive
horizon, independent of the numerical epsilon. -/
theorem falseTrue_not_approximate (horizon : ℕ) (hpositive : 0 < horizon)
    (epsilon : ℝ) :
    ¬ game.IsεFiniteRepeatedNash horizon epsilon
      (game.stationaryRepeatedProfile falseTrue) := by
  intro happrox
  have hne : horizon ≠ 0 := Nat.pos_iff_ne_zero.1 hpositive
  have : NeZero horizon := ⟨hne⟩
  have hdevStage : ∀ t, game.form.play (game.repeatedPlay
      (Profile.update (game.stationaryRepeatedProfile falseTrue) 0 deviatesTrue) t) =
        geometric := by
    intro t
    rw [game.repeatedPlay_update_stationaryRepeatedProfile]
    exact (congrArg game.form.play falseTrue_update_true).trans allTrue_play
  have hbaseStage : ∀ t, game.form.play
      (game.repeatedPlay (game.stationaryRepeatedProfile falseTrue) t) = PMF.pure 0 := by
    intro t
    rw [game.repeatedPlay_stationaryRepeatedProfile]
    simp [game, form, falseTrue]
  have hdevLaw : (game.finiteAverageForm horizon).play
      (Profile.update (game.stationaryRepeatedProfile falseTrue) 0 deviatesTrue) =
        geometric.map some := by
    rw [UtilityGame.finiteAverageForm_play_pos]
    calc
      _ = (PMF.uniformOfFintype (Fin horizon)).bind fun _ => geometric.map some := by
        congr 1
        funext t
        exact congrArg (PMF.map some) (hdevStage t)
      _ = _ := PMF.bind_const _ _
  have hbaseLaw : (game.finiteAverageForm horizon).play
      (game.stationaryRepeatedProfile falseTrue) = PMF.pure (some 0) := by
    rw [UtilityGame.finiteAverageForm_play_pos]
    calc
      _ = (PMF.uniformOfFintype (Fin horizon)).bind fun _ => PMF.pure (some 0) := by
        congr 1
        funext t
        exact (congrArg (PMF.map some) (hbaseStage t)).trans (PMF.pure_map _ _)
      _ = _ := PMF.bind_const _ _
  obtain ⟨-, -, hle⟩ := (isεNash_iff _ _).1 happrox 0 deviatesTrue
  rw [hdevLaw, hbaseLaw, extendedExpectedUtility_map, extendedExpectedUtility_pure] at hle
  have htop : extendedExpectedUtility
      (fun outcome => game.finiteAverageOutcomeUtility (some outcome)) 0 geometric = ⊤ :=
    exploding_extendedExpect
  rw [htop, top_le_iff, ← EReal.coe_add] at hle
  exact EReal.coe_ne_top _ hle

/-- The zero-horizon form uses its explicit zero-payoff outcome. -/
theorem zeroHorizon_play (profile : game.RepeatedProfile) :
    (game.finiteAverageForm 0).play profile = PMF.pure none :=
  by simp [UtilityGame.finiteAverageForm]

theorem zeroHorizon_expectedUtility (profile : game.RepeatedProfile)
    (who : Fin 2) :
    expectedUtility game.finiteAverageOutcomeUtility who
      ((game.finiteAverageForm 0).play profile)
       = 0 := by
  exact expectedUtility_pure game.finiteAverageOutcomeUtility who
    (none : Option ℕ)

/-- Every profile is zero-horizon approximate Nash precisely when the
nonnegative slack makes the two zero values comparable. -/
theorem zeroHorizon_approximate (profile : game.RepeatedProfile)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    game.IsεFiniteRepeatedNash 0 epsilon profile := by
  rw [game.isεFiniteRepeatedNash_iff fun _ _ t ht => (Nat.not_lt_zero t ht).elim]
  intro who deviation
  simpa [UtilityGame.finiteAveragePayoff] using hepsilon

end GameTheory.Experimental.PMFUniformGate
