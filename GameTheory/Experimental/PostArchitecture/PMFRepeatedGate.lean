/-
EXP-133: stage integration and discounted time-series summability are distinct.
The infinite geometric stage noise has an integrable unbounded payoff at every
pure action. An exponentially growing repeated action path defeats half-discounted
summability even though all of its individual stages remain integrable.
-/

import GameTheory.Repeated.Discounted
import GameTheory.Experimental.PostArchitecture.PMFStaticGate
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section

namespace GameTheory.Experimental.PMFRepeatedGate

open GameTheory GameTheory.Math.Probability
open GameTheory.Experimental.PMFRestoration
open GameTheory.Experimental.PMFStaticGate

@[reducible]
def form : GameForm Unit where
  sig :=
    { Strategy := fun _ => ℕ
      Outcome := ℕ × ℕ }
  play profile := geometric.map fun noise => (profile (), noise)

@[reducible]
def game : UtilityGame Unit where
  form := form
  utility outcome _ := (outcome.1 : ℝ) + ((outcome.2 : ℝ) + 1)

/-- Every stage law is genuinely infinite, not a finite-support shortcut. -/
theorem stage_law_infinite_support (profile : Profile game.form.sig) :
    (game.form.play profile).support.Infinite := by
  have hinj : Function.Injective (fun noise : ℕ => (profile (), noise)) := by
    intro n m h
    exact congrArg Prod.snd h
  apply (Set.infinite_range_of_injective hinj).mono
  rintro _ ⟨noise, rfl⟩
  rw [PMF.mem_support_map_iff]
  exact ⟨noise, (geometric_positive noise).ne', rfl⟩

/-- Unbounded geometric noise is absolutely integrable at each chosen action. -/
theorem stage_integrable : game.form.HasIntegrableUtility game.utility := by
  intro who profile
  have hconst := payoffIntegrable_constant geometric (profile () : ℝ)
  have hlinear := linearUtility_integrable_geometric
  have hsum : PayoffIntegrable geometric
      (fun noise => (profile () : ℝ) + ((noise : ℝ) + 1)) := by
    simpa [linearUtility] using payoffIntegrable_add hconst hlinear
  exact (payoffIntegrable_map_iff
    (fun noise : ℕ => (profile (), noise)) geometric
    (fun outcome : ℕ × ℕ => game.utility outcome who)).mpr (by
      simpa [game, Function.comp_def] using hsum)

private def noiseMean : ℝ :=
  expectedUtility linearUtility (0 : Fin 2) geometric
    linearUtility_integrable_geometric

private theorem noiseMean_nonneg : 0 ≤ noiseMean := by
  exact expect_nonneg geometric (fun noise => linearUtility noise 0)
    linearUtility_integrable_geometric (fun noise _ => by
      unfold linearUtility
      positivity)

/-- The actual stage expected payoff adds the chosen action to a finite noise mean. -/
private theorem stagePayoff_eq (profile : Profile game.form.sig) :
    game.stagePayoff profile () (stage_integrable () profile) =
      (profile () : ℝ) + noiseMean := by
  have hmap := expectedUtility_map game.utility ()
    (fun noise : ℕ => (profile (), noise)) geometric
    (stage_integrable () profile)
  have hconst := payoffIntegrable_constant geometric (profile () : ℝ)
  have hlinear := linearUtility_integrable_geometric
  have hsum := payoffIntegrable_add hconst hlinear
  calc
    game.stagePayoff profile () (stage_integrable () profile) =
        expect geometric (fun noise =>
          (profile () : ℝ) + ((noise : ℝ) + 1)) hsum := by
      simpa [UtilityGame.stagePayoff, form, game, linearUtility,
        expectedUtility] using hmap
    _ = (profile () : ℝ) + noiseMean := by
      have hadd := expect_add hconst hlinear
      rw [expect_constant] at hadd
      simpa [noiseMean, linearUtility, expectedUtility] using hadd

def stationary : game.RepeatedProfile :=
  game.stationaryRepeatedProfile (fun _ => 0)

/-- The stationary profile has a summable half-discounted expected-payoff series. -/
theorem stationary_summable :
    Summable fun t : ℕ => (1 / 2 : ℝ) ^ t *
      game.stagePayoff (game.repeatedPlay stationary t) ()
        (stage_integrable () (game.repeatedPlay stationary t)) := by
  have hgeom := (summable_geometric_of_lt_one
    (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1))
      |>.mul_right noiseMean
  simpa [stationary, stagePayoff_eq] using hgeom

def exponential : game.RepeatedProfile := fun _ history => 2 ^ history.length

theorem exponential_action (t : ℕ) :
    game.repeatedPlay exponential t () = 2 ^ t := by
  rw [UtilityGame.repeatedPlay]
  simp [exponential]

/-- Every discounted term on the exponential path is at least one. -/
theorem exponential_weighted_term_ge_one (t : ℕ) :
    1 ≤ (1 / 2 : ℝ) ^ t *
      game.stagePayoff (game.repeatedPlay exponential t) ()
        (stage_integrable () (game.repeatedPlay exponential t)) := by
  rw [stagePayoff_eq, exponential_action]
  have hpow : (1 / 2 : ℝ) ^ t * (2 ^ t : ℕ) = 1 := by
    norm_num [Nat.cast_pow, ← mul_pow]
  calc
    (1 : ℝ) = (1 / 2 : ℝ) ^ t * (2 ^ t : ℕ) := hpow.symm
    _ ≤ (1 / 2 : ℝ) ^ t * ((2 ^ t : ℕ) + noiseMean) := by
      exact mul_le_mul_of_nonneg_left (by linarith [noiseMean_nonneg])
        (pow_nonneg (by norm_num) _)

/-- Stagewise integration does not define the nonsummable discounted payoff. -/
theorem exponential_not_summable :
    ¬ Summable (fun t : ℕ => (1 / 2 : ℝ) ^ t *
      game.stagePayoff (game.repeatedPlay exponential t) ()
        (stage_integrable () (game.repeatedPlay exponential t))) := by
  intro hsum
  have hone : Summable (fun _ : ℕ => (1 : ℝ)) :=
    Summable.of_nonneg_of_le (fun _ => by norm_num)
      exponential_weighted_term_ge_one hsum
  have hzero : (1 : ℝ) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hone.tendsto_atTop_zero
  norm_num at hzero

end GameTheory.Experimental.PMFRepeatedGate
