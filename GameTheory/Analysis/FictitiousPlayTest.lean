/-
Analytic consumer of the finite fictitious-play fixture.

The Core test already separates nonconstant empirical-law arithmetic from the
constant best-response trajectory.  This file checks that the latter passes
through the shared finite-law convergence interface and the public
limit-to-Nash theorem.
-/

import GameTheory.Analysis.Learning
import GameTheory.Tests.FictitiousPlay
import Mathlib.Data.Int.CardIntervalMod

noncomputable section

namespace GameTheory.Tests.FictitiousPlay

/-- Every coordinate of the constant history's empirical belief converges to
the corresponding pure mixed strategy. -/
theorem constant_empiricalBelief_converges (who : Fin 2) :
    GameTheory.Math.Probability.FinDistConvergesPointwise
      (fun t => game.form.empiricalBelief constantHistory (t + 1) who)
      (game.form.purify coordinated who) := by
  have hsequence :
      (fun t => game.form.empiricalBelief constantHistory (t + 1) who) =
        fun _ => game.form.purify coordinated who := by
    funext t
    exact congrFun (constant_empiricalBelief t) who
  rw [hsequence]
  exact GameTheory.Math.Probability.finDistConvergesPointwise_const _

/-- The analytic theorem returns the sole canonical mixed Nash predicate on
the concrete fictitious-play trajectory. -/
theorem constant_limit_isNash :
    IsNash game.form.mixed (euPreference game.utility)
      (game.form.purify coordinated) :=
  UtilityGame.IsFictitiousPlay.limit_isNash
    (G := game) constant_isFictitiousPlay constant_empiricalBelief_converges

/-! ## A genuinely nonconstant trajectory -/

@[reducible]
def cyclingSignature : GameSignature (Fin 2) where
  Strategy _ := Fin 2
  Outcome := Fin 2 × Fin 2

@[reducible]
def cyclingForm : GameForm (Fin 2) :=
  GameForm.deterministic cyclingSignature fun profile => (profile 0, profile 1)

/-- Each player's payoff follows the other player's action. Thus both own
actions are best responses, while the realized payoff path remains live. -/
def cyclingUtility (outcome : Fin 2 × Fin 2) (who : Fin 2) : ℝ :=
  if who = 0 then outcome.2 else outcome.1

@[reducible]
def cyclingGame : UtilityGame (Fin 2) where
  form := cyclingForm
  utility := cyclingUtility

/-- Both players alternate forever, so neither coordinate is eventually
constant. -/
def cyclingHistory (round : ℕ) : Profile cyclingSignature :=
  fun _ => ⟨round % 2, Nat.mod_lt _ (by decide)⟩

/-- The alternating path is genuine fictitious play because a unilateral
replacement cannot change the replacing player's payoff. -/
theorem cycling_isFictitiousPlay :
    cyclingGame.IsFictitiousPlay cyclingHistory := by
  intro t who alternative
  rw [euPreference_apply]
  simp only [cyclingGame, cyclingForm, expectedUtility_bind, expectedUtility_pure]
  fin_cases who
  · show
      (GameTheory.Math.Probability.FinDist.pi (Profile.update
        (cyclingForm.empiricalBelief cyclingHistory (t + 1)) 0 alternative)).expect
          (fun profile => (profile 1 : ℝ)) ≤
        (GameTheory.Math.Probability.FinDist.pi (Profile.update
          (cyclingForm.empiricalBelief cyclingHistory (t + 1)) 0
            (GameTheory.Math.Probability.FinDist.pure (cyclingHistory (t + 1) 0)))).expect
          (fun profile => (profile 1 : ℝ))
    rw [← GameTheory.Math.Probability.FinDist.expect_map (fun profile => profile 1)
        (GameTheory.Math.Probability.FinDist.pi (Profile.update
          (cyclingForm.empiricalBelief cyclingHistory (t + 1)) 0 alternative))
        (fun action : Fin 2 => (action : ℝ)),
      ← GameTheory.Math.Probability.FinDist.expect_map (fun profile => profile 1)
        (GameTheory.Math.Probability.FinDist.pi (Profile.update
          (cyclingForm.empiricalBelief cyclingHistory (t + 1)) 0
            (GameTheory.Math.Probability.FinDist.pure (cyclingHistory (t + 1) 0))))
        (fun action : Fin 2 => (action : ℝ)),
      GameTheory.Math.Probability.FinDist.map_apply_pi,
      GameTheory.Math.Probability.FinDist.map_apply_pi]
    simp
  · show
      (GameTheory.Math.Probability.FinDist.pi (Profile.update
        (cyclingForm.empiricalBelief cyclingHistory (t + 1)) 1 alternative)).expect
          (fun profile => (profile 0 : ℝ)) ≤
        (GameTheory.Math.Probability.FinDist.pi (Profile.update
          (cyclingForm.empiricalBelief cyclingHistory (t + 1)) 1
            (GameTheory.Math.Probability.FinDist.pure (cyclingHistory (t + 1) 1)))).expect
          (fun profile => (profile 0 : ℝ))
    rw [← GameTheory.Math.Probability.FinDist.expect_map (fun profile => profile 0)
        (GameTheory.Math.Probability.FinDist.pi (Profile.update
          (cyclingForm.empiricalBelief cyclingHistory (t + 1)) 1 alternative))
        (fun action : Fin 2 => (action : ℝ)),
      ← GameTheory.Math.Probability.FinDist.expect_map (fun profile => profile 0)
        (GameTheory.Math.Probability.FinDist.pi (Profile.update
          (cyclingForm.empiricalBelief cyclingHistory (t + 1)) 1
            (GameTheory.Math.Probability.FinDist.pure (cyclingHistory (t + 1) 1))))
        (fun action : Fin 2 => (action : ℝ)),
      GameTheory.Math.Probability.FinDist.map_apply_pi,
      GameTheory.Math.Probability.FinDist.map_apply_pi]
    simp

/-- The long-run empirical target of the alternating path. -/
def cyclingTarget : Profile cyclingSignature.mixed :=
  fun _ => GameTheory.Math.Probability.FinDist.uniformFin 2

private theorem cycling_filter_card_eq_count (T : ℕ) (who action : Fin 2) :
    ((Finset.univ.filter fun round : Fin T =>
      cyclingHistory round who = action).card) =
      T.count (fun round => round % 2 = action.val) := by
  rw [Nat.count_eq_card_filter_range]
  refine Finset.card_bij (fun round _ => round.val) ?_ ?_ ?_
  · intro round hround
    rw [Finset.mem_filter] at hround ⊢
    refine ⟨Finset.mem_range.mpr round.isLt, ?_⟩
    simpa [cyclingHistory, Fin.ext_iff] using congrArg Fin.val hround.2
  · intro first hfirst second hsecond heq
    exact Fin.ext heq
  · intro round hround
    rw [Finset.mem_filter] at hround
    refine ⟨⟨round, Finset.mem_range.mp hround.1⟩, ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    apply Fin.ext
    simpa [cyclingHistory] using hround.2

private theorem cycling_count_bounds (T : ℕ) (action : Fin 2) :
    2 * T.count (fun round => round % 2 = action.val) ≤ T + 2 ∧
      T ≤ 2 * T.count (fun round => round % 2 = action.val) + 1 := by
  have hcount := Nat.count_modEq_card (b := T) (r := 2) (by decide) action.val
  have hcount' :
      T.count (fun round => round % 2 = action.val) =
        T / 2 + if action.val % 2 < T % 2 then 1 else 0 := by
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt action.isLt] using hcount
  have hdecompose := Nat.div_add_mod T 2
  have hmod : T % 2 < 2 := Nat.mod_lt T (by decide)
  rw [hcount']
  split <;> omega

private theorem cycling_empirical_prob_error
    (T : ℕ) [NeZero T] (who action : Fin 2) :
    |(cyclingForm.empiricalMarginal cyclingHistory who T).prob action - 1 / 2| ≤
      1 / (T : ℝ) := by
  rw [cyclingForm.empiricalMarginal_prob, cycling_filter_card_eq_count]
  obtain ⟨hupper, hlower⟩ := cycling_count_bounds T action
  have hTnat : 0 < T := Nat.pos_of_neZero T
  have hT : (0 : ℝ) < T := by exact_mod_cast hTnat
  have hupper' :
      2 * (T.count (fun round => round % 2 = action.val) : ℝ) ≤ T + 2 := by
    exact_mod_cast hupper
  have hlower' :
      (T : ℝ) ≤ 2 * T.count (fun round => round % 2 = action.val) + 1 := by
    exact_mod_cast hlower
  rw [abs_le]
  constructor
  · rw [show -(1 / (T : ℝ)) = (-1) / T by ring, div_le_iff₀ hT]
    field_simp
    nlinarith
  · rw [le_div_iff₀ hT]
    field_simp
    nlinarith

/-- Every coordinate of the forever-alternating trajectory converges to the
uniform law on its two actions. -/
theorem cycling_empiricalBelief_converges (who : Fin 2) :
    GameTheory.Math.Probability.FinDistConvergesPointwise
      (fun t => cyclingForm.empiricalBelief cyclingHistory (t + 1) who)
      (cyclingTarget who) := by
  intro action
  rw [show (cyclingTarget who).prob action = 1 / 2 by
    simp [cyclingTarget, GameTheory.Math.Probability.FinDist.prob_uniformFin]]
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (g := fun t : ℕ => 1 / ((t + 1 : ℕ) : ℝ))
    (fun _ => dist_nonneg) (fun t => ?_) ?_
  · simpa [GameForm.empiricalBelief, Real.dist_eq] using
      cycling_empirical_prob_error (t + 1) who action
  · simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- The public limit theorem now runs on a trajectory that changes forever in
both player coordinates. -/
theorem cycling_limit_isNash :
    IsNash cyclingGame.form.mixed (euPreference cyclingGame.utility)
      cyclingTarget :=
  UtilityGame.IsFictitiousPlay.limit_isNash
    (G := cyclingGame) cycling_isFictitiousPlay cycling_empiricalBelief_converges

end GameTheory.Tests.FictitiousPlay
