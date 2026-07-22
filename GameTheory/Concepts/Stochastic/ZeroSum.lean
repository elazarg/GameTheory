/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.Discounted
import Math.ProbabilityMassFunction.Simplex
import Math.ShapleyOperator

/-!
# Discounted Two-Player Zero-Sum Stochastic Games

This file connects the abstract matrix-form Shapley operator to the behavioral
stochastic-game semantics.  It supplies the three pieces of the verification
bridge:

* a pair presentation of dependent joint actions for player type `Fin 2`;
* the dictionary between simplex `wsum`s and expectations under independent
  product PMFs;
* stationary Shapley actions and their Bellman inequalities against arbitrary
  history-dependent opposing play.

Combined with the excessive-function guarantee theorem in
`GameTheory.Concepts.Stochastic.Discounted`, these ingredients prove that the
selected stationary strategies guarantee the normalized discounted Shapley
value against every behavioral strategy.
-/

noncomputable section

open scoped BigOperators NNReal

namespace GameTheory
namespace StochasticGame

open Math.Probability Math.PMFProduct Math.ProbabilityMassFunction
open Math.ShapleyOperator

/-- Build a dependent two-player joint action from its row and column
coordinates. -/
def pairJointAct (G : StochasticGame (Fin 2)) (row : G.Act 0)
    (col : G.Act 1) : G.JointAct :=
  Fin.cons row (Fin.cons col (fun k : Fin 0 => k.elim0))

@[simp] theorem pairJointAct_zero (G : StochasticGame (Fin 2))
    (row : G.Act 0) (col : G.Act 1) :
    G.pairJointAct row col 0 = row :=
  rfl

@[simp] theorem pairJointAct_one (G : StochasticGame (Fin 2))
    (row : G.Act 0) (col : G.Act 1) :
    G.pairJointAct row col 1 = col :=
  rfl

/-- Two-player joint actions are equivalent to row/column action pairs. -/
def jointActPairEquiv (G : StochasticGame (Fin 2)) :
    G.JointAct ≃ G.Act 0 × G.Act 1 where
  toFun a := (a 0, a 1)
  invFun p := G.pairJointAct p.1 p.2
  left_inv := by
    intro a
    funext i
    fin_cases i <;> rfl
  right_inv := by
    intro p
    ext <;> rfl

/-- Assemble the two marginal mixed actions into a dependent mixed profile. -/
def pairMixedActionProfile (G : StochasticGame (Fin 2))
    (row : PMF (G.Act 0)) (col : PMF (G.Act 1)) :
    ∀ i, PMF (G.Act i) :=
  Fin.cons row (Fin.cons col (fun k : Fin 0 => k.elim0))

@[simp] theorem pairMixedActionProfile_zero (G : StochasticGame (Fin 2))
    (row : PMF (G.Act 0)) (col : PMF (G.Act 1)) :
    G.pairMixedActionProfile row col 0 = row :=
  rfl

@[simp] theorem pairMixedActionProfile_one (G : StochasticGame (Fin 2))
    (row : PMF (G.Act 0)) (col : PMF (G.Act 1)) :
    G.pairMixedActionProfile row col 1 = col :=
  rfl

/-- Fubini for a two-player product mixed action, expressed through the pair
presentation of dependent joint actions. -/
theorem expect_pairMixedActionProfile (G : StochasticGame (Fin 2))
    [∀ i, Finite (G.Act i)] (row : PMF (G.Act 0)) (col : PMF (G.Act 1))
    (f : G.JointAct → ℝ) :
    expect (pmfPi (G.pairMixedActionProfile row col)) f =
      expect row (fun i => expect col (fun j => f (G.pairJointAct i j))) := by
  letI (i : Fin 2) : Fintype (G.Act i) := Fintype.ofFinite (G.Act i)
  rw [expect_eq_sum, expect_eq_sum]
  simp_rw [expect_eq_sum]
  let e := G.jointActPairEquiv
  calc
    (∑ a : G.JointAct,
        ((pmfPi (G.pairMixedActionProfile row col)) a).toReal * f a)
        = ∑ p : G.Act 0 × G.Act 1,
            (row p.1).toReal * (col p.2).toReal *
              f (G.pairJointAct p.1 p.2) := by
          refine Fintype.sum_equiv e _ _ ?_
          intro a
          change ((pmfPi (G.pairMixedActionProfile row col)) a).toReal * f a =
            (row (a 0)).toReal * (col (a 1)).toReal *
              f (G.pairJointAct (a 0) (a 1))
          rw [show G.pairJointAct (a 0) (a 1) = a from
            (G.jointActPairEquiv).left_inv a]
          simp [pmfPi_apply, Fin.prod_univ_two,
            ENNReal.toReal_mul]
    _ = ∑ i : G.Act 0, ∑ j : G.Act 1,
          (row i).toReal * (col j).toReal * f (G.pairJointAct i j) :=
        Fintype.sum_prod_type _
    _ = ∑ i : G.Act 0, (row i).toReal *
          ∑ j : G.Act 1, (col j).toReal * f (G.pairJointAct i j) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring

/-- The `wsum`/`pmfPi` dictionary for two-player mixed actions. -/
theorem expect_pairSimplex_eq_wsum (G : StochasticGame (Fin 2))
    [∀ i, Fintype (G.Act i)]
    (x : stdSimplex ℝ (G.Act 0)) (y : stdSimplex ℝ (G.Act 1))
    (f : G.JointAct → ℝ) :
    expect (pmfPi (G.pairMixedActionProfile
        ((stdSimplexEquiv (α := G.Act 0)).symm x)
        ((stdSimplexEquiv (α := G.Act 1)).symm y))) f =
      wsum x (fun i => wsum y (fun j => f (G.pairJointAct i j))) := by
  rw [G.expect_pairMixedActionProfile,
    expect_stdSimplexEquiv_symm_eq_wsum]
  apply congrArg (wsum x)
  funext i
  exact expect_stdSimplexEquiv_symm_eq_wsum y _

-- ============================================================================
-- Matrix-form presentation and selected Shapley actions
-- ============================================================================

/-- The row player's stage payoff in row/column matrix coordinates. -/
def rowStagePayoff (G : StochasticGame (Fin 2))
    (s : G.State) (i : G.Act 0) (j : G.Act 1) : ℝ :=
  G.stagePayoff s (G.pairJointAct i j) 0

/-- The transition kernel in row/column matrix coordinates. -/
def pairTransition (G : StochasticGame (Fin 2))
    (s : G.State) (i : G.Act 0) (j : G.Act 1) : PMF G.State :=
  G.transition s (G.pairJointAct i j)

/-- Stage payoff used by the normalized discounted Shapley equation. -/
def normalizedRowStagePayoff (G : StochasticGame (Fin 2)) (β : ℝ)
    (s : G.State) (i : G.Act 0) (j : G.Act 1) : ℝ :=
  (1 - β) * G.rowStagePayoff s i j

/-- The normalized discounted Shapley value of a finite two-player stochastic
game, presented as the fixed point of its statewise auxiliary matrix games. -/
noncomputable def discountedShapleyValue (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)] {β : ℝ≥0} (hβ : β < 1) : G.State → ℝ :=
  Math.ShapleyOperator.discountedValue
    (G.normalizedRowStagePayoff (β : ℝ)) G.pairTransition hβ

/-- The selected row simplex from Shapley's one-shot optimality certificate. -/
noncomputable def rowShapleySimplex (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)] {β : ℝ≥0} (hβ : β < 1)
    (s : G.State) : stdSimplex ℝ (G.Act 0) :=
  Classical.choose (Math.ShapleyOperator.exists_row_optimal_discountedValue
    (G.normalizedRowStagePayoff (β : ℝ)) G.pairTransition hβ s)

/-- The selected column simplex from Shapley's one-shot optimality
certificate. -/
noncomputable def colShapleySimplex (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)] {β : ℝ≥0} (hβ : β < 1)
    (s : G.State) : stdSimplex ℝ (G.Act 1) :=
  Classical.choose (Math.ShapleyOperator.exists_col_optimal_discountedValue
    (G.normalizedRowStagePayoff (β : ℝ)) G.pairTransition hβ s)

theorem rowShapleySimplex_spec (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)] {β : ℝ≥0} (hβ : β < 1)
    (s : G.State) (j : G.Act 1) :
    G.discountedShapleyValue hβ s ≤
      wsum (G.rowShapleySimplex hβ s) (fun i =>
        G.normalizedRowStagePayoff (β : ℝ) s i j +
          (β : ℝ) * expect (G.pairTransition s i j)
            (G.discountedShapleyValue hβ)) :=
  Classical.choose_spec
    (Math.ShapleyOperator.exists_row_optimal_discountedValue
      (G.normalizedRowStagePayoff (β : ℝ)) G.pairTransition hβ s) j

theorem colShapleySimplex_spec (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)] {β : ℝ≥0} (hβ : β < 1)
    (s : G.State) (i : G.Act 0) :
    wsum (G.colShapleySimplex hβ s) (fun j =>
        G.normalizedRowStagePayoff (β : ℝ) s i j +
          (β : ℝ) * expect (G.pairTransition s i j)
            (G.discountedShapleyValue hβ)) ≤
      G.discountedShapleyValue hβ s :=
  Classical.choose_spec
    (Math.ShapleyOperator.exists_col_optimal_discountedValue
      (G.normalizedRowStagePayoff (β : ℝ)) G.pairTransition hβ s) i

/-- The selected row mixed action, converted from its simplex certificate. -/
noncomputable def rowShapleyAction (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)] {β : ℝ≥0} (hβ : β < 1)
    (s : G.State) : PMF (G.Act 0) :=
  (stdSimplexEquiv (α := G.Act 0)).symm (G.rowShapleySimplex hβ s)

/-- The selected column mixed action, converted from its simplex certificate. -/
noncomputable def colShapleyAction (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)] {β : ℝ≥0} (hβ : β < 1)
    (s : G.State) : PMF (G.Act 1) :=
  (stdSimplexEquiv (α := G.Act 1)).symm (G.colShapleySimplex hβ s)

/-- Assemble a row and column behavior strategy into a dependent two-player
behavior profile. -/
def pairBehaviorProfile (G : StochasticGame (Fin 2))
    (row : G.BehaviorStrategy 0) (col : G.BehaviorStrategy 1) :
    G.BehaviorProfile :=
  Fin.cons row (Fin.cons col (fun k : Fin 0 => k.elim0))

@[simp] theorem pairBehaviorProfile_zero (G : StochasticGame (Fin 2))
    (row : G.BehaviorStrategy 0) (col : G.BehaviorStrategy 1) :
    G.pairBehaviorProfile row col 0 = row :=
  rfl

@[simp] theorem pairBehaviorProfile_one (G : StochasticGame (Fin 2))
    (row : G.BehaviorStrategy 0) (col : G.BehaviorStrategy 1) :
    G.pairBehaviorProfile row col 1 = col :=
  rfl

/-- The stationary Markov behavior strategy induced by the selected row
Shapley actions. -/
noncomputable def rowShapleyBehaviorStrategy (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)] {β : ℝ≥0} (hβ : β < 1) :
    G.BehaviorStrategy 0 :=
  fun _ h => G.rowShapleyAction hβ h.2

/-- The stationary Markov behavior strategy induced by the selected column
Shapley actions. -/
noncomputable def colShapleyBehaviorStrategy (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)] {β : ℝ≥0} (hβ : β < 1) :
    G.BehaviorStrategy 1 :=
  fun _ h => G.colShapleyAction hβ h.2

/-- The stationary profile formed by the selected row and column Shapley
actions. -/
noncomputable def shapleyBehaviorProfile (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)] {β : ℝ≥0} (hβ : β < 1) :
    G.BehaviorProfile :=
  G.pairBehaviorProfile (G.rowShapleyBehaviorStrategy hβ)
    (G.colShapleyBehaviorStrategy hβ)

@[simp] theorem stageActionDist_pairBehaviorProfile
    (G : StochasticGame (Fin 2))
    (row : G.BehaviorStrategy 0) (col : G.BehaviorStrategy 1)
    {t : ℕ} (h : G.Hist t) :
    G.stageActionDist (G.pairBehaviorProfile row col) h =
      pmfPi (G.pairMixedActionProfile (row t h) (col t h)) :=
  rfl

/-- The selected row action satisfies the Bellman lower inequality after
every history, against an arbitrary history-dependent column strategy. -/
theorem rowShapley_bellman_le (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)] {β : ℝ≥0} (hβ : β < 1)
    (col : G.BehaviorStrategy 1) (t : ℕ) (h : G.Hist t) :
    G.discountedShapleyValue hβ h.2 ≤
      (1 - (β : ℝ)) * G.stageEUAt
        (G.pairBehaviorProfile (G.rowShapleyBehaviorStrategy hβ) col) h 0 +
      (β : ℝ) * expect
        (G.stageActionDist
          (G.pairBehaviorProfile (G.rowShapleyBehaviorStrategy hβ) col) h)
        (fun a => expect (G.transition h.2 a)
          (G.discountedShapleyValue hβ)) := by
  let x := G.rowShapleySimplex hβ h.2
  let y := stdSimplexEquiv (col t h)
  let F : G.JointAct → ℝ := fun a =>
    (1 - (β : ℝ)) * G.stagePayoff h.2 a 0 +
      (β : ℝ) * expect (G.transition h.2 a)
        (G.discountedShapleyValue hβ)
  have hcert : ∀ j : G.Act 1,
      G.discountedShapleyValue hβ h.2 ≤
        wsum x (fun i => F (G.pairJointAct i j)) := by
    intro j
    simpa [x, F, normalizedRowStagePayoff, rowStagePayoff,
      pairTransition] using G.rowShapleySimplex_spec hβ h.2 j
  have havg : G.discountedShapleyValue hβ h.2 ≤
      wsum y (fun j => wsum x (fun i => F (G.pairJointAct i j))) := by
    calc
      G.discountedShapleyValue hβ h.2 =
          wsum y (fun _ => G.discountedShapleyValue hβ h.2) :=
        (wsum_const y _).symm
      _ ≤ wsum y (fun j => wsum x (fun i => F (G.pairJointAct i j))) :=
        wsum_le_wsum y hcert
  calc
    G.discountedShapleyValue hβ h.2 ≤
        wsum x (fun i => wsum y (fun j => F (G.pairJointAct i j))) := by
      rwa [wsum_wsum_comm x y]
    _ = expect (pmfPi (G.pairMixedActionProfile
          (G.rowShapleyAction hβ h.2) (col t h))) F := by
      rw [show G.rowShapleyAction hβ h.2 =
          (stdSimplexEquiv (α := G.Act 0)).symm x by rfl]
      rw [show col t h =
          (stdSimplexEquiv (α := G.Act 1)).symm y by
            exact (stdSimplexEquiv (α := G.Act 1)).symm_apply_apply (col t h) |>.symm]
      exact (G.expect_pairSimplex_eq_wsum x y F).symm
    _ = (1 - (β : ℝ)) * G.stageEUAt
          (G.pairBehaviorProfile (G.rowShapleyBehaviorStrategy hβ) col) h 0 +
        (β : ℝ) * expect
          (G.stageActionDist
            (G.pairBehaviorProfile (G.rowShapleyBehaviorStrategy hβ) col) h)
          (fun a => expect (G.transition h.2 a)
            (G.discountedShapleyValue hβ)) := by
      rw [expect_add, expect_const_mul, expect_const_mul]
      rfl

/-- A two-player stochastic game is zero-sum when the column player's stage
payoff is the negative of the row player's payoff at every state and action. -/
def IsZeroSum (G : StochasticGame (Fin 2)) : Prop :=
  ∀ (s : G.State) (a : G.JointAct),
    G.stagePayoff s a 1 = -G.stagePayoff s a 0

/-- The stationary Shapley row strategy guarantees the discounted value
against every history-dependent column strategy. -/
theorem discountedShapleyValue_le_row_discountedPayoff
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)] {β : ℝ≥0} (hβ : β < 1)
    (col : G.BehaviorStrategy 1) (s₀ : G.State) :
    G.discountedShapleyValue hβ s₀ ≤
      G.discountedPayoff (β : ℝ)
        (G.pairBehaviorProfile (G.rowShapleyBehaviorStrategy hβ) col) s₀ 0 := by
  obtain ⟨C, hC⟩ := exists_abs_bound_of_finite
    (fun p : G.State × G.JointAct => G.stagePayoff p.1 p.2 0)
  apply G.le_discountedPayoff_of_bellman_le
    (C := C) (fun s a => hC (s, a))
    (G.pairBehaviorProfile (G.rowShapleyBehaviorStrategy hβ) col) s₀
    (G.discountedShapleyValue hβ) (β := (β : ℝ)) β.coe_nonneg
    (by exact_mod_cast hβ)
  exact G.rowShapley_bellman_le hβ col

/-- The selected column action satisfies the Bellman lower inequality for the
column player's continuation value `-v`, against an arbitrary
history-dependent row strategy. -/
theorem colShapley_bellman_le (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)] (hzs : G.IsZeroSum)
    {β : ℝ≥0} (hβ : β < 1)
    (row : G.BehaviorStrategy 0) (t : ℕ) (h : G.Hist t) :
    -G.discountedShapleyValue hβ h.2 ≤
      (1 - (β : ℝ)) * G.stageEUAt
        (G.pairBehaviorProfile row (G.colShapleyBehaviorStrategy hβ)) h 1 +
      (β : ℝ) * expect
        (G.stageActionDist
          (G.pairBehaviorProfile row (G.colShapleyBehaviorStrategy hβ)) h)
        (fun a => expect (G.transition h.2 a)
          (fun s => -G.discountedShapleyValue hβ s)) := by
  let x := stdSimplexEquiv (row t h)
  let y := G.colShapleySimplex hβ h.2
  let F : G.JointAct → ℝ := fun a =>
    (1 - (β : ℝ)) * G.stagePayoff h.2 a 0 +
      (β : ℝ) * expect (G.transition h.2 a)
        (G.discountedShapleyValue hβ)
  let Fcol : G.JointAct → ℝ := fun a =>
    (1 - (β : ℝ)) * G.stagePayoff h.2 a 1 +
      (β : ℝ) * expect (G.transition h.2 a)
        (fun s => -G.discountedShapleyValue hβ s)
  have hcert : ∀ i : G.Act 0,
      wsum y (fun j => F (G.pairJointAct i j)) ≤
        G.discountedShapleyValue hβ h.2 := by
    intro i
    simpa [y, F, normalizedRowStagePayoff, rowStagePayoff,
      pairTransition] using G.colShapleySimplex_spec hβ h.2 i
  have havg : wsum x (fun i => wsum y (fun j =>
      F (G.pairJointAct i j))) ≤ G.discountedShapleyValue hβ h.2 := by
    calc
      wsum x (fun i => wsum y (fun j => F (G.pairJointAct i j))) ≤
          wsum x (fun _ => G.discountedShapleyValue hβ h.2) :=
        wsum_le_wsum x hcert
      _ = G.discountedShapleyValue hβ h.2 := wsum_const x _
  have hexpect : expect (pmfPi (G.pairMixedActionProfile
      (row t h) (G.colShapleyAction hβ h.2))) F ≤
      G.discountedShapleyValue hβ h.2 := by
    rw [show row t h = (stdSimplexEquiv (α := G.Act 0)).symm x by
      exact (stdSimplexEquiv (α := G.Act 0)).symm_apply_apply (row t h) |>.symm]
    rw [show G.colShapleyAction hβ h.2 =
      (stdSimplexEquiv (α := G.Act 1)).symm y by rfl]
    rw [G.expect_pairSimplex_eq_wsum]
    exact havg
  have hFcol : Fcol = fun a => -F a := by
    funext a
    unfold Fcol F
    rw [show expect (G.transition h.2 a)
        (fun s => -G.discountedShapleyValue hβ s) =
        -expect (G.transition h.2 a) (G.discountedShapleyValue hβ) by
      rw [show (fun s => -G.discountedShapleyValue hβ s) =
          fun s => (-1 : ℝ) * G.discountedShapleyValue hβ s by
        funext s
        ring]
      rw [expect_const_mul]
      ring]
    rw [hzs h.2 a]
    ring
  calc
    -G.discountedShapleyValue hβ h.2 ≤
        -expect (pmfPi (G.pairMixedActionProfile
          (row t h) (G.colShapleyAction hβ h.2))) F :=
      neg_le_neg hexpect
    _ = expect (pmfPi (G.pairMixedActionProfile
          (row t h) (G.colShapleyAction hβ h.2))) Fcol := by
      rw [hFcol, show (fun a => -F a) = fun a => (-1 : ℝ) * F a by
        funext a
        ring]
      rw [expect_const_mul]
      ring
    _ = (1 - (β : ℝ)) * G.stageEUAt
          (G.pairBehaviorProfile row (G.colShapleyBehaviorStrategy hβ)) h 1 +
        (β : ℝ) * expect
          (G.stageActionDist
            (G.pairBehaviorProfile row (G.colShapleyBehaviorStrategy hβ)) h)
          (fun a => expect (G.transition h.2 a)
            (fun s => -G.discountedShapleyValue hβ s)) := by
      rw [expect_add, expect_const_mul, expect_const_mul]
      rfl

/-- In a zero-sum game, the stationary Shapley column strategy guarantees
the negative discounted value against every history-dependent row strategy. -/
theorem neg_discountedShapleyValue_le_col_discountedPayoff
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)] (hzs : G.IsZeroSum)
    {β : ℝ≥0} (hβ : β < 1)
    (row : G.BehaviorStrategy 0) (s₀ : G.State) :
    -G.discountedShapleyValue hβ s₀ ≤
      G.discountedPayoff (β : ℝ)
        (G.pairBehaviorProfile row (G.colShapleyBehaviorStrategy hβ)) s₀ 1 := by
  obtain ⟨C, hC⟩ := exists_abs_bound_of_finite
    (fun p : G.State × G.JointAct => G.stagePayoff p.1 p.2 1)
  apply G.le_discountedPayoff_of_bellman_le
    (C := C) (fun s a => hC (s, a))
    (G.pairBehaviorProfile row (G.colShapleyBehaviorStrategy hβ)) s₀
    (fun s => -G.discountedShapleyValue hβ s) (β := (β : ℝ))
    β.coe_nonneg (by exact_mod_cast hβ)
  exact G.colShapley_bellman_le hzs hβ row

-- ============================================================================
-- Zero-sum payoff identities and discounted equilibrium
-- ============================================================================

theorem IsZeroSum.stageEUAt_one_eq_neg_zero
    {G : StochasticGame (Fin 2)} (hzs : G.IsZeroSum)
    (σ : G.BehaviorProfile) {t : ℕ} (h : G.Hist t) :
    G.stageEUAt σ h 1 = -G.stageEUAt σ h 0 := by
  unfold stageEUAt
  rw [show (fun a => G.stagePayoff h.2 a 1) =
      fun a => (-1 : ℝ) * G.stagePayoff h.2 a 0 by
    funext a
    rw [hzs h.2 a]
    ring]
  rw [expect_const_mul]
  ring

theorem IsZeroSum.expectedStagePayoff_one_eq_neg_zero
    {G : StochasticGame (Fin 2)} (hzs : G.IsZeroSum)
    (σ : G.BehaviorProfile) (s₀ : G.State) (t : ℕ) :
    G.expectedStagePayoff σ s₀ t 1 =
      -G.expectedStagePayoff σ s₀ t 0 := by
  unfold expectedStagePayoff
  rw [show (fun h => G.stageEUAt σ h 1) =
      fun h => (-1 : ℝ) * G.stageEUAt σ h 0 by
    funext h
    rw [hzs.stageEUAt_one_eq_neg_zero]
    ring]
  rw [expect_const_mul]
  ring

/-- Discounted payoffs remain zero-sum under every behavior profile. -/
theorem IsZeroSum.discountedPayoff_one_eq_neg_zero
    {G : StochasticGame (Fin 2)} (hzs : G.IsZeroSum)
    (β : ℝ) (σ : G.BehaviorProfile) (s₀ : G.State) :
    G.discountedPayoff β σ s₀ 1 = -G.discountedPayoff β σ s₀ 0 := by
  unfold discountedPayoff
  rw [show (fun t : ℕ => β ^ t * G.expectedStagePayoff σ s₀ t 1) =
      fun t : ℕ => -(β ^ t * G.expectedStagePayoff σ s₀ t 0) by
    funext t
    rw [hzs.expectedStagePayoff_one_eq_neg_zero]
    ring]
  rw [tsum_neg]
  ring

@[simp] theorem update_pairBehaviorProfile_zero
    (G : StochasticGame (Fin 2))
    (row row' : G.BehaviorStrategy 0) (col : G.BehaviorStrategy 1) :
    Function.update (G.pairBehaviorProfile row col) 0 row' =
      G.pairBehaviorProfile row' col := by
  funext i
  fin_cases i <;> simp

@[simp] theorem update_pairBehaviorProfile_one
    (G : StochasticGame (Fin 2))
    (row : G.BehaviorStrategy 0) (col col' : G.BehaviorStrategy 1) :
    Function.update (G.pairBehaviorProfile row col) 1 col' =
      G.pairBehaviorProfile row col' := by
  funext i
  fin_cases i <;> simp

/-- At the selected stationary profile, the row player's discounted payoff is
exactly the normalized Shapley value. -/
theorem discountedPayoff_shapleyBehaviorProfile_zero
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)] (hzs : G.IsZeroSum)
    {β : ℝ≥0} (hβ : β < 1) (s₀ : G.State) :
    G.discountedPayoff (β : ℝ) (G.shapleyBehaviorProfile hβ) s₀ 0 =
      G.discountedShapleyValue hβ s₀ := by
  have hrow := G.discountedShapleyValue_le_row_discountedPayoff hβ
    (G.colShapleyBehaviorStrategy hβ) s₀
  have hcol := G.neg_discountedShapleyValue_le_col_discountedPayoff hzs hβ
    (G.rowShapleyBehaviorStrategy hβ) s₀
  have hzero := hzs.discountedPayoff_one_eq_neg_zero (β : ℝ)
    (G.shapleyBehaviorProfile hβ) s₀
  change G.discountedShapleyValue hβ s₀ ≤
    G.discountedPayoff (β : ℝ) (G.shapleyBehaviorProfile hβ) s₀ 0 at hrow
  change -G.discountedShapleyValue hβ s₀ ≤
    G.discountedPayoff (β : ℝ) (G.shapleyBehaviorProfile hβ) s₀ 1 at hcol
  linarith

/-- At the selected stationary profile, the column player's discounted payoff
is the negative normalized Shapley value. -/
theorem discountedPayoff_shapleyBehaviorProfile_one
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)] (hzs : G.IsZeroSum)
    {β : ℝ≥0} (hβ : β < 1) (s₀ : G.State) :
    G.discountedPayoff (β : ℝ) (G.shapleyBehaviorProfile hβ) s₀ 1 =
      -G.discountedShapleyValue hβ s₀ := by
  rw [hzs.discountedPayoff_one_eq_neg_zero,
    G.discountedPayoff_shapleyBehaviorProfile_zero hzs hβ]

/-- **Shapley's discounted equilibrium theorem, behavioral form.**  The
selected stationary row and column actions form an exact Nash equilibrium of
the normalized discounted stochastic game against arbitrary
history-dependent unilateral deviations. -/
theorem shapleyBehaviorProfile_isDiscountedNash
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)] (hzs : G.IsZeroSum)
    {β : ℝ≥0} (hβ : β < 1) (s₀ : G.State) :
    G.IsDiscountedεNash (β : ℝ) s₀ 0 (G.shapleyBehaviorProfile hβ) := by
  intro who dev
  fin_cases who
  · change G.discountedPayoff (β : ℝ) (G.shapleyBehaviorProfile hβ) s₀ 0 + 0 ≥
      G.discountedPayoff (β : ℝ)
        (Function.update (G.shapleyBehaviorProfile hβ) 0 dev) s₀ 0
    rw [add_zero, G.discountedPayoff_shapleyBehaviorProfile_zero hzs hβ]
    have hcol := G.neg_discountedShapleyValue_le_col_discountedPayoff hzs hβ
      dev s₀
    have hzero := hzs.discountedPayoff_one_eq_neg_zero (β : ℝ)
      (G.pairBehaviorProfile dev (G.colShapleyBehaviorStrategy hβ)) s₀
    rw [show Function.update (G.shapleyBehaviorProfile hβ) 0 dev =
      G.pairBehaviorProfile dev (G.colShapleyBehaviorStrategy hβ) by
        exact G.update_pairBehaviorProfile_zero _ _ _]
    linarith
  · change G.discountedPayoff (β : ℝ) (G.shapleyBehaviorProfile hβ) s₀ 1 + 0 ≥
      G.discountedPayoff (β : ℝ)
        (Function.update (G.shapleyBehaviorProfile hβ) 1 dev) s₀ 1
    rw [add_zero, G.discountedPayoff_shapleyBehaviorProfile_one hzs hβ]
    have hrow := G.discountedShapleyValue_le_row_discountedPayoff hβ dev s₀
    have hzero := hzs.discountedPayoff_one_eq_neg_zero (β : ℝ)
      (G.pairBehaviorProfile (G.rowShapleyBehaviorStrategy hβ) dev) s₀
    rw [show Function.update (G.shapleyBehaviorProfile hβ) 1 dev =
      G.pairBehaviorProfile (G.rowShapleyBehaviorStrategy hβ) dev by
        exact G.update_pairBehaviorProfile_one _ _ _]
    linarith

end StochasticGame
end GameTheory
