/-
EXP-132: the product-belief/mixed-dominator integration boundary.

Every pure payoff row and mixed-dominator payoff column is integrable. The
joint product law is not: the baseline is an independent best response to an
infinite-support belief, while a PMF mixture strictly dominates it at every
pure opponent action.
-/

import GameTheory.Core.Rationalizability
import GameTheory.Experimental.PostArchitecture.PMFRestorationProbe

noncomputable section

namespace GameTheory.Experimental.PMFRationalizabilityGate

open GameTheory GameTheory.Math.Probability
open GameTheory.Experimental.PMFRestoration

def weight (n : ℕ) : ℝ := (geometric n).toReal

theorem weight_pos (n : ℕ) : 0 < weight n := by
  exact ENNReal.toReal_pos (geometric_positive n).ne' (geometric.apply_ne_top n)

private theorem integrable_two_points {α : Type*} [DecidableEq α]
    (μ : PMF α) (f : α → ℝ) (a b : α)
    (hzero : ∀ x, x ≠ a → x ≠ b → f x = 0) : PayoffIntegrable μ f := by
  apply payoffIntegrable_of_bounded μ f (C := max |f a| |f b|)
  intro x
  by_cases hxa : x = a
  · simp [hxa]
  by_cases hxb : x = b
  · simp [hxb]
  simp [hzero x hxa hxb]

private theorem expect_two_points {α : Type*} [DecidableEq α]
    (μ : PMF α) (f : α → ℝ) (a b : α) (hab : a ≠ b)
    (hzero : ∀ x, x ≠ a → x ≠ b → f x = 0)
    (hi : PayoffIntegrable μ f) :
    expect μ f hi = (μ a).toReal * f a + (μ b).toReal * f b := by
  unfold expect
  rw [tsum_eq_sum (s := {a, b})]
  · simp [hab]
  · intro x hx
    have hxa : x ≠ a := by
      intro heq
      apply hx
      simp [heq]
    have hxb : x ≠ b := by
      intro heq
      apply hx
      simp [heq]
    simp [hzero x hxa hxb]

/-- The two adjacent diagonals have cancelling opponent averages in each
positive row, but positive own-mixture averages in every column. -/
def matrix (n m : ℕ) : ℝ :=
  if n = m then -((n : ℝ) + 1) / (weight n * weight n)
  else if n = m + 1 then ((n : ℝ) + 1) / (weight n * weight m)
  else 0

private theorem matrix_row_support (n m : ℕ)
    (hdiag : m ≠ n) (hprev : m + 1 ≠ n) : matrix n m = 0 := by
  simp [matrix, Ne.symm hdiag, Ne.symm hprev]

private theorem matrix_col_support (n m : ℕ)
    (hdiag : n ≠ m) (hnext : n ≠ m + 1) : matrix n m = 0 := by
  simp [matrix, hdiag, hnext]

theorem row_integrable (n : ℕ) :
    PayoffIntegrable geometric (matrix n) := by
  cases n with
  | zero =>
      apply integrable_two_points geometric (matrix 0) 0 1
      intro m hm0 hm1
      exact matrix_row_support 0 m hm0 (by omega)
  | succ k =>
      apply integrable_two_points geometric (matrix (k + 1)) k (k + 1)
      intro m hmk hmkn
      exact matrix_row_support (k + 1) m hmkn (by omega)

theorem column_integrable (m : ℕ) :
    PayoffIntegrable geometric (fun n => matrix n m) := by
  apply integrable_two_points geometric (fun n => matrix n m) m (m + 1)
  intro n hnm hnnext
  exact matrix_col_support n m hnm hnnext

theorem row_expect_zero :
    expect geometric (matrix 0) (row_integrable 0) = -1 / weight 0 := by
  have hne := (weight_pos 0).ne'
  rw [expect_two_points geometric (matrix 0) 0 1 (by omega)]
  · simp [matrix, weight]
    field_simp [hne]
  · intro m hm0 _
    exact matrix_row_support 0 m hm0 (by omega)

theorem row_expect_succ (k : ℕ) :
    expect geometric (matrix (k + 1)) (row_integrable (k + 1)) = 0 := by
  have hk := (weight_pos k).ne'
  have hks := (weight_pos (k + 1)).ne'
  rw [expect_two_points geometric (matrix (k + 1)) k (k + 1) (by omega)]
  · simp [matrix]
    dsimp only [weight] at hk hks ⊢
    field_simp [hk, hks]
    ring
  · intro m hmk hmkn
    exact matrix_row_support (k + 1) m hmkn (by omega)

theorem column_expect (m : ℕ) :
    expect geometric (fun n => matrix n m) (column_integrable m) =
      1 / weight m := by
  have hm := (weight_pos m).ne'
  have hms := (weight_pos (m + 1)).ne'
  rw [expect_two_points geometric (fun n => matrix n m) m (m + 1) (by omega)]
  · simp [matrix]
    dsimp only [weight] at hm hms ⊢
    field_simp [hm, hms]
    ring
  · intro n hnm hnnext
    exact matrix_col_support n m hnm hnnext

def focalPayoff : ℕ × ℕ → ℝ
  | (0, _) => 0
  | (n + 1, m) => matrix n m

abbrev sig : GameSignature Bool where
  Strategy _ := ℕ
  Outcome := ℕ × ℕ

abbrev form : GameForm Bool :=
  GameForm.deterministic sig fun profile => (profile false, profile true)

def utility (outcome : sig.Outcome) (who : Bool) : ℝ :=
  if who then 0 else focalPayoff outcome

def beliefs : Profile sig.mixed :=
  fun who => if who then geometric else PMF.pure 0

def replacement : PMF (sig.Strategy false) := geometric.map Nat.succ

theorem pure_action_law (action : ℕ) :
    form.mixed.play (Profile.update beliefs false (PMF.pure action)) =
      geometric.map (fun m => (action, m)) := by
  rw [mixed_play_update_pure_eq_bind]
  have hkernel :
      (fun profile : Profile sig =>
        form.play (Profile.update profile false action)) =
        (PMF.pure ∘ fun profile : Profile sig => (action, profile true)) := by
    funext profile
    simp [form, Profile.update_same, Profile.update_of_ne]
  rw [hkernel, PMF.bind_pure_comp]
  calc
    (independentProduct beliefs).map (fun profile : Profile sig =>
        (action, profile true)) =
        ((independentProduct beliefs).map (fun profile => profile true)).map
          (fun m => (action, m)) := by
      rw [PMF.map_comp]
      rfl
    _ = geometric.map (fun m => (action, m)) := by
      rw [independentProduct_map_eval]
      rfl

theorem randomized_law (profile : Profile sig) :
    randomizedDeviationOutcome form profile false replacement =
      geometric.map (fun n => (n + 1, profile true)) := by
  rw [randomizedDeviationOutcome_eq_bind]
  have hkernel :
      (fun action : ℕ => form.play (Profile.update profile false action)) =
        (PMF.pure ∘ fun action : ℕ => (action, profile true)) := by
    funext action
    simp [form, Profile.update_same, Profile.update_of_ne]
  rw [hkernel, PMF.bind_pure_comp, replacement, PMF.map_comp]
  rfl

theorem pure_action_integrable (action : ℕ) :
    UtilityIntegrable utility false
      (form.mixed.play (Profile.update beliefs false (PMF.pure action))) := by
  rw [pure_action_law]
  apply (payoffIntegrable_map_iff (fun m => (action, m)) geometric
    (fun outcome => utility outcome false)).mpr
  cases action with
  | zero =>
      exact payoffIntegrable_constant geometric (0 : ℝ)
  | succ n =>
      exact row_integrable n

theorem pure_action_value_zero :
    expectedUtility utility false
      (form.mixed.play (Profile.update beliefs false (PMF.pure 0)))
      (pure_action_integrable 0) = 0 := by
  have hmap : UtilityIntegrable utility false
      (geometric.map (fun m => (0, m))) := by
    rw [← pure_action_law]
    exact pure_action_integrable 0
  calc
    _ = expectedUtility utility false (geometric.map (fun m => (0, m))) hmap :=
      expectedUtility_congr_law utility false (pure_action_law 0) _ hmap
    _ = 0 := by
      rw [expectedUtility_map]
      exact expect_constant geometric (0 : ℝ) _

theorem pure_action_value_succ (n : ℕ) :
    expectedUtility utility false
      (form.mixed.play (Profile.update beliefs false (PMF.pure (n + 1))))
      (pure_action_integrable (n + 1)) =
        expect geometric (matrix n) (row_integrable n) := by
  have hmap : UtilityIntegrable utility false
      (geometric.map (fun m => (n + 1, m))) := by
    rw [← pure_action_law]
    exact pure_action_integrable (n + 1)
  calc
    _ = expectedUtility utility false (geometric.map (fun m => (n + 1, m))) hmap :=
      expectedUtility_congr_law utility false (pure_action_law (n + 1)) _ hmap
    _ = expect geometric (matrix n) (row_integrable n) := by
      rw [expectedUtility_map]
      rfl

theorem randomized_integrable (profile : Profile sig) :
    UtilityIntegrable utility false
      (randomizedDeviationOutcome form profile false replacement) := by
  rw [randomized_law]
  apply (payoffIntegrable_map_iff (fun n => (n + 1, profile true)) geometric
    (fun outcome => utility outcome false)).mpr
  exact column_integrable (profile true)

theorem randomized_value (profile : Profile sig) :
    expectedUtility utility false
      (randomizedDeviationOutcome form profile false replacement)
      (randomized_integrable profile) = 1 / weight (profile true) := by
  have hmap : UtilityIntegrable utility false
      (geometric.map (fun n => (n + 1, profile true))) := by
    rw [← randomized_law]
    exact randomized_integrable profile
  calc
    _ = expectedUtility utility false
          (geometric.map (fun n => (n + 1, profile true))) hmap :=
      expectedUtility_congr_law utility false (randomized_law profile) _ hmap
    _ = 1 / weight (profile true) := by
      rw [expectedUtility_map]
      exact column_expect (profile true)

theorem pure_action_value_le_zero (action : ℕ) :
    expectedUtility utility false
      (form.mixed.play (Profile.update beliefs false (PMF.pure action)))
      (pure_action_integrable action) ≤ 0 := by
  cases action with
  | zero => rw [pure_action_value_zero]
  | succ n =>
      rw [pure_action_value_succ]
      cases n with
      | zero =>
          rw [row_expect_zero]
          have hnonneg : 0 ≤ 1 / weight 0 :=
            (one_div_pos.mpr (weight_pos 0)).le
          simpa only [neg_div] using neg_nonpos.mpr hnonneg
      | succ k =>
          rw [row_expect_succ]

theorem baseline_best :
    IsIndependentBestResponse form (euPreference utility) false 0 beliefs := by
  intro alternative
  exact (euPreference_iff utility false _ _
    (pure_action_integrable 0) (pure_action_integrable alternative)).mpr (by
      rw [pure_action_value_zero]
      exact pure_action_value_le_zero alternative)

theorem replacement_strict (profile : Profile sig) :
    Preference.strict (euPreference utility) false
      (randomizedDeviationOutcome form profile false replacement)
      (form.play (Profile.update profile false 0)) := by
  have hbase : UtilityIntegrable utility false
      (form.play (Profile.update profile false 0)) := by
    exact payoffIntegrable_pure _ _
  apply (euPreference_strict_iff utility false _ _
    (randomized_integrable profile) hbase).mpr
  rw [randomized_value]
  have hzero : expectedUtility utility false
      (form.play (Profile.update profile false 0)) hbase = 0 := by
    simp [form, expectedUtility_pure, utility, focalPayoff,
      Profile.update_same, Profile.update_of_ne]
  rw [hzero]
  exact one_div_pos.mpr (weight_pos (profile true))

theorem baseline_strictly_dominated :
    StrictlyDominatedByMixed form (euPreference utility) false 0 :=
  ⟨replacement, replacement_strict⟩

/-- The original unguarded inclusion already fails after one elimination round. -/
theorem baseline_survives_independent_round_one :
    (0 : ℕ) ∈ independentSurvivors form (euPreference utility) 1 false := by
  refine ⟨Set.mem_univ _, beliefs, ?_, baseline_best⟩
  intro player _ action _
  exact Set.mem_univ action

theorem opponent_best (action : ℕ) :
    IsIndependentBestResponse form (euPreference utility) true action beliefs := by
  intro alternative
  have hi (law : PMF sig.Outcome) : UtilityIntegrable utility true law :=
    payoffIntegrable_constant law 0
  have hvalue (law : PMF sig.Outcome) (hlaw : UtilityIntegrable utility true law) :
      expectedUtility utility true law hlaw = 0 := by
    exact expect_constant law 0 hlaw
  exact (euPreference_iff utility true _ _ (hi _) (hi _)).mpr (by
    rw [hvalue, hvalue])

theorem baseline_survives_independent_all_rounds (round : ℕ) :
    (0 : ℕ) ∈ independentSurvivors form (euPreference utility) round false ∧
      ∀ action : ℕ,
        action ∈ independentSurvivors form (euPreference utility) round true := by
  induction round with
  | zero => exact ⟨Set.mem_univ _, fun action => Set.mem_univ action⟩
  | succ earlier ih =>
      constructor
      · refine ⟨ih.1, beliefs, ?_, baseline_best⟩
        intro player hother action _
        cases player with
        | false => exact False.elim (hother rfl)
        | true => exact ih.2 action
      · intro action
        refine ⟨ih.2 action, beliefs, ?_, opponent_best action⟩
        intro player hother alternative hsupport
        cases player with
        | false =>
            have heq : alternative = 0 := by
              simpa [beliefs, PMF.mem_support_pure_iff] using hsupport
            subst alternative
            exact ih.1
        | true => exact False.elim (hother rfl)

theorem baseline_is_independent_rationalizable :
    IsIndependentRationalizable form (euPreference utility) false 0 :=
  fun round => (baseline_survives_independent_all_rounds round).1

theorem baseline_removed_correlated_round_one :
    (0 : ℕ) ∉ correlatedSurvivors form (euPreference utility) 1 false := by
  intro hsurvives
  obtain ⟨_, hnot⟩ := hsurvives
  apply hnot
  exact ⟨replacement, (fun action _ => Set.mem_univ action),
    fun profile _ => replacement_strict profile⟩

theorem baseline_not_correlated_rationalizable :
    ¬ IsCorrelatedRationalizable form (euPreference utility) false 0 :=
  fun h => baseline_removed_correlated_round_one (h 1)

theorem original_all_round_inclusion_false :
    ¬ (∀ action : ℕ,
      IsIndependentRationalizable form (euPreference utility) false action →
        IsCorrelatedRationalizable form (euPreference utility) false action) := by
  intro hinclusion
  exact baseline_not_correlated_rationalizable
    (hinclusion 0 baseline_is_independent_rationalizable)

theorem infinite_opponent_belief_support :
    ¬ (beliefs true).support.Finite := by
  rw [show beliefs true = geometric by rfl, geometric_support]
  exact Set.infinite_univ

/-- Pointwise row and column integration cannot be promoted to integration
of the joint product-belief/mixed-dominator outcome law. -/
theorem joint_law_not_integrable :
    ¬ UtilityIntegrable utility false
      (form.mixed.play (Profile.update beliefs false replacement)) := by
  intro hjoint
  exact IsIndependentBestResponse.not_strict_mixed_on_support form
    baseline_best replacement hjoint (fun profile _ => replacement_strict profile)

end GameTheory.Experimental.PMFRationalizabilityGate
