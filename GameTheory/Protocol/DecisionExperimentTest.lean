/-
# Controls for observation abstraction

Erasing a supported bit prevents randomized reporting, while merging an
unreachable state is harmless. Infinite hidden-state and action carriers use
the same guarded optimal-law correspondence.
-/

import GameTheory.Protocol.DecisionPayoff
import GameTheory.Math.Probability.Mixture
noncomputable section
namespace GameTheory.Tests.DecisionExperiment
open GameTheory.Math.Probability GameTheory.Math.Probability.ObservationAbstraction
open GameTheory.DecisionExperiment

private def fair : PMF Bool := mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure false) (PMF.pure
  true)

private theorem erased_fact_not_determined : ¬ Determines fair (fun _ => ()) id := by
  intro determines
  have left : false ∈ fair.support :=
    mem_support_mix_left _ _ _ (by norm_num) (PMF.mem_support_pure_iff false false |>.mpr rfl)
  have right : true ∈ fair.support :=
    mem_support_mix_right _ _ _ (by norm_num) (PMF.mem_support_pure_iff true true |>.mpr rfl)
  have same : false = true := @determines ⟨false, left⟩ ⟨true, right⟩ rfl
  cases same

/-- Randomization cannot recover a supported bit erased by the observation. -/
theorem erased_bit_has_no_report_law :
    ¬ ∃ policy : Unit → PMF Bool, responseLaw fair (fun _ => ()) id policy =
      fair.map (fun state => (state, state)) := by
  intro matching
  exact erased_fact_not_determined
    ((exists_report_law_iff_determines fair (fun _ => ()) id).mp matching)

private theorem unreachable_merge_determines : Determines (PMF.pure false) (fun _ => ()) id := by
  intro first second _
  have left : first.1 = false := (PMF.mem_support_pure_iff false first.1).mp first.2
  have right : second.1 = false := (PMF.mem_support_pure_iff false second.1).mp second.2
  exact left.trans right.symm

/-- Merging a zero-prior state is harmless, even with an infinite action carrier. -/
theorem unreachable_merge_preserves_law (policy : Bool → PMF ℕ) :
    responseLaw (PMF.pure false) (fun _ => ()) id
      (averagePolicy (PMF.pure false) (fun _ => ()) policy) =
        responseLaw (PMF.pure false) id id policy :=
  averagePolicy_response_law _ _ _ unreachable_merge_determines policy

/-- The hidden state and action carriers can be infinite and utility need not be bounded. -/
theorem infinite_carrier_optimal_laws (prior : PMF (Bool × ℕ)) (utility : Bool → ℕ → ℝ)
    (law : PMF (Bool × ℕ)) :
    (∃ policy : Bool → PMF ℕ, IsOptimal prior Prod.fst Prod.fst utility policy ∧
      responseLaw prior Prod.fst Prod.fst policy = law) ↔
    (∃ policy : (Bool × ℕ) → PMF ℕ, IsOptimal prior id Prod.fst utility policy ∧
      responseLaw prior id Prod.fst policy = law) :=
  optimal_response_law_iff prior Prod.fst Prod.fst (fun _ _ same => same) utility law

private def varyingReward (state action : Bool) : ℝ :=
  if action then (if state then 2 else 1) else 0

private theorem varyingReward_bounded :
    ∀ state ∈ fair.support, ∀ action, |varyingReward state action| ≤ 2 := by
  intro state _ action
  cases state <;> cases action <;> norm_num [varyingReward]

/-- Payoff-relevant state differences need not force different optimal decisions. -/
theorem common_action_without_fact_recovery :
    HasCommonMaximizer fair (fun _ => ()) varyingReward ∧
      ¬ Determines fair (fun _ => ()) id := by
  refine ⟨?_, erased_fact_not_determined⟩
  intro signal _
  refine ⟨true, ?_⟩
  intro state _ _ alternative
  cases state <;> cases alternative <;> norm_num [varyingReward]

/-- This fixed payoff's coarse optima survive full observation despite the erased bit. -/
theorem varying_reward_preserves_optima :
    ∀ source : Unit → PMF Bool, IsOptimal fair (fun _ => ()) id varyingReward source →
      ∃ target : Bool → PMF Bool, IsOptimal fair id id varyingReward target ∧
        responseLaw fair id id target = responseLaw fair (fun _ => ()) id source :=
  (preserves_fixed_payoff_iff_commonMaximizer fair (fun _ => ()) id varyingReward
    varyingReward_bounded).mpr common_action_without_fact_recovery.1

/-- Constant-payoff preservation does not imply equality of all optimal retained laws:
truthful informed reporting is optimal but no erased-observation policy matches it. -/
theorem constant_payoff_has_extra_informed_law :
    IsOptimal fair id id (fun _ _ : Bool => (0 : ℝ)) (fun state => PMF.pure state) ∧
      ¬ ∃ source : Unit → PMF Bool,
        responseLaw fair (fun _ => ()) id source =
          responseLaw fair id id (fun state => PMF.pure state) := by
  constructor
  · apply (fullInformation_optimal_iff fair id (fun _ _ : Bool => (0 : ℝ))
      (C := 0) (fun _ _ _ => by norm_num) _).mpr
    intro state _ action
    simp only [expect_zero, le_refl]
  · rintro ⟨source, same⟩
    exact erased_bit_has_no_report_law ⟨source, same.trans (responseLaw_report_eq_map fair id)⟩

/-- A supported collision rules out preservation across all reporting utilities. -/
theorem erased_bit_fails_universal_optimality :
    ¬ (∀ utility : Bool → Bool → ℝ, ∀ source : Unit → PMF Bool,
      IsOptimal fair (fun _ => ()) id utility source →
        ∃ target : Bool → PMF Bool, IsOptimal fair id id utility target ∧
          responseLaw fair id id target = responseLaw fair (fun _ => ()) id source) := by
  intro preserves
  exact erased_fact_not_determined
    ((all_utilities_optimal_laws_iff_determines fair (fun _ => ()) id).mp preserves)

/-- Finite decisions admit an optimum even with an unrestricted prior on infinite states. -/
theorem infinite_prior_finite_menu (prior : PMF ℕ) (observe : ℕ → ℕ)
    (utility : ℕ → Bool → ℝ) {C : ℝ}
    (bounded : ∀ state ∈ prior.support, ∀ action, |utility state action| ≤ C) :
    ∃ policy : ℕ → PMF Bool, IsOptimal prior observe id utility policy :=
  exists_optimal prior observe id utility bounded

end GameTheory.Tests.DecisionExperiment
