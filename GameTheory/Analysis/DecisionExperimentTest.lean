/-
# Controls for observation abstraction

Erasing a supported bit prevents randomized reporting, while merging an
unreachable state is harmless. Infinite hidden-state and action carriers use
the same guarded optimal-law correspondence.
-/

import GameTheory.Analysis.DecisionExperiment
import GameTheory.Math.Probability.Mixture
noncomputable section
namespace GameTheory.Tests.DecisionExperiment
open GameTheory.Math.Probability GameTheory.Math.Probability.ObservationAbstraction
open GameTheory.DecisionExperiment

private def fair : PMF Bool := mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure false) (PMF.pure true)

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

end GameTheory.Tests.DecisionExperiment
