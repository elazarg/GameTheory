/-
# EXP-055 witness: real knapsack VCG

The stable definitions live in `GameTheory.Mechanism.Knapsack.Basic` and
`GameTheory.Mechanism.Knapsack.Mechanism`.  This file retains the hostile
capacity-constrained instance used to validate pivot normalization.
-/

import GameTheory.Mechanism.Knapsack.Mechanism

namespace GameTheory.Experimental.KnapsackVCG

open GameTheory.Mechanism.Knapsack

private def unitCapacityData : Data (Fin 2) where
  weight := fun _ => 1
  capacity := 1

private theorem unitCapacity_nonnegative : 0 ≤ unitCapacityData.capacity := by
  norm_num [unitCapacityData]

private def lowReports : GameTheory.Mechanism.Auction.BidProfile (Fin 2) :=
  fun _ => 0

private def highOpponentReport : GameTheory.Mechanism.Auction.BidProfile (Fin 2)
  | 0 => 0
  | 1 => 3

example : ¬ Feasible unitCapacityData ({0, 1} : Finset (Fin 2)) := by
  norm_num [Feasible, load, aggregate, unitCapacityData]

example :
    (vcgSetup unitCapacityData unitCapacity_nonnegative).h 0 lowReports = 0 := by
  simp only [pivotOffset, maximalWelfare]
  rw [show (0 : ℝ) = lowReports 0 by rfl]
  rw [Profile.update_eq_self]
  apply Finset.sum_eq_zero
  intro who hwho
  simp [lowReports]

private theorem pivotOffset_highOpponent :
    (vcgSetup unitCapacityData unitCapacity_nonnegative).h 0 highOpponentReport = 3 := by
  simp only [pivotOffset]
  rw [show (0 : ℝ) = highOpponentReport 0 by rfl]
  rw [Profile.update_eq_self]
  have hsingleton :
      ({1} : Finset (Fin 2)) ∈
        feasibleAllocations unitCapacityData Finset.univ := by
    norm_num [feasibleAllocations, Feasible, load, aggregate, unitCapacityData]
  have hge := welfareMaximizer_ge unitCapacityData highOpponentReport
    Finset.univ unitCapacity_nonnegative hsingleton
  have hwelfare (selected : Finset (Fin 2)) :
      welfare highOpponentReport selected =
        if (1 : Fin 2) ∈ selected then 3 else 0 := by
    unfold welfare aggregate
    by_cases hone : (1 : Fin 2) ∈ selected
    · rw [if_pos hone, ← Finset.add_sum_erase selected _ hone]
      simp only [highOpponentReport]
      have hzero :
          (∑ x ∈ selected.erase 1,
              match x with
              | 0 => (0 : ℝ)
              | 1 => 3) = 0 := by
        apply Finset.sum_eq_zero
        intro who hwho
        have hne : who ≠ 1 := (Finset.mem_erase.mp hwho).1
        fin_cases who <;> simp_all
      rw [hzero]
      norm_num
    · rw [if_neg hone]
      apply Finset.sum_eq_zero
      intro who hwho
      fin_cases who <;> simp_all [highOpponentReport]
  unfold maximalWelfare
  rw [hwelfare ({1} : Finset (Fin 2)),
    hwelfare (welfareMaximizer unitCapacityData highOpponentReport Finset.univ
      unitCapacity_nonnegative)] at hge
  rw [hwelfare]
  simp only [Finset.mem_singleton, if_true] at hge
  by_cases hchosen :
      (1 : Fin 2) ∈
        welfareMaximizer unitCapacityData highOpponentReport Finset.univ
          unitCapacity_nonnegative
  · rw [if_pos hchosen]
  · rw [if_neg hchosen] at hge
    norm_num at hge

example (replacement : ℝ) :
    (vcgSetup unitCapacityData unitCapacity_nonnegative).h 0
        (Profile.update highOpponentReport 0 replacement) = 3 := by
  rw [vcgSetup_offset_independent]
  exact pivotOffset_highOpponent

example (reports : GameTheory.Mechanism.Auction.BidProfile (Fin 2)) :
    (vcgSetup unitCapacityData unitCapacity_nonnegative).vcgPayment
      (Profile.update reports 0 0) 0 = 0 :=
  vcgPayment_update_zero unitCapacityData unitCapacity_nonnegative reports 0

example :
    ∀ trueTypes : (vcgSetup unitCapacityData unitCapacity_nonnegative).ReportProfile,
      IsNash
        ((vcgSetup unitCapacityData unitCapacity_nonnegative).toUtilityGame trueTypes).form
        (euPreference
          ((vcgSetup unitCapacityData unitCapacity_nonnegative).toUtilityGame trueTypes).utility)
        trueTypes :=
  vcgSetup_truthful_isExPostNash unitCapacityData unitCapacity_nonnegative

#print axioms GameTheory.Mechanism.Knapsack.allocationRule_monotone
#print axioms GameTheory.Mechanism.Knapsack.vcgPayment_update_zero
#print axioms GameTheory.Mechanism.Knapsack.vcgSetup_truthful_isExPostNash

end GameTheory.Experimental.KnapsackVCG
