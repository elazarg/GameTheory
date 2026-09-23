/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Core.Approximate

/-! # An optimal plan does not determine optimal restricted continuations

Both utility profiles select `a` in the full one-decision game. When a retained
prefix leaves only `b` and `c` available, their best replies disagree. No
randomized continuation is optimal for both. A utility-independent compiler
cannot recover this missing ranking from the common source plan alone.
-/

noncomputable section

namespace GameTheory.Tests.ContinuationMenus

open GameTheory GameTheory.Math.Probability

inductive Outcome where
  | a | b | c
  deriving DecidableEq

abbrev source : GameForm Unit where
  sig := { Strategy := fun _ => FinDist Outcome, Outcome := Outcome }
  play profile := profile ()

def remainingOutcome (choice : Bool) : Outcome := if choice then .b else .c

abbrev continuation : GameForm Unit where
  sig := { Strategy := fun _ => FinDist Bool, Outcome := Outcome }
  play profile := (profile ()).map remainingOutcome

def utilityB : Outcome → Unit → ℝ
  | .a, _ => 3
  | .b, _ => 2
  | .c, _ => 1

def utilityC : Outcome → Unit → ℝ
  | .a, _ => 3
  | .b, _ => 1
  | .c, _ => 2

def sourcePlan : Profile source.sig := fun _ => FinDist.pure .a

theorem sourcePlan_optimal_for_both :
    IsεNash source utilityB 0 sourcePlan ∧ IsεNash source utilityC 0 sourcePlan := by
  constructor <;> rw [isεNash_iff] <;> intro who replacement <;> cases who
  all_goals
    simp only [expectedUtility, source, Profile.update_same, sourcePlan, FinDist.expect_pure,
      utilityB, utilityC, add_zero]
    apply FinDist.expect_le_of_forall
    intro result _
    cases result <;> norm_num [utilityB, utilityC]

theorem continuation_utility_sum (profile : Profile continuation.sig) :
    (continuation.play profile).expect (fun outcome => utilityB outcome ()) +
      (continuation.play profile).expect (fun outcome => utilityC outcome ()) = 3 := by
  simp only [continuation, FinDist.expect_map]
  rw [← FinDist.expect_add]
  have values : (fun choice =>
      utilityB (remainingOutcome choice) () + utilityC (remainingOutcome choice) ()) =
      fun _ => (3 : ℝ) := by
    funext choice
    cases choice <;> norm_num [remainingOutcome, utilityB, utilityC]
  rw [values, FinDist.expect_const]

theorem no_common_optimal_continuation :
    ¬ ∃ profile : Profile continuation.sig,
      IsεNash continuation utilityB 0 profile ∧ IsεNash continuation utilityC 0 profile := by
  rintro ⟨profile, bestB, bestC⟩
  rw [isεNash_iff] at bestB bestC
  have prefersB := bestB () (FinDist.pure true)
  have prefersC := bestC () (FinDist.pure false)
  simp only [expectedUtility, continuation, Profile.update_same, FinDist.map_pure,
    FinDist.expect_pure, remainingOutcome, ite_true, utilityB, utilityC,
    add_zero] at prefersB prefersC
  have total := continuation_utility_sum profile
  simp only [continuation, FinDist.expect_map] at total
  simp only [FinDist.expect_map] at prefersB prefersC
  have prefersB : (2 : ℝ) ≤ (profile ()).expect
      (fun choice => utilityB (remainingOutcome choice) ()) := prefersB
  have prefersC : (2 : ℝ) ≤ (profile ()).expect
      (fun choice => utilityC (remainingOutcome choice) ()) := prefersC
  linarith

/-- Even randomized completion cannot preserve optimality for every utility
when it receives only the source plan and the restricted menu. -/
theorem no_utility_independent_completion :
    ¬ ∃ complete : FinDist Outcome → FinDist Bool,
      ∀ utility : Outcome → Unit → ℝ,
        IsεNash source utility 0 sourcePlan →
          IsεNash continuation utility 0 (fun _ => complete (sourcePlan ())) := by
  rintro ⟨complete, preserves⟩
  exact no_common_optimal_continuation
    ⟨fun _ => complete (sourcePlan ()),
      preserves utilityB sourcePlan_optimal_for_both.1,
      preserves utilityC sourcePlan_optimal_for_both.2⟩

end GameTheory.Tests.ContinuationMenus
