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

noncomputable instance : Fintype Outcome :=
  ⟨{.a, .b, .c}, by intro outcome; cases outcome <;> simp⟩

abbrev source : GameForm Unit where
  sig := { Strategy := fun _ => PMF Outcome, Outcome := Outcome }
  play profile := profile ()

def remainingOutcome (choice : Bool) : Outcome := if choice then .b else .c

abbrev continuation : GameForm Unit where
  sig := { Strategy := fun _ => PMF Bool, Outcome := Outcome }
  play profile := (profile ()).map remainingOutcome

def utilityB : Outcome → Unit → ℝ
  | .a, _ => 3
  | .b, _ => 2
  | .c, _ => 1

def utilityC : Outcome → Unit → ℝ
  | .a, _ => 3
  | .b, _ => 1
  | .c, _ => 2

def sourcePlan : Profile source.sig := fun _ => PMF.pure .a

private theorem sourcePlan_optimal_of_le (u : Outcome → Unit → ℝ)
    (hmax : ∀ outcome, u outcome () ≤ u .a ()) :
    IsεNash source u 0 sourcePlan := by
  rw [isεNash_iff]
  intro who replacement
  cases who
  let hbase := payoffIntegrable_pure Outcome.a (fun outcome => u outcome ())
  let hdev := payoffIntegrable_of_finite replacement (fun outcome => u outcome ())
  refine ⟨hbase, hdev, ?_⟩
  simp only [source, Profile.update_same, sourcePlan, expectedUtility_pure, add_zero]
  calc
    expectedUtility u () replacement hdev ≤
        expect replacement (fun _ => u .a ()) (payoffIntegrable_constant _ _) := by
      exact expect_mono (fun outcome _ => hmax outcome)
        hdev (payoffIntegrable_constant _ _)
    _ = u .a () := expect_constant _ _ _

theorem sourcePlan_optimal_for_both :
    IsεNash source utilityB 0 sourcePlan ∧ IsεNash source utilityC 0 sourcePlan := by
  constructor
  · apply sourcePlan_optimal_of_le
    intro outcome
    cases outcome <;> norm_num [utilityB]
  · apply sourcePlan_optimal_of_le
    intro outcome
    cases outcome <;> norm_num [utilityC]

theorem continuation_utility_sum (profile : Profile continuation.sig) :
    expectedUtility utilityB () (continuation.play profile)
        (payoffIntegrable_of_finite _ _) +
      expectedUtility utilityC () (continuation.play profile)
        (payoffIntegrable_of_finite _ _) = 3 := by
  let hB := payoffIntegrable_of_finite (continuation.play profile)
    (fun outcome => utilityB outcome ())
  let hC := payoffIntegrable_of_finite (continuation.play profile)
    (fun outcome => utilityC outcome ())
  have values : (fun choice =>
      utilityB (remainingOutcome choice) () + utilityC (remainingOutcome choice) ()) =
      fun _ => (3 : ℝ) := by
    funext choice
    cases choice <;> norm_num [remainingOutcome, utilityB, utilityC]
  let hmap : PayoffIntegrable (profile ()) (fun choice =>
      utilityB (remainingOutcome choice) () + utilityC (remainingOutcome choice) ()) :=
    payoffIntegrable_of_finite _ _
  calc
    _ = expect (continuation.play profile)
        (fun outcome => utilityB outcome () + utilityC outcome ())
        (payoffIntegrable_add hB hC) := (expect_add hB hC).symm
    _ = expect (profile ())
        (fun choice => utilityB (remainingOutcome choice) () +
          utilityC (remainingOutcome choice) ()) hmap := by
      exact expect_map remainingOutcome (profile ())
        (fun outcome => utilityB outcome () + utilityC outcome ())
        hmap (payoffIntegrable_add hB hC)
    _ = expect (profile ()) (fun _ => (3 : ℝ))
        (payoffIntegrable_constant _ _) := by
      exact expect_congr_on_support (fun choice _ => congrFun values choice)
        hmap (payoffIntegrable_constant _ _)
    _ = 3 := expect_constant _ _ _

theorem no_common_optimal_continuation :
    ¬ ∃ profile : Profile continuation.sig,
      IsεNash continuation utilityB 0 profile ∧ IsεNash continuation utilityC 0 profile := by
  rintro ⟨profile, bestB, bestC⟩
  rw [isεNash_iff] at bestB bestC
  have prefersB := bestB () (PMF.pure true)
  have prefersC := bestC () (PMF.pure false)
  obtain ⟨hbaseB, hdevB, hleB⟩ := prefersB
  obtain ⟨hbaseC, hdevC, hleC⟩ := prefersC
  have hvalueB : expectedUtility utilityB ()
      (continuation.play (Profile.update profile () (PMF.pure true))) hdevB = 2 := by
    simp [continuation, expectedUtility_pure, remainingOutcome, utilityB]
  have hvalueC : expectedUtility utilityC ()
      (continuation.play (Profile.update profile () (PMF.pure false))) hdevC = 2 := by
    simp [continuation, expectedUtility_pure, remainingOutcome, utilityC]
  rw [hvalueB] at hleB
  rw [hvalueC] at hleC
  simp only [add_zero] at hleB hleC
  have total := continuation_utility_sum profile
  have hsameB : expectedUtility utilityB () (continuation.play profile) hbaseB =
      expectedUtility utilityB () (continuation.play profile)
        (payoffIntegrable_of_finite _ _) := by
    exact expect_proof_irrel _ _ _ _
  have hsameC : expectedUtility utilityC () (continuation.play profile) hbaseC =
      expectedUtility utilityC () (continuation.play profile)
        (payoffIntegrable_of_finite _ _) := by
    exact expect_proof_irrel _ _ _ _
  rw [hsameB] at hleB
  rw [hsameC] at hleC
  linarith

/-- Even randomized completion cannot preserve optimality for every utility
when it receives only the source plan and the restricted menu. -/
theorem no_utility_independent_completion :
    ¬ ∃ complete : PMF Outcome → PMF Bool,
      ∀ utility : Outcome → Unit → ℝ,
        IsεNash source utility 0 sourcePlan →
          IsεNash continuation utility 0 (fun _ => complete (sourcePlan ())) := by
  rintro ⟨complete, preserves⟩
  exact no_common_optimal_continuation
    ⟨fun _ => complete (sourcePlan ()),
      preserves utilityB sourcePlan_optimal_for_both.1,
      preserves utilityC sourcePlan_optimal_for_both.2⟩

end GameTheory.Tests.ContinuationMenus
