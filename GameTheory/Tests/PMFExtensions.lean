import GameTheory.Math.Probability.ExpectationAlgebra
import GameTheory.Math.Probability.Bounds
import GameTheory.Math.Probability.Conditioning
import GameTheory.Math.Probability.Support
import GameTheory.Math.Probability.Mixture

noncomputable section

open GameTheory.Math.Probability

namespace GameTheory.Tests.PMFExtensions

def coin : PMF Bool :=
  mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure false) (PMF.pure true)

def sharedCoin : PMF (ℕ → Bool) := coin.map fun value _ => value

theorem infinite_shared_coin_marginal (index : ℕ) :
    sharedCoin.map (fun assignment => assignment index) = coin := by
  rw [sharedCoin, PMF.map_comp]
  exact PMF.map_id coin

theorem infinite_shared_coin_support :
    sharedCoin.support ⊆ {fun _ : ℕ => false, fun _ => true} := by
  intro assignment hmem
  rw [sharedCoin, PMF.mem_support_map_iff] at hmem
  obtain ⟨value, hvalue, rfl⟩ := hmem
  cases value <;> simp

theorem infinite_shared_coin_fair (index : ℕ) :
    (sharedCoin.map (fun assignment => assignment index) false).toReal = 1 / 2 ∧
      (sharedCoin.map (fun assignment => assignment index) true).toReal = 1 / 2 := by
  rw [infinite_shared_coin_marginal]
  constructor <;> rw [coin, mix_apply, PMF.pure_apply] <;> norm_num

theorem unique_branch_may_be_unsupported :
    let law : PMF Bool := PMF.pure false
    let branch := fun value : Bool => PMF.pure (if value then 1 else 0 : ℕ)
    true ∉ law.support ∧
      (law.bind branch) 1 = law true * branch true 1 := by
  dsimp only
  constructor
  · simp
  · rw [PMF.bind_apply]
    simp

theorem empty_event_weighting (law reference : PMF ℕ) :
    law.toOuterMeasure (∅ : Set ℕ) = 0 ∧
      expect law (fun value => if value ∈ (∅ : Set ℕ) then 1 else 0)
          (payoffIntegrable_of_bounded law _ (C := 1) (by intro x; simp)) =
        expect reference (fun _ => 0) (payoffIntegrable_zero reference) := by
  classical
  constructor
  · simp
  · calc
      expect law (fun value => if value ∈ (∅ : Set ℕ) then 1 else 0)
          (payoffIntegrable_of_bounded law _ (C := 1) (by intro x; simp)) =
        expect law (fun _ => 0) (payoffIntegrable_zero law) :=
          expect_congr_on_support (fun _ _ => by simp)
            (payoffIntegrable_of_bounded law _ (C := 1) (by intro x; simp))
            (payoffIntegrable_zero law)
      _ = expect reference (fun _ => 0) (payoffIntegrable_zero reference) := by
        rw [expect_constant, expect_constant]

/-- Embedding a law supported on even integers into the genuine subtype
preserves the source and every mapped observable. -/
theorem infinite_subtype_preserves_law (law : PMF ℕ)
    (supported : ∀ value ∈ law.support, Even value) :
  (PMF.bindOnSupport law (fun (value : ℕ) h =>
      PMF.pure (⟨value, supported value h⟩ : {n : ℕ // Even n}))).map
        Subtype.val = law ∧
      (PMF.bindOnSupport law (fun (value : ℕ) h =>
          PMF.pure (⟨value, supported value h⟩ : {n : ℕ // Even n}))).map
          (fun value => value.1 / 2) = law.map (fun value => value / 2) := by
  constructor
  · rw [map_bindOnSupport]
    have hmap : (fun (value : ℕ) (h : value ∈ law.support) =>
        PMF.map Subtype.val
          (PMF.pure (⟨value, supported value h⟩ : {n : ℕ // Even n}))) =
        fun value _ => PMF.pure value := by
      funext value h
      rw [PMF.pure_map]
    rw [hmap, PMF.bindOnSupport_eq_bind]
    calc
      law.bind PMF.pure = law.map id := PMF.bind_pure_comp id law
      _ = law := PMF.map_id law
  · rw [map_bindOnSupport]
    calc
      law.bindOnSupport (fun value h => PMF.map (fun x : {n : ℕ // Even n} => x.1 / 2)
          (PMF.pure (⟨value, supported value h⟩ : {n : ℕ // Even n}))) =
        law.bindOnSupport (fun value _ => PMF.pure (value / 2)) := by
          apply bindOnSupport_congr
          intro value h
          rw [PMF.pure_map]
      _ = law.map (fun value => value / 2) := by
          rw [PMF.bindOnSupport_eq_bind]
          exact PMF.bind_pure_comp (fun value => value / 2) law

/-! `mayFail` is public because the rejection theorem exposes this fixture's
support in its statement. -/
def mayFail : PMF (Option ℕ) :=
  mix (1 / 2) (by norm_num) (by norm_num)
    (PMF.pure (some 7)) (PMF.pure none)

theorem positive_failure_rejects_value_subtype :
    ¬ ∀ result ∈ mayFail.support, result.isSome = true := by
  intro supported
  have failed : none ∈ mayFail.support := by
    rw [PMF.mem_support_iff, mayFail, mix_apply]
    norm_num [PMF.pure_apply]
  exact Bool.false_ne_true (supported none failed)

/-- The null fiber has zero marginal, so the canonical posterior's positive-
weight premise cannot be supplied. This replaces the retired fallback law. -/
theorem null_fibre_not_conditionable :
    ¬ 0 < ((PMF.pure false : PMF Bool).map id true) := by
  simp

end GameTheory.Tests.PMFExtensions
