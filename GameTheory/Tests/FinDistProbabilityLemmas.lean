/-
# Finite-law probability identities

The fixtures deliberately use `Nat` carriers: finite support does not require
the carrier itself to be finite.
-/

import GameTheory.Math.Probability.FinDist

noncomputable section

namespace GameTheory.Tests.FinDistProbabilityLemmas

open GameTheory.Math.Probability

def twoPointNat : FinDist Nat :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num) (FinDist.pure 1) (FinDist.pure 2)

def mergeAtZero (n : Nat) : Nat := if n = 1 ∨ n = 2 then 0 else n

def twoPointBool : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num) (FinDist.pure true) (FinDist.pure false)

def jointObservable : Nat × Bool → ℝ := fun p =>
  if p.1 = 1 ∧ p.2 then 3 else if p.1 = 2 ∧ ¬p.2 then 5 else 0

theorem map_probability_merges_at_zero :
    (twoPointNat.map mergeAtZero).prob 0 =
      twoPointNat.probOf (mergeAtZero ⁻¹' ({0} : Set Nat)) := by
  exact FinDist.prob_map_eq_probOf_preimage_singleton mergeAtZero twoPointNat 0

theorem map_probability_merges_at_zero_is_one :
    (twoPointNat.map mergeAtZero).prob 0 = 1 := by
  rw [FinDist.prob_map]
  norm_num [twoPointNat, mergeAtZero, FinDist.expect_mix, FinDist.expect_pure,
    FinDist.prob_pure_eq_ite]

theorem map_probability_outside_support_is_zero :
    (twoPointNat.map mergeAtZero).prob 99 = 0 := by
  rw [FinDist.prob_map]
  norm_num [twoPointNat, mergeAtZero, FinDist.expect_mix, FinDist.expect_pure,
    FinDist.prob_pure_eq_ite]

theorem expect_product_nonseparable :
    (FinDist.product twoPointNat twoPointBool).expect jointObservable =
      twoPointNat.expect (fun a => twoPointBool.expect (fun b => jointObservable (a, b))) := by
  exact FinDist.expect_product twoPointNat twoPointBool jointObservable

theorem expect_product_nonseparable_value :
    (FinDist.product twoPointNat twoPointBool).expect jointObservable = 2 := by
  rw [FinDist.expect_product]
  norm_num [twoPointNat, twoPointBool, jointObservable, FinDist.expect_mix,
    FinDist.expect_pure]

theorem expect_product_pure_right (a : Nat) (b : Bool) (u : Nat × Bool → ℝ) :
    (FinDist.product (FinDist.pure a) (FinDist.pure b)).expect u =
      (FinDist.pure a).expect (fun x => (FinDist.pure b).expect (fun y => u (x, y))) := by
  exact FinDist.expect_product (FinDist.pure a) (FinDist.pure b) u

theorem expect_product_on_infinite_carriers (μ ν : FinDist Nat) (u : Nat × Nat → ℝ) :
    (FinDist.product μ ν).expect u = μ.expect (fun a => ν.expect (fun b => u (a, b))) := by
  exact FinDist.expect_product μ ν u

end GameTheory.Tests.FinDistProbabilityLemmas
