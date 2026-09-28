/-
# Incentive implication without law matching, and through coupled utilities

A fair success chance against certain failure is implied by certain success
against certain failure, although no mixture of the source's prescribed law is
the target's prescribed law.

When two players' utilities sum to zero at each outcome, the second player
preferring `false` to `true` is implied by the first preferring `true` to
`false`. The two incentive differences lie on different player coordinates and
become equal only after projection onto the zero-sum class. Without that
restriction the implication fails, and a separating utility exhibits it.
-/

import GameTheory.Analysis.IncentiveCone
import GameTheory.Math.Probability.Mixture

noncomputable section

namespace GameTheory.Analysis.IncentiveConeTest

open GameTheory GameTheory.Math.Probability

/-! ## A scaled comparison -/

/-- Certain success against certain failure. -/
def source : Unit → IncentiveComparison Bool :=
  fun _ => ⟨PMF.pure true, PMF.pure false⟩

/-- A fair coin between success and failure. -/
def fair : PMF Bool := mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure true) (PMF.pure false)

/-- A fair success chance against certain failure. -/
def target : IncentiveComparison Bool := ⟨fair, PMF.pure false⟩

theorem target_difference : target.difference = (1 / 2 : ℝ) • (source ()).difference := by
  ext outcome
  cases outcome <;>
    norm_num [target, source, fair, IncentiveComparison.difference, mix_apply_toReal]

theorem target_mem_cone : target.difference ∈ IncentiveComparison.cone source := by
  rw [target_difference]
  exact (IncentiveComparison.cone source).smul_mem
    (IncentiveComparison.difference_mem_cone source ()) (by norm_num)

theorem target_holds_of_source (utility : Bool → ℝ) (respected : (source ()).Holds utility) :
    target.Holds utility :=
  (IncentiveComparison.mem_cone_iff source target).1 target_mem_cone utility fun _ => respected

/-- The target's prescribed law is no mixture of the source's. -/
theorem no_prescribed_mixture (roots : PMF Unit) :
    target.prescribed ≠ roots.bind fun root => (source root).prescribed := by
  intro same
  have hmass := congrArg (fun law : PMF Bool => (law true).toReal) same
  simp only [target, source, fair, mix_apply_toReal, PMF.bind_const] at hmass
  norm_num at hmass

/-! ## A zero-sum coupling -/

/-- Player-tagged outcomes. -/
abbrev Coordinate := Fin 2 × Bool

/-- The utilities of the two players sum to zero at every outcome. -/
def zeroSumUtilities : Submodule ℝ (EuclideanSpace ℝ Coordinate) where
  carrier := {utility | ∀ outcome, utility (0, outcome) + utility (1, outcome) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro first second hfirst hsecond outcome
    change first (0, outcome) + second (0, outcome) +
      (first (1, outcome) + second (1, outcome)) = 0
    linarith [hfirst outcome, hsecond outcome]
  smul_mem' := by
    intro amount utility hzero outcome
    change amount * utility (0, outcome) + amount * utility (1, outcome) = 0
    rw [← mul_add, hzero outcome, mul_zero]

/-- The second player prefers `false` to `true`. -/
def secondPrefersFalse : Unit → IncentiveComparison Coordinate :=
  fun _ => ⟨PMF.pure (1, false), PMF.pure (1, true)⟩

/-- The first player prefers `true` to `false`. -/
def firstPrefersTrue : IncentiveComparison Coordinate :=
  ⟨PMF.pure (0, true), PMF.pure (0, false)⟩

theorem projected_differences_equal :
    zeroSumUtilities.orthogonalProjectionOnto firstPrefersTrue.difference =
      zeroSumUtilities.orthogonalProjectionOnto (secondPrefersFalse ()).difference := by
  rw [IncentiveComparison.projected_difference_eq_iff]
  intro utility
  have hfalse := utility.property false
  have htrue := utility.property true
  simp only [firstPrefersTrue, secondPrefersFalse, expect_pure]
  change WithLp.ofLp utility.val (0, true) + WithLp.ofLp utility.val (1, true) = 0 at htrue
  change WithLp.ofLp utility.val (0, false) + WithLp.ofLp utility.val (1, false) = 0 at hfalse
  linarith

theorem firstPrefersTrue_mem_coneWithin :
    zeroSumUtilities.orthogonalProjectionOnto firstPrefersTrue.difference ∈
      IncentiveComparison.coneWithin zeroSumUtilities secondPrefersFalse := by
  rw [projected_differences_equal]
  exact IncentiveComparison.projected_difference_mem_coneWithin zeroSumUtilities
    secondPrefersFalse ()

/-- Without the coupling the implication fails: rewarding the first player for
`false` and ignoring the second player satisfies the source and violates the
target. -/
theorem firstPrefersTrue_not_mem_cone :
    firstPrefersTrue.difference ∉ IncentiveComparison.cone secondPrefersFalse := by
  rw [IncentiveComparison.mem_cone_iff]
  intro hpreserves
  let utility : Coordinate → ℝ := fun outcome => if outcome = (0, false) then 1 else 0
  have hsource : ∀ index, (secondPrefersFalse index).Holds utility := by
    intro index
    rw [IncentiveComparison.holds_iff]
    simp [secondPrefersFalse, utility, expect_pure]
  have htarget := (IncentiveComparison.holds_iff _ _).1 (hpreserves utility hsource)
  simp [firstPrefersTrue, utility, expect_pure] at htarget
  linarith

end GameTheory.Analysis.IncentiveConeTest
