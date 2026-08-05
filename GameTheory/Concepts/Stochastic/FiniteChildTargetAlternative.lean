/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Math.Probability

/-!
# Finite child-target transport or strict payoff separation

A recurrent child cannot carry an arbitrary whole payoff-vector target.
For a finite family of eligible children, the exact geometric split is:

* the parent target belongs to the convex hull of the child targets, so a
  public randomized selector can in principle transport it in expectation;
* or one continuous linear payoff direction strictly separates the parent
  target from every eligible child target.

Both leaves contain positive data.  In particular, the second leaf is not
merely the negation of target feasibility.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Set Math.Probability

universe uPlayer uChild

variable {Player : Type uPlayer} {Child : Type uChild}

/-- Expected whole-vector target transport through a finite randomized
child selection. -/
def IsFiniteChildTargetTransportable
    (childTarget : Child → Player → ℝ)
    (parentTarget : Player → ℝ) : Prop :=
  parentTarget ∈ convexHull ℝ (Set.range childTarget)

/-- Operational presentation of target transport as one probability law on
the eligible child type. -/
def IsFiniteChildTargetLottery
    (childTarget : Child → Player → ℝ)
    (parentTarget : Player → ℝ) : Prop :=
  ∃ law : PMF Child,
    ∀ who, expect law (fun child => childTarget child who) =
      parentTarget who

/-- Convex target transport is exactly transport by a probability law on
the finite eligible child family. -/
theorem isFiniteChildTargetTransportable_iff_lottery
    [Finite Child]
    (childTarget : Child → Player → ℝ)
    (parentTarget : Player → ℝ) :
    IsFiniteChildTargetTransportable childTarget parentTarget ↔
      IsFiniteChildTargetLottery childTarget parentTarget := by
  classical
  constructor
  · intro feasible
    obtain ⟨Index, finiteIndex, weight, value,
        hweightNonneg, hweightSum, hvalue, hsum⟩ :=
      mem_convexHull_iff_exists_fintype.mp feasible
    letI : Fintype Index := finiteIndex
    choose child hchild using hvalue
    let indexLaw : PMF Index :=
      PMF.ofFintype
        (fun index => ENNReal.ofReal (weight index)) (by
          rw [← ENNReal.ofReal_one, ← hweightSum]
          exact
            (ENNReal.ofReal_sum_of_nonneg
              (fun index _ => hweightNonneg index)).symm)
    let childLaw : PMF Child := indexLaw.map child
    refine ⟨childLaw, ?_⟩
    intro who
    rw [expect_map]
    have hindexLaw (index : Index) :
        (indexLaw index).toReal = weight index := by
      simp [indexLaw, PMF.ofFintype_apply,
        ENNReal.toReal_ofReal (hweightNonneg index)]
    have hcoordinate :=
      congrFun hsum who
    simpa [expect_eq_sum, hindexLaw, hchild,
      Pi.smul_apply, smul_eq_mul] using hcoordinate
  · rintro ⟨law, hlaw⟩
    letI : Fintype Child := Fintype.ofFinite Child
    apply mem_convexHull_of_exists_fintype
      (fun child => (law child).toReal) childTarget
    · exact fun _ => ENNReal.toReal_nonneg
    · exact pmf_toReal_sum_one law
    · exact fun child => ⟨child, rfl⟩
    · funext who
      simpa [expect_eq_sum, Pi.smul_apply, smul_eq_mul]
        using hlaw who

/-- A positive obstruction to whole-vector target transport: one payoff
direction values the parent strictly above every eligible child. -/
structure FiniteChildTargetSeparator
    [Fintype Player]
    (childTarget : Child → Player → ℝ)
    (parentTarget : Player → ℝ) where
  direction : StrongDual ℝ (Player → ℝ)
  margin : ℝ
  margin_pos : 0 < margin
  child_add_margin_le :
    ∀ child,
      direction (childTarget child) + margin ≤
        direction parentTarget

namespace FiniteChildTargetSeparator

/-- The quantitative margin in particular gives strict separation. -/
theorem child_lt_parent
    [Fintype Player]
    {childTarget : Child → Player → ℝ}
    {parentTarget : Player → ℝ}
    (separator :
      FiniteChildTargetSeparator childTarget parentTarget)
    (child : Child) :
    separator.direction (childTarget child) <
      separator.direction parentTarget :=
  lt_of_lt_of_le
    (lt_add_of_pos_right _ separator.margin_pos)
    (separator.child_add_margin_le child)

end FiniteChildTargetSeparator

/-- The two exhaustive target leaves used by the obstruction atlas. -/
inductive FiniteChildTargetAlternative
    [Fintype Player]
    (childTarget : Child → Player → ℝ)
    (parentTarget : Player → ℝ) :
    Type (max (uPlayer + 1) uChild)
  | transport
      (feasible :
        IsFiniteChildTargetTransportable childTarget parentTarget)
  | separate
      (separator :
        FiniteChildTargetSeparator childTarget parentTarget)

/-- A strict target separator excludes every convex mixture of the eligible
child targets. -/
theorem FiniteChildTargetSeparator.not_transportable
    [Fintype Player]
    {childTarget : Child → Player → ℝ}
    {parentTarget : Player → ℝ}
    (separator :
      FiniteChildTargetSeparator childTarget parentTarget) :
    ¬IsFiniteChildTargetTransportable childTarget parentTarget := by
  intro feasible
  let childSet : Set (Player → ℝ) := Set.range childTarget
  have hbound :
      ∀ value ∈ childSet,
        separator.direction value < separator.direction parentTarget := by
    rintro value ⟨child, rfl⟩
    exact separator.child_lt_parent child
  have hconvexBound :
      ∀ value ∈ convexHull ℝ childSet,
        separator.direction value < separator.direction parentTarget := by
    let openHalfSpace : Set (Player → ℝ) :=
      {value |
        separator.direction value < separator.direction parentTarget}
    have hopenConvex : Convex ℝ openHalfSpace := by
      exact convex_halfSpace_lt
        (separator.direction :
          (Player → ℝ) →ₗ[ℝ] ℝ).isLinear
        (separator.direction parentTarget)
    have hsubset : childSet ⊆ openHalfSpace := by
      intro value hvalue
      exact hbound value hvalue
    have hhull : convexHull ℝ childSet ⊆ openHalfSpace :=
      convexHull_min hsubset hopenConvex
    exact fun value hvalue => hhull hvalue
  exact (lt_irrefl (separator.direction parentTarget))
    (hconvexBound parentTarget feasible)

/-- Every finite child family admits an honest whole-target alternative:
convex transport or one fixed strict payoff separator. -/
theorem exists_finiteChildTargetAlternative
    [Fintype Player] [Finite Child]
    (childTarget : Child → Player → ℝ)
    (parentTarget : Player → ℝ) :
    Nonempty
      (FiniteChildTargetAlternative childTarget parentTarget) := by
  classical
  by_cases feasible :
      IsFiniteChildTargetTransportable childTarget parentTarget
  · exact ⟨.transport feasible⟩
  · let childSet : Set (Player → ℝ) := Set.range childTarget
    have hfinite : childSet.Finite := Set.finite_range childTarget
    have hconvex : Convex ℝ (convexHull ℝ childSet) :=
      convex_convexHull ℝ childSet
    have hclosed : IsClosed (convexHull ℝ childSet) :=
      hfinite.isClosed_convexHull ℝ
    obtain ⟨direction, threshold, hchild, hparent⟩ :=
      geometric_hahn_banach_closed_point
        hconvex hclosed feasible
    refine ⟨.separate {
      direction := direction
      margin := direction parentTarget - threshold
      margin_pos := sub_pos.mpr hparent
      child_add_margin_le := ?_
    }⟩
    intro child
    have hmem :
        childTarget child ∈ convexHull ℝ childSet :=
      subset_convexHull ℝ childSet ⟨child, rfl⟩
    have hbelow := hchild (childTarget child) hmem
    linarith

end StochasticGame
end GameTheory
