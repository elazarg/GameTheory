/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Divisible Fair Division

Foundational definitions for divisible-goods fair division. An allocation gives
each agent a measurable subset of the cake, and a complete allocation is a
measurable partition of the whole cake.
-/

open MeasureTheory Set
open scoped BigOperators

namespace GameTheory
namespace SocialChoice
namespace FairDivision
namespace Divisible

/-- A divisible allocation assigns each agent a cake piece. -/
abbrev Allocation (N Ω : Type*) := N → Set Ω

/-- A complete divisible allocation is a measurable partition of the cake. -/
structure IsAllocation {N Ω : Type*} [MeasurableSpace Ω] [Fintype N]
    (A : Allocation N Ω) : Prop where
  /-- Each piece is measurable. -/
  measurable : ∀ i : N, MeasurableSet (A i)
  /-- Distinct agents receive disjoint pieces. -/
  disjoint : ∀ i j : N, i ≠ j → Disjoint (A i) (A j)
  /-- The pieces cover the cake. -/
  cover : ⋃ i : N, A i = Set.univ

namespace IsAllocation

variable {N Ω : Type*} [MeasurableSpace Ω] [Fintype N] {A : Allocation N Ω}

/-- Every point of the cake belongs to some allocated piece. -/
theorem mem_iUnion (hA : IsAllocation A) (x : Ω) : ∃ i : N, x ∈ A i := by
  have hx : x ∈ ⋃ i, A i := hA.cover ▸ Set.mem_univ x
  exact Set.mem_iUnion.mp hx

end IsAllocation

/-- A contiguous allocation on the real line gives every agent an order-connected
piece. -/
def IsContiguousAllocation {N : Type*} (A : Allocation N ℝ) : Prop :=
  ∀ i : N, (A i).OrdConnected

/-- An abstract cake valuation assigns a value to each agent-piece pair. -/
structure CakeValuation (N Ω V : Type*) where
  /-- The value function. -/
  val : N → Set Ω → V

/-- A measure-based cake valuation. -/
def MeasureValuation {N Ω : Type*} [MeasurableSpace Ω]
    (μ : N → Measure Ω) : CakeValuation N Ω ENNReal where
  val := fun i S => μ i S

namespace MeasureValuation

variable {N Ω : Type*} [MeasurableSpace Ω] (μ : N → Measure Ω)

/-- The value of the empty piece is zero. -/
@[simp] theorem val_empty (i : N) : (MeasureValuation μ).val i ∅ = 0 :=
  measure_empty

/-- For disjoint measurable sets, measure valuation is additive. -/
theorem val_union (i : N) (S T : Set Ω)
    (hdisj : Disjoint S T) (hT : MeasurableSet T) :
    (MeasureValuation μ).val i (S ∪ T) =
      (MeasureValuation μ).val i S + (MeasureValuation μ).val i T :=
  measure_union hdisj hT

/-- For a countable disjoint measurable allocation, measure valuation is
countably additive. -/
theorem val_iUnion [Countable N] (i : N) (A : Allocation N Ω)
    (hdisj : ∀ j k : N, j ≠ k → Disjoint (A j) (A k))
    (hmeas : ∀ j, MeasurableSet (A j)) :
    (MeasureValuation μ).val i (⋃ j, A j) =
      ∑' j, (MeasureValuation μ).val i (A j) :=
  measure_iUnion (fun ⦃j k⦄ hjk => hdisj j k hjk) hmeas

end MeasureValuation

/-- A normalized cake valuation gives every agent value `1` for the whole cake. -/
def IsNormalized {N Ω V : Type*} [One V] (cv : CakeValuation N Ω V) : Prop :=
  ∀ i : N, cv.val i Set.univ = 1

namespace IsNormalized

/-- For measure valuations, normalization is the same as every measure being a
probability measure. -/
theorem iff_isProbabilityMeasure {N Ω : Type*} [MeasurableSpace Ω]
    (μ : N → Measure Ω) :
    IsNormalized (MeasureValuation μ) ↔ ∀ i, IsProbabilityMeasure (μ i) := by
  simp only [IsNormalized, MeasureValuation]
  exact ⟨fun h i => ⟨h i⟩, fun h i => (h i).measure_univ⟩

end IsNormalized

/-! ## Fairness predicates -/

/-- Envy-freeness: every agent weakly prefers their own piece to every other
agent's piece. -/
def IsEnvyFree {N Ω V : Type*} [Preorder V]
    (μ : CakeValuation N Ω V) (A : Allocation N Ω) : Prop :=
  ∀ i j : N, μ.val i (A j) ≤ μ.val i (A i)

/-- Proportionality, stated as `whole ≤ n * own` to avoid division. -/
def IsProportional {N Ω V : Type*} [Preorder V] [Semiring V] (n : ℕ)
    (μ : CakeValuation N Ω V) (A : Allocation N Ω) : Prop :=
  ∀ i : N, μ.val i Set.univ ≤ (n : V) * μ.val i (A i)

/-- Equitability: all agents assign the same value to their own pieces. -/
def IsEquitable {N Ω V : Type*} [Preorder V]
    (μ : CakeValuation N Ω V) (A : Allocation N Ω) : Prop :=
  ∀ i j : N, μ.val i (A i) = μ.val j (A j)

/-- Envy-free complete measure allocations are proportional. -/
theorem IsEnvyFree.isProportional
    {N Ω : Type*} [MeasurableSpace Ω] [Fintype N]
    (μ : N → Measure Ω) (A : Allocation N Ω)
    (hA : IsAllocation A) (hef : IsEnvyFree (MeasureValuation μ) A) :
    IsProportional (Fintype.card N) (MeasureValuation μ) A := by
  intro i
  calc
    μ i Set.univ = μ i (⋃ j, A j) := by rw [hA.cover]
    _ = ∑' j, μ i (A j) :=
      measure_iUnion (fun ⦃j k⦄ hjk => hA.disjoint j k hjk) hA.measurable
    _ = ∑ j : N, μ i (A j) := tsum_fintype _
    _ ≤ ∑ j : N, μ i (A i) := Finset.sum_le_sum fun j _ => hef i j
    _ = Fintype.card N * μ i (A i) := by
      simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-! ## Bundled measure instances -/

/-- A real-valued cardinal divisible-goods instance. -/
structure CardinalInstance (N Ω : Type*) where
  /-- Utility assigned by each agent to each cake piece. -/
  utility : N → Set Ω → ℝ

namespace CardinalInstance

/-- Envy-freeness for a cardinal divisible-goods instance. -/
def IsEnvyFree {N Ω : Type*} (I : CardinalInstance N Ω)
    (A : Allocation N Ω) : Prop :=
  ∀ i j : N, I.utility i (A j) ≤ I.utility i (A i)

end CardinalInstance

/-- A measure-based divisible-goods instance. -/
structure MeasureInstance (N Ω : Type*) [MeasurableSpace Ω] where
  /-- Each agent's measure over cake pieces. -/
  measure : N → Measure Ω

namespace MeasureInstance

variable {N Ω : Type*} [MeasurableSpace Ω]

/-- The raw cake valuation induced by a measure instance. -/
def toCakeValuation (I : MeasureInstance N Ω) : CakeValuation N Ω ENNReal :=
  MeasureValuation I.measure

/-- The real-valued cardinal instance induced by finite measure values. -/
noncomputable def toCardinalInstance (I : MeasureInstance N Ω) :
    CardinalInstance N Ω where
  utility := fun i S => (I.measure i S).toReal

/-- Feasibility for a measure-based divisible instance. -/
def feasible [Fintype N] (_I : MeasureInstance N Ω) (A : Allocation N Ω) : Prop :=
  IsAllocation A

/-- Envy-freeness for a measure-based divisible instance, stated in `ENNReal`. -/
def IsEnvyFree (I : MeasureInstance N Ω) (A : Allocation N Ω) : Prop :=
  Divisible.IsEnvyFree I.toCakeValuation A

/-- For finite measure instances, `ENNReal` envy-freeness agrees with the
real-valued cardinal predicate induced by `toReal`. -/
theorem isEnvyFree_iff_toCardinalInstance_isEnvyFree
    (I : MeasureInstance N Ω) [∀ i, IsFiniteMeasure (I.measure i)]
    (A : Allocation N Ω) :
    I.IsEnvyFree A ↔ I.toCardinalInstance.IsEnvyFree A := by
  constructor
  · intro h i j
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr (h i j)
  · intro h i j
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp (h i j)

/-- Proportionality for a measure-based divisible instance, stated in `ENNReal`. -/
def IsProportional (I : MeasureInstance N Ω) (n : ℕ)
    (A : Allocation N Ω) : Prop :=
  Divisible.IsProportional n I.toCakeValuation A

/-- Equitability for a measure-based divisible instance, stated in `ENNReal`. -/
def IsEquitable (I : MeasureInstance N Ω) (A : Allocation N Ω) : Prop :=
  Divisible.IsEquitable I.toCakeValuation A

/-- Envy-freeness implies proportionality for complete measure-based divisible
allocations. -/
theorem IsEnvyFree.isProportional [Fintype N]
    (I : MeasureInstance N Ω) (A : Allocation N Ω)
    (hA : IsAllocation A) (hef : I.IsEnvyFree A) :
    I.IsProportional (Fintype.card N) A :=
  Divisible.IsEnvyFree.isProportional I.measure A hA hef

end MeasureInstance

end Divisible
end FairDivision
end SocialChoice
end GameTheory
