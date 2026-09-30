/-
# Comparing conditional probabilities by injections and symmetries

An injection carrying one event into another while weakly increasing point
masses compares the two events' probabilities. If it also preserves an
observation, the comparison survives conditioning on that observation. Unlike
a symmetry argument, this permits a biased law and a map that is not onto. An
involution preserving a law gives equality instead, again within every
observation fiber, while other outcomes may keep positive probability.
Comparisons along a pointwise convergent sequence pass to its limit on any
carrier.
-/

import GameTheory.Math.Probability.Bounds
import GameTheory.Math.Probability.Conditioning
import GameTheory.Math.Probability.Convergence

noncomputable section

namespace GameTheory.Math.Probability

variable {α β : Type*}

/-- An injection carrying one event into another with weakly increasing point
masses compares their masses. -/
theorem toOuterMeasure_le_of_injection (law : PMF α) (first second : Set α) (move : α → α)
    (injective : Set.InjOn move (first ∩ law.support))
    (lands : ∀ value ∈ first, value ∈ law.support → move value ∈ second)
    (increases : ∀ value ∈ first, value ∈ law.support → law value ≤ law (move value)) :
    law.toOuterMeasure first ≤ law.toOuterMeasure second := by
  classical
  let source := first ∩ law.support
  have toSecond (value : source) : move value.1 ∈ second :=
    lands value.1 value.2.1 value.2.2
  calc
    law.toOuterMeasure first = law.toOuterMeasure source := by
      rw [← PMF.toOuterMeasure_apply_inter_support]
    _ = ∑' value : source, law value := by
      rw [PMF.toOuterMeasure_apply, ← tsum_subtype]
    _ ≤ ∑' value : source, law (move value) :=
      ENNReal.tsum_le_tsum fun value => increases value.1 value.2.1 value.2.2
    _ ≤ ∑' value : second, law value := by
      let embed : source → second := fun value => ⟨move value.1, toSecond value⟩
      have embedInjective : Function.Injective embed := fun left right same =>
        Subtype.ext (injective left.2 right.2 (congrArg Subtype.val same))
      exact ENNReal.tsum_comp_le_tsum_of_injective embedInjective (fun value => law value)
    _ = law.toOuterMeasure second := by
      rw [PMF.toOuterMeasure_apply, ← tsum_subtype]

/-- Observation-preserving injections compare posterior event probabilities,
including when other outcomes retain positive probability. -/
theorem filter_observation_toOuterMeasure_le (law : PMF α) (first second : Set α)
    (move : α → α) (observe : α → β) (info : β)
    (positive : ∃ value ∈ {value | observe value = info}, value ∈ law.support)
    (injective : Set.InjOn move (first ∩ law.support))
    (lands : ∀ value ∈ first, value ∈ law.support → move value ∈ second)
    (sameView : ∀ value ∈ first, value ∈ law.support → observe (move value) = observe value)
    (increases : ∀ value ∈ first, value ∈ law.support → law value ≤ law (move value)) :
    (law.filter {value | observe value = info} positive).toOuterMeasure first ≤
      (law.filter {value | observe value = info} positive).toOuterMeasure second := by
  classical
  apply toOuterMeasure_le_of_injection _ first second move
  · intro left leftMem right rightMem same
    exact injective ⟨leftMem.1, ((PMF.mem_support_filter_iff _).mp leftMem.2).2⟩
      ⟨rightMem.1, ((PMF.mem_support_filter_iff _).mp rightMem.2).2⟩ same
  · intro value member supported
    exact lands value member ((PMF.mem_support_filter_iff _).mp supported).2
  · intro value member supported
    obtain ⟨observed, supported⟩ := (PMF.mem_support_filter_iff _).mp supported
    have moved : observe (move value) = info :=
      (sameView value member supported).trans observed
    rw [PMF.filter_apply, PMF.filter_apply, Set.indicator_of_mem observed,
      Set.indicator_of_mem (show move value ∈ {value | observe value = info} from moved)]
    exact mul_le_mul_left (increases value member supported) _

/-- An event comparison holding along a pointwise convergent sequence of laws
holds in its limit. -/
theorem PMFConvergesPointwise.toOuterMeasure_toReal_le {sequence : ℕ → PMF α} {target : PMF α}
    (converges : PMFConvergesPointwise sequence target) (first second : Set α)
    (comparison : ∀ n, ((sequence n).toOuterMeasure first).toReal ≤
      ((sequence n).toOuterMeasure second).toReal) :
    (target.toOuterMeasure first).toReal ≤ (target.toOuterMeasure second).toReal := by
  classical
  have bounded (event : Set α) (value : α) :
      |(fun value => if value ∈ event then (1 : ℝ) else 0) value| ≤ 1 := by
    by_cases member : value ∈ event <;> simp [member]
  have left := converges.expect_of_bounded _ (bounded first)
  have right := converges.expect_of_bounded _ (bounded second)
  simp only [expect_indicator] at left right
  exact le_of_tendsto_of_tendsto left right (Filter.Eventually.of_forall comparison)

/-- A law preserved by an involution gives each point and its image the same
mass. -/
theorem apply_involution (law : PMF α) (swap : α → α)
    (involution : Function.Involutive swap) (symmetric : law.map swap = law) (value : α) :
    law (swap value) = law value := by
  conv_lhs => rw [← symmetric]
  exact pmf_map_apply_of_injective law involution.injective value

/-- Conditioning a symmetric law on an invariant event keeps it symmetric. -/
theorem filter_involution (law : PMF α) (swap : α → α)
    (involution : Function.Involutive swap) (symmetric : law.map swap = law)
    (event : Set α) (invariant : ∀ value, swap value ∈ event ↔ value ∈ event)
    (positive : ∃ value ∈ event, value ∈ law.support) :
    (law.filter event positive).map swap = law.filter event positive := by
  classical
  ext value
  have swapped := pmf_map_apply_of_injective (law.filter event positive)
    involution.injective (swap value)
  rw [involution value] at swapped
  rw [swapped, PMF.filter_apply, PMF.filter_apply]
  congr 1
  by_cases member : value ∈ event
  · have swappedMember := (invariant value).mpr member
    simp only [Set.indicator, member, swappedMember, ↓reduceIte]
    exact apply_involution law swap involution symmetric value
  · have swappedMember : swap value ∉ event := fun inside => member ((invariant value).mp inside)
    simp only [Set.indicator, member, swappedMember, ↓reduceIte]

/-- Two events exchanged by a law-preserving map on the support have equal mass. -/
theorem toOuterMeasure_eq_of_involution (law : PMF α) (swap : α → α)
    (symmetric : law.map swap = law) (first second : Set α)
    (exchanged : ∀ value ∈ law.support, swap value ∈ first ↔ value ∈ second) :
    law.toOuterMeasure first = law.toOuterMeasure second := by
  conv_lhs => rw [← symmetric]
  rw [PMF.toOuterMeasure_map_apply]
  apply PMF.toOuterMeasure_apply_eq_of_inter_support_eq
  ext value
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · exact fun ⟨member, supported⟩ => ⟨(exchanged value supported).mp member, supported⟩
  · exact fun ⟨member, supported⟩ => ⟨(exchanged value supported).mpr member, supported⟩

/-- Events exchanged by an observation-preserving symmetry have equal
probabilities within each observed fiber. The symmetry need only exchange the
events on the support. -/
theorem filter_observation_toOuterMeasure_eq (law : PMF α) (swap : α → α)
    (involution : Function.Involutive swap) (symmetric : law.map swap = law)
    (observe : α → β) (sameView : ∀ value, observe (swap value) = observe value)
    (info : β) (positive : ∃ value ∈ {value | observe value = info}, value ∈ law.support)
    (first second : Set α)
    (exchanged : ∀ value ∈ law.support, swap value ∈ first ↔ value ∈ second) :
    (law.filter {value | observe value = info} positive).toOuterMeasure first =
      (law.filter {value | observe value = info} positive).toOuterMeasure second := by
  apply toOuterMeasure_eq_of_involution _ swap
    (filter_involution law swap involution symmetric _ (fun value => by
      change observe (swap value) = info ↔ observe value = info
      rw [sameView value]) positive) first second
  intro value supported
  exact exchanged value ((PMF.mem_support_filter_iff _).mp supported).2

end GameTheory.Math.Probability
