module

/-
# Compactness of finite conditional probability systems

A conditional probability system assigns a supported law to every nonempty
event. On a finite carrier, simultaneous pointwise limits preserve support and
the chain rule, so every sequence has a subsequence converging to another
conditional probability system. No topology on the semantic system is needed.
-/

public import GameTheory.Math.Probability.ConditionalSystem
public import GameTheory.Math.Probability.Compactness

@[expose] public section

noncomputable section

namespace GameTheory.Math.Probability

open Filter
open scoped ENNReal

/-- On a finite carrier, pointwise PMF convergence preserves every event's
probability. -/
theorem PMFConvergesPointwise.toOuterMeasure_finite {α : Type*} [Finite α]
    {sequence : ℕ → PMF α} {target : PMF α}
    (converges : PMFConvergesPointwise sequence target) (event : Set α) :
    Tendsto (fun n => (sequence n).toOuterMeasure event) atTop
      (nhds (target.toOuterMeasure event)) := by
  classical
  let : Fintype α := Fintype.ofFinite α
  simp only [PMF.toOuterMeasure_apply_fintype]
  apply tendsto_finsetSum
  intro value _
  by_cases member : value ∈ event
  · simpa only [Set.indicator_of_mem member] using converges value
  · simp only [Set.indicator_of_notMem member]
    exact tendsto_const_nhds

/-- Every sequence of conditional probability systems on a finite carrier has
one subsequence converging at every nonempty conditioning event. The target
still satisfies support and the full conditional-probability chain rule. -/
theorem exists_subseq_conditionalSystemConverges {α : Type*} [Finite α]
    (sequence : ℕ → ConditionalProbabilitySystem α) :
    ∃ (target : ConditionalProbabilitySystem α) (subseq : ℕ → ℕ),
      StrictMono subseq ∧ ∀ (event : Set α) (nonempty : event.Nonempty),
        PMFConvergesPointwise (fun n => (sequence (subseq n)).law event nonempty)
          (target.law event nonempty) := by
  classical
  obtain ⟨laws, subseq, increasing, converges⟩ :=
    exists_subseq_pmfConvergesPointwise_pi
      (ι := {event : Set α // event.Nonempty})
      (fun n event => (sequence n).law event.1 event.2)
  have supported (event : Set α) (nonempty : event.Nonempty) (value : α)
      (positive : value ∈ (laws ⟨event, nonempty⟩).support) : value ∈ event := by
    by_contra absent
    have zero (n : ℕ) : (sequence (subseq n)).law event nonempty value = 0 := by
      by_contra nonzero
      exact absent ((sequence (subseq n)).supported event nonempty value nonzero)
    have zeroLimit : Tendsto
        (fun n => (sequence (subseq n)).law event nonempty value) atTop (nhds 0) := by
      simpa only [zero] using (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (nhds 0))
    exact positive (tendsto_nhds_unique (converges ⟨event, nonempty⟩ value) zeroLimit)
  have chain (first second : Set α) (firstNonempty : first.Nonempty)
      (secondNonempty : second.Nonempty) (subset : first ⊆ second)
      (value : α) (member : value ∈ first) :
      laws ⟨first, firstNonempty⟩ value *
          (laws ⟨second, secondNonempty⟩).toOuterMeasure first =
        laws ⟨second, secondNonempty⟩ value := by
    have productLimit := ENNReal.Tendsto.mul
      (converges ⟨first, firstNonempty⟩ value)
      (Or.inr (outerMeasure_ne_top (laws ⟨second, secondNonempty⟩) first))
      ((converges ⟨second, secondNonempty⟩).toOuterMeasure_finite first)
      (Or.inr ((laws ⟨first, firstNonempty⟩).apply_ne_top value))
    have same : (fun n => (sequence (subseq n)).law first firstNonempty value *
        ((sequence (subseq n)).law second secondNonempty).toOuterMeasure first) =
        fun n => (sequence (subseq n)).law second secondNonempty value := by
      funext n
      exact (sequence (subseq n)).chain first second firstNonempty secondNonempty
        subset value member
    rw [same] at productLimit
    exact tendsto_nhds_unique productLimit (converges ⟨second, secondNonempty⟩ value)
  exact ⟨⟨fun event nonempty => laws ⟨event, nonempty⟩, supported, chain⟩,
    subseq, increasing, fun event nonempty => converges ⟨event, nonempty⟩⟩

end GameTheory.Math.Probability
