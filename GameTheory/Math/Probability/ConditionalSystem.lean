module

/-
# Discrete conditional probability systems

A conditional probability system specifies an ordinary PMF conditional on each
nonempty event, including events assigned probability zero by its unconditional
law. Every conditional law is supported on its conditioning event. Nested
events obey the probability chain rule, so null-event beliefs cannot be chosen
independently when another conditional law gives their event positive mass.
-/

public import GameTheory.Math.Probability.Conditioning

@[expose] public section

noncomputable section

namespace GameTheory.Math.Probability

open scoped ENNReal

/-- PMF-valued conditional laws on all nonempty events, with support and nested
conditioning compatibility. -/
structure ConditionalProbabilitySystem (α : Type*) where
  /-- The conditional law given a nonempty event. -/
  law : (B : Set α) → B.Nonempty → PMF α
  /-- Conditional probability is concentrated on the event conditioned upon. -/
  supported : ∀ (B : Set α) (nonempty : B.Nonempty) (a : α),
    a ∈ (law B nonempty).support → a ∈ B
  /-- Nested conditioning obeys the chain rule at every atom of the inner event. -/
  chain : ∀ (A B : Set α) (inner : A.Nonempty) (outer : B.Nonempty),
    A ⊆ B → ∀ a, a ∈ A →
      law A inner a * (law B outer).toOuterMeasure A = law B outer a

namespace ConditionalProbabilitySystem

variable {α : Type*}

/-- Conditional event probability under an ordinary PMF. -/
def prob (C : ConditionalProbabilitySystem α) (event B : Set α) (nonempty : B.Nonempty) :
    ℝ≥0∞ :=
  (C.law B nonempty).toOuterMeasure event

@[simp]
theorem prob_self (C : ConditionalProbabilitySystem α) (B : Set α) (nonempty : B.Nonempty) :
    C.prob B B nonempty = 1 :=
  (PMF.toOuterMeasure_apply_eq_one_iff _ B).mpr (C.supported B nonempty)

@[simp]
theorem prob_univ (C : ConditionalProbabilitySystem α) (B : Set α) (nonempty : B.Nonempty) :
    C.prob Set.univ B nonempty = 1 :=
  (PMF.toOuterMeasure_apply_eq_one_iff _ Set.univ).mpr (Set.subset_univ _)

/-- A conditional law gives zero mass to every atom outside its event. -/
theorem law_apply_eq_zero_of_not_mem (C : ConditionalProbabilitySystem α)
    (B : Set α) (nonempty : B.Nonempty) (a : α) (outside : a ∉ B) :
    C.law B nonempty a = 0 := by
  by_contra positive
  exact outside (C.supported B nonempty a positive)

/-- The atomwise chain rule also gives the ordinary chain rule for arbitrary
events, including those of conditional probability zero. -/
theorem prob_chain (C : ConditionalProbabilitySystem α) (event A B : Set α)
    (inner : A.Nonempty) (outer : B.Nonempty) (subset : A ⊆ B) :
    C.prob event A inner * C.prob A B outer = C.prob (event ∩ A) B outer := by
  classical
  simp only [prob, PMF.toOuterMeasure_apply, ENNReal.tsum_mul_right.symm]
  apply tsum_congr
  intro a
  by_cases hevent : a ∈ event <;> by_cases hinner : a ∈ A
  · simpa only [PMF.toOuterMeasure_apply, Set.indicator_of_mem hevent,
      Set.indicator_of_mem (show a ∈ event ∩ A from ⟨hevent, hinner⟩)] using
      C.chain A B inner outer subset a hinner
  · simp [Set.indicator, hevent, hinner, C.law_apply_eq_zero_of_not_mem A inner a hinner]
  · simp [Set.indicator, hevent]
  · simp [Set.indicator, hevent]

private theorem event_meets_support (μ : PMF α) (full : FullSupport μ)
    (event : Set α) (nonempty : event.Nonempty) : ∃ a ∈ event, a ∈ μ.support := by
  obtain ⟨a, member⟩ := nonempty
  exact ⟨a, member, full a⟩

open Classical in
private theorem event_fiber (event : Set α) :
    {a : α | decide (a ∈ event) = true} = event := by
  classical
  ext a
  simp

open Classical in
private theorem posterior_event (μ : PMF α) (full : FullSupport μ)
    (event : Set α) (nonempty : event.Nonempty) :
    fiberPosterior μ (fun a => decide (a ∈ event)) true =
      μ.filter event (event_meets_support μ full event nonempty) := by
  classical
  have meets : ∃ a ∈ {a : α | decide (a ∈ event) = true}, a ∈ μ.support := by
    rw [event_fiber]
    exact event_meets_support μ full event nonempty
  rw [fiberPosterior_eq_filter μ _ meets]
  simp only [event_fiber]

private theorem filter_atom_mul_mass (μ : PMF α) (event : Set α)
    (meets : ∃ a ∈ event, a ∈ μ.support) (a : α) (member : a ∈ event) :
    μ.filter event meets a * μ.toOuterMeasure event = μ a := by
  classical
  rw [PMF.filter_apply, Set.indicator_of_mem member, ← PMF.toOuterMeasure_apply]
  exact ENNReal.inv_mul_cancel_right (toOuterMeasure_ne_zero_iff μ event |>.mpr meets)
    (outerMeasure_ne_top μ event)

/-- A fully supported PMF canonically supplies conditional laws on every
nonempty event, using the shared posterior operator. -/
def ofFullSupport (μ : PMF α) (full : FullSupport μ) : ConditionalProbabilitySystem α where
  law B _ := by
    classical
    exact fiberPosterior μ (fun a => decide (a ∈ B)) true
  supported := by
    intro B nonempty a member
    rw [posterior_event μ full B nonempty, PMF.support_filter] at member
    exact member.1
  chain := by
    intro A B inner outer subset a member
    rw [posterior_event μ full A inner, posterior_event μ full B outer]
    have meetsA := event_meets_support μ full A inner
    have meetsB := event_meets_support μ full B outer
    have meetsInner : ∃ a ∈ A, a ∈ (μ.filter B meetsB).support := by
      obtain ⟨a, ha⟩ := inner
      exact ⟨a, ha, by rw [PMF.support_filter]; exact ⟨subset ha, full a⟩⟩
    rw [← filter_filter_of_subset μ B A meetsB meetsInner subset]
    exact filter_atom_mul_mass (μ.filter B meetsB) A meetsInner a member

/-- The full-support construction is exactly the shared PMF filter at a
nonempty conditioning event. -/
private theorem ofFullSupport_law_eq_filter (μ : PMF α) (full : FullSupport μ)
    (B : Set α) (nonempty : B.Nonempty) :
    (ofFullSupport μ full).law B nonempty =
      μ.filter B (event_meets_support μ full B nonempty) :=
  posterior_event μ full B nonempty

/-- Conditional event probability for a fully supported law is the usual
intersection probability divided by the conditioning probability. -/
theorem ofFullSupport_prob (μ : PMF α) (full : FullSupport μ)
    (event B : Set α) (nonempty : B.Nonempty) :
    (ofFullSupport μ full).prob event B nonempty =
      μ.toOuterMeasure (event ∩ B) / μ.toOuterMeasure B := by
  rw [prob, ofFullSupport_law_eq_filter, toOuterMeasure_filter_apply]

/-- The unconditional law of the canonical full-support system is the
original PMF. The statement is independent of the chosen nonemptiness proof. -/
@[simp]
theorem ofFullSupport_law_univ (μ : PMF α) (full : FullSupport μ)
    (nonempty : (Set.univ : Set α).Nonempty) :
    (ofFullSupport μ full).law Set.univ nonempty = μ := by
  rw [ofFullSupport_law_eq_filter]
  exact filter_of_support_subset μ Set.univ _ (Set.subset_univ _)

/-- An atom's conditional mass in the full-support construction. -/
theorem ofFullSupport_law_apply (μ : PMF α) (full : FullSupport μ)
    (B : Set α) (nonempty : B.Nonempty) (a : α) :
    (ofFullSupport μ full).law B nonempty a =
      B.indicator μ a / μ.toOuterMeasure B := by
  classical
  rw [ofFullSupport_law_eq_filter, PMF.filter_apply, ← PMF.toOuterMeasure_apply,
    div_eq_mul_inv]

end ConditionalProbabilitySystem

end GameTheory.Math.Probability
