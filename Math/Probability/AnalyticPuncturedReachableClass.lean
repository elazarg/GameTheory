/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.AnalyticKernelRegeneration
import Math.Probability.FiniteReachableClosedClass

/-!
# Reachable closed classes in an analytic punctured support

The support graph of a finite analytic stochastic kernel stabilizes for
sufficiently small positive parameters.  Freezing the kernel at one such
parameter and applying the finite reachable-class theorem therefore gives
a class intrinsic to the punctured analytic germ.

This is a graph-theoretic and probabilistic statement.  It does not claim
that the class is a legal continuation component of a stochastic game or
that it preserves a vector payoff target.
-/

set_option autoImplicit false

noncomputable section

namespace Math
namespace Probability

open Filter Set

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- A closed communicating class in the stabilized punctured support graph,
together with a punctured-support path from the supplied entry state. -/
structure AnalyticPuncturedReachableClass
    (kernel : ℝ → S → PMF S) (initial : S) where
  states : Finset S
  states_nonempty : states.Nonempty
  closed :
    ∀ ⦃source⦄, source ∈ states →
      ∀ ⦃destination⦄,
        analyticPuncturedSupport kernel source destination →
          destination ∈ states
  communicates :
    ∀ ⦃source⦄, source ∈ states →
      ∀ ⦃destination⦄, destination ∈ states →
        Relation.ReflTransGen
          (analyticPuncturedSupport kernel) source destination
  entry : S
  entry_mem : entry ∈ states
  reachable_entry :
    Relation.ReflTransGen
      (analyticPuncturedSupport kernel) initial entry

omit [Fintype S] [DecidableEq S] in
private theorem reflTransGen_mono
    {relation₁ relation₂ : S → S → Prop}
    (implication :
      ∀ ⦃source destination⦄,
        relation₁ source destination →
          relation₂ source destination)
    {source destination : S}
    (reachable :
      Relation.ReflTransGen relation₁ source destination) :
    Relation.ReflTransGen relation₂ source destination := by
  induction reachable with
  | refl =>
      exact Relation.ReflTransGen.refl
  | @tail middle destination hprefix step inductionHypothesis =>
      exact inductionHypothesis.tail (implication step)

omit [Fintype S] [DecidableEq S] in
/-- On a support-stabilized parameter, positive PMF support is exactly the
analytic punctured support. -/
private theorem pmfSupportStep_iff_puncturedSupport
    (kernel : ℝ → S → PMF S) (t : ℝ)
    (support :
      ∀ source destination,
        0 < (kernel t source destination).toReal ↔
          analyticPuncturedSupport kernel source destination)
    (source destination : S) :
    PMFSupportStep (kernel t) source destination ↔
      analyticPuncturedSupport kernel source destination := by
  constructor
  · intro step
    apply (support source destination).mp
    exact ENNReal.toReal_pos step
      (PMF.apply_ne_top (kernel t source) destination)
  · intro edge
    have positive :=
      (support source destination).mpr edge
    intro coordinate_zero
    rw [coordinate_zero] at positive
    exact (lt_irrefl 0) positive

omit [Fintype S] [DecidableEq S] in
/-- Every finite analytic stochastic kernel has an entry-reachable closed
communicating class in its stabilized punctured support graph. -/
theorem exists_analyticPuncturedReachableClass
    [Finite S]
    (kernel : ℝ → S → PMF S) (initial : S)
    (hanalytic :
      ∀ source destination,
        AnalyticAt ℝ
          (fun t => (kernel t source destination).toReal) 0) :
    Nonempty (AnalyticPuncturedReachableClass kernel initial) := by
  classical
  letI : Fintype S := Fintype.ofFinite S
  letI : DecidableEq S := Classical.decEq S
  have eventuallySupport :=
    eventually_kernel_support_iff_analyticPuncturedSupport
      kernel hanalytic
  obtain ⟨t, support⟩ := eventuallySupport.exists
  obtain ⟨frozenClass⟩ :=
    exists_reachableClosedClass (kernel t) initial
  have stepIff :
      ∀ source destination,
        PMFSupportStep (kernel t) source destination ↔
          analyticPuncturedSupport kernel source destination :=
    pmfSupportStep_iff_puncturedSupport
      kernel t support
  refine ⟨{
    states := frozenClass.states
    states_nonempty := frozenClass.states_nonempty
    closed := ?_
    communicates := ?_
    entry := frozenClass.entry
    entry_mem := frozenClass.entry_mem
    reachable_entry := ?_
  }⟩
  · intro source source_mem destination edge
    exact frozenClass.closed source_mem
      ((stepIff source destination).mpr edge)
  · intro source source_mem destination destination_mem
    refine reflTransGen_mono
      (relation₁ := PMFSupportStep (kernel t))
      (relation₂ := analyticPuncturedSupport kernel) ?_ ?_
    · intro current next step
      exact (stepIff current next).mp step
    · exact frozenClass.communicates
        source_mem destination_mem
  · refine reflTransGen_mono
      (relation₁ := PMFSupportStep (kernel t))
      (relation₂ := analyticPuncturedSupport kernel) ?_ ?_
    · intro current next step
      exact (stepIff current next).mp step
    · exact frozenClass.reachable_entry

end Probability
end Math
