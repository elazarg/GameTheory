/-
# Finite-law probability-bound regression

A proper event has mass one quarter, while a nonconstant observable is four on
that event and zero elsewhere.  Markov's inequality is exact, so the public
bound cannot pass through a zero event or an inflated expectation.
-/

import GameTheory.Math.Probability.Bounds

noncomputable section

namespace GameTheory.Tests.ProbabilityBounds

open GameTheory.Math.Probability

def witnessLaw : FinDist Bool :=
  FinDist.mix (1 / 4) (by norm_num) (by norm_num)
    (FinDist.pure true) (FinDist.pure false)

def witnessEvent : Set Bool := {true}

def witnessObservable (value : Bool) : ℝ := if value then 4 else 0

theorem witness_event_probability : witnessLaw.probOf witnessEvent = 1 / 4 := by
  classical
  rw [← FinDist.expect_indicator_eq_probOf]
  norm_num [witnessLaw, witnessEvent, FinDist.expect_mix]

theorem witness_expectation : witnessLaw.expect witnessObservable = 1 := by
  norm_num [witnessLaw, witnessObservable, FinDist.expect_mix]

theorem witness_markov_bound :
    witnessLaw.probOf witnessEvent ≤ witnessLaw.expect witnessObservable / 4 := by
  apply FinDist.probOf_le_expect_div witnessLaw witnessEvent witnessObservable (by norm_num)
  · intro value _
    cases value <;> norm_num [witnessObservable]
  · intro value _ hEvent
    simp only [witnessEvent, Set.mem_singleton_iff] at hEvent
    subst value
    norm_num [witnessObservable]

theorem witness_markov_bound_is_exact :
    witnessLaw.probOf witnessEvent = witnessLaw.expect witnessObservable / 4 := by
  rw [witness_event_probability, witness_expectation]

end GameTheory.Tests.ProbabilityBounds
