/-
# Finite-law probability-bound regression

A proper event has mass one quarter, while a nonconstant observable is four on
that event and zero elsewhere. Markov's inequality is exact.
-/

import GameTheory.Math.Probability.Bounds
import GameTheory.Math.Probability.Uniform

noncomputable section

namespace GameTheory.Tests.ProbabilityBounds

open GameTheory.Math.Probability

def witnessLaw : PMF Bool :=
  (PMF.uniformOfFintype (Fin 4)).map (fun value => decide (value = 0))

def witnessEvent : Set Bool := {true}

def witnessObservable (value : Bool) : ℝ := if value then 4 else 0

/-- The finite probability witness integrates its observable. -/
theorem witnessIntegrable :
    PayoffIntegrable witnessLaw witnessObservable :=
  payoffIntegrable_of_finite witnessLaw witnessObservable

theorem witness_event_probability :
    (witnessLaw.toOuterMeasure witnessEvent).toReal = 1 / 4 := by
  classical
  rw [PMF.toOuterMeasure_apply, tsum_fintype]
  norm_num [witnessLaw, witnessEvent, Fintype.sum_bool, Set.indicator,
    PMF.map_apply, PMF.uniformOfFintype_apply, tsum_fintype, Fin.sum_univ_succ]

theorem witness_expectation :
    expect witnessLaw witnessObservable witnessIntegrable = 1 := by
  rw [expect_eq_sum]
  norm_num [witnessLaw, witnessObservable, Fintype.sum_bool,
    PMF.map_apply, PMF.uniformOfFintype_apply, tsum_fintype, Fin.sum_univ_succ]

theorem witness_markov_bound :
    (witnessLaw.toOuterMeasure witnessEvent).toReal ≤
      expect witnessLaw witnessObservable witnessIntegrable / 4 := by
  apply eventMass_toReal_le_expect_div witnessLaw witnessEvent
    witnessObservable (by norm_num) witnessIntegrable
  · intro value _
    cases value <;> norm_num [witnessObservable]
  · intro value _ hEvent
    simp only [witnessEvent, Set.mem_singleton_iff] at hEvent
    subst value
    norm_num [witnessObservable]

theorem witness_markov_bound_is_exact :
    (witnessLaw.toOuterMeasure witnessEvent).toReal =
      expect witnessLaw witnessObservable witnessIntegrable / 4 := by
  rw [witness_event_probability, witness_expectation]

end GameTheory.Tests.ProbabilityBounds
