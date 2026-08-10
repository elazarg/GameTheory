/-
# Evolutionary stability with mixed mutants

A Boolean resident faces every finite-law mutant, not only the other pure
action. The fair mutant is an explicit non-point-mass negative control.
-/

import GameTheory.Evolutionary
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

noncomputable section

namespace GameTheory.Tests.Evolutionary

open GameTheory.Evolutionary GameTheory.Probability

/-- Only choosing `true` earns a payoff; the opponent action is immaterial. -/
def payoff (own _other : Bool) : ℝ := if own then 1 else 0

def resident : FinDist Bool := FinDist.pure true

def fairMutant : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure true) (FinDist.pure false)

theorem mixedPayoff_eq_prob_true (own opponent : FinDist Bool) :
    mixedPayoff payoff own opponent = own.prob true := by
  unfold mixedPayoff
  rw [FinDist.expect_eq_sum, Fintype.sum_bool]
  simp [payoff]

private theorem prob_true_lt_one_of_ne_resident
    (mutant : FinDist Bool) (hne : mutant ≠ resident) :
    mutant.prob true < 1 := by
  apply lt_of_le_of_ne (FinDist.prob_le_one mutant true)
  intro heq
  apply hne
  apply FinDist.ext_of_prob
  intro action
  cases action
  · have hsum := FinDist.sum_prob mutant
    rw [Fintype.sum_bool, heq] at hsum
    rw [resident, FinDist.prob_pure_of_ne (by decide : false ≠ true)]
    linarith
  · rw [resident, FinDist.prob_pure_self]
    exact heq

/-- The pure `true` population is ESS against every finite-law mutant. -/
theorem resident_isMixedESS : IsMixedESS payoff resident := by
  apply isESS_of_strict_nash
  intro mutant hne
  rw [mixedPayoff_eq_prob_true, mixedPayoff_eq_prob_true]
  rw [resident, FinDist.prob_pure_self]
  exact prob_true_lt_one_of_ne_resident mutant hne

theorem resident_isMixedNSS : IsMixedNSS payoff resident :=
  resident_isMixedESS.isNSS

def vulnerableResident : FinDist Bool := FinDist.pure false

/-- A resident fixed at the payoff-zero action fails even the first neutral-
stability clause against the pure-`true` mutant. -/
theorem vulnerableResident_not_isMixedNSS :
    ¬ IsMixedNSS payoff vulnerableResident := by
  intro hnss
  have hfirst := hnss.1 resident
  rw [mixedPayoff_eq_prob_true, mixedPayoff_eq_prob_true] at hfirst
  norm_num [vulnerableResident, resident, FinDist.prob_pure_eq_ite] at hfirst

theorem vulnerableResident_not_isMixedESS :
    ¬ IsMixedESS payoff vulnerableResident := by
  intro hess
  exact vulnerableResident_not_isMixedNSS hess.isNSS

/-- The genuinely mixed mutant obtains only half the resident payoff. -/
theorem fairMutant_loses :
    mixedPayoff payoff resident fairMutant >
      mixedPayoff payoff fairMutant fairMutant := by
  rw [mixedPayoff_eq_prob_true, mixedPayoff_eq_prob_true]
  norm_num [resident, fairMutant, FinDist.prob_pure_of_ne]

/-- The mixed-mutation ESS reaches the canonical Nash predicate through the
symmetric population-law encounter game. -/
theorem resident_isNash_symmetric :
    IsNash (symmetricForm (FinDist Bool))
      (euPreference (symmetricUtility (mixedPayoff payoff)))
      (residentProfile resident) :=
  resident_isMixedESS.isNash_symmetric

end GameTheory.Tests.Evolutionary
