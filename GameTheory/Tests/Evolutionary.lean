/-
# Evolutionary stability with mixed mutants

A Boolean resident faces every finite-law mutant, not only the other pure
action. The fair mutant is an explicit non-point-mass negative control.
-/

import GameTheory.Evolutionary
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

noncomputable section

namespace GameTheory.Tests.Evolutionary

open GameTheory.Evolutionary GameTheory.Probability

/-! ## The second-order clause is load-bearing -/

/-- The mutant ties the resident when facing the resident, but loses when the
resident and mutant are each tested against the mutant. -/
def tieBreakPayoff : Bool → Bool → ℝ
  | true, true => 1
  | false, true => 1
  | true, false => 2
  | false, false => 0

theorem tieBreak_mutant_ties_first_order :
    tieBreakPayoff true true = tieBreakPayoff false true :=
  rfl

theorem tieBreak_resident_wins_second_order :
    tieBreakPayoff true false > tieBreakPayoff false false := by
  norm_num [tieBreakPayoff]

/-- A stable ESS whose distinct mutant reaches, and is rejected by, the
second-order clause. A strict-Nash-only proof cannot establish this result. -/
theorem tieBreak_true_isESS : IsESS tieBreakPayoff true := by
  constructor
  · intro mutant
    cases mutant <;> norm_num [tieBreakPayoff]
  · intro mutant _ hne
    cases mutant
    · norm_num [tieBreakPayoff]
    · exact False.elim (hne rfl)

/-- Reverse the second-order comparison while retaining the same first-order
tie. The resident is Nash in the symmetric encounter but is not even neutrally
stable. -/
def nashOnlyPayoff : Bool → Bool → ℝ
  | true, true => 1
  | false, true => 1
  | true, false => 0
  | false, false => 2

theorem nashOnly_true_isNash :
    IsNash (symmetricForm Bool) (euPreference (symmetricUtility nashOnlyPayoff))
      (residentProfile true) := by
  have hfirst :
      ∀ mutant, nashOnlyPayoff true true ≥ nashOnlyPayoff mutant true := by
    intro mutant
    cases mutant <;> norm_num [nashOnlyPayoff]
  rw [isNash_iff]
  intro who replacement
  rw [euPreference_apply]
  fin_cases who <;>
    simpa [symmetricForm, symmetricUtility, residentProfile, opponent] using
      hfirst replacement

theorem nashOnly_true_not_isNSS : ¬ IsNSS nashOnlyPayoff true := by
  intro hnss
  have hsecond := hnss.2 false rfl
  norm_num [nashOnlyPayoff] at hsecond

theorem nashOnly_true_not_isESS : ¬ IsESS nashOnlyPayoff true := by
  intro hess
  exact nashOnly_true_not_isNSS hess.isNSS

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
