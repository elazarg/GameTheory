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

open GameTheory.Evolutionary GameTheory.Math.Probability

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
  refine ⟨payoffIntegrable_pure _ _, payoffIntegrable_pure _ _, ?_⟩
  fin_cases who <;>
    simpa [symmetricForm, symmetricUtility, residentProfile, opponent,
      expectedUtility_pure] using hfirst replacement

theorem nashOnly_true_not_isNSS : ¬ IsNSS nashOnlyPayoff true := by
  intro hnss
  have hsecond := hnss.2 false rfl
  norm_num [nashOnlyPayoff] at hsecond

theorem nashOnly_true_not_isESS : ¬ IsESS nashOnlyPayoff true := by
  intro hess
  exact nashOnly_true_not_isNSS hess.isNSS

/-- Only choosing `true` earns a payoff; the opponent action is immaterial. -/
def payoff (own _other : Bool) : ℝ := if own then 1 else 0

def resident : PMF Bool := PMF.pure true

def fairMutant : PMF Bool :=
  mix (1 / 2) (by norm_num) (by norm_num)
    (PMF.pure true) (PMF.pure false)

/-- Finite encounter outcomes make the fixture payoff integrable. -/
theorem encounterGuard (own opponent : PMF Bool) :
    PayoffIntegrable (bindPairLaw own (fun _ => opponent))
      (fun pair => payoff pair.1 pair.2) :=
  payoffIntegrable_of_finite _ _

theorem mixedPayoff_eq_mass_true (own opponent : PMF Bool)
    (hguard : PayoffIntegrable (bindPairLaw own (fun _ => opponent))
      (fun pair => payoff pair.1 pair.2)) :
    mixedPayoff payoff own opponent hguard = (own true).toReal := by
  let joint := bindPairLaw own (fun _ => opponent)
  let score : Bool → ℝ := fun action => if action then 1 else 0
  have hown : PayoffIntegrable own score := payoffIntegrable_of_finite _ _
  have hmap : PayoffIntegrable (joint.map Prod.fst) score := by
    exact payoffIntegrable_congr_law
      (bindPairLaw_map_fst own (fun _ => opponent)).symm hown
  calc
    mixedPayoff payoff own opponent hguard =
        expect (joint.map Prod.fst) score hmap := by
      unfold mixedPayoff
      symm
      exact expect_map Prod.fst joint score hguard hmap
    _ = expect own score hown := by
      exact expect_congr_law (bindPairLaw_map_fst own (fun _ => opponent))
        score hmap hown
    _ = (own true).toReal := by
      rw [expect_eq_sum, Fintype.sum_bool]
      simp [score]

private theorem mass_true_lt_one_of_ne_resident
    (mutant : PMF Bool) (hne : mutant ≠ resident) :
    (mutant true).toReal < 1 := by
  have hfalse : mutant false ≠ 0 := by
    intro hzero
    apply hne
    apply pmf_eq_pure_of_support_subset_singleton mutant true
    intro action ha
    cases action with
    | false =>
        have hpositive := (mutant.mem_support_iff false).mp ha
        exact False.elim (hpositive hzero)
    | true => simp
  have hpositive : 0 < (mutant false).toReal :=
    ENNReal.toReal_pos hfalse (mutant.apply_ne_top false)
  have hsum : (mutant false).toReal + (mutant true).toReal = 1 := by
    simpa only [tsum_fintype, Fintype.sum_bool, add_comm] using
      (pmf_weight_tsum_one mutant)
  linarith

/-- The pure `true` population is ESS against every finite-law mutant. -/
theorem resident_isMixedESS : IsMixedESS payoff resident := by
  refine ⟨encounterGuard, isESS_of_strict_nash ?_⟩
  intro mutant hne
  rw [mixedPayoff_eq_mass_true, mixedPayoff_eq_mass_true]
  simp only [resident, PMF.pure_apply, ite_true, ENNReal.toReal_one]
  exact mass_true_lt_one_of_ne_resident mutant hne

theorem resident_isMixedNSS : IsMixedNSS payoff resident :=
  resident_isMixedESS.isNSS

def vulnerableResident : PMF Bool := PMF.pure false

/-- A resident fixed at the payoff-zero action fails even the first neutral-
stability clause against the pure-`true` mutant. -/
theorem vulnerableResident_not_isMixedNSS :
    ¬ IsMixedNSS payoff vulnerableResident := by
  rintro ⟨hall, hnss⟩
  have hfirst := hnss.1 resident
  have hfirst' :
      mixedPayoff payoff vulnerableResident vulnerableResident
          (hall vulnerableResident vulnerableResident) ≥
        mixedPayoff payoff resident vulnerableResident
          (hall resident vulnerableResident) := hfirst
  rw [mixedPayoff_eq_mass_true, mixedPayoff_eq_mass_true] at hfirst'
  norm_num [vulnerableResident, resident, PMF.pure_apply] at hfirst'

theorem vulnerableResident_not_isMixedESS :
    ¬ IsMixedESS payoff vulnerableResident := by
  intro hess
  exact vulnerableResident_not_isMixedNSS hess.isNSS

/-- The genuinely mixed mutant obtains only half the resident payoff. -/
theorem fairMutant_loses :
    mixedPayoff payoff resident fairMutant (encounterGuard resident fairMutant) >
      mixedPayoff payoff fairMutant fairMutant (encounterGuard fairMutant fairMutant) := by
  rw [mixedPayoff_eq_mass_true, mixedPayoff_eq_mass_true]
  norm_num [resident, fairMutant, mix_apply, PMF.pure_apply]

/-- The mixed-mutation ESS reaches the canonical Nash predicate through the
symmetric population-law encounter game. -/
theorem resident_isNash_symmetric :
    ∃ hall : ∀ own opponent : PMF Bool,
        PayoffIntegrable (bindPairLaw own (fun _ => opponent))
          (fun pair => payoff pair.1 pair.2),
      IsNash (symmetricForm (PMF Bool))
        (euPreference (symmetricUtility
          (fun own opponent => mixedPayoff payoff own opponent (hall own opponent))))
        (residentProfile resident) :=
  resident_isMixedESS.isNash_symmetric

end GameTheory.Tests.Evolutionary
