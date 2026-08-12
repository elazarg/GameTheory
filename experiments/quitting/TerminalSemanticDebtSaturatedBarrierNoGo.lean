/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import experiments.quitting.TerminalSemanticGlobalDebtBarrierCertificate
import Math.Probability.DiscreteHazardMixture

/-!
# Debt-saturated semantic barriers cannot carry a positive floor

The global semantic barrier certificate must distinguish absolute payoff and
envelope levels.  If membership depends only on their difference, every
complete fixed-debt fiber is present once one point of it is present.  Inside
each such fiber one can calibrate the absolute level so that a product-root
prefix multiplies every debt coordinate by the joint all-Continue mass.

Applying this to the Never boundary and a rational symmetric four-player root
with sufficiently small Continue probability contradicts any positive debt
floor.  Thus debt-only polyhedral, semialgebraic, or max-plus cylinders are
ruled out as certificate barriers.  This is an architectural no-go, not a
counterexample to uniform equilibrium existence.
-/

noncomputable section

namespace GameTheory
namespace TerminalSemanticDebtSaturatedBarrierNoGo

open Math.Probability Math.PMFProduct Set
open Math.Probability.DiscreteHazard

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A barrier is debt-saturated when membership is constant on every fiber of
`(prescribed, envelope) ↦ envelope - prescribed`.  Equivalently, it is
invariant under simultaneous translation of the two semantic coordinates. -/
def IsDebtSaturated
    (barrier : Set (QuittingTerminalSemanticPair ι)) : Prop :=
  ∀ first second : QuittingTerminalSemanticPair ι,
    (∀ who, quittingTerminalSemanticDebt first who =
      quittingTerminalSemanticDebt second who) →
    (first ∈ barrier ↔ second ∈ barrier)

/-- Simultaneous translation of prescribed payoff and envelope. -/
def semanticTranslate (pair : QuittingTerminalSemanticPair ι)
    (shift : Payoff ι) : QuittingTerminalSemanticPair ι :=
  (pair.1 + shift, pair.2 + shift)

omit [Fintype ι] [DecidableEq ι] in
/-- Debt saturation implies literal simultaneous-translation invariance. -/
theorem isDebtSaturated_translate_iff
    {barrier : Set (QuittingTerminalSemanticPair ι)}
    (hsaturated : IsDebtSaturated barrier)
    (pair : QuittingTerminalSemanticPair ι) (shift : Payoff ι) :
    pair ∈ barrier ↔ semanticTranslate pair shift ∈ barrier := by
  apply hsaturated
  intro who
  simp [semanticTranslate, quittingTerminalSemanticDebt]

/-- The exact debt action of an arbitrary product-root prefix.  It depends on
the pure-endpoint gap `Quit - Continue`, the opponent Continue mass, the input
debt, and the root's own Quit probability.  No Nash assumption is used. -/
theorem quittingTerminalSemanticDebt_prefix_eq_max_gap_sub
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (pair : QuittingTerminalSemanticPair ι) (who : ι) :
    let quitValue := quittingRootQuitPayoff reward pair.1 root who
    let continueValue := quittingRootContinuePayoff reward pair.1 root who
    let gap := quitValue - continueValue
    let debt := quittingTerminalSemanticDebt pair who
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root pair) who =
      max gap (quittingRootOpponentContinueMass root who * debt) -
        (root who true).toReal * gap := by
  dsimp only
  let quitValue := quittingRootQuitPayoff reward pair.1 root who
  let continueValue := quittingRootContinuePayoff reward pair.1 root who
  let debt := quittingTerminalSemanticDebt pair who
  change quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root pair) who =
      max (quitValue - continueValue)
          (quittingRootOpponentContinueMass root who * debt) -
        (root who true).toReal * (quitValue - continueValue)
  have henvelope : pair.2 who = pair.1 who + debt := by
    dsimp only [debt, quittingTerminalSemanticDebt]
    ring
  have hcontinue := quittingRootContinuePayoff_update_add reward pair.1 root
    who debt
  have hcontinueEnvelope : quittingRootContinuePayoff reward
        (Function.update pair.1 who (pair.2 who)) root who =
      quittingRootContinuePayoff reward pair.1 root who +
        quittingRootOpponentContinueMass root who * debt := by
    rw [henvelope]
    exact hcontinue
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPrefix
  dsimp only
  rw [quittingRootSuccessorPayoff_eq_endpointMix, hcontinueEnvelope]
  change max quitValue
      (continueValue + quittingRootOpponentContinueMass root who * debt) -
        ((root who true).toReal * quitValue +
          (root who false).toReal * continueValue) = _
  by_cases hgap : quitValue ≤
      continueValue + quittingRootOpponentContinueMass root who * debt
  · rw [max_eq_right hgap, max_eq_right (by linarith)]
    have hfalse : (root who false).toReal = 1 - (root who true).toReal := by
      linarith
    rw [hfalse]
    ring
  · have hgap' : continueValue +
        quittingRootOpponentContinueMass root who * debt < quitValue :=
      lt_of_not_ge hgap
    rw [max_eq_left hgap'.le, max_eq_left (by linarith)]
    have hfalse : (root who false).toReal = 1 - (root who true).toReal := by
      linarith
    rw [hfalse]
    ring

/-- Envelope level which ties pure Quit and pure Continue for one player at a
given root. -/
def calibratedEnvelope
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) : Payoff ι :=
  fun who =>
    (quittingRootQuitPayoff reward 0 root who -
      quittingRootContinuePayoff reward 0 root who) /
        quittingRootOpponentContinueMass root who

/-- The calibrated point on the complete fiber with debt vector `debt`. -/
def calibratedPair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (debt : Payoff ι) :
    QuittingTerminalSemanticPair ι :=
  (calibratedEnvelope reward root - debt,
    calibratedEnvelope reward root)

/-- Calibration preserves the requested debt vector exactly. -/
theorem calibratedPair_debt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (debt : Payoff ι) (who : ι) :
    quittingTerminalSemanticDebt (calibratedPair reward root debt) who =
      debt who := by
  simp [calibratedPair, quittingTerminalSemanticDebt]

/-- At a root with positive opponent Continue mass, the calibrated fiber point
has exact prefix debt `jointContinueMass * debt` in every coordinate. -/
theorem calibratedPair_prefix_debt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (debt : Payoff ι)
    (hpositive : ∀ who, 0 < quittingRootOpponentContinueMass root who)
    (who : ι) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root
          (calibratedPair reward root debt)) who =
      quittingStationaryContinueMass root * debt who := by
  let mass := quittingRootOpponentContinueMass root who
  let envelope := calibratedEnvelope reward root
  let pair := calibratedPair reward root debt
  have hmass : mass ≠ 0 := ne_of_gt (hpositive who)
  have hquitInvariant := quittingRootQuitPayoff_continuation_invariant reward
    pair.1 0 root who
  have hcontinueZero := quittingRootContinuePayoff_update_add reward 0 root who
    (pair.1 who)
  have hzeroUpdate : Function.update (0 : Payoff ι) who
      ((0 : Payoff ι) who + pair.1 who) =
        Function.update (0 : Payoff ι) who (pair.1 who) := by simp
  rw [hzeroUpdate] at hcontinueZero
  have hcontinueOnly : quittingRootContinuePayoff reward pair.1 root who =
      quittingRootContinuePayoff reward
        (Function.update (0 : Payoff ι) who (pair.1 who)) root who := by
    unfold quittingRootContinuePayoff
    rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
      quittingRootExpectedPayoff_eq_absorbingContribution_add]
    simp
  have hgap : quittingRootQuitPayoff reward pair.1 root who -
        quittingRootContinuePayoff reward pair.1 root who = mass * debt who := by
    rw [hquitInvariant]
    rw [hcontinueOnly, hcontinueZero]
    let baseGap := quittingRootQuitPayoff reward 0 root who -
      quittingRootContinuePayoff reward 0 root who
    have hcalibration : mass * envelope who = baseGap := by
      dsimp only [mass, envelope, calibratedEnvelope, baseGap]
      exact mul_div_cancel₀ _ hmass
    have hpairFirst : pair.1 who = envelope who - debt who := by
      rfl
    rw [hpairFirst]
    calc
      _ = baseGap - mass * (envelope who - debt who) := by
        dsimp only [baseGap, mass]
        ring
      _ = mass * debt who := by
        rw [mul_sub, hcalibration]
        ring
  have hformula := quittingTerminalSemanticDebt_prefix_eq_max_gap_sub
    reward root pair who
  have hdebt : quittingTerminalSemanticDebt pair who = debt who := by
    exact calibratedPair_debt reward root debt who
  dsimp only at hformula
  rw [hgap, hdebt, max_self] at hformula
  rw [hformula]
  rw [quittingStationaryContinueMass_eq_forcedContinue_mul_own root who]
  have hprobability :=
    quittingRoot_continueProbability_add_quitProbability root who
  have hfalse : (root who false).toReal = 1 - (root who true).toReal := by
    linarith
  rw [hfalse]
  dsimp only [mass, quittingRootOpponentContinueMass]
  ring

/-! ## Rational symmetric four-player contraction -/

/-- The rational symmetric root whose Continue probability is `1 / N`. -/
def rationalSymmetricRoot (N : ℕ) (hN : 0 < N) : Fin 4 → PMF Bool :=
  fun _ => booleanCoin (1 - 1 / (N : ℝ)) (by
    have hNreal : 1 ≤ (N : ℝ) := by exact_mod_cast hN
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
    have honeDiv : 1 / (N : ℝ) ≤ 1 := (div_le_one hNpos).2 hNreal
    linarith) (by
      have honeDiv : 0 ≤ 1 / (N : ℝ) := by positivity
      linarith)

@[simp] theorem rationalSymmetricRoot_continue
    (N : ℕ) (hN : 0 < N) (who : Fin 4) :
    (rationalSymmetricRoot N hN who false).toReal = 1 / (N : ℝ) := by
  simp [rationalSymmetricRoot]

@[simp] theorem rationalSymmetricRoot_quit
    (N : ℕ) (hN : 0 < N) (who : Fin 4) :
    (rationalSymmetricRoot N hN who true).toReal = 1 - 1 / (N : ℝ) := by
  simp [rationalSymmetricRoot]

theorem rationalSymmetricRoot_continueMass
    (N : ℕ) (hN : 0 < N) :
    quittingStationaryContinueMass (rationalSymmetricRoot N hN) =
      (1 / (N : ℝ)) ^ 4 := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  simp

theorem rationalSymmetricRoot_opponentContinueMass_pos
    (N : ℕ) (hN : 0 < N) (who : Fin 4) :
    0 < quittingRootOpponentContinueMass
      (rationalSymmetricRoot N hN) who := by
  unfold quittingRootOpponentContinueMass
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  apply Finset.prod_pos
  intro player _hplayer
  by_cases hsame : player = who
  · subst player
    simp
  · rw [Function.update_of_ne hsame]
    rw [rationalSymmetricRoot_continue]
    positivity

/-- **Debt-saturated barrier no-go.**  For four players, no barrier can
simultaneously contain the Never boundary, be invariant under all product-root
prefixes, depend only on debt, and carry a strictly positive total-debt floor. -/
theorem not_positiveDebtFloor_of_never_prefixInvariant_debtSaturated
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (barrier : Set (QuittingTerminalSemanticPair (Fin 4))) (delta : ℝ)
    (hnever : quittingNeverBoundarySemanticPair reward ∈ barrier)
    (hprefix : ∀ pair ∈ barrier, ∀ root : Fin 4 → PMF Bool,
      quittingTerminalSemanticPrefix reward root pair ∈ barrier)
    (hsaturated : IsDebtSaturated barrier)
    (hfloor : ∀ pair ∈ barrier,
      delta ≤ quittingTerminalSemanticDebtSum pair)
    (hdelta : 0 < delta) : False := by
  let never := quittingNeverBoundarySemanticPair reward
  let debt : Payoff (Fin 4) := fun who =>
    quittingTerminalSemanticDebt never who
  let total := quittingTerminalSemanticDebtSum never
  have htotalFloor : delta ≤ total := hfloor never hnever
  have htotalPos : 0 < total := hdelta.trans_le htotalFloor
  have hsmallPositive : 0 < min (1 / 2 : ℝ) (delta / (total + 1)) := by
    apply lt_min
    · norm_num
    · exact div_pos hdelta (by linarith)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (K := ℝ) hsmallPositive
  let N := n + 1
  have hN : 0 < N := Nat.succ_pos n
  let root := rationalSymmetricRoot N hN
  let calibrated := calibratedPair reward root debt
  have hsameDebt : ∀ who,
      quittingTerminalSemanticDebt never who =
        quittingTerminalSemanticDebt calibrated who := by
    intro who
    exact (calibratedPair_debt reward root debt who).symm
  have hcalibrated : calibrated ∈ barrier :=
    (hsaturated never calibrated hsameDebt).mp hnever
  have hprefixed : quittingTerminalSemanticPrefix reward root calibrated ∈
      barrier := hprefix calibrated hcalibrated root
  have hcoordinate : ∀ who,
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPrefix reward root calibrated) who =
        quittingStationaryContinueMass root * debt who := by
    intro who
    exact calibratedPair_prefix_debt reward root debt
      (rationalSymmetricRoot_opponentContinueMass_pos N hN) who
  have hsum : quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPrefix reward root calibrated) =
      quittingStationaryContinueMass root * total := by
    unfold quittingTerminalSemanticDebtSum
    simp_rw [hcoordinate]
    dsimp only [total]
    unfold quittingTerminalSemanticDebtSum
    rw [Finset.mul_sum]
  have hcastN : (N : ℝ) = (n : ℝ) + 1 := by
    simp [N]
  have hNsmall : 1 / (N : ℝ) < delta / (total + 1) := by
    rw [hcastN]
    exact hn.trans_le (min_le_right _ _)
  have hNhalf : 1 / (N : ℝ) < 1 / 2 := by
    rw [hcastN]
    exact hn.trans_le (min_le_left _ _)
  have hunit : 0 ≤ 1 / (N : ℝ) := by positivity
  have hunitLe : 1 / (N : ℝ) ≤ 1 := by linarith
  have hpowerLe : (1 / (N : ℝ)) ^ 4 ≤ 1 / (N : ℝ) := by
    nlinarith [sq_nonneg (1 / (N : ℝ)),
      mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ)) hunitLe]
  have hscaledSmall : (1 / (N : ℝ)) ^ 4 * total < delta := by
    have hfirst : (1 / (N : ℝ)) * total < delta := by
      have hmul := mul_lt_mul_of_pos_right hNsmall (by linarith : 0 < total + 1)
      have hdenne : total + 1 ≠ 0 := by linarith
      have hcancel : delta / (total + 1) * (total + 1) = delta := by
        field_simp [hdenne]
      rw [hcancel] at hmul
      have hstrict : (1 / (N : ℝ)) * total <
          (1 / (N : ℝ)) * (total + 1) := by
        exact mul_lt_mul_of_pos_left (by linarith) (by positivity)
      exact hstrict.trans hmul
    exact (mul_le_mul_of_nonneg_right hpowerLe htotalPos.le).trans_lt hfirst
  have hfloorPrefixed := hfloor _ hprefixed
  rw [hsum] at hfloorPrefixed
  change delta ≤ quittingStationaryContinueMass
      (rationalSymmetricRoot N hN) * total at hfloorPrefixed
  rw [rationalSymmetricRoot_continueMass] at hfloorPrefixed
  linarith

/-- Certificate-facing form: a positive global-debt certificate cannot have a
debt-saturated barrier. -/
theorem certificate_barrier_not_debtSaturated
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {delta : ℝ} (hdelta : 0 < delta)
    (certificate :
      TerminalSemanticGlobalDebtBarrierCertificate.Certificate reward delta) :
    ¬ IsDebtSaturated certificate.barrier := by
  intro hsaturated
  exact not_positiveDebtFloor_of_never_prefixInvariant_debtSaturated reward
    certificate.barrier delta
    (by simpa [quittingElementaryBoundarySemanticPair] using
      certificate.elementaryBoundary_mem (.never))
    certificate.prefix_mem hsaturated certificate.debt_floor hdelta

end TerminalSemanticDebtSaturatedBarrierNoGo
end GameTheory

namespace GameTheory.TerminalSemanticDebtSaturatedBarrierNoGo

#print axioms certificate_barrier_not_debtSaturated

end GameTheory.TerminalSemanticDebtSaturatedBarrierNoGo
