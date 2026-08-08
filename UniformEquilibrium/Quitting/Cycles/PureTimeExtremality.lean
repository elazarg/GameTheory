/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.SuccessorCertificate

/-!
# Pure quit-time extremality on a finite truncation

Fix the opponents' product marginals along the unique live path of a quitting
game.  Over `fuel` remaining stages, a player's behavior is a sequence of
Boolean hazards.  The resulting zero-boundary terminal payoff is a convex
combination of `fuel + 1` deterministic values: quit at one of the remaining
stages, or continue throughout the truncation.

The proof is finite Bellman algebra.  It introduces neither an infinite
stopping-time type nor extended-real or measure-theoretic scaffolding.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The finite hazard simplex -/

/-- The weight of a deterministic quit-time alternative.  For `fuel`
remaining stages, indices `0, ..., fuel - 1` mean quitting at that offset;
the last index means continuing throughout the truncation. -/
def quittingFiniteHazardWeight
    (hazard : ℕ → PMF Bool) (start : ℕ) :
    (fuel : ℕ) → Fin (fuel + 1) → ℝ
  | 0, _ => 1
  | fuel + 1, choice =>
      Fin.cases
        ((hazard start true).toReal)
        (fun later =>
          (hazard start false).toReal *
            quittingFiniteHazardWeight hazard (start + 1) fuel later)
        choice

/-- Every finite hazard weight is nonnegative. -/
theorem quittingFiniteHazardWeight_nonneg
    (hazard : ℕ → PMF Bool) (start : ℕ) :
    ∀ (fuel : ℕ) (choice : Fin (fuel + 1)),
      0 ≤ quittingFiniteHazardWeight hazard start fuel choice := by
  intro fuel
  induction fuel generalizing start with
  | zero =>
      intro choice
      simp [quittingFiniteHazardWeight]
  | succ fuel ih =>
      intro choice
      refine Fin.cases ?_ (fun later => ?_) choice
      · simp [quittingFiniteHazardWeight]
      · simp only [quittingFiniteHazardWeight, Fin.cases_succ]
        exact mul_nonneg ENNReal.toReal_nonneg (ih (start + 1) later)

/-- The deterministic quit-time weights exhaust unit mass. -/
theorem sum_quittingFiniteHazardWeight
    (hazard : ℕ → PMF Bool) (start fuel : ℕ) :
    ∑ choice : Fin (fuel + 1),
      quittingFiniteHazardWeight hazard start fuel choice = 1 := by
  induction fuel generalizing start with
  | zero =>
      simp [quittingFiniteHazardWeight]
  | succ fuel ih =>
      rw [Fin.sum_univ_succ]
      simp only [quittingFiniteHazardWeight, Fin.cases_zero, Fin.cases_succ,
        ← Finset.mul_sum, ih]
      have hsum :
          (hazard start true).toReal + (hazard start false).toReal = 1 := by
        simpa [Fintype.sum_bool] using pmf_toReal_sum_one (hazard start)
      linarith

/-- Closed form for the weight of quitting at a specified offset. -/
theorem quittingFiniteHazardWeight_castSucc
    (hazard : ℕ → PMF Bool) (start fuel : ℕ) (choice : Fin fuel) :
    quittingFiniteHazardWeight hazard start fuel choice.castSucc =
      (∏ offset ∈ Finset.range choice.val,
          (hazard (start + offset) false).toReal) *
        (hazard (start + choice.val) true).toReal := by
  induction fuel generalizing start with
  | zero => exact Fin.elim0 choice
  | succ fuel ih =>
      refine Fin.cases ?_ (fun later => ?_) choice
      · simp [quittingFiniteHazardWeight]
      · simp only [Fin.castSucc_succ, quittingFiniteHazardWeight,
          Fin.cases_succ, Fin.val_succ, Finset.prod_range_succ', ih]
        simp only [Nat.add_left_comm, Nat.add_comm]
        ring_nf

/-- Closed form for the final weight: the player continues throughout the
whole truncation. -/
theorem quittingFiniteHazardWeight_last
    (hazard : ℕ → PMF Bool) (start fuel : ℕ) :
    quittingFiniteHazardWeight hazard start fuel (Fin.last fuel) =
      ∏ offset ∈ Finset.range fuel,
        (hazard (start + offset) false).toReal := by
  induction fuel generalizing start with
  | zero =>
      simp [quittingFiniteHazardWeight]
  | succ fuel ih =>
      rw [show Fin.last (fuel + 1) = (Fin.last fuel).succ by rfl]
      simp only [quittingFiniteHazardWeight, Fin.cases_succ,
        Finset.prod_range_succ', ih]
      simp only [Nat.add_left_comm, Nat.add_comm]
      ring_nf

/-! ## Abstract finite stopping recursion -/

/-- Finite-horizon payoff of an arbitrary hazard sequence.  At each live
stage, quitting gives `quitValue`; continuing gives `continueReward` plus
`continueMass` times the remaining value.  The boundary after `fuel` stages
is zero. -/
def quittingFiniteHazardValue
    (quitValue continueReward continueMass : ℕ → ℝ)
    (hazard : ℕ → PMF Bool) : ℕ → ℕ → ℝ
  | _, 0 => 0
  | start, fuel + 1 =>
      (hazard start true).toReal * quitValue start +
        (hazard start false).toReal *
          (continueReward start + continueMass start *
            quittingFiniteHazardValue quitValue continueReward continueMass
              hazard (start + 1) fuel)

/-- Payoff of one deterministic alternative.  Index zero quits now; a
successor index continues now and follows the corresponding deterministic
alternative in the remaining truncation.  At zero fuel, the sole alternative
is the zero-boundary `never` value. -/
def quittingFinitePureTimeValue
    (quitValue continueReward continueMass : ℕ → ℝ) (start : ℕ) :
    (fuel : ℕ) → Fin (fuel + 1) → ℝ
  | 0, _ => 0
  | fuel + 1, choice =>
      Fin.cases
        (quitValue start)
        (fun later =>
          continueReward start + continueMass start *
            quittingFinitePureTimeValue quitValue continueReward continueMass
              (start + 1) fuel later)
        choice

/-- An arbitrary finite hazard payoff is exactly the convex combination of
the deterministic quit-time and never values. -/
theorem quittingFiniteHazardValue_eq_sum_pureTime
    (quitValue continueReward continueMass : ℕ → ℝ)
    (hazard : ℕ → PMF Bool) (start fuel : ℕ) :
    quittingFiniteHazardValue quitValue continueReward continueMass
        hazard start fuel =
      ∑ choice : Fin (fuel + 1),
        quittingFiniteHazardWeight hazard start fuel choice *
          quittingFinitePureTimeValue quitValue continueReward continueMass
            start fuel choice := by
  induction fuel generalizing start with
  | zero =>
      simp [quittingFiniteHazardValue, quittingFiniteHazardWeight,
        quittingFinitePureTimeValue]
  | succ fuel ih =>
      rw [Fin.sum_univ_succ]
      simp only [quittingFiniteHazardValue, quittingFiniteHazardWeight,
        quittingFinitePureTimeValue, Fin.cases_zero, Fin.cases_succ]
      have hweights := sum_quittingFiniteHazardWeight
        hazard (start + 1) fuel
      have htail := ih (start + 1)
      calc
        (hazard start true).toReal * quitValue start +
            (hazard start false).toReal *
              (continueReward start + continueMass start *
                quittingFiniteHazardValue quitValue continueReward
                  continueMass hazard (start + 1) fuel) =
          (hazard start true).toReal * quitValue start +
            (hazard start false).toReal *
              (continueReward start *
                  (∑ choice : Fin (fuel + 1),
                    quittingFiniteHazardWeight hazard (start + 1) fuel choice) +
                continueMass start *
                  (∑ choice : Fin (fuel + 1),
                    quittingFiniteHazardWeight hazard (start + 1) fuel choice *
                      quittingFinitePureTimeValue quitValue continueReward
                        continueMass (start + 1) fuel choice)) := by
            rw [hweights, ← htail]
            ring
        _ = (hazard start true).toReal * quitValue start +
            ∑ choice : Fin (fuel + 1),
              ((hazard start false).toReal *
                  quittingFiniteHazardWeight hazard (start + 1) fuel choice) *
                (continueReward start + continueMass start *
                  quittingFinitePureTimeValue quitValue continueReward
                    continueMass (start + 1) fuel choice) := by
            simp_rw [mul_add, Finset.mul_sum]
            rw [Finset.sum_add_distrib]
            ring_nf

/-- Some deterministic quit-time (including `never` at the last index) does
at least as well as an arbitrary finite hazard. -/
theorem exists_pureTime_ge_quittingFiniteHazardValue
    (quitValue continueReward continueMass : ℕ → ℝ)
    (hazard : ℕ → PMF Bool) (start fuel : ℕ) :
    ∃ choice : Fin (fuel + 1),
      quittingFiniteHazardValue quitValue continueReward continueMass
          hazard start fuel ≤
        quittingFinitePureTimeValue quitValue continueReward continueMass
          start fuel choice := by
  obtain ⟨best, _, hbest⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin (fuel + 1)))
    (quittingFinitePureTimeValue quitValue continueReward continueMass
      start fuel)
    Finset.univ_nonempty
  refine ⟨best, ?_⟩
  rw [quittingFiniteHazardValue_eq_sum_pureTime]
  calc
    (∑ choice : Fin (fuel + 1),
        quittingFiniteHazardWeight hazard start fuel choice *
          quittingFinitePureTimeValue quitValue continueReward continueMass
            start fuel choice) ≤
      ∑ choice : Fin (fuel + 1),
        quittingFiniteHazardWeight hazard start fuel choice *
          quittingFinitePureTimeValue quitValue continueReward continueMass
            start fuel best := by
          apply Finset.sum_le_sum
          intro choice _
          exact mul_le_mul_of_nonneg_left
            (hbest choice (Finset.mem_univ choice))
            (quittingFiniteHazardWeight_nonneg hazard start fuel choice)
    _ = quittingFinitePureTimeValue quitValue continueReward continueMass
          start fuel best := by
      rw [← Finset.sum_mul, sum_quittingFiniteHazardWeight, one_mul]

/-! ## Quitting-game specialization -/

/-- Payoff from quitting now against the supplied opponent marginals. -/
def quittingFixedOpponentsQuitValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ) : ℝ :=
  quittingRootAbsorbingContribution reward
    (Function.update (roots time) who (PMF.pure true)) who

/-- Immediate absorbing contribution when `who` continues now. -/
def quittingFixedOpponentsContinueReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ) : ℝ :=
  quittingRootAbsorbingContribution reward
    (Function.update (roots time) who (PMF.pure false)) who

/-- Probability that all opponents continue at the current stage. -/
def quittingFixedOpponentsContinueMass
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ) : ℝ :=
  quittingStationaryContinueMass
    (Function.update (roots time) who (PMF.pure false))

/-- The actual finite zero-boundary terminal payoff, computed by composing
the existing one-root quitting payoff along the live path. -/
def quittingFiniteRootPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) : ℕ → ℕ → ℝ
  | _, 0 => 0
  | start, fuel + 1 =>
      quittingRootExpectedPayoff reward
        (fun _ => quittingFiniteRootPayoff reward roots who hazard
          (start + 1) fuel)
        (Function.update (roots start) who (hazard start)) who

/-- A root at which `who` quits surely has zero all-continue mass. -/
theorem quittingStationaryContinueMass_update_pure_true_eq_zero
    (root : ι → PMF Bool) (who : ι) :
    quittingStationaryContinueMass
        (Function.update root who (PMF.pure true)) = 0 := by
  unfold quittingStationaryContinueMass
  have hsure : QuittingRootHasSureQuitter
      (Function.update root who (PMF.pure true)) :=
    ⟨who, Function.update_self who (PMF.pure true) root⟩
  have hzero :=
    (quittingRootHasSureQuitter_iff_allContinue_mass_zero
      (Function.update root who (PMF.pure true))).mp hsure
  rw [show (quittingAllContinueAction : ι → Bool) =
      (fun _ => false) by rfl, hzero]
  simp

/-- The finite root recursion is the scalar hazard Bellman recursion with the
three fixed-opponent coefficients above. -/
theorem quittingFiniteRootPayoff_eq_hazardValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (start fuel : ℕ) :
    quittingFiniteRootPayoff reward roots who hazard start fuel =
      quittingFiniteHazardValue
        (quittingFixedOpponentsQuitValue reward roots who)
        (quittingFixedOpponentsContinueReward reward roots who)
        (quittingFixedOpponentsContinueMass roots who)
        hazard start fuel := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      rw [quittingFiniteRootPayoff, quittingFiniteHazardValue,
        quittingRootExpectedPayoff_update_eq_endpointMix]
      have hquit :
          quittingRootQuitPayoff reward
              (fun _ => quittingFiniteRootPayoff reward roots who hazard
                (start + 1) fuel)
              (roots start) who =
            quittingFixedOpponentsQuitValue reward roots who start := by
        unfold quittingRootQuitPayoff quittingFixedOpponentsQuitValue
        rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
          quittingStationaryContinueMass_update_pure_true_eq_zero]
        simp
      have hcontinue :
          quittingRootContinuePayoff reward
              (fun _ => quittingFiniteRootPayoff reward roots who hazard
                (start + 1) fuel)
              (roots start) who =
            quittingFixedOpponentsContinueReward reward roots who start +
              quittingFixedOpponentsContinueMass roots who start *
                quittingFiniteRootPayoff reward roots who hazard
                  (start + 1) fuel := by
        unfold quittingRootContinuePayoff
          quittingFixedOpponentsContinueReward
          quittingFixedOpponentsContinueMass
        rw [quittingRootExpectedPayoff_eq_absorbingContribution_add]
      rw [hquit, hcontinue, ih]

/-- Deterministic quit-time value against fixed opponent marginals.  The last
index is the plan that continues throughout the truncation. -/
def quittingFinitePureTimePayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start fuel : ℕ)
    (choice : Fin (fuel + 1)) : ℝ :=
  quittingFinitePureTimeValue
    (quittingFixedOpponentsQuitValue reward roots who)
    (quittingFixedOpponentsContinueReward reward roots who)
    (quittingFixedOpponentsContinueMass roots who)
    start fuel choice

/-- Exact pure quit-time decomposition of a finite zero-boundary quitting
payoff against fixed opponents. -/
theorem quittingFiniteRootPayoff_eq_sum_pureTime
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (start fuel : ℕ) :
    quittingFiniteRootPayoff reward roots who hazard start fuel =
      ∑ choice : Fin (fuel + 1),
        quittingFiniteHazardWeight hazard start fuel choice *
          quittingFinitePureTimePayoff reward roots who start fuel choice := by
  rw [quittingFiniteRootPayoff_eq_hazardValue,
    quittingFiniteHazardValue_eq_sum_pureTime]
  rfl

/-- Pure quit-time extremality: some deterministic quit stage, or never
within the truncation, weakly dominates every arbitrary finite hazard. -/
theorem exists_quittingFinitePureTimePayoff_ge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (start fuel : ℕ) :
    ∃ choice : Fin (fuel + 1),
      quittingFiniteRootPayoff reward roots who hazard start fuel ≤
        quittingFinitePureTimePayoff reward roots who start fuel choice := by
  rw [quittingFiniteRootPayoff_eq_hazardValue]
  exact exists_pureTime_ge_quittingFiniteHazardValue
    (quittingFixedOpponentsQuitValue reward roots who)
    (quittingFixedOpponentsContinueReward reward roots who)
    (quittingFixedOpponentsContinueMass roots who)
    hazard start fuel

end GameTheory
