/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingPureTimeExtremality

/-!
# Selected stationary Snell caps

For constant stopping data, the infinite-horizon unilateral cap has two
extreme alternatives: quit immediately, or never quit.  When the continuation
mass `q` lies in `[0,1)`, every later deterministic quit time lies between
those two values.  This file proves that exact least-upper-bound statement,
the selected Bellman fixed point and its uniqueness, and convergence of the
zero-terminal finite-horizon Bellman recursion.

Keeping the never-quit alternative explicit is essential.  In particular,
the cap is not selected merely by asking for an arbitrary bounded solution
of a Bellman equation when `q = 1`; all results below therefore state the
strict contraction hypothesis `q < 1`.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Filter

/-! ## Deterministic quit times and the selected cap -/

/-- Payoff from continuing for exactly `steps` stages and then quitting,
for constant quit value, continuation reward, and continuation mass. -/
def quittingStationaryPureTimeValue
    (quitValue continueReward continueMass : ℝ) : ℕ → ℝ
  | 0 => quitValue
  | steps + 1 => continueReward + continueMass *
      quittingStationaryPureTimeValue quitValue continueReward continueMass steps

/-- Payoff from never quitting in the strictly contracting stationary
regime. -/
def quittingStationaryNeverValue
    (continueReward continueMass : ℝ) : ℝ :=
  continueReward / (1 - continueMass)

/-- The selected stationary cap: the better of quitting immediately and
never quitting. -/
def quittingStationarySelectedCap
    (quitValue continueReward continueMass : ℝ) : ℝ :=
  max quitValue
    (quittingStationaryNeverValue continueReward continueMass)

/-- The complete set of deterministic stationary stopping alternatives;
`some steps` quits after `steps` continuations and `none` never quits. -/
def quittingStationaryDeterministicValue
    (quitValue continueReward continueMass : ℝ) : Option ℕ → ℝ
  | some steps =>
      quittingStationaryPureTimeValue quitValue continueReward continueMass steps
  | none => quittingStationaryNeverValue continueReward continueMass

/-- The never-quit value satisfies its affine continuation equation. -/
theorem quittingStationaryNeverValue_balance
    (continueReward continueMass : ℝ)
    (hcontinue : continueMass < 1) :
    continueReward + continueMass *
        quittingStationaryNeverValue continueReward continueMass =
      quittingStationaryNeverValue continueReward continueMass := by
  have hne : 1 - continueMass ≠ 0 := ne_of_gt (sub_pos.mpr hcontinue)
  unfold quittingStationaryNeverValue
  field_simp [hne]
  ring

/-- The selected cap satisfies the stationary Snell equation. -/
theorem quittingStationarySelectedCap_bellman
    (quitValue continueReward continueMass : ℝ)
    (hmass1 : continueMass < 1) :
    quittingStationarySelectedCap quitValue continueReward continueMass =
      max quitValue (continueReward + continueMass *
        quittingStationarySelectedCap quitValue continueReward continueMass) := by
  let neverValue := quittingStationaryNeverValue continueReward continueMass
  have hbalance : continueReward + continueMass * neverValue = neverValue :=
    quittingStationaryNeverValue_balance continueReward continueMass hmass1
  by_cases hquit : quitValue ≤ neverValue
  · rw [quittingStationarySelectedCap, max_eq_right hquit]
    rw [hbalance, max_eq_right hquit]
  · have hnever : neverValue ≤ quitValue := le_of_not_ge hquit
    have hmassUpper : continueMass ≤ 1 := hmass1.le
    have hproduct :
        0 ≤ (1 - continueMass) * (quitValue - neverValue) :=
      mul_nonneg (sub_nonneg.mpr hmassUpper) (sub_nonneg.mpr hnever)
    have hcontinueValue :
        continueReward + continueMass * quitValue ≤ quitValue := by
      nlinarith [hbalance]
    rw [quittingStationarySelectedCap, max_eq_left hnever,
      max_eq_left hcontinueValue]

/-- Every finite deterministic quit time is bounded by the selected cap. -/
theorem quittingStationaryPureTimeValue_le_selectedCap
    (quitValue continueReward continueMass : ℝ)
    (hmass0 : 0 ≤ continueMass) (hmass1 : continueMass < 1) :
    ∀ steps : ℕ,
      quittingStationaryPureTimeValue quitValue continueReward continueMass steps ≤
        quittingStationarySelectedCap quitValue continueReward continueMass := by
  intro steps
  induction steps with
  | zero =>
      exact le_max_left _ _
  | succ steps ih =>
      rw [quittingStationaryPureTimeValue]
      have hscaled := mul_le_mul_of_nonneg_left ih hmass0
      have hcontinue : continueReward + continueMass *
          quittingStationarySelectedCap quitValue continueReward continueMass ≤
          quittingStationarySelectedCap quitValue continueReward continueMass := by
        calc
          continueReward + continueMass *
              quittingStationarySelectedCap
                quitValue continueReward continueMass ≤
              max quitValue (continueReward + continueMass *
                quittingStationarySelectedCap
                  quitValue continueReward continueMass) :=
            le_max_right _ _
          _ = quittingStationarySelectedCap
                quitValue continueReward continueMass :=
            (quittingStationarySelectedCap_bellman
              quitValue continueReward continueMass hmass1).symm
      linarith

/-- The selected cap is the least upper bound of all finite deterministic
quit times together with the never-quit alternative. -/
theorem quittingStationarySelectedCap_isLUB
    (quitValue continueReward continueMass : ℝ)
    (hmass0 : 0 ≤ continueMass) (hmass1 : continueMass < 1) :
    IsLUB (Set.range
      (quittingStationaryDeterministicValue
        quitValue continueReward continueMass))
      (quittingStationarySelectedCap
        quitValue continueReward continueMass) := by
  constructor
  · rintro value ⟨choice, rfl⟩
    cases choice with
    | none => exact le_max_right _ _
    | some steps =>
        exact quittingStationaryPureTimeValue_le_selectedCap
          quitValue continueReward continueMass hmass0 hmass1 steps
  · intro bound hbound
    apply max_le
    · have hquit := hbound ⟨some 0, rfl⟩
      simpa [quittingStationaryDeterministicValue,
        quittingStationaryPureTimeValue] using hquit
    · exact hbound ⟨none, rfl⟩

/-- The strict-contraction Bellman equation has no spurious real solution:
its unique solution is the selected cap. -/
theorem eq_quittingStationarySelectedCap_of_bellman
    (quitValue continueReward continueMass value : ℝ)
    (hmass0 : 0 ≤ continueMass) (hmass1 : continueMass < 1)
    (hvalue : value = max quitValue
      (continueReward + continueMass * value)) :
    value = quittingStationarySelectedCap
      quitValue continueReward continueMass := by
  let cap := quittingStationarySelectedCap
    quitValue continueReward continueMass
  have hcap : cap = max quitValue (continueReward + continueMass * cap) :=
    quittingStationarySelectedCap_bellman
      quitValue continueReward continueMass hmass1
  have hcontract : |value - cap| ≤ continueMass * |value - cap| := by
    calc
      |value - cap| =
          |max quitValue (continueReward + continueMass * value) -
            max quitValue (continueReward + continueMass * cap)| := by
              rw [← hvalue, ← hcap]
      _ = |max (continueReward + continueMass * value) quitValue -
            max (continueReward + continueMass * cap) quitValue| := by
              rw [max_comm quitValue, max_comm quitValue]
      _ ≤ |(continueReward + continueMass * value) -
            (continueReward + continueMass * cap)| :=
          abs_max_sub_max_le_abs _ _ _
      _ = continueMass * |value - cap| := by
          rw [show (continueReward + continueMass * value) -
              (continueReward + continueMass * cap) =
            continueMass * (value - cap) by ring,
            abs_mul, abs_of_nonneg hmass0]
  have habs : |value - cap| = 0 := by
    have := abs_nonneg (value - cap)
    nlinarith
  exact sub_eq_zero.mp (abs_eq_zero.mp habs)

/-! ## Zero-terminal finite-horizon approximation -/

/-- Stationary zero-terminal backward recursion.  `fuel = 0` assigns zero
at the artificial terminal boundary. -/
def quittingStationaryFiniteSnellValue
    (quitValue continueReward continueMass : ℝ) : ℕ → ℝ
  | 0 => 0
  | fuel + 1 => max quitValue (continueReward + continueMass *
      quittingStationaryFiniteSnellValue
        quitValue continueReward continueMass fuel)

/-- The finite recursion contracts geometrically toward the selected cap.
No monotonicity assertion is made. -/
theorem abs_quittingStationaryFiniteSnellValue_sub_selectedCap_le
    (quitValue continueReward continueMass : ℝ)
    (hmass0 : 0 ≤ continueMass) (hmass1 : continueMass < 1) :
    ∀ fuel : ℕ,
      |quittingStationaryFiniteSnellValue
          quitValue continueReward continueMass fuel -
        quittingStationarySelectedCap
          quitValue continueReward continueMass| ≤
        continueMass ^ fuel *
          |quittingStationarySelectedCap
            quitValue continueReward continueMass| := by
  intro fuel
  induction fuel with
  | zero => simp [quittingStationaryFiniteSnellValue]
  | succ fuel ih =>
      rw [quittingStationaryFiniteSnellValue, pow_succ]
      have hcap := quittingStationarySelectedCap_bellman
        quitValue continueReward continueMass hmass1
      calc
        |max quitValue (continueReward + continueMass *
              quittingStationaryFiniteSnellValue
                quitValue continueReward continueMass fuel) -
            quittingStationarySelectedCap
              quitValue continueReward continueMass| =
            |max quitValue (continueReward + continueMass *
                quittingStationaryFiniteSnellValue
                  quitValue continueReward continueMass fuel) -
            max quitValue (continueReward + continueMass *
              quittingStationarySelectedCap
                quitValue continueReward continueMass)| := by
              rw [← hcap]
        _ =
            |max (continueReward + continueMass *
                quittingStationaryFiniteSnellValue
                  quitValue continueReward continueMass fuel) quitValue -
              max (continueReward + continueMass *
                quittingStationarySelectedCap
                  quitValue continueReward continueMass) quitValue| := by
                rw [max_comm quitValue, max_comm quitValue]
        _ ≤ |(continueReward + continueMass *
                quittingStationaryFiniteSnellValue
                  quitValue continueReward continueMass fuel) -
              (continueReward + continueMass *
                quittingStationarySelectedCap
                  quitValue continueReward continueMass)| :=
            abs_max_sub_max_le_abs _ _ _
        _ = continueMass *
              |quittingStationaryFiniteSnellValue
                  quitValue continueReward continueMass fuel -
                quittingStationarySelectedCap
                  quitValue continueReward continueMass| := by
            rw [show (continueReward + continueMass *
                  quittingStationaryFiniteSnellValue
                    quitValue continueReward continueMass fuel) -
                (continueReward + continueMass *
                  quittingStationarySelectedCap
                    quitValue continueReward continueMass) =
              continueMass *
                (quittingStationaryFiniteSnellValue
                  quitValue continueReward continueMass fuel -
                quittingStationarySelectedCap
                  quitValue continueReward continueMass) by ring,
              abs_mul, abs_of_nonneg hmass0]
        _ ≤ continueMass * (continueMass ^ fuel *
              |quittingStationarySelectedCap
                quitValue continueReward continueMass|) :=
            mul_le_mul_of_nonneg_left ih hmass0
        _ = continueMass ^ fuel * continueMass *
              |quittingStationarySelectedCap
                quitValue continueReward continueMass| := by ring

/-- Zero-terminal stationary backward values converge to the selected cap.
The estimate above, rather than a false monotonicity claim, selects the
limit. -/
theorem tendsto_quittingStationaryFiniteSnellValue
    (quitValue continueReward continueMass : ℝ)
    (hmass0 : 0 ≤ continueMass) (hmass1 : continueMass < 1) :
    Tendsto (quittingStationaryFiniteSnellValue
      quitValue continueReward continueMass) atTop
      (nhds (quittingStationarySelectedCap
        quitValue continueReward continueMass)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hgeom : Tendsto (fun fuel : ℕ => continueMass ^ fuel *
      |quittingStationarySelectedCap
        quitValue continueReward continueMass|) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hmass0 hmass1).mul_const
      |quittingStationarySelectedCap
        quitValue continueReward continueMass|
  have habs : Tendsto (fun fuel : ℕ =>
      |quittingStationaryFiniteSnellValue
          quitValue continueReward continueMass fuel -
        quittingStationarySelectedCap
          quitValue continueReward continueMass|) atTop (nhds 0) :=
    squeeze_zero
      (fun fuel => abs_nonneg _)
      (abs_quittingStationaryFiniteSnellValue_sub_selectedCap_le
        quitValue continueReward continueMass hmass0 hmass1)
      hgeom
  simpa [Real.dist_eq] using habs

/-! ## Quitting-game specialization -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Stationary pure-Quit value against fixed opponent marginals. -/
def quittingStationaryFixedOpponentsQuitValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) : ℝ :=
  quittingFixedOpponentsQuitValue reward (fun _ => root) who 0

/-- Stationary unconditional absorbing contribution when the selected
player continues. -/
def quittingStationaryFixedOpponentsContinueReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) : ℝ :=
  quittingFixedOpponentsContinueReward reward (fun _ => root) who 0

/-- Stationary probability that all opponents continue. -/
def quittingStationaryFixedOpponentsContinueMass
    (root : ι → PMF Bool) (who : ι) : ℝ :=
  quittingFixedOpponentsContinueMass (fun _ => root) who 0

/-- The selected infinite-horizon unilateral cap against a stationary
product profile. -/
def quittingStationaryUnilateralCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) : ℝ :=
  quittingStationarySelectedCap
    (quittingStationaryFixedOpponentsQuitValue reward root who)
    (quittingStationaryFixedOpponentsContinueReward reward root who)
    (quittingStationaryFixedOpponentsContinueMass root who)

/-- Opponent continuation mass is nonnegative. -/
theorem quittingStationaryFixedOpponentsContinueMass_nonneg
    (root : ι → PMF Bool) (who : ι) :
    0 ≤ quittingStationaryFixedOpponentsContinueMass root who :=
  quittingStationaryContinueMass_nonneg
    (Function.update root who (PMF.pure false))

/-- Game-facing stationary Snell equation. -/
theorem quittingStationaryUnilateralCap_bellman
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι)
    (hcontracts : quittingStationaryFixedOpponentsContinueMass root who < 1) :
    quittingStationaryUnilateralCap reward root who =
      max (quittingStationaryFixedOpponentsQuitValue reward root who)
        (quittingStationaryFixedOpponentsContinueReward reward root who +
          quittingStationaryFixedOpponentsContinueMass root who *
            quittingStationaryUnilateralCap reward root who) := by
  exact quittingStationarySelectedCap_bellman _ _ _ hcontracts

/-- Under stationary opponent contraction, the game-facing Bellman equation
has the selected unilateral cap as its unique real solution. -/
theorem eq_quittingStationaryUnilateralCap_of_bellman
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) (value : ℝ)
    (hcontracts : quittingStationaryFixedOpponentsContinueMass root who < 1)
    (hvalue : value =
      max (quittingStationaryFixedOpponentsQuitValue reward root who)
        (quittingStationaryFixedOpponentsContinueReward reward root who +
          quittingStationaryFixedOpponentsContinueMass root who * value)) :
    value = quittingStationaryUnilateralCap reward root who := by
  exact eq_quittingStationarySelectedCap_of_bellman _ _ _ value
    (quittingStationaryFixedOpponentsContinueMass_nonneg root who)
    hcontracts hvalue

/-- Finite zero-terminal stationary Snell recursions converge to the
game-facing selected unilateral cap. -/
theorem tendsto_quittingStationaryUnilateralFiniteSnellValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι)
    (hcontracts : quittingStationaryFixedOpponentsContinueMass root who < 1) :
    Tendsto (quittingStationaryFiniteSnellValue
      (quittingStationaryFixedOpponentsQuitValue reward root who)
      (quittingStationaryFixedOpponentsContinueReward reward root who)
      (quittingStationaryFixedOpponentsContinueMass root who)) atTop
      (nhds (quittingStationaryUnilateralCap reward root who)) := by
  exact tendsto_quittingStationaryFiniteSnellValue _ _ _
    (quittingStationaryFixedOpponentsContinueMass_nonneg root who)
    hcontracts

end GameTheory
