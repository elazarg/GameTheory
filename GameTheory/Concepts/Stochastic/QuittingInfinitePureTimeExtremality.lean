/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingExceptionalInfiniteLTG

/-!
# Infinite pure quit-time extremality

Against a fixed sequence of opponent marginals, every time-dependent quitting
hazard is bounded by the supremum of the deterministic alternatives: quit at
one finite time, or never quit.  The supremum need not be attained when the
opponents and rewards vary with time, so the exact conclusion is an `sSup`
bound together with an epsilon-approximation corollary.

The proof passes through the finite pure-time simplex.  Its final atom is the
finite payoff from continuing throughout the truncation; that atom converges
to the explicit infinite `Never` payoff.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The deterministic hazard that quits at `some quitTime`, and never quits
when its argument is `none`. -/
def quittingPureTimeHazard (quitTime : Option ℕ) (time : ℕ) : PMF Bool :=
  match quitTime with
  | none => PMF.pure false
  | some quitTime =>
      if time = quitTime then PMF.pure true else PMF.pure false

@[simp] theorem quittingPureTimeHazard_none (time : ℕ) :
    quittingPureTimeHazard none time = PMF.pure false :=
  rfl

@[simp] theorem quittingPureTimeHazard_some_self (time : ℕ) :
    quittingPureTimeHazard (some time) time = PMF.pure true := by
  simp [quittingPureTimeHazard]

@[simp] theorem quittingPureTimeHazard_some_of_ne
    {quitTime time : ℕ} (hne : time ≠ quitTime) :
    quittingPureTimeHazard (some quitTime) time = PMF.pure false := by
  simp [quittingPureTimeHazard, hne]

/-- Terminal payoff of a deterministic finite quit time or of `Never`. -/
def quittingRootSequencePureTimeTerminalValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (quitTime : Option ℕ) (start : ℕ := 0) : ℝ :=
  quittingRootSequenceHazardTerminalValue reward roots who
    (quittingPureTimeHazard quitTime) start

/-- The terminal value of an arbitrary hazard satisfies the scalar
fixed-opponent Bellman recursion. -/
theorem quittingRootSequenceHazardTerminalValue_eq_hazardBellman
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (start : ℕ) :
    quittingRootSequenceHazardTerminalValue reward roots who hazard start =
      (hazard start true).toReal *
          quittingFixedOpponentsQuitValue reward roots who start +
        (hazard start false).toReal *
          (quittingFixedOpponentsContinueReward reward roots who start +
            quittingFixedOpponentsContinueMass roots who start *
              quittingRootSequenceHazardTerminalValue reward roots who hazard
                (start + 1)) := by
  rw [quittingRootSequenceHazardTerminalValue_eq_rootExpectedPayoff,
    quittingRootExpectedPayoff_update_eq_endpointMix,
    quittingRootQuitPayoff_eq_fixedOpponentsQuitValue,
    quittingRootContinuePayoff_eq_fixedOpponents]

/-- A finite deterministic quit atom is already its infinite terminal payoff:
the player surely quits before the finite boundary is reached. -/
theorem quittingFinitePureTimePayoff_castSucc_eq_terminal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) :
    ∀ (start fuel : ℕ) (choice : Fin fuel),
      quittingFinitePureTimePayoff reward roots who start fuel
          choice.castSucc =
        quittingRootSequencePureTimeTerminalValue reward roots who
          (some (start + choice.val)) start := by
  intro start fuel
  induction fuel generalizing start with
  | zero => exact fun choice => Fin.elim0 choice
  | succ fuel ih =>
      intro choice
      refine Fin.cases ?_ (fun later => ?_) choice
      · rw [quittingFinitePureTimePayoff, quittingFinitePureTimeValue]
        unfold quittingRootSequencePureTimeTerminalValue
        rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman]
        simp
      · rw [quittingFinitePureTimePayoff, quittingFinitePureTimeValue]
        simp only [Fin.castSucc_succ, Fin.cases_succ]
        unfold quittingRootSequencePureTimeTerminalValue
        rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman]
        have hne : start ≠ start + (Fin.succ later).val := by
          simp [Fin.val_succ]
        have htime :
            start + (Fin.succ later).val = (start + 1) + later.val := by
          simp [Fin.val_succ, Nat.add_comm, Nat.add_left_comm]
        rw [quittingPureTimeHazard_some_of_ne hne]
        simp only [PMF.pure_apply, if_neg (by decide : (true : Bool) ≠ false),
          ENNReal.toReal_zero, if_true,
          ENNReal.toReal_one, zero_mul, one_mul]
        change _ + _ * quittingFinitePureTimePayoff reward roots who
          (start + 1) fuel later.castSucc = _
        rw [ih (start + 1) later]
        rw [htime]
        simp only [zero_add]
        rfl

/-- The last finite pure-time atom is the zero-boundary finite payoff of the
explicit `Never` hazard. -/
theorem quittingFinitePureTimePayoff_last_eq_neverFinite
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) :
    ∀ (start fuel : ℕ),
      quittingFinitePureTimePayoff reward roots who start fuel
          (Fin.last fuel) =
        quittingFiniteRootPayoff reward roots who
          (quittingPureTimeHazard none) start fuel := by
  intro start fuel
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      rw [show Fin.last (fuel + 1) = (Fin.last fuel).succ by rfl]
      rw [quittingFinitePureTimePayoff, quittingFinitePureTimeValue,
        quittingFiniteRootPayoff]
      simp only [Fin.cases_succ]
      rw [quittingRootExpectedPayoff_update_eq_endpointMix,
        quittingRootQuitPayoff_eq_fixedOpponentsQuitValue,
        quittingRootContinuePayoff_eq_fixedOpponents]
      simp only [quittingPureTimeHazard_none, PMF.pure_apply,
        if_neg (by decide : (true : Bool) ≠ false), ENNReal.toReal_zero,
        if_true, ENNReal.toReal_one, zero_mul, one_mul]
      change _ + _ * quittingFinitePureTimePayoff reward roots who
        (start + 1) fuel (Fin.last fuel) = _
      rw [ih (start + 1)]
      simp only [zero_add]

/-! ## Infinite extremality against a root sequence -/

/-- Every arbitrary infinite hazard can be epsilon-approximated from above by
one deterministic finite quit time or by `Never`. -/
theorem exists_quittingRootSequencePureTimeTerminalValue_ge_sub
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) {ε : ℝ} (hε : 0 < ε) :
    ∃ quitTime : Option ℕ,
      quittingRootSequenceHazardTerminalValue reward roots who hazard 0 ≤
        quittingRootSequencePureTimeTerminalValue reward roots who quitTime 0 +
          ε := by
  let sourceValue :=
    quittingRootSequenceHazardTerminalValue reward roots who hazard 0
  let neverValue :=
    quittingRootSequencePureTimeTerminalValue reward roots who none 0
  have hsource : Tendsto (fun fuel =>
      quittingFiniteRootPayoff reward roots who hazard 0 fuel)
      atTop (nhds sourceValue) := by
    simpa [sourceValue, quittingRootSequenceHazardTerminalValue,
      quittingRootSequenceTerminalValue] using
      (tendsto_quittingFiniteRootPayoff_terminal reward roots who hazard 0)
  have hnever : Tendsto (fun fuel =>
      quittingFiniteRootPayoff reward roots who
        (quittingPureTimeHazard none) 0 fuel)
      atTop (nhds neverValue) := by
    simpa [neverValue, quittingRootSequencePureTimeTerminalValue,
      quittingRootSequenceHazardTerminalValue,
      quittingRootSequenceTerminalValue] using
      (tendsto_quittingFiniteRootPayoff_terminal reward roots who
        (quittingPureTimeHazard none) 0)
  obtain ⟨sourceThreshold, hsourceAfter⟩ :=
    (Metric.tendsto_atTop.mp hsource) (ε / 2) (half_pos hε)
  obtain ⟨neverThreshold, hneverAfter⟩ :=
    (Metric.tendsto_atTop.mp hnever) (ε / 2) (half_pos hε)
  let fuel := max sourceThreshold neverThreshold
  have hsourceClose := hsourceAfter fuel (le_max_left _ _)
  have hneverClose := hneverAfter fuel (le_max_right _ _)
  rw [Real.dist_eq] at hsourceClose hneverClose
  obtain ⟨choice, hchoice⟩ := exists_quittingFinitePureTimePayoff_ge
    reward roots who hazard 0 fuel
  revert hchoice
  refine Fin.lastCases ?_ (fun earlier => ?_) choice
  · intro hchoice
    refine ⟨none, ?_⟩
    rw [quittingFinitePureTimePayoff_last_eq_neverFinite] at hchoice
    have hsourceLower := (abs_lt.mp hsourceClose).1
    have hneverUpper := (abs_lt.mp hneverClose).2
    dsimp [sourceValue, neverValue] at hsourceLower hneverUpper ⊢
    linarith
  · intro hchoice
    refine ⟨some earlier.val, ?_⟩
    rw [quittingFinitePureTimePayoff_castSucc_eq_terminal] at hchoice
    simp only [Nat.zero_add] at hchoice
    have hsourceLower := (abs_lt.mp hsourceClose).1
    dsimp [sourceValue] at hsourceLower ⊢
    simpa only [Nat.zero_add] using (show
      quittingRootSequenceHazardTerminalValue reward roots who hazard 0 ≤
        quittingRootSequencePureTimeTerminalValue reward roots who
            (some earlier.val) 0 + ε by
      linarith)

/-- The deterministic pure-time payoff set is bounded above by every uniform
bound on the quitting rewards. -/
theorem bddAbove_range_quittingRootSequencePureTimeTerminalValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    BddAbove (Set.range fun quitTime : Option ℕ =>
      quittingRootSequencePureTimeTerminalValue reward roots who quitTime 0) := by
  refine ⟨M, ?_⟩
  rintro value ⟨quitTime, rfl⟩
  exact (le_abs_self _).trans (by
    simpa [quittingRootSequencePureTimeTerminalValue,
      quittingRootSequenceHazardTerminalValue,
      quittingRootSequenceTerminalValue] using
      (abs_quittingTerminalPayoff_le reward
        (quittingRootSequenceProfile reward
          (quittingRootSequenceUpdate roots who
            (quittingPureTimeHazard quitTime)) 0)
        who hM hreward))

/-- Infinite pure quit-time extremality.  The supremum contains every finite
quit date and the explicit `Never` atom. -/
theorem quittingRootSequenceHazardTerminalValue_le_sSup_pureTime
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    quittingRootSequenceHazardTerminalValue reward roots who hazard 0 ≤
      sSup (Set.range fun quitTime : Option ℕ =>
        quittingRootSequencePureTimeTerminalValue reward roots who
          quitTime 0) := by
  let values : Set ℝ := Set.range fun quitTime : Option ℕ =>
    quittingRootSequencePureTimeTerminalValue reward roots who quitTime 0
  have hbounded : BddAbove values :=
    bddAbove_range_quittingRootSequencePureTimeTerminalValue
      reward roots who hM hreward
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨quitTime, hquitTime⟩ :=
    exists_quittingRootSequencePureTimeTerminalValue_ge_sub
      reward roots who hazard hε
  calc
    quittingRootSequenceHazardTerminalValue reward roots who hazard 0 ≤
        quittingRootSequencePureTimeTerminalValue reward roots who
          quitTime 0 + ε := hquitTime
    _ ≤ sSup values + ε := by
      simpa only [add_comm] using
        (add_le_add_right (le_csSup hbounded ⟨quitTime, rfl⟩) ε)

end GameTheory
