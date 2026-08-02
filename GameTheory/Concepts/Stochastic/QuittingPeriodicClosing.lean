/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingPeriodicCompiler

/-!
# Closing approximately recurrent quitting paths into finite cycles

Repeating a finite segment changes the declared all-continue continuation at
its seam.  This file records the quantitative part of that closing argument.
An approximate cyclic policy recursion selects a genuine terminal value by
playerwise opponent contraction, and exact root Nash at the unclosed values
transfers to the selected cyclic values with an explicit continuation error.

This is deliberately not a compactness or recurrence theorem.  In particular,
nearby continuation endpoints do not imply playerwise opponent contraction.
The exceptional noncontracting player and its singleton-reward sign remain a
separate local-to-global boundary.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Root Nash transfers between two continuation vectors that are close in
the selected player's coordinate.  The factor two charges the prescribed and
deviating root payoffs separately. -/
theorem quittingRootDeviation_le_of_continuation_close
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : Payoff ι) (root : ι → PMF Bool)
    (who : ι) (deviation : PMF Bool) {ε δ : ℝ}
    (hδ : 0 ≤ δ) (hclose : |first who - second who| ≤ δ)
    (hnash : IsεQuittingRootNash reward first ε root) :
    quittingRootExpectedPayoff reward second
        (Function.update root who deviation) who ≤
      quittingRootExpectedPayoff reward second root who + ε + 2 * δ := by
  rw [abs_le] at hclose
  have hsecondFirst : second who ≤ first who + δ := by linarith
  have hfirstSecond : first who ≤ second who + δ := by linarith
  have hdeviation := quittingRootExpectedPayoff_continuation_le_add
    reward second first (Function.update root who deviation) who hδ hsecondFirst
  have hroot := quittingRootExpectedPayoff_continuation_le_add
    reward first second root who hδ hfirstSecond
  have hnashWho := hnash who deviation
  linarith

/-- Uniform continuation closeness transfers an `ε`-Nash root to an
`(ε + 2δ)`-Nash root. -/
theorem isεQuittingRootNash_of_continuation_close
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : Payoff ι) (root : ι → PMF Bool)
    {ε δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ who, |first who - second who| ≤ δ)
    (hnash : IsεQuittingRootNash reward first ε root) :
    IsεQuittingRootNash reward second (ε + 2 * δ) root := by
  intro who deviation
  simpa only [add_assoc] using
    (quittingRootDeviation_le_of_continuation_close
      reward first second root who deviation hδ (hclose who) hnash)

/-- An `ε`-Nash root makes the prescribed one-step Bellman residual at most
`ε`, provided the supplied scalar sequence is its policy-evaluation value. -/
theorem quittingPrescribedOneStepResidual_le_of_isεRootNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue
      reward roots who prescribed)
    (ε : ℝ)
    (hnash : ∀ time (deviation : PMF Bool),
      quittingRootExpectedPayoff reward
          (fun _ => prescribed (time + 1))
          (Function.update (roots time) who deviation) who ≤
        quittingRootExpectedPayoff reward
            (fun _ => prescribed (time + 1)) (roots time) who + ε)
    (time : ℕ) :
    quittingPrescribedOneStepResidual
      reward roots who prescribed time ≤ ε := by
  let tail : Payoff ι := fun _ => prescribed (time + 1)
  have hquit := hnash time (PMF.pure true)
  have hcontinue := hnash time (PMF.pure false)
  have hquit' : quittingFixedOpponentsQuitValue reward roots who time ≤
      quittingRootSuccessorPayoff reward tail (roots time) who + ε := by
    rw [← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
      reward roots who tail time]
    simpa only [tail, quittingRootQuitPayoff,
      quittingRootSuccessorPayoff] using hquit
  have hcontinue' :
      quittingFixedOpponentsContinueReward reward roots who time +
          quittingFixedOpponentsContinueMass roots who time *
            prescribed (time + 1) ≤
        quittingRootSuccessorPayoff reward tail (roots time) who + ε := by
    rw [← quittingRootContinuePayoff_eq_fixedOpponents
      reward roots who tail time]
    simpa only [tail, quittingRootContinuePayoff,
      quittingRootSuccessorPayoff] using hcontinue
  have hmax : quittingLiveBellmanValue reward roots who prescribed time ≤
      quittingRootSuccessorPayoff reward tail (roots time) who + ε := by
    unfold quittingLiveBellmanValue
    exact max_le hquit' hcontinue'
  have hpolicy : quittingRootSuccessorPayoff reward tail (roots time) who =
      prescribed time := by
    symm
    exact hprescribed time
  unfold quittingPrescribedOneStepResidual
  rw [hpolicy] at hmax
  linarith

/-- The playerwise error with which an approximate cyclic policy vector
selects the genuine terminal payoff of the repeated root segment. -/
def quittingCyclicPolicySelectionError {K : ℕ}
    (cycle : Fin K → ι → PMF Bool)
    (error : Fin K → ι → ℝ) (who : ι) (phase : Fin K) : ℝ :=
  quittingCyclicResidualCharge
      (fun cyclePhase =>
        quittingStationaryFixedOpponentsContinueMass
          (cycle cyclePhase) who)
      (fun cyclePhase => error cyclePhase who) phase K /
    (1 - ∏ cyclePhase : Fin K,
      quittingStationaryFixedOpponentsContinueMass
        (cycle cyclePhase) who)

/-- Policy-recursion error produced by identifying the two endpoints of a
nonempty finite segment.  Only the last phase pays the seam displacement. -/
def quittingCyclicSeamPolicyError {K : ℕ}
    (cycle : Fin (K + 1) → ι → PMF Bool) (δ : ℝ)
    (phase : Fin (K + 1)) (_who : ι) : ℝ :=
  if phase = Fin.last K then
    quittingStationaryContinueMass (cycle phase) * δ
  else 0

omit [DecidableEq ι] in
/-- Exact policy evaluation along an open segment becomes approximate cyclic
policy evaluation after a near-return seam is identified. -/
theorem abs_cyclicPolicyResidual_le_seamError
    {K : ℕ}
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin (K + 1) → ι → PMF Bool)
    (value : Fin (K + 1) → Payoff ι) (endpoint : Payoff ι)
    {δ : ℝ}
    (hstep : ∀ phase, phase ≠ Fin.last K →
      value phase = quittingRootSuccessorPayoff reward
        (value (finRotate (K + 1) phase)) (cycle phase))
    (hlast : value (Fin.last K) =
      quittingRootSuccessorPayoff reward endpoint (cycle (Fin.last K)))
    (hclose : ∀ who, |endpoint who - value 0 who| ≤ δ)
    (phase : Fin (K + 1)) (who : ι) :
    |value phase who -
        quittingRootSuccessorPayoff reward
          (value (finRotate (K + 1) phase)) (cycle phase) who| ≤
      quittingCyclicSeamPolicyError cycle δ phase who := by
  by_cases hlastPhase : phase = Fin.last K
  · subst phase
    rw [congrFun hlast who, finRotate_last]
    rw [quittingRootSuccessorPayoff_sub_eq_continueMass_mul,
      abs_mul, abs_of_nonneg
        (quittingStationaryContinueMass_nonneg (cycle (Fin.last K)))]
    unfold quittingCyclicSeamPolicyError
    rw [if_pos rfl]
    exact mul_le_mul_of_nonneg_left (hclose who)
      (quittingStationaryContinueMass_nonneg (cycle (Fin.last K)))
  · rw [congrFun (hstep phase hlastPhase) who]
    simp [quittingCyclicSeamPolicyError, hlastPhase]

/-- Approximate cyclic policy evaluation plus exact local Nash at the
unclosed continuation values gives explicit local Nash bounds at the genuine
terminal values selected by repeating the segment. -/
theorem quittingRootDeviation_le_cyclicTerminalValue_of_approximate_certificate
    {K : ℕ}
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool)
    (value : Fin K → Payoff ι) (error : Fin K → ι → ℝ) (ε : ℝ)
    (hpolicy : ∀ phase who,
      |value phase who -
        quittingRootSuccessorPayoff reward
          (value (finRotate K phase)) (cycle phase) who| ≤
        error phase who)
    (hnash : ∀ phase,
      IsεQuittingRootNash reward
        (value (finRotate K phase)) ε (cycle phase))
    (hcontracts : ∀ who,
      (∏ phase : Fin K,
        quittingStationaryFixedOpponentsContinueMass
          (cycle phase) who) < 1)
    (phase : Fin K) (who : ι) (deviation : PMF Bool) :
    quittingRootExpectedPayoff reward
        (quittingCyclicTerminalValue reward cycle (finRotate K phase))
        (Function.update (cycle phase) who deviation) who ≤
      quittingRootExpectedPayoff reward
          (quittingCyclicTerminalValue reward cycle (finRotate K phase))
          (cycle phase) who + ε +
        2 * quittingCyclicPolicySelectionError
          cycle error who (finRotate K phase) := by
  have hclose := abs_sub_quittingCyclicTerminalValue_le
    reward cycle value error hpolicy who (hcontracts who)
      (finRotate K phase)
  have herror0 : 0 ≤ quittingCyclicPolicySelectionError
      cycle error who (finRotate K phase) :=
    (abs_nonneg _).trans hclose
  exact quittingRootDeviation_le_of_continuation_close
    reward (value (finRotate K phase))
      (quittingCyclicTerminalValue reward cycle (finRotate K phase))
      (cycle phase) who deviation herror0 hclose (hnash phase)

/-- **Near-return closing lemma, local form.**  Repeat an exactly evaluated
finite root segment after identifying continuation endpoints within `δ`.
If its playerwise opponent products contract, then every repeated phase is a
root Nash action at the genuinely selected cyclic terminal continuation up to
the explicit seam-selection charge below. -/
theorem quittingRootDeviation_le_cyclicTerminalValue_of_nearReturn
    {K : ℕ}
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin (K + 1) → ι → PMF Bool)
    (value : Fin (K + 1) → Payoff ι) (endpoint : Payoff ι)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hstep : ∀ phase, phase ≠ Fin.last K →
      value phase = quittingRootSuccessorPayoff reward
        (value (finRotate (K + 1) phase)) (cycle phase))
    (hlast : value (Fin.last K) =
      quittingRootSuccessorPayoff reward endpoint (cycle (Fin.last K)))
    (hclose : ∀ who, |endpoint who - value 0 who| ≤ δ)
    (hnash : ∀ phase,
      IsεQuittingRootNash reward
        (if phase = Fin.last K then endpoint
          else value (finRotate (K + 1) phase))
        0 (cycle phase))
    (hcontracts : ∀ who,
      (∏ phase : Fin (K + 1),
        quittingStationaryFixedOpponentsContinueMass
          (cycle phase) who) < 1)
    (phase : Fin (K + 1)) (who : ι) (deviation : PMF Bool) :
    quittingRootExpectedPayoff reward
        (quittingCyclicTerminalValue reward cycle
          (finRotate (K + 1) phase))
        (Function.update (cycle phase) who deviation) who ≤
      quittingRootExpectedPayoff reward
          (quittingCyclicTerminalValue reward cycle
            (finRotate (K + 1) phase))
          (cycle phase) who + 2 * δ +
        2 * quittingCyclicPolicySelectionError
          cycle (quittingCyclicSeamPolicyError cycle δ) who
            (finRotate (K + 1) phase) := by
  have hpolicy : ∀ cyclePhase player,
      |value cyclePhase player -
        quittingRootSuccessorPayoff reward
          (value (finRotate (K + 1) cyclePhase))
          (cycle cyclePhase) player| ≤
        quittingCyclicSeamPolicyError cycle δ cyclePhase player :=
    abs_cyclicPolicyResidual_le_seamError
      reward cycle value endpoint hstep hlast hclose
  have hnashClosed : ∀ cyclePhase,
      IsεQuittingRootNash reward
        (value (finRotate (K + 1) cyclePhase)) (2 * δ)
        (cycle cyclePhase) := by
    intro cyclePhase
    by_cases hlastPhase : cyclePhase = Fin.last K
    · subst cyclePhase
      rw [finRotate_last]
      have htransfer := isεQuittingRootNash_of_continuation_close
        reward endpoint (value 0) (cycle (Fin.last K)) hδ hclose
          (by simpa using hnash (Fin.last K))
      simpa using htransfer
    · have hexact : IsεQuittingRootNash reward
          (value (finRotate (K + 1) cyclePhase)) 0
          (cycle cyclePhase) := by
        simpa [hlastPhase] using hnash cyclePhase
      intro player playerDeviation
      have hlocal := hexact player playerDeviation
      linarith
  exact
    quittingRootDeviation_le_cyclicTerminalValue_of_approximate_certificate
      reward cycle value (quittingCyclicSeamPolicyError cycle δ) (2 * δ)
        hpolicy hnashClosed hcontracts phase who deviation

/-! ## Abstract finite-block fixed-point closing

The game-facing lemmas above transport local root conditions across a seam.
The following scalar facts isolate the complementary global calculation. A
repeated block selects fixed points of its prescribed affine map and of each
player's one-block Snell operator. Approximate super-solutions are amplified
by at most the geometric factor one over one minus delta.
-/

/-- A fixed point of an affine contraction stays close to an approximate fixed
point, uniformly when the contraction coefficient is at most delta below
one. -/
theorem affineFixedPoint_dist_le_of_residual
    {G σ δ η V w : ℝ}
    (_hσ0 : 0 ≤ σ) (hσδ : σ ≤ δ) (hδ1 : δ < 1) (_hη0 : 0 ≤ η)
    (hfixed : V = G + σ * V)
    (hresidual : |(G + σ * w) - w| ≤ η) :
    |V - w| ≤ η / (1 - δ) := by
  have hσ1 : σ < 1 := lt_of_le_of_lt hσδ hδ1
  have hσden0 : 0 ≤ 1 - σ := (sub_pos.mpr hσ1).le
  have hδden : 0 < 1 - δ := sub_pos.mpr hδ1
  have hidentity :
      (1 - σ) * (V - w) = (G + σ * w) - w := by
    calc
      (1 - σ) * (V - w) = V - σ * V - w + σ * w := by ring
      _ = (G + σ * w) - w := by nlinarith [hfixed]
  have hscaled :
      (1 - σ) * |V - w| = |(G + σ * w) - w| := by
    calc
      (1 - σ) * |V - w| = |1 - σ| * |V - w| := by
        rw [abs_of_nonneg hσden0]
      _ = |(1 - σ) * (V - w)| := (abs_mul _ _).symm
      _ = |(G + σ * w) - w| := by rw [hidentity]
  have hactual : (1 - σ) * |V - w| ≤ η := by
    rw [hscaled]
    exact hresidual
  have hdelta : (1 - δ) * |V - w| ≤ η := by
    have habs0 : 0 ≤ |V - w| := abs_nonneg _
    nlinarith
  exact (le_div_iff₀ hδden).2 (by simpa [mul_comm] using hdelta)

/-- A fixed point of a scalar contraction lies below every approximate
super-solution, with the usual geometric amplification. -/
theorem contractingFixedPoint_le_of_approximateSuperSolution
    (T : ℝ → ℝ) {σ δ η B w : ℝ}
    (_hσ0 : 0 ≤ σ) (hσδ : σ ≤ δ) (hδ1 : δ < 1) (hη0 : 0 ≤ η)
    (hlipschitz : ∀ x y, |T x - T y| ≤ σ * |x - y|)
    (hfixed : T B = B) (hsuper : T w ≤ w + η) :
    B ≤ w + η / (1 - δ) := by
  have hδden : 0 < 1 - δ := sub_pos.mpr hδ1
  by_cases hBw : B ≤ w
  · have hquotient0 : 0 ≤ η / (1 - δ) :=
      div_nonneg hη0 hδden.le
    linarith
  · have hwB : w < B := lt_of_not_ge hBw
    have habs : |B - w| = B - w := abs_of_pos (sub_pos.mpr hwB)
    have hlip := hlipschitz B w
    have hdiff : B - T w ≤ σ * (B - w) := by
      rw [hfixed, habs] at hlip
      exact (le_abs_self (B - T w)).trans hlip
    have hactual : (1 - σ) * (B - w) ≤ η := by
      nlinarith
    have hdelta : (1 - δ) * (B - w) ≤ η := by
      nlinarith
    have hgap : B - w ≤ η / (1 - δ) :=
      (le_div_iff₀ hδden).2 (by simpa [mul_comm] using hdelta)
    linarith

/-- Combining an approximate prescribed fixed point with an approximate Snell
super-solution bounds the repeated block's deviation gap. -/
theorem finiteBlockClosingGap_le
    (T : ℝ → ℝ) {G σ σi δ η V B w : ℝ}
    (hσ0 : 0 ≤ σ) (hσδ : σ ≤ δ)
    (hσi0 : 0 ≤ σi) (hσiδ : σi ≤ δ)
    (hδ1 : δ < 1) (hη0 : 0 ≤ η)
    (hVfixed : V = G + σ * V)
    (hVresidual : |(G + σ * w) - w| ≤ η)
    (hTlipschitz : ∀ x y, |T x - T y| ≤ σi * |x - y|)
    (hBfixed : T B = B) (hTsuper : T w ≤ w + η) :
    B - V ≤ 2 * η / (1 - δ) := by
  have hprescribed := affineFixedPoint_dist_le_of_residual
    hσ0 hσδ hδ1 hη0 hVfixed hVresidual
  have hcap := contractingFixedPoint_le_of_approximateSuperSolution
    T hσi0 hσiδ hδ1 hη0 hTlipschitz hBfixed hTsuper
  have hbackward : w - V ≤ η / (1 - δ) :=
    (le_abs_self (w - V)).trans (by simpa [abs_sub_comm] using hprescribed)
  have hδden : 0 < 1 - δ := sub_pos.mpr hδ1
  rw [div_eq_mul_inv] at hcap hbackward ⊢
  nlinarith [inv_pos.mpr hδden]

end GameTheory
