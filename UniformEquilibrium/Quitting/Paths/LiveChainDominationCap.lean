/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Debt.Ledger.PunishClock
import UniformEquilibrium.Quitting.Cycles.InfinitePureTimeExtremality

/-!
# Domination of every live-chain deviation by the ledger cap

`QuittingLedgerPunishClock.lean` reduces the plan phase of Simon's
Proposition 3 to one named residual, `hdominate`: that *every* unilateral
hazard deviation is beaten by the always-Continue deviation up to a slack.
This file discharges the plan-phase cap **without** that hypothesis, by the
exact performance-difference decomposition and the survival-weighted Abel
argument.

## Why `hdominate` is not the right shape

`hdominate` compares an arbitrary deviation with the *always-Continue*
deviation.  That comparison is false with a small slack.  Take one player,
`reward {who} who = 1`, and the plan that quits surely at every stage: every
ledger increment is `0` and the quit regret is `0`, so both caps below are
`0`, yet the always-Continue deviation never absorbs and is worth `0` while
quitting at stage `0` is worth `1`.  The gap is of the order of the payoff
range, not of the order of the per-stage caps.  What *is* true, and what the
consumer actually needs, is the comparison with the **plan's own value**:

`hazard deviation value ≤ plan value + (ledger cap + one-stage quit regret)`.

That is the statement proved here, and it is literally hypothesis (a) of
`quittingTerminalPayoff_update_quittingPhaseSwitchProfile_le`.

## The decomposition

Write `V_k` for the plan's own value at live stage `k`, `Q_k` for the payoff
from quitting there against the plan's opponents' marginals, `R_k` and `s_k`
for the opponents' immediate absorbing contribution and survival mass, and

* `d_k := quittingLedgerStageAdvantage = R_k + s_k · V_{k+1} − V_k`, the
  ledger increment;
* `e_k := quittingLedgerQuitRegret = Q_k − V_k`, the quit regret;
* `c_k := quittingOpponentSurvivalWeight … 0 k = ∏_{j<k} s_j`, the reach
  weight.

The pure deviation "continue at `0, …, t−1`, quit at `t`" then satisfies the
*exact* identity
`quittingRootSequencePureTimeTerminalValue_some_sub_eq`:

`U^{(t)}_0 − V_0 = ∑_{k<t} c_k d_k + c_t e_t`,

with no independence assumption between stages: the possibility that an
opponent quits first is already encoded in the decreasing weights `c_k`.
Abel summation against the ledger cap (`quittingLedgerPunishClock`'s
`sum_mul_le_initialWeight_mul_of_partialSum_le`, reused verbatim rather than
duplicated) turns `∑_{k<t} c_k d_k ≤ ε` out of `W_j ≤ ε`, because the weights
are antitone, nonnegative and start at `1`.

## The side condition the residual was hiding

The cap quantifies over deviations that quit at *any* stage, including stages
past the cutoff, where the truncated plan is all-Continue and worth zero.
Quitting alone there is worth `reward {who} who`, so any cap of the form
`ε + δ` forces `δ ≥ reward {who} who`.  That is not an artefact of the proof:
`quittingLedgerQuitRegret_quittingTruncatedRoots_of_le` computes the tail
regret exactly.  The hypothesis `hregret` states the condition openly instead
of burying it in a dominance assumption.

## The unrestricted quantifier

The quantifier over deviations is genuinely *all* behavioural hazards.  Its
reduction to the two pure shapes -- quit at some finite stage, or never quit
-- is `exists_quittingRootSequencePureTimeTerminalValue_ge_sub`, already
proved in `QuittingInfinitePureTimeExtremality.lean` by convexity of the
finite hazard simplex followed by a limit.  This file supplies the bound for
each pure shape; the never-quit shape is exactly the always-Continue
deviation the ledger cash-out already prices.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The quit regret and the reach weights -/

/-- **The quit regret `e_k`.**  Quitting now against the plan's own
opponents' marginals, measured against the plan's own value at that stage.
It is the second half of the root endpoint test, in the same conditional
normalisation as `quittingLedgerStageAdvantage`. -/
def quittingLedgerQuitRegret
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (stage : ℕ) : ℝ :=
  quittingFixedOpponentsQuitValue reward roots who stage -
    quittingRootSequenceTerminalValue reward roots who stage

/-- Under root endpoint `ε`-Nash at the stage, the quit regret is at most
`ε`: it *is* the pure-Quit regret of the endpoint test, just as the ledger
increment is the pure-Continue one. -/
theorem quittingLedgerQuitRegret_le_of_isεQuittingRootEndpointNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (stage : ℕ) {ε : ℝ}
    (hnash : IsεQuittingRootEndpointNash reward
      (quittingRootSequenceTailVector reward roots (stage + 1)) ε (roots stage)) :
    quittingLedgerQuitRegret reward roots who stage ≤ ε := by
  have hsum := quittingRoot_continueProbability_add_quitProbability (roots stage) who
  have hvalue := quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector
    reward roots who stage
  have hmix := quittingRootSuccessorPayoff_eq_endpointMix reward
    (quittingRootSequenceTailVector reward roots (stage + 1)) (roots stage) who
  have hquit := quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward roots who
    (quittingRootSequenceTailVector reward roots (stage + 1)) stage
  have hendpoint := (hnash who).1
  unfold quittingRootEndpointDifference at hendpoint
  unfold quittingLedgerQuitRegret
  rw [← hquit, hvalue, hmix]
  have hcontinue : (roots stage who false).toReal =
      1 - (roots stage who true).toReal := by linarith
  rw [hcontinue] at hendpoint ⊢
  have hregroup :
      quittingRootQuitPayoff reward
            (quittingRootSequenceTailVector reward roots (stage + 1))
            (roots stage) who -
          ((roots stage who true).toReal *
              quittingRootQuitPayoff reward
                (quittingRootSequenceTailVector reward roots (stage + 1))
                (roots stage) who +
            (1 - (roots stage who true).toReal) *
              quittingRootContinuePayoff reward
                (quittingRootSequenceTailVector reward roots (stage + 1))
                (roots stage) who) =
        (1 - (roots stage who true).toReal) *
          (quittingRootQuitPayoff reward
              (quittingRootSequenceTailVector reward roots (stage + 1))
              (roots stage) who -
            quittingRootContinuePayoff reward
              (quittingRootSequenceTailVector reward roots (stage + 1))
              (roots stage) who) := by ring
  linarith [hendpoint, hregroup]

/-- Every finite reach weight is at most one: it is a product of
probabilities. -/
theorem quittingOpponentSurvivalWeight_le_one_of_mass
    (roots : ℕ → ι → PMF Bool) (who : ι) (start fuel : ℕ) :
    quittingOpponentSurvivalWeight roots who start fuel ≤ 1 := by
  refine Finset.prod_le_one (fun offset _ => ?_) (fun offset _ => ?_)
  · exact quittingStationaryContinueMass_nonneg
      (Function.update (roots (start + offset)) who (PMF.pure false))
  · exact quittingStationaryContinueMass_le_one
      (Function.update (roots (start + offset)) who (PMF.pure false))

/-! ## The exact performance-difference identity -/

/-- **The performance-difference identity.**  The pure deviation that
continues at `start, …, start + delay − 1` and quits at `start + delay`
gains, over the plan's own value, exactly the reach-weighted ledger prefix
plus the reach-weighted quit regret at the quitting stage.

This is an identity, not a bound: no independence between stages is used,
and the possibility that an opponent quits first is carried entirely by the
decreasing weights. -/
theorem quittingRootSequencePureTimeTerminalValue_some_sub_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (delay : ℕ) :
    ∀ start : ℕ,
      quittingRootSequencePureTimeTerminalValue reward roots who
            (some (start + delay)) start -
          quittingRootSequenceTerminalValue reward roots who start =
        (∑ offset ∈ Finset.range delay,
            quittingOpponentSurvivalWeight roots who start offset *
              quittingLedgerStageAdvantage reward roots who (start + offset)) +
          quittingOpponentSurvivalWeight roots who start delay *
            quittingLedgerQuitRegret reward roots who (start + delay) := by
  induction delay with
  | zero =>
      intro start
      unfold quittingRootSequencePureTimeTerminalValue
      rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman]
      simp [quittingOpponentSurvivalWeight, quittingLedgerQuitRegret]
  | succ delay ih =>
      intro start
      have hne : start ≠ start + (delay + 1) := by omega
      have hstep :
          quittingRootSequencePureTimeTerminalValue reward roots who
              (some (start + (delay + 1))) start =
            quittingFixedOpponentsContinueReward reward roots who start +
              quittingFixedOpponentsContinueMass roots who start *
                quittingRootSequencePureTimeTerminalValue reward roots who
                  (some (start + (delay + 1))) (start + 1) := by
        unfold quittingRootSequencePureTimeTerminalValue
        rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman,
          quittingPureTimeHazard_some_of_ne hne]
        simp
      have hindex : start + 1 + delay = start + (delay + 1) := by omega
      have htail := ih (start + 1)
      rw [hindex] at htail
      have hpeel : ∀ offset ∈ Finset.range delay,
          quittingOpponentSurvivalWeight roots who start (offset + 1) *
              quittingLedgerStageAdvantage reward roots who
                (start + (offset + 1)) =
            quittingFixedOpponentsContinueMass roots who start *
              (quittingOpponentSurvivalWeight roots who (start + 1) offset *
                quittingLedgerStageAdvantage reward roots who
                  (start + 1 + offset)) := by
        intro offset _
        have hoffset : start + (offset + 1) = start + 1 + offset := by omega
        rw [quittingOpponentSurvivalWeight_succ_left, hoffset, mul_assoc]
      have hsplit := Finset.sum_range_succ' (fun offset =>
        quittingOpponentSurvivalWeight roots who start offset *
          quittingLedgerStageAdvantage reward roots who (start + offset)) delay
      rw [Finset.sum_congr rfl hpeel, ← Finset.mul_sum] at hsplit
      have hfirst : quittingOpponentSurvivalWeight roots who start 0 = 1 := by
        simp [quittingOpponentSurvivalWeight]
      have hadvantage := quittingLedgerStageAdvantage_eq_fixedOpponents
        reward roots who start
      rw [hstep, hsplit, hfirst, quittingOpponentSurvivalWeight_succ_left]
      simp only [Nat.add_zero, one_mul]
      linear_combination
        quittingFixedOpponentsContinueMass roots who start * htail - hadvantage

/-! ## The Abel bound for a finite quit date -/

/-- **The finite-quit-date cap (`D.13`).**  Under the ledger cap up to the
quit date and a quit regret at most `δ` there, quitting at that date gains at
most `ε + δ` over the plan's own value: the first-crossing rule caps every
survival-weighted Continue prefix by `ε`, and the terminating Quit contributes
one further `δ`-sized half-step. -/
theorem quittingRootSequencePureTimeTerminalValue_some_le_of_ledger_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (delay : ℕ) {ε δ : ℝ}
    (hδ : 0 ≤ δ)
    (hledger : ∀ index, index ≤ delay →
      quittingLedger reward roots who index ≤ ε)
    (hregret : quittingLedgerQuitRegret reward roots who delay ≤ δ) :
    quittingRootSequencePureTimeTerminalValue reward roots who (some delay) 0 ≤
      quittingRootSequenceTerminalValue reward roots who 0 + (ε + δ) := by
  have hidentity :=
    quittingRootSequencePureTimeTerminalValue_some_sub_eq reward roots who delay 0
  simp only [Nat.zero_add] at hidentity
  have habel := sum_mul_le_initialWeight_mul_of_partialSum_le
    (weight := quittingOpponentSurvivalWeight roots who 0)
    (summand := quittingLedgerStageAdvantage reward roots who) delay
    (fun stage => antitone_quittingOpponentSurvivalWeight roots who 0
      (Nat.le_succ stage))
    (quittingOpponentSurvivalWeight_nonneg roots who 0 delay) hledger
  rw [show quittingOpponentSurvivalWeight roots who 0 0 = 1 by
    simp [quittingOpponentSurvivalWeight], one_mul] at habel
  have hweight := quittingOpponentSurvivalWeight_nonneg roots who 0 delay
  have hweightOne := quittingOpponentSurvivalWeight_le_one_of_mass roots who 0 delay
  nlinarith [hidentity, habel, hregret, hweight, hweightOne, hδ]

/-! ## The never-quit branch -/

/-- The `Never` atom of the pure-time family *is* the always-Continue
deviation. -/
theorem quittingPureTimeHazard_none_eq_quittingAlwaysContinueHazard :
    quittingPureTimeHazard none = quittingAlwaysContinueHazard :=
  rfl

/-! ## The unrestricted domination cap -/

/-- **Every behavioural deviation, capped by the ledger (general form).**
For an arbitrary root sequence, an arbitrary unilateral hazard gains at most
`ε + δ` over the plan's own value, plus the reach weight at any chosen
horizon times the payoff range.

The quantifier is over *all* hazard sequences: randomised, history-dependent,
anything.  The reduction to the two pure shapes is
`exists_quittingRootSequencePureTimeTerminalValue_ge_sub`. -/
theorem quittingRootSequenceHazardTerminalValue_le_of_ledger_le_of_quitRegret_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (horizon : ℕ)
    {ε δ bound : ℝ} (hbound : 0 ≤ bound) (hδ : 0 ≤ δ)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hledger : ∀ index, quittingLedger reward roots who index ≤ ε)
    (hregret : ∀ stage, quittingLedgerQuitRegret reward roots who stage ≤ δ)
    (hazard : ℕ → PMF Bool) :
    quittingRootSequenceHazardTerminalValue reward roots who hazard 0 ≤
      quittingRootSequenceTerminalValue reward roots who 0 +
        (ε + δ +
          quittingOpponentSurvivalWeight roots who 0 horizon * (2 * bound)) := by
  have htail : 0 ≤ quittingOpponentSurvivalWeight roots who 0 horizon * (2 * bound) :=
    mul_nonneg (quittingOpponentSurvivalWeight_nonneg roots who 0 horizon)
      (by linarith)
  refine le_of_forall_pos_le_add fun slack hslack => ?_
  obtain ⟨quitTime, hquitTime⟩ :=
    exists_quittingRootSequencePureTimeTerminalValue_ge_sub
      reward roots who hazard hslack
  cases quitTime with
  | none =>
      have hcontinue :=
        quittingRootSequenceHazardTerminalValue_quittingAlwaysContinueHazard_le_of_ledger_le
          reward roots who horizon hbound hreward (fun index _ => hledger index)
      rw [quittingRootSequencePureTimeTerminalValue,
        quittingPureTimeHazard_none_eq_quittingAlwaysContinueHazard] at hquitTime
      linarith [hquitTime, hcontinue]
  | some delay =>
      have hpure := quittingRootSequencePureTimeTerminalValue_some_le_of_ledger_le
        reward roots who delay hδ (fun index _ => hledger index) (hregret delay)
      linarith [hquitTime, hpure]

/-! ## The truncated plan: hypothesis (a) with no residual -/

/-- Past the cutoff the truncated plan puts no mass on quitting, so its
ledger increment vanishes there. -/
theorem quittingLedgerStageAdvantage_quittingTruncatedRoots_eq_zero_of_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan : ℕ → ι → PMF Bool) (who : ι) {cutoff stage : ℕ}
    (hstage : cutoff ≤ stage) :
    quittingLedgerStageAdvantage reward (quittingTruncatedRoots plan cutoff)
      who stage = 0 := by
  rw [quittingLedgerStageAdvantage_eq_neg_quitProbability_mul_endpointDifference,
    quittingTruncatedRoots_of_le plan hstage]
  simp [quittingAllContinueRoot]

/-- Past the cutoff the truncated plan's ledger is frozen. -/
theorem quittingLedger_quittingTruncatedRoots_add_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan : ℕ → ι → PMF Bool) (who : ι) (cutoff extra : ℕ) :
    quittingLedger reward (quittingTruncatedRoots plan cutoff) who
        (cutoff + extra) =
      quittingLedger reward (quittingTruncatedRoots plan cutoff) who cutoff := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
      rw [show cutoff + (extra + 1) = (cutoff + extra) + 1 by omega,
        quittingLedger_succ,
        quittingLedgerStageAdvantage_quittingTruncatedRoots_eq_zero_of_le
          reward plan who (Nat.le_add_right cutoff extra),
        add_zero, ih]

/-- Past the cutoff every opponent surely continues, so the truncated plan's
opponent-survival mass is one there. -/
theorem quittingFixedOpponentsContinueMass_quittingTruncatedRoots_of_le
    (plan : ℕ → ι → PMF Bool) (who : ι) {cutoff stage : ℕ}
    (hstage : cutoff ≤ stage) :
    quittingFixedOpponentsContinueMass (quittingTruncatedRoots plan cutoff)
      who stage = 1 := by
  unfold quittingFixedOpponentsContinueMass quittingStationaryContinueMass
  rw [quittingTruncatedRoots_of_le plan hstage]
  have hupdate : Function.update (quittingAllContinueRoot : ι → PMF Bool) who
      (PMF.pure false) = (quittingAllContinueRoot : ι → PMF Bool) :=
    Function.update_eq_self who (quittingAllContinueRoot : ι → PMF Bool)
  rw [hupdate, pmfPi_apply]
  simp [quittingAllContinueRoot, quittingAllContinueAction]

/-- **The tail of the quit regret, computed.**  From the cutoff on the
truncated plan is all-Continue, so its value there is zero and quitting there
is worth exactly the solo-quitting reward.  Consequently the hypothesis
`hregret` below genuinely forces `δ ≥ reward {who} who`: with an all-Continue
suffix a player who profits from quitting alone will do so, and no ledger
argument can prevent it.  This is the side condition the `hdominate` residual
was hiding. -/
theorem quittingLedgerQuitRegret_quittingTruncatedRoots_of_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan : ℕ → ι → PMF Bool) (who : ι) {cutoff stage : ℕ}
    (hstage : cutoff ≤ stage) {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ S, |reward S who| ≤ bound) :
    quittingLedgerQuitRegret reward (quittingTruncatedRoots plan cutoff) who
        stage =
      reward (quittingSingletonTerminal who) who := by
  have hmass := quittingFixedOpponentsContinueMass_quittingTruncatedRoots_of_le
    plan who hstage
  have hvalue : quittingRootSequenceTerminalValue reward
      (quittingTruncatedRoots plan cutoff) who stage = 0 :=
    quittingRootSequenceTerminalValue_eq_zero_of_allContinue_from reward _ who stage
      fun time htime =>
        quittingTruncatedRoots_of_le plan (le_trans hstage htime)
  have hclose := abs_quittingFixedOpponentsQuitValue_sub_continueMass_mul_solo_le
    reward (quittingTruncatedRoots plan cutoff) who stage bound hbound hreward
  rw [hmass, one_mul, sub_self, mul_zero] at hclose
  unfold quittingLedgerQuitRegret
  rw [hvalue, sub_zero]
  have := abs_nonpos_iff.mp hclose
  linarith [this]

/-- The truncated plan's ledger cap on `[0, cutoff]` already caps every
index. -/
theorem quittingLedger_quittingTruncatedRoots_le_of_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan : ℕ → ι → PMF Bool) (who : ι) (cutoff : ℕ) {ε : ℝ}
    (hledger : ∀ index, index ≤ cutoff →
      quittingLedger reward (quittingTruncatedRoots plan cutoff) who index ≤ ε)
    (index : ℕ) :
    quittingLedger reward (quittingTruncatedRoots plan cutoff) who index ≤ ε := by
  rcases le_or_gt index cutoff with hle | hgt
  · exact hledger index hle
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hgt.le
    rw [quittingLedger_quittingTruncatedRoots_add_eq]
    exact hledger cutoff le_rfl

/-- Against the truncated plan the ledger cash-out has no remainder, so the
always-Continue deviation gains at most the ledger cap. -/
theorem quittingRootSequenceHazardTerminalValue_quittingTruncatedRoots_alwaysContinue_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan : ℕ → ι → PMF Bool) (who : ι) (cutoff : ℕ) {ε : ℝ}
    (hledger : ∀ index, index ≤ cutoff →
      quittingLedger reward (quittingTruncatedRoots plan cutoff) who index ≤ ε) :
    quittingRootSequenceHazardTerminalValue reward
        (quittingTruncatedRoots plan cutoff) who quittingAlwaysContinueHazard 0 ≤
      quittingRootSequenceTerminalValue reward
        (quittingTruncatedRoots plan cutoff) who 0 + ε := by
  have hidentity :=
    quittingRootSequenceHazardTerminalValue_quittingAlwaysContinueHazard_sub_eq_ledgerSum
      reward (quittingTruncatedRoots plan cutoff) who cutoff
  rw [quittingRootSequenceHazardTerminalValue_quittingTruncatedRoots_alwaysContinue_eq_zero,
    quittingRootSequenceTerminalValue_quittingTruncatedRoots_cutoff_eq_zero,
    sub_zero, mul_zero, add_zero] at hidentity
  have habel := sum_mul_le_initialWeight_mul_of_partialSum_le
    (weight := quittingOpponentSurvivalWeight (quittingTruncatedRoots plan cutoff) who 0)
    (summand := quittingLedgerStageAdvantage reward
      (quittingTruncatedRoots plan cutoff) who) cutoff
    (fun stage => antitone_quittingOpponentSurvivalWeight _ who 0 (Nat.le_succ stage))
    (quittingOpponentSurvivalWeight_nonneg _ who 0 cutoff) hledger
  rw [show quittingOpponentSurvivalWeight (quittingTruncatedRoots plan cutoff) who 0 0 = 1
    by simp [quittingOpponentSurvivalWeight], one_mul] at habel
  linarith [hidentity, habel]

/-- **Hypothesis (a), proved.**  Against the truncated plan *every*
unilateral behavioural deviation gains at most `ε + δ` over the plan's own
value, where `ε` caps the ledger up to the cutoff and `δ` caps the quit
regret.  This is literally the plan-phase hypothesis of
`quittingTerminalPayoff_update_quittingPhaseSwitchProfile_le`, with
`planError = ε + δ`, and it replaces the `hdominate` residual of
`QuittingLedgerPunishClock.lean`. -/
theorem quittingRootSequenceHazardTerminalValue_quittingTruncatedRoots_le_of_quitRegret_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan : ℕ → ι → PMF Bool) (who : ι) (cutoff : ℕ) {ε δ : ℝ} (hδ : 0 ≤ δ)
    (hledger : ∀ index, index ≤ cutoff →
      quittingLedger reward (quittingTruncatedRoots plan cutoff) who index ≤ ε)
    (hregret : ∀ stage, quittingLedgerQuitRegret reward
      (quittingTruncatedRoots plan cutoff) who stage ≤ δ)
    (hazard : ℕ → PMF Bool) :
    quittingRootSequenceHazardTerminalValue reward
        (quittingTruncatedRoots plan cutoff) who hazard 0 ≤
      quittingRootSequenceTerminalValue reward
          (quittingTruncatedRoots plan cutoff) who 0 + (ε + δ) := by
  have hall := quittingLedger_quittingTruncatedRoots_le_of_le reward plan who cutoff
    hledger
  refine le_of_forall_pos_le_add fun slack hslack => ?_
  obtain ⟨quitTime, hquitTime⟩ :=
    exists_quittingRootSequencePureTimeTerminalValue_ge_sub
      reward (quittingTruncatedRoots plan cutoff) who hazard hslack
  cases quitTime with
  | none =>
      have hcontinue :=
        quittingRootSequenceHazardTerminalValue_quittingTruncatedRoots_alwaysContinue_le
          reward plan who cutoff hledger
      rw [quittingRootSequencePureTimeTerminalValue,
        quittingPureTimeHazard_none_eq_quittingAlwaysContinueHazard] at hquitTime
      linarith [hquitTime, hcontinue]
  | some delay =>
      have hpure := quittingRootSequencePureTimeTerminalValue_some_le_of_ledger_le
        reward (quittingTruncatedRoots plan cutoff) who delay hδ
        (fun index _ => hall index) (hregret delay)
      linarith [hquitTime, hpure]

/-- **The assembled cap with no residual.**  The phase-switch deviation cap
whose plan phase is discharged by the ledger cap and the quit-regret cap.
Compared with
`quittingTerminalPayoff_update_quittingPhaseSwitchProfile_le_of_ledger_le`
the `hdominate` hypothesis is gone: it has been replaced by `hregret`, a
per-stage one-sided bound that root endpoint `ε`-Nash supplies directly
through `quittingLedgerQuitRegret_le_of_isεQuittingRootEndpointNash`. -/
theorem quittingTerminalPayoff_update_quittingPhaseSwitchProfile_le_of_quitRegret_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan punish : ℕ → ι → PMF Bool) (switch : ℕ) (who : ι)
    {ε δ punishError punishCap survivalCap bound : ℝ}
    (hbound : 0 ≤ bound) (hδ : 0 ≤ δ)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hledger : ∀ index, index ≤ switch →
      quittingLedger reward (quittingTruncatedRoots plan switch) who index ≤ ε)
    (hregret : ∀ stage, quittingLedgerQuitRegret reward
      (quittingTruncatedRoots plan switch) who stage ≤ δ)
    (hpunish : ∀ g : ℕ → PMF Bool,
      quittingRootSequenceHazardTerminalValue reward punish who g 0 ≤
        punishCap + punishError)
    (hsurvival : quittingOpponentSurvivalWeight plan who 0 switch ≤ survivalCap)
    (deviation : (quittingGame reward).BehaviorStrategy who) :
    quittingTerminalPayoff reward
        (Function.update (quittingPhaseSwitchProfile reward plan punish switch)
          who deviation) who ≤
      quittingTerminalPayoff reward
          (quittingPhaseSwitchProfile reward plan punish switch) who +
        (ε + δ) +
        survivalCap * (max (punishCap + punishError) 0 + bound) :=
  quittingTerminalPayoff_update_quittingPhaseSwitchProfile_le reward plan punish
    switch who hbound hreward
    (quittingRootSequenceHazardTerminalValue_quittingTruncatedRoots_le_of_quitRegret_le
      reward plan who switch hδ hledger hregret)
    hpunish hsurvival deviation

end GameTheory
