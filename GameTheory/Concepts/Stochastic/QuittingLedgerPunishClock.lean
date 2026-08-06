/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingSurvivalWindowLanding
import GameTheory.Concepts.Stochastic.QuittingPlannedSurvivalStoppingIndex
import GameTheory.Concepts.Stochastic.QuittingFiniteChainTerminalCompiler
import GameTheory.Concepts.Stochastic.QuittingSurvivalPrefixBridge
import GameTheory.Concepts.Stochastic.QuittingNashBellmanSpine
import GameTheory.Concepts.Stochastic.QuittingExceptionalTailLimits

/-!
# The cumulative-advantage ledger and the punish clock

Simon (Adv. Appl. Math. 38 (2007) 1-26) opens the proof of Proposition 3 by
attaching to every player `n` a **ledger**

`W_i^n := ∑_{k<i} (b_n(r_{k+1}(p), p_k) − r_k^n(p))`,

"the cumulative advantage `n` has obtained by choosing `c` at all stages
before `i`, conditioned on no other player having quit", and two clocks:
`i^n_∗`, the first `i` with `W_i^n ≥ ε`, and `i^n_♯`, the first `i` at which
the player's own *prescribed* survival `c_i^n = ∏_{k<i}(1 − p_k^n)` has
fallen to `ε/M`.  The switch stage is `î := min_n min(i^n_∗, i^n_♯)` and the
punished player `n̂` is a minimiser, preferring an `i^n_♯`-achiever.

This file formalises that layer for the mixture encoding over root sequences.

## Which quantity the summand is

Simon's `b_n(r_{k+1}(p), p_k)` is the **deleted** object: player `n`'s payoff
from playing pure Continue at stage `k` against the *other* players' stage-`k`
marginals, resumed by the plan's own continuation vector.  In this repository
that is `quittingRootContinuePayoff` at the root `roots k` with tail
`quittingRootSequenceTailVector reward roots (k + 1)`, and `r_k^n(p)` is
`quittingRootSequenceTerminalValue reward roots who k`.  So

`quittingLedgerStageAdvantage = quittingRootContinuePayoff − terminalValue`,

and the deleted normalisation is visible in
`quittingLedgerStageAdvantage_eq_fixedOpponents`: the summand is
`R_k + c_k · V_{k+1} − V_k` with `c_k` the *opponent-only* continue mass
`quittingFixedOpponentsContinueMass`, never the joint mass.  The two are
related by the survival-prefix bridge, recorded here in ledger form as
`quittingLedgerJointContinueMass_eq_own_mul_deleted`: the joint mass is the
deleted mass times `who`'s own continue probability.  Both terms of the
summand are *conditional on reaching stage `k` live*; the ledger is a plain
unweighted sum of conditional advantages, and the survival weights appear
only when it is cashed against a global deviation (part 3 below).

The exact identity landed on is

`quittingLedgerStageAdvantage_eq_neg_quitProbability_mul_endpointDifference`:

`W_{k+1} − W_k = −(p_k^n · quittingRootEndpointDifference …)`,

`p_k^n` being `who`'s own prescribed quit probability at stage `k`.  It is
*not* the negation of `quittingStageGap`: that gap measures Quit against the
Continue value, whereas the ledger measures Continue against the plan's own
mixture.  The exact difference between the two readings is recorded in
`quittingLedgerStageAdvantage_add_quittingStageGap`.  What the increment *is*
is the "pure Continue regret" half of `IsεQuittingRootEndpointNash`, which is
why an `ε`-rational plan has every ledger increment at most `ε`.

## What is proved

1. **The ledger.**  `quittingLedger`, its vanishing at `0`, its one-step
   recursion, the increment bound `2·bound` and hence `|W_i| ≤ i·(2·bound)`,
   and the per-stage `ε` bound under root endpoint `ε`-Nash.
2. **The clocks.**  `quittingLedgerStoppingIndex` (`i^n_∗`) in the
   `Nat.find`-with-`0`-default shape of `quittingPlannedSurvivalStoppingIndex`
   (`i^n_♯`, imported as is), the combinator `quittingPunishSwitchIndex` (`î`)
   as a `Finset.inf'` over players, the punish target
   `quittingPunishTarget` (`n̂`) preferring `i^n_♯`-achievers, and the
   consumer lemma `quittingLedger_lt_of_lt_quittingPunishSwitchIndex`: before
   the switch **no** player's ledger has reached `ε`.
3. **The feed-in.**  Against the always-Continue deviation the *global* gain
   is the opponent-survival-weighted ledger sum plus a survival-weighted
   remainder (`…_sub_eq_ledgerSum`), and Abel summation against the ledger cap
   turns that into the plan-phase cap
   (`…_quittingAlwaysContinueHazard_le_of_ledger_le`).  Specialised to the
   truncated plan the remainder vanishes and one gets literally hypothesis
   (a) of `quittingTerminalPayoff_update_quittingPhaseSwitchProfile_le`.

## The honest residual

The feed-in is stated with an explicit hypothesis `hdominate`: that every
hazard deviation is beaten by the always-Continue one up to `quitSlack`.
That hypothesis is exactly Simon's sentence "since quitting terminates the
game immediately and the one-stage advantage of doing so never exceeds
`ε⁴/(2M³)`, the only deviation to consider is repetitive continuing", and it
is **not** proved here: closing it is the rank-1 decision-discrepancy-process
argument of Propositions 1-2, a separate component.  Everything else on the
plan-phase side of Proposition 3 is discharged.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

/-! ## Abel summation against a partial-sum sequence -/

/-- **Summation by parts.**  A weighted sum rewrites as the weight
increments tested against the partial sums, plus the final weight times the
final partial sum. -/
theorem sum_mul_eq_sum_weightStep_mul_partialSum (weight summand : ℕ → ℝ)
    (horizon : ℕ) :
    ∑ stage ∈ Finset.range horizon, weight stage * summand stage =
      (∑ stage ∈ Finset.range horizon,
          (weight stage - weight (stage + 1)) *
            ∑ earlier ∈ Finset.range (stage + 1), summand earlier) +
        weight horizon * ∑ earlier ∈ Finset.range horizon, summand earlier := by
  induction horizon with
  | zero => simp
  | succ horizon ih =>
      rw [Finset.sum_range_succ (f := fun stage => weight stage * summand stage),
        Finset.sum_range_succ (f := fun stage =>
          (weight stage - weight (stage + 1)) *
            ∑ earlier ∈ Finset.range (stage + 1), summand earlier),
        ih, Finset.sum_range_succ (f := summand) (n := horizon)]
      ring

/-- **Abel's inequality.**  If the weights are antitone and nonnegative and
every partial sum up to the horizon is at most `ε`, then the weighted sum is
at most the initial weight times `ε`. -/
theorem sum_mul_le_initialWeight_mul_of_partialSum_le {weight summand : ℕ → ℝ}
    {ε : ℝ} (horizon : ℕ)
    (hanti : ∀ stage, weight (stage + 1) ≤ weight stage)
    (hlast : 0 ≤ weight horizon)
    (hpartial : ∀ index, index ≤ horizon →
      ∑ earlier ∈ Finset.range index, summand earlier ≤ ε) :
    ∑ stage ∈ Finset.range horizon, weight stage * summand stage ≤
      weight 0 * ε := by
  have hstepBound : ∀ stage ∈ Finset.range horizon,
      (weight stage - weight (stage + 1)) *
          ∑ earlier ∈ Finset.range (stage + 1), summand earlier ≤
        (weight stage - weight (stage + 1)) * ε := by
    intro stage hstage
    exact mul_le_mul_of_nonneg_left
      (hpartial (stage + 1) (Finset.mem_range.mp hstage))
      (sub_nonneg.mpr (hanti stage))
  have hfinal : weight horizon * ∑ earlier ∈ Finset.range horizon, summand earlier ≤
      weight horizon * ε :=
    mul_le_mul_of_nonneg_left (hpartial horizon le_rfl) hlast
  have htelescope :
      ∑ stage ∈ Finset.range horizon, (weight stage - weight (stage + 1)) * ε =
        (weight 0 - weight horizon) * ε := by
    rw [← Finset.sum_mul, Finset.sum_range_sub' weight horizon]
  rw [sum_mul_eq_sum_weightStep_mul_partialSum weight summand horizon]
  have hsum := Finset.sum_le_sum hstepBound
  rw [htelescope] at hsum
  nlinarith [hsum, hfinal]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## (1) The ledger -/

/-- **One stage's continue advantage.**  Simon's `b_n(r_{k+1}(p), p_k) −
r_k^n(p)`: player `who`'s pure-Continue payoff at stage `stage` against the
plan's own stage marginals and its own continuation vector, minus the plan's
own value at that stage.  Both terms are conditional on stage `stage` being
reached live, and the Continue endpoint is the *deleted* object -- `who`'s own
marginal is replaced by pure Continue -- which is the conditioning "on no
other player having quit". -/
def quittingLedgerStageAdvantage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (stage : ℕ) : ℝ :=
  quittingRootContinuePayoff reward
      (quittingRootSequenceTailVector reward roots (stage + 1)) (roots stage) who -
    quittingRootSequenceTerminalValue reward roots who stage

/-- **The deleted normalisation, written out.**  The stage advantage is the
opponents' immediate absorbing contribution plus the *opponent-only* survival
mass times the plan's next value, minus the plan's current value.  The
coefficient is `quittingFixedOpponentsContinueMass`, never the joint mass. -/
theorem quittingLedgerStageAdvantage_eq_fixedOpponents
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (stage : ℕ) :
    quittingLedgerStageAdvantage reward roots who stage =
      quittingFixedOpponentsContinueReward reward roots who stage +
        quittingFixedOpponentsContinueMass roots who stage *
          quittingRootSequenceTerminalValue reward roots who (stage + 1) -
        quittingRootSequenceTerminalValue reward roots who stage := by
  unfold quittingLedgerStageAdvantage
  rw [quittingRootContinuePayoff_eq_fixedOpponents]
  rfl

/-- **Joint versus deleted, in ledger position.**  The joint continue mass
appearing in the survival weights of a global deviation is the deleted mass
of the ledger's summand times `who`'s own continue probability.  This is the
survival-prefix bridge specialised to the stage the ledger reads. -/
theorem quittingLedgerJointContinueMass_eq_own_mul_deleted
    (roots : ℕ → ι → PMF Bool) (who : ι) (stage : ℕ) :
    quittingStationaryContinueMass (roots stage) =
      quittingFixedOpponentsContinueMass roots who stage *
        (roots stage who false).toReal := by
  rw [quittingStationaryContinueMass_eq_deletedContinueMass_mul_own (roots stage) who,
    quittingRootDeletedContinueMass_eq_fixedOpponents]

/-- **The identity the summand lands on.**  The stage advantage is minus
`who`'s own prescribed quit probability times the Quit-minus-Continue
endpoint difference: continuing is worth exactly the mass the plan puts on
quitting times the endpoint gap it gives up. -/
theorem quittingLedgerStageAdvantage_eq_neg_quitProbability_mul_endpointDifference
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (stage : ℕ) :
    quittingLedgerStageAdvantage reward roots who stage =
      -((roots stage who true).toReal *
        quittingRootEndpointDifference reward
          (quittingRootSequenceTailVector reward roots (stage + 1))
          (roots stage) who) := by
  have hsum := quittingRoot_continueProbability_add_quitProbability (roots stage) who
  have hcontinue : (roots stage who false).toReal =
      1 - (roots stage who true).toReal := by linarith
  have hvalue := quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector
    reward roots who stage
  have hmix := quittingRootSuccessorPayoff_eq_endpointMix reward
    (quittingRootSequenceTailVector reward roots (stage + 1)) (roots stage) who
  unfold quittingLedgerStageAdvantage quittingRootEndpointDifference
  rw [hvalue, hmix, hcontinue]
  ring

/-- **Reconciliation with `quittingStageGap`.**  The ledger increment is
*not* the negation of the stage gap: the gap measures the Quit endpoint
against the Continue value, the ledger measures the Continue endpoint against
the plan's own mixture.  Added together at the plan's own prescription they
give the plan's Quit-minus-value regret, which is the exact difference
between the two readings. -/
theorem quittingLedgerStageAdvantage_add_quittingStageGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (stage : ℕ) :
    quittingLedgerStageAdvantage reward roots who stage +
        quittingStageGap reward roots who
          (quittingRootSequenceTerminalValue reward roots who) stage =
      quittingFixedOpponentsQuitValue reward roots who stage -
        quittingRootSequenceTerminalValue reward roots who stage := by
  rw [quittingLedgerStageAdvantage_eq_fixedOpponents, quittingStageGap]
  ring

/-- Under root endpoint `ε`-Nash at the stage, the ledger increment is at
most `ε`: it *is* the pure-Continue regret of the endpoint test. -/
theorem quittingLedgerStageAdvantage_le_of_isεQuittingRootEndpointNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (stage : ℕ) {ε : ℝ}
    (hnash : IsεQuittingRootEndpointNash reward
      (quittingRootSequenceTailVector reward roots (stage + 1)) ε (roots stage)) :
    quittingLedgerStageAdvantage reward roots who stage ≤ ε := by
  rw [quittingLedgerStageAdvantage_eq_neg_quitProbability_mul_endpointDifference]
  linarith [(hnash who).2]

/-- Every ledger increment is bounded by twice the reward bound. -/
theorem abs_quittingLedgerStageAdvantage_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (stage : ℕ)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ S player, |reward S player| ≤ bound) :
    |quittingLedgerStageAdvantage reward roots who stage| ≤ 2 * bound := by
  have htail : ∀ player,
      |quittingRootSequenceTailVector reward roots (stage + 1) player| ≤ bound :=
    fun player => abs_quittingRootSequenceTerminalValue_le reward roots player
      (stage + 1) hbound hreward
  have hcontinue : |quittingRootContinuePayoff reward
      (quittingRootSequenceTailVector reward roots (stage + 1)) (roots stage) who| ≤
      bound :=
    abs_quittingRootExpectedPayoff_le_bound reward _ _ who hreward htail
  have hvalue : |quittingRootSequenceTerminalValue reward roots who stage| ≤ bound :=
    abs_quittingRootSequenceTerminalValue_le reward roots who stage hbound hreward
  unfold quittingLedgerStageAdvantage
  rw [abs_le] at hcontinue hvalue ⊢
  constructor <;> [linarith [hcontinue.1, hvalue.2]; linarith [hcontinue.2, hvalue.1]]

/-- **The ledger.**  `W_i^n`: the cumulative advantage player `who` has
obtained by continuing at every stage before `index`, each stage's advantage
conditioned on that stage being reached live. -/
def quittingLedger
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (index : ℕ) : ℝ :=
  ∑ stage ∈ Finset.range index, quittingLedgerStageAdvantage reward roots who stage

/-- The ledger starts empty. -/
@[simp] theorem quittingLedger_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) :
    quittingLedger reward roots who 0 = 0 := by
  simp [quittingLedger]

/-- The ledger's one-step recursion. -/
theorem quittingLedger_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (index : ℕ) :
    quittingLedger reward roots who (index + 1) =
      quittingLedger reward roots who index +
        quittingLedgerStageAdvantage reward roots who index := by
  simp [quittingLedger, Finset.sum_range_succ]

/-- The ledger grows at most linearly: `|W_i| ≤ i · (2·bound)`. -/
theorem abs_quittingLedger_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (index : ℕ)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ S player, |reward S player| ≤ bound) :
    |quittingLedger reward roots who index| ≤ index * (2 * bound) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum (fun stage _ =>
    abs_quittingLedgerStageAdvantage_le reward roots who stage hbound hreward)).trans ?_
  simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Under root endpoint `ε`-Nash at every stage, the ledger at `index` is at
most `index · ε`. -/
theorem quittingLedger_le_of_isεQuittingRootEndpointNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (index : ℕ) {ε : ℝ}
    (hnash : ∀ stage, IsεQuittingRootEndpointNash reward
      (quittingRootSequenceTailVector reward roots (stage + 1)) ε (roots stage)) :
    quittingLedger reward roots who index ≤ index * ε := by
  refine (Finset.sum_le_sum (fun stage _ =>
    quittingLedgerStageAdvantage_le_of_isεQuittingRootEndpointNash reward roots who
      stage (hnash stage))).trans ?_
  simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ## (2) The two clocks and the combinator -/

/-- **The ledger clock `i^n_∗`.**  The first index at which player `who`'s
ledger has reached `ε`, or `0` if it never does -- the same
`Nat.find`-with-`0`-default convention as
`quittingPlannedSurvivalStoppingIndex`. -/
def quittingLedgerStoppingIndex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (ε : ℝ) : ℕ := by
  classical
  exact
    if hexists : ∃ index, ε ≤ quittingLedger reward roots who index then
      Nat.find hexists
    else 0

/-- At the ledger clock the ledger has indeed reached `ε`. -/
theorem le_quittingLedger_quittingLedgerStoppingIndex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) {ε : ℝ}
    (hexists : ∃ index, ε ≤ quittingLedger reward roots who index) :
    ε ≤ quittingLedger reward roots who
      (quittingLedgerStoppingIndex reward roots who ε) := by
  unfold quittingLedgerStoppingIndex
  rw [dif_pos hexists]
  exact Nat.find_spec hexists

/-- **First crossing, unconditionally.**  Strictly before the ledger clock
the ledger is still below `ε`; when the clock never fires the index is `0`
and the statement is vacuous. -/
theorem quittingLedger_lt_of_lt_quittingLedgerStoppingIndex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) {ε : ℝ} {index : ℕ}
    (hindex : index < quittingLedgerStoppingIndex reward roots who ε) :
    quittingLedger reward roots who index < ε := by
  unfold quittingLedgerStoppingIndex at hindex
  split_ifs at hindex with hexists
  · exact not_le.mp (Nat.find_min hexists hindex)
  · exact absurd hindex (Nat.not_lt_zero index)

/-- Player `who`'s own prescribed hazard sequence, read off a root
sequence. -/
def quittingRootSequenceOwnHazard
    (roots : ℕ → ι → PMF Bool) (who : ι) : ℕ → PMF Bool :=
  fun stage => roots stage who

omit [Fintype ι] [DecidableEq ι] in
/-- The planned survival curve of that hazard is Simon's `c_i^n =
∏_{k<i} (1 − p_k^n)`. -/
theorem quittingHazardSurvival_quittingRootSequenceOwnHazard
    (roots : ℕ → ι → PMF Bool) (who : ι) (cutoff : ℕ) :
    quittingHazardSurvival (quittingRootSequenceOwnHazard roots who) cutoff =
      ∏ stage ∈ Finset.range cutoff, (roots stage who false).toReal := by
  simpa only [quittingRootSequenceOwnHazard] using
    quittingHazardSurvival_eq_prod (quittingRootSequenceOwnHazard roots who) cutoff

/-- **The planned-survival clock `i^n_♯` for a root sequence.**  The landed
index of `QuittingPlannedSurvivalStoppingIndex.lean`, instantiated at the
player's own prescribed hazard; imported as is, with no new content. -/
def quittingRootSequencePlannedSurvivalStoppingIndex
    (roots : ℕ → ι → PMF Bool) (who : ι) (threshold : ℝ) : ℕ :=
  quittingPlannedSurvivalStoppingIndex
    (quittingRootSequenceOwnHazard roots who) threshold

omit [Fintype ι] [DecidableEq ι] in
/-- At the planned-survival clock the player's own prescribed survival is at
or below the threshold. -/
theorem quittingHazardSurvival_quittingRootSequencePlannedSurvivalStoppingIndex_le
    (roots : ℕ → ι → PMF Bool) (who : ι) {threshold : ℝ}
    (hexists : ∃ cutoff,
      quittingHazardSurvival (quittingRootSequenceOwnHazard roots who) cutoff ≤
        threshold) :
    quittingHazardSurvival (quittingRootSequenceOwnHazard roots who)
        (quittingRootSequencePlannedSurvivalStoppingIndex roots who threshold) ≤
      threshold :=
  quittingHazardSurvival_stoppingIndex_le _ threshold hexists

/-- **The switch stage `î`.**  The earliest firing of either clock over all
players: `î = min_n min(i^n_∗, i^n_♯)`. -/
def quittingPunishSwitchIndex [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (ε threshold : ℝ) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty fun who =>
    min (quittingLedgerStoppingIndex reward roots who ε)
      (quittingRootSequencePlannedSurvivalStoppingIndex roots who threshold)

/-- The switch stage is at or before every player's pair of clocks. -/
theorem quittingPunishSwitchIndex_le [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (ε threshold : ℝ) (who : ι) :
    quittingPunishSwitchIndex reward roots ε threshold ≤
      min (quittingLedgerStoppingIndex reward roots who ε)
        (quittingRootSequencePlannedSurvivalStoppingIndex roots who threshold) :=
  Finset.inf'_le _ (Finset.mem_univ who)

/-- **No one has accumulated advantage before the switch.**  For every player
and every stage strictly before `î`, that player's ledger is still below `ε`.
This is what the phase-switch plan-phase cap hypothesis consumes. -/
theorem quittingLedger_lt_of_lt_quittingPunishSwitchIndex [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) {ε threshold : ℝ} (who : ι) {index : ℕ}
    (hindex : index < quittingPunishSwitchIndex reward roots ε threshold) :
    quittingLedger reward roots who index < ε :=
  quittingLedger_lt_of_lt_quittingLedgerStoppingIndex reward roots who
    (lt_of_lt_of_le hindex
      ((quittingPunishSwitchIndex_le reward roots ε threshold who).trans
        (min_le_left _ _)))

/-- **The ledger at the switch, with the one-stage slack.**  Up to and
including `î` every player's ledger is below `ε` plus one stage's advantage:
the clock can only overshoot by a single increment. -/
theorem quittingLedger_le_of_le_quittingPunishSwitchIndex [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) {ε threshold bound : ℝ} (who : ι) {index : ℕ}
    (hbound : 0 ≤ bound) (hε : 0 ≤ ε)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hindex : index ≤ quittingPunishSwitchIndex reward roots ε threshold) :
    quittingLedger reward roots who index ≤ ε + 2 * bound := by
  rcases Nat.eq_zero_or_pos index with hzero | hpos
  · rw [hzero, quittingLedger_zero]
    linarith
  · obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    have hprevious : previous <
        quittingPunishSwitchIndex reward roots ε threshold := by omega
    have hearlier := quittingLedger_lt_of_lt_quittingPunishSwitchIndex
      reward roots who hprevious
    have hstep := abs_quittingLedgerStageAdvantage_le reward roots who previous
      hbound hreward
    rw [abs_le] at hstep
    rw [quittingLedger_succ]
    linarith [hstep.2]

/-- **The punished player `n̂`.**  A player achieving the switch stage,
preferring one whose *planned-survival* clock achieves it, exactly as the
source selects. -/
def quittingPunishTarget [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (ε threshold : ℝ) : ι := by
  classical
  exact
    if hsharp : ∃ who, quittingPunishSwitchIndex reward roots ε threshold =
        quittingRootSequencePlannedSurvivalStoppingIndex roots who threshold then
      hsharp.choose
    else
      (Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := ι)) fun who =>
        min (quittingLedgerStoppingIndex reward roots who ε)
          (quittingRootSequencePlannedSurvivalStoppingIndex roots who
            threshold)).choose

/-- When some player's planned-survival clock achieves the switch stage, the
punish target is such a player: the switch stage *is* the target's `i^n_♯`. -/
theorem quittingPunishSwitchIndex_eq_plannedSurvival_quittingPunishTarget
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (ε threshold : ℝ)
    (hsharp : ∃ who, quittingPunishSwitchIndex reward roots ε threshold =
      quittingRootSequencePlannedSurvivalStoppingIndex roots who threshold) :
    quittingPunishSwitchIndex reward roots ε threshold =
      quittingRootSequencePlannedSurvivalStoppingIndex roots
        (quittingPunishTarget reward roots ε threshold) threshold := by
  classical
  unfold quittingPunishTarget
  rw [dif_pos hsharp]
  exact hsharp.choose_spec

/-- **The punish target achieves the switch stage.**  In either branch the
switch stage is the minimum of the target's own two clocks. -/
theorem quittingPunishSwitchIndex_eq_min_quittingPunishTarget [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (ε threshold : ℝ) :
    quittingPunishSwitchIndex reward roots ε threshold =
      min (quittingLedgerStoppingIndex reward roots
          (quittingPunishTarget reward roots ε threshold) ε)
        (quittingRootSequencePlannedSurvivalStoppingIndex roots
          (quittingPunishTarget reward roots ε threshold) threshold) := by
  classical
  by_cases hsharp : ∃ who, quittingPunishSwitchIndex reward roots ε threshold =
      quittingRootSequencePlannedSurvivalStoppingIndex roots who threshold
  · have hachieved :=
      quittingPunishSwitchIndex_eq_plannedSurvival_quittingPunishTarget
        reward roots ε threshold hsharp
    refine le_antisymm ?_ ?_
    · exact le_min
        ((quittingPunishSwitchIndex_le reward roots ε threshold _).trans
          (min_le_left _ _))
        ((quittingPunishSwitchIndex_le reward roots ε threshold _).trans
          (min_le_right _ _))
    · exact (min_le_right _ _).trans hachieved.ge
  · unfold quittingPunishTarget
    rw [dif_neg hsharp]
    exact (Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := ι)) fun who =>
      min (quittingLedgerStoppingIndex reward roots who ε)
        (quittingRootSequencePlannedSurvivalStoppingIndex roots who
          threshold)).choose_spec.2

/-! ## (3) The feed-in: from the ledger to the plan-phase cap -/

/-- The hazard sequence that continues at every stage: Simon's "repetitive
continuing", the only deviation the ledger has to price. -/
def quittingAlwaysContinueHazard : ℕ → PMF Bool :=
  fun _ => PMF.pure false

/-- Replacing `who`'s own marginal changes no pure-Continue endpoint: the
endpoint already deletes that coordinate. -/
theorem quittingRootContinuePayoff_quittingRootSequenceUpdate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (hazard : ℕ → PMF Bool)
    (tail : Payoff ι) (time : ℕ) :
    quittingRootContinuePayoff reward tail
        (quittingRootSequenceUpdate roots who hazard time) who =
      quittingRootContinuePayoff reward tail (roots time) who := by
  unfold quittingRootContinuePayoff quittingRootSequenceUpdate
  rw [Function.update_idem]

/-- Along the always-Continue deviation the successor payoff *is* the
pure-Continue endpoint: the deviator puts no mass on quitting. -/
theorem quittingRootSuccessorPayoff_quittingRootSequenceUpdate_alwaysContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (tail : Payoff ι) (stage : ℕ) :
    quittingRootSuccessorPayoff reward tail
        (quittingRootSequenceUpdate roots who quittingAlwaysContinueHazard stage)
        who =
      quittingRootContinuePayoff reward tail (roots stage) who := rfl

/-- The always-Continue deviation obeys the scalar deleted recursion: no
absorbing mass of its own, opponents' contribution plus opponent survival
times its own next value. -/
theorem quittingRootSequenceHazardTerminalValue_quittingAlwaysContinueHazard_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (stage : ℕ) :
    quittingRootSequenceHazardTerminalValue reward roots who
        quittingAlwaysContinueHazard stage =
      quittingFixedOpponentsContinueReward reward roots who stage +
        quittingFixedOpponentsContinueMass roots who stage *
          quittingRootSequenceHazardTerminalValue reward roots who
            quittingAlwaysContinueHazard (stage + 1) := by
  rw [quittingRootSequenceHazardTerminalValue,
    quittingRootSequenceTerminalValue_eq_rootSuccessorPayoff,
    quittingRootSuccessorPayoff_quittingRootSequenceUpdate_alwaysContinue,
    quittingRootContinuePayoff_eq_fixedOpponents]
  rfl

/-- **One step of the ledger cash-out.**  The always-Continue deviation's
conditional gain at a stage is that stage's ledger increment plus the
opponent survival mass times its conditional gain one stage later. -/
theorem quittingRootSequenceHazardTerminalValue_quittingAlwaysContinueHazard_sub_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (stage : ℕ) :
    quittingRootSequenceHazardTerminalValue reward roots who
          quittingAlwaysContinueHazard stage -
        quittingRootSequenceTerminalValue reward roots who stage =
      quittingLedgerStageAdvantage reward roots who stage +
        quittingFixedOpponentsContinueMass roots who stage *
          (quittingRootSequenceHazardTerminalValue reward roots who
              quittingAlwaysContinueHazard (stage + 1) -
            quittingRootSequenceTerminalValue reward roots who (stage + 1)) := by
  rw [quittingRootSequenceHazardTerminalValue_quittingAlwaysContinueHazard_succ,
    quittingLedgerStageAdvantage_eq_fixedOpponents]
  ring

/-- **The ledger cash-out.**  The always-Continue deviation's *global* gain
is the opponent-survival-weighted ledger sum over any horizon, plus the
survival at that horizon times the conditional gain from it on. -/
theorem quittingRootSequenceHazardTerminalValue_quittingAlwaysContinueHazard_sub_eq_ledgerSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (horizon : ℕ) :
    quittingRootSequenceHazardTerminalValue reward roots who
          quittingAlwaysContinueHazard 0 -
        quittingRootSequenceTerminalValue reward roots who 0 =
      (∑ stage ∈ Finset.range horizon,
          quittingOpponentSurvivalWeight roots who 0 stage *
            quittingLedgerStageAdvantage reward roots who stage) +
        quittingOpponentSurvivalWeight roots who 0 horizon *
          (quittingRootSequenceHazardTerminalValue reward roots who
              quittingAlwaysContinueHazard horizon -
            quittingRootSequenceTerminalValue reward roots who horizon) := by
  induction horizon with
  | zero => simp [quittingOpponentSurvivalWeight]
  | succ horizon ih =>
      rw [quittingRootSequenceHazardTerminalValue_quittingAlwaysContinueHazard_sub_succ
        reward roots who horizon] at ih
      rw [Finset.sum_range_succ, quittingOpponentSurvivalWeight_succ, Nat.zero_add,
        ih]
      ring

/-- **The plan-phase cap from the ledger.**  If every ledger value up to the
horizon is at most `ε`, the always-Continue deviation gains at most `ε` plus
the opponent survival at the horizon times the payoff range. -/
theorem quittingRootSequenceHazardTerminalValue_quittingAlwaysContinueHazard_le_of_ledger_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (horizon : ℕ)
    {ε bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hledger : ∀ index, index ≤ horizon →
      quittingLedger reward roots who index ≤ ε) :
    quittingRootSequenceHazardTerminalValue reward roots who
        quittingAlwaysContinueHazard 0 ≤
      quittingRootSequenceTerminalValue reward roots who 0 + ε +
        quittingOpponentSurvivalWeight roots who 0 horizon * (2 * bound) := by
  have habel := sum_mul_le_initialWeight_mul_of_partialSum_le
    (weight := quittingOpponentSurvivalWeight roots who 0)
    (summand := quittingLedgerStageAdvantage reward roots who) horizon
    (fun stage => antitone_quittingOpponentSurvivalWeight roots who 0
      (Nat.le_succ stage))
    (quittingOpponentSurvivalWeight_nonneg roots who 0 horizon) hledger
  rw [show quittingOpponentSurvivalWeight roots who 0 0 = 1 by
    simp [quittingOpponentSurvivalWeight], one_mul] at habel
  have hdeviated : |quittingRootSequenceHazardTerminalValue reward roots who
      quittingAlwaysContinueHazard horizon| ≤ bound :=
    abs_quittingRootSequenceTerminalValue_le reward _ who horizon hbound hreward
  have hprescribed : |quittingRootSequenceTerminalValue reward roots who horizon| ≤
      bound :=
    abs_quittingRootSequenceTerminalValue_le reward roots who horizon hbound hreward
  have htail : quittingOpponentSurvivalWeight roots who 0 horizon *
      (quittingRootSequenceHazardTerminalValue reward roots who
          quittingAlwaysContinueHazard horizon -
        quittingRootSequenceTerminalValue reward roots who horizon) ≤
      quittingOpponentSurvivalWeight roots who 0 horizon * (2 * bound) := by
    refine mul_le_mul_of_nonneg_left ?_
      (quittingOpponentSurvivalWeight_nonneg roots who 0 horizon)
    rw [abs_le] at hdeviated hprescribed
    linarith [hdeviated.2, hprescribed.1]
  have hidentity :=
    quittingRootSequenceHazardTerminalValue_quittingAlwaysContinueHazard_sub_eq_ledgerSum
      reward roots who horizon
  linarith [hidentity, habel, htail]

/-- **The feed-in, with its honest residual.**  Assume the ledger cap up to
the horizon and assume `hdominate`: every hazard deviation is beaten by
always continuing up to `quitSlack`.  Then *every* hazard deviation is capped
in exactly the shape hypothesis (a) of
`quittingTerminalPayoff_update_quittingPhaseSwitchProfile_le` demands.

`hdominate` is the inequality that remains: it is Simon's "the only deviation
to consider is repetitive continuing", whose proof is the rank-1
decision-discrepancy-process argument of Propositions 1-2, deliberately not
built here. -/
theorem quittingRootSequenceHazardTerminalValue_le_of_ledger_le_of_dominated
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (horizon : ℕ)
    {ε quitSlack bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hledger : ∀ index, index ≤ horizon →
      quittingLedger reward roots who index ≤ ε)
    (hdominate : ∀ hazard : ℕ → PMF Bool,
      quittingRootSequenceHazardTerminalValue reward roots who hazard 0 ≤
        quittingRootSequenceHazardTerminalValue reward roots who
          quittingAlwaysContinueHazard 0 + quitSlack)
    (hazard : ℕ → PMF Bool) :
    quittingRootSequenceHazardTerminalValue reward roots who hazard 0 ≤
      quittingRootSequenceTerminalValue reward roots who 0 +
        (ε + quitSlack +
          quittingOpponentSurvivalWeight roots who 0 horizon * (2 * bound)) := by
  have hcontinue :=
    quittingRootSequenceHazardTerminalValue_quittingAlwaysContinueHazard_le_of_ledger_le
      reward roots who horizon hbound hreward hledger
  linarith [hdominate hazard, hcontinue]

/-! ## The truncated plan: the residual term vanishes -/

omit [Fintype ι] in
/-- Deviating by always continuing against the truncated plan leaves the
all-Continue suffix untouched. -/
theorem quittingRootSequenceUpdate_quittingTruncatedRoots_alwaysContinue_of_le
    (plan : ℕ → ι → PMF Bool) (who : ι) (cutoff time : ℕ) (htime : cutoff ≤ time) :
    quittingRootSequenceUpdate (quittingTruncatedRoots plan cutoff) who
        quittingAlwaysContinueHazard time =
      (quittingAllContinueRoot : ι → PMF Bool) := by
  rw [quittingRootSequenceUpdate, quittingTruncatedRoots_of_le plan htime]
  exact Function.update_eq_self who (quittingAllContinueRoot : ι → PMF Bool)

/-- From the cutoff on, both the truncated plan and its always-Continue
deviation have value zero, so the cash-out's remainder term vanishes. -/
theorem quittingRootSequenceHazardTerminalValue_quittingTruncatedRoots_alwaysContinue_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan : ℕ → ι → PMF Bool) (who : ι) (cutoff : ℕ) :
    quittingRootSequenceHazardTerminalValue reward
        (quittingTruncatedRoots plan cutoff) who quittingAlwaysContinueHazard
        cutoff = 0 :=
  quittingRootSequenceTerminalValue_eq_zero_of_allContinue_from reward _ who cutoff
    fun time htime =>
      quittingRootSequenceUpdate_quittingTruncatedRoots_alwaysContinue_of_le plan
        who cutoff time htime

omit [DecidableEq ι] in
/-- The truncated plan's own value from the cutoff on is zero. -/
theorem quittingRootSequenceTerminalValue_quittingTruncatedRoots_cutoff_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan : ℕ → ι → PMF Bool) (who : ι) (cutoff : ℕ) :
    quittingRootSequenceTerminalValue reward (quittingTruncatedRoots plan cutoff)
        who cutoff = 0 :=
  quittingRootSequenceTerminalValue_eq_zero_of_allContinue_from reward _ who cutoff
    fun _ htime => quittingTruncatedRoots_of_le plan htime

/-- **Hypothesis (a) as a ledger condition.**  Against the truncated plan the
remainder of the cash-out vanishes, so the ledger cap over `[0, cutoff]` plus
the dominance residual is literally the plan-phase hypothesis of
`quittingTerminalPayoff_update_quittingPhaseSwitchProfile_le`, with
`planError = ε + quitSlack`. -/
theorem quittingRootSequenceHazardTerminalValue_quittingTruncatedRoots_le_of_ledger_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan : ℕ → ι → PMF Bool) (who : ι) (cutoff : ℕ)
    {ε quitSlack : ℝ}
    (hledger : ∀ index, index ≤ cutoff →
      quittingLedger reward (quittingTruncatedRoots plan cutoff) who index ≤ ε)
    (hdominate : ∀ hazard : ℕ → PMF Bool,
      quittingRootSequenceHazardTerminalValue reward
          (quittingTruncatedRoots plan cutoff) who hazard 0 ≤
        quittingRootSequenceHazardTerminalValue reward
          (quittingTruncatedRoots plan cutoff) who quittingAlwaysContinueHazard 0 +
          quitSlack)
    (hazard : ℕ → PMF Bool) :
    quittingRootSequenceHazardTerminalValue reward
        (quittingTruncatedRoots plan cutoff) who hazard 0 ≤
      quittingRootSequenceTerminalValue reward
          (quittingTruncatedRoots plan cutoff) who 0 + (ε + quitSlack) := by
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
  linarith [hdominate hazard, hidentity, habel]

/-- **The assembled cap, with the plan phase discharged by the ledger.**  The
phase-switch deviation cap with hypothesis (a) replaced by the ledger
condition on the truncated plan.  Hypotheses (b) and (c) are unchanged, and
`hdominate` is the residual named above. -/
theorem quittingTerminalPayoff_update_quittingPhaseSwitchProfile_le_of_ledger_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan punish : ℕ → ι → PMF Bool) (switch : ℕ) (who : ι)
    {ε quitSlack punishError punishCap survivalCap bound : ℝ}
    (hbound : 0 ≤ bound)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hledger : ∀ index, index ≤ switch →
      quittingLedger reward (quittingTruncatedRoots plan switch) who index ≤ ε)
    (hdominate : ∀ hazard : ℕ → PMF Bool,
      quittingRootSequenceHazardTerminalValue reward
          (quittingTruncatedRoots plan switch) who hazard 0 ≤
        quittingRootSequenceHazardTerminalValue reward
          (quittingTruncatedRoots plan switch) who quittingAlwaysContinueHazard 0 +
          quitSlack)
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
        (ε + quitSlack) +
        survivalCap * (max (punishCap + punishError) 0 + bound) :=
  quittingTerminalPayoff_update_quittingPhaseSwitchProfile_le reward plan punish
    switch who hbound hreward
    (quittingRootSequenceHazardTerminalValue_quittingTruncatedRoots_le_of_ledger_le
      reward plan who switch hledger hdominate)
    hpunish hsurvival deviation

end GameTheory
