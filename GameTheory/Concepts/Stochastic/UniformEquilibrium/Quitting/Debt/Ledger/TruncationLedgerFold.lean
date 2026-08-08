/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Paths.LiveChainDominationCap

/-!
# Folding the truncation correction into the plan phase

`QuittingPhaseSwitchResiduals.lean` records, but does not prove, the shape of
the discrepancy between a plan and its truncation at a cutoff: the value
curves differ, at *every* index up to the cutoff, by the joint survival from
that index to the cutoff times the discarded continuation value.  This file
proves that transfer and folds it into the one place it is consumed.

## The transfer, exactly

`quittingRootSequenceTerminalValue_quittingTruncatedRoots_eq_sub`:

`Ṽ_i = V_i − S(i, gap) · V_{i+gap}`,

with `S(i, gap)` the plan's own joint survival over the window.  The ledger
increment therefore transfers with an explicit correction
(`quittingLedgerStageAdvantage_quittingTruncatedRoots_eq_sub`):

`d̃_k = d_k − V_switch · (s_k · p_k · S(k+1, gap))`,

`s_k` the opponent-only continue mass and `p_k` the player's own prescribed
quit probability -- and summing gives the ledger transfer
`quittingLedger_quittingTruncatedRoots_eq_sub`.

## Why the raw ledger is the wrong place to fold

The correction sum is *not* small.  Each summand is a product of
probabilities, but the sum telescopes to roughly `1 − ∏_k (1 − p_k)`, so the
truncated ledger can exceed the plan's by the whole payoff range even when
the plan phase is reached with tiny probability.  The reason is that the
ledger is an *unweighted* sum of conditional advantages, and the correction
is concentrated at the late stages, which are reached with vanishing
probability.

What the assembly consumes is not the ledger but the plan-phase deviation
cap, which weighs each stage by the reach probability.  So the fold is done
one level up, on the values themselves: every deviation against the truncated
plan is a deviation against the plan, corrected by the reach probability
times a payoff-range term.  Concretely, for the three shapes the pure-time
reduction leaves:

* the always-Continue deviation and the plan's own value differ from their
  truncated counterparts by `reach ·(payoff range)` each;
* a quit date strictly before the cutoff gives *equal* values against the
  plan and against its truncation -- the deviated joint survival through the
  cutoff is zero, so the truncation removes nothing;
* a quit date at or past the cutoff is the always-Continue deviation plus one
  further reach-weighted term.

`quittingRootSequenceHazardTerminalValue_quittingTruncatedRoots_le_of_plan_ledger_le`
assembles them: the clock's bound on the *plan's* ledger, a quit-regret bound
before the cutoff, and a reach bound at the cutoff give hypothesis (a) with
error `ε + δ + reach · (5 · bound)`.

## Where the reach bound comes from, and where it does not

The reach bound `quittingOpponentSurvivalWeight plan who 0 switch ≤ reach` is
supplied in Simon's Case 2 by
`quittingOpponentSurvivalWeight_le_of_target_plannedSurvivalStoppingIndex`
(`QuittingPhaseSwitchResiduals.lean`): the punished player's own
planned-survival clock has crossed the threshold there, and that player is
one factor of every other player's opponent-survival product.

In Case 1 -- the switch achieved by a ledger clock rather than a survival
clock -- no such bound is available, and it stays an explicit hypothesis of
every theorem below.  Supplying it is the rank-one crossing-probability
estimate: its abstract layer is the one-sided decision-variation maximal
inequality of `Math/Probability/DecisionVariationMaximalInequality.lean`, but
the excursion infrastructure that would instantiate it -- the
decision-discrepancy process of a quitting plan, its excursions, and their
crossing counts -- does not exist in this repository, so no theorem here
claims it.

## Main results

* `quittingRootSequenceTerminalValue_quittingTruncatedRoots_eq_sub` -- the
  value transfer, with the correction explicit
* `quittingLedgerStageAdvantage_quittingTruncatedRoots_eq_sub`,
  `quittingLedger_quittingTruncatedRoots_eq_sub` -- the ledger transfer
* `quittingRootSequenceHazardTerminalValue_quittingTruncatedRoots_le_of_plan_ledger_le`
  -- hypothesis (a) from the plan's ledger and the reach bound
* `quittingTerminalPayoff_update_quittingPhaseSwitchProfile_le_of_plan_ledger_le`
  -- the assembled cap, fed entirely by quantities the clocks bound
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The value transfer -/

omit [DecidableEq ι] in
/-- **The truncation correction, exactly.**  Read at an index inside the plan
phase, the truncated plan's value is the plan's own value less the joint
survival from that index to the cutoff times the continuation value the
truncation discards.  The discrepancy back-propagates geometrically through
the whole prefix; it is not localised at the cutoff. -/
theorem quittingRootSequenceTerminalValue_quittingTruncatedRoots_eq_sub
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan : ℕ → ι → PMF Bool) (who : ι) (index gap : ℕ) :
    quittingRootSequenceTerminalValue reward
        (quittingTruncatedRoots plan (index + gap)) who index =
      quittingRootSequenceTerminalValue reward plan who index -
        quittingJointSurvivalWeight plan index gap *
          quittingRootSequenceTerminalValue reward plan who (index + gap) := by
  have hshift : (fun time => quittingTruncatedRoots plan (index + gap) (index + time)) =
      quittingTruncatedRoots (fun time => plan (index + time)) gap := by
    funext time
    by_cases htime : time < gap
    · rw [quittingTruncatedRoots_of_lt (fun t => plan (index + t)) htime,
        quittingTruncatedRoots_of_lt plan (show index + time < index + gap by omega)]
    · rw [quittingTruncatedRoots_of_le (fun t => plan (index + t)) (Nat.not_lt.mp htime),
        quittingTruncatedRoots_of_le plan (show index + gap ≤ index + time by omega)]
  have hdecomp := quittingRootSequenceTerminalValue_eq_truncated_add_jointSurvival_mul
    reward (fun time => plan (index + time)) who gap
  have hstart : quittingRootSequenceTerminalValue reward
      (quittingTruncatedRoots plan (index + gap)) who index =
      quittingRootSequenceTerminalValue reward
        (quittingTruncatedRoots (fun time => plan (index + time)) gap) who 0 := by
    rw [quittingRootSequenceTerminalValue_eq_shift reward
      (quittingTruncatedRoots plan (index + gap)) who index, hshift]
  have hplan : quittingRootSequenceTerminalValue reward plan who index =
      quittingRootSequenceTerminalValue reward (fun time => plan (index + time)) who 0 :=
    quittingRootSequenceTerminalValue_eq_shift reward plan who index
  have hsurvival : quittingJointSurvivalWeight plan index gap =
      quittingJointSurvivalWeight (fun time => plan (index + time)) 0 gap :=
    quittingJointSurvivalWeight_eq_shift plan index gap
  have hend : quittingRootSequenceTerminalValue reward
      (fun time => plan (index + time)) who gap =
      quittingRootSequenceTerminalValue reward plan who (index + gap) := by
    rw [quittingRootSequenceTerminalValue_eq_shift reward
        (fun time => plan (index + time)) who gap,
      quittingRootSequenceTerminalValue_eq_shift reward plan who (index + gap)]
    congr 1
    funext time
    rw [Nat.add_assoc]
  rw [hstart, hplan, hsurvival, ← hend]
  linarith [hdecomp]

/-! ## The ledger transfer -/

/-- **The ledger increment transfers with an explicit correction.**  Inside
the plan phase, the truncated plan's stage advantage is the plan's own less
the discarded continuation value weighted by the opponent-only continue mass,
the player's own prescribed quit probability, and the joint survival from the
next stage to the cutoff. -/
theorem quittingLedgerStageAdvantage_quittingTruncatedRoots_eq_sub
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan : ℕ → ι → PMF Bool) (who : ι) (stage gap : ℕ) :
    quittingLedgerStageAdvantage reward
        (quittingTruncatedRoots plan (stage + 1 + gap)) who stage =
      quittingLedgerStageAdvantage reward plan who stage -
        quittingRootSequenceTerminalValue reward plan who (stage + 1 + gap) *
          (quittingFixedOpponentsContinueMass plan who stage *
            ((plan stage who true).toReal *
              quittingJointSurvivalWeight plan (stage + 1) gap)) := by
  have hroot : quittingTruncatedRoots plan (stage + 1 + gap) stage = plan stage :=
    quittingTruncatedRoots_of_lt plan (by omega)
  have hcontribution : quittingFixedOpponentsContinueReward reward
      (quittingTruncatedRoots plan (stage + 1 + gap)) who stage =
      quittingFixedOpponentsContinueReward reward plan who stage := by
    unfold quittingFixedOpponentsContinueReward
    rw [hroot]
  have hmass : quittingFixedOpponentsContinueMass
      (quittingTruncatedRoots plan (stage + 1 + gap)) who stage =
      quittingFixedOpponentsContinueMass plan who stage := by
    unfold quittingFixedOpponentsContinueMass
    rw [hroot]
  have hnext := quittingRootSequenceTerminalValue_quittingTruncatedRoots_eq_sub
    reward plan who (stage + 1) gap
  have hcurrent := quittingRootSequenceTerminalValue_quittingTruncatedRoots_eq_sub
    reward plan who stage (gap + 1)
  have hindex : stage + (gap + 1) = stage + 1 + gap := by omega
  rw [hindex] at hcurrent
  have hsplit : quittingJointSurvivalWeight plan stage (gap + 1) =
      quittingStationaryContinueMass (plan stage) *
        quittingJointSurvivalWeight plan (stage + 1) gap := by
    have hadd := quittingJointSurvivalWeight_add plan stage 1 gap
    rw [show (1 : ℕ) + gap = gap + 1 by omega] at hadd
    rw [hadd, quittingJointSurvivalWeight_succ plan stage 0,
      quittingJointSurvivalWeight_zero_fuel plan stage]
    ring_nf
  rw [hsplit] at hcurrent
  have hown := quittingLedgerJointContinueMass_eq_own_mul_deleted plan who stage
  rw [hown] at hcurrent
  have hsum := quittingRoot_continueProbability_add_quitProbability (plan stage) who
  rw [quittingLedgerStageAdvantage_eq_fixedOpponents,
    quittingLedgerStageAdvantage_eq_fixedOpponents, hcontribution, hmass, hnext, hcurrent]
  linear_combination (quittingFixedOpponentsContinueMass plan who stage *
    quittingJointSurvivalWeight plan (stage + 1) gap *
    quittingRootSequenceTerminalValue reward plan who (stage + 1 + gap)) * hsum

/-- **The ledger transfer.**  Up to the cutoff, the truncated plan's ledger is
the plan's own less the discarded continuation value times an explicit
survival-weighted sum of the player's own quit probabilities.  The correction
is a genuine sum, not a single boundary term: this is the geometric
back-propagation. -/
theorem quittingLedger_quittingTruncatedRoots_eq_sub
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan : ℕ → ι → PMF Bool) (who : ι) (cutoff index : ℕ) (hindex : index ≤ cutoff) :
    quittingLedger reward (quittingTruncatedRoots plan cutoff) who index =
      quittingLedger reward plan who index -
        quittingRootSequenceTerminalValue reward plan who cutoff *
          ∑ stage ∈ Finset.range index,
            quittingFixedOpponentsContinueMass plan who stage *
              ((plan stage who true).toReal *
                quittingJointSurvivalWeight plan (stage + 1) (cutoff - (stage + 1))) := by
  rw [quittingLedger, quittingLedger, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun stage hstage => ?_
  have hlt : stage < index := Finset.mem_range.mp hstage
  have hgap : stage + 1 + (cutoff - (stage + 1)) = cutoff := by omega
  have htransfer := quittingLedgerStageAdvantage_quittingTruncatedRoots_eq_sub
    reward plan who stage (cutoff - (stage + 1))
  rw [hgap] at htransfer
  exact htransfer

/-! ## Survival products of the two pure deviation shapes -/

/-- Deviating by always continuing makes the joint survival the opponents'
own survival: the deviator removes no mass. -/
theorem quittingJointSurvivalWeight_quittingRootSequenceUpdate_alwaysContinue
    (roots : ℕ → ι → PMF Bool) (who : ι) (start fuel : ℕ) :
    quittingJointSurvivalWeight
        (quittingRootSequenceUpdate roots who quittingAlwaysContinueHazard) start fuel =
      quittingOpponentSurvivalWeight roots who start fuel := by
  rw [quittingJointSurvivalWeight_eq_prod]
  unfold quittingOpponentSurvivalWeight
  exact Finset.prod_congr rfl fun _ _ => rfl

/-- A deviation that quits surely inside the window kills the joint survival
across it. -/
theorem quittingJointSurvivalWeight_quittingRootSequenceUpdate_pureTime_eq_zero
    (roots : ℕ → ι → PMF Bool) (who : ι) {quitTime fuel : ℕ} (hquit : quitTime < fuel) :
    quittingJointSurvivalWeight
        (quittingRootSequenceUpdate roots who (quittingPureTimeHazard (some quitTime)))
        0 fuel = 0 := by
  rw [quittingJointSurvivalWeight_eq_prod]
  refine Finset.prod_eq_zero (Finset.mem_range.mpr hquit) ?_
  rw [Nat.zero_add, quittingRootSequenceUpdate, quittingPureTimeHazard_some_self,
    quittingStationaryContinueMass_eq_prod_continueProbability]
  exact Finset.prod_eq_zero (Finset.mem_univ who) (by simp)

/-! ## The three deviation shapes against the truncated plan -/

/-- **The always-Continue deviation transfers by one reach-weighted term.** -/
theorem quittingRootSequenceHazardTerminalValue_quittingTruncatedRoots_alwaysContinue_eq_sub
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan : ℕ → ι → PMF Bool) (who : ι) (cutoff : ℕ) :
    quittingRootSequenceHazardTerminalValue reward
        (quittingTruncatedRoots plan cutoff) who quittingAlwaysContinueHazard 0 =
      quittingRootSequenceHazardTerminalValue reward plan who
          quittingAlwaysContinueHazard 0 -
        quittingOpponentSurvivalWeight plan who 0 cutoff *
          quittingRootSequenceTerminalValue reward
            (quittingRootSequenceUpdate plan who quittingAlwaysContinueHazard) who cutoff := by
  have htruncated : quittingTruncatedHazard quittingAlwaysContinueHazard cutoff =
      quittingAlwaysContinueHazard := by
    funext time
    by_cases htime : time < cutoff
    · rw [quittingTruncatedHazard_of_lt _ htime]
    · rw [quittingTruncatedHazard_of_le _ (Nat.not_lt.mp htime)]
      rfl
  have hupdate := quittingRootSequenceUpdate_quittingTruncatedRoots plan who
    quittingAlwaysContinueHazard cutoff
  rw [htruncated] at hupdate
  have hdecomp := quittingRootSequenceTerminalValue_eq_truncated_add_jointSurvival_mul
    reward (quittingRootSequenceUpdate plan who quittingAlwaysContinueHazard) who cutoff
  rw [← hupdate, quittingJointSurvivalWeight_quittingRootSequenceUpdate_alwaysContinue]
    at hdecomp
  rw [quittingRootSequenceHazardTerminalValue, quittingRootSequenceHazardTerminalValue]
  linarith [hdecomp]

/-- **A quit date strictly before the cutoff sees no truncation at all.**  The
deviated sequence absorbs surely before the cutoff, so the joint survival the
truncation would discard is zero and the two values coincide exactly. -/
theorem quittingRootSequencePureTimeTerminalValue_quittingTruncatedRoots_of_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan : ℕ → ι → PMF Bool) (who : ι) {cutoff quitTime : ℕ} (hquit : quitTime < cutoff) :
    quittingRootSequencePureTimeTerminalValue reward
        (quittingTruncatedRoots plan cutoff) who (some quitTime) 0 =
      quittingRootSequencePureTimeTerminalValue reward plan who (some quitTime) 0 := by
  have htruncated : quittingTruncatedHazard (quittingPureTimeHazard (some quitTime)) cutoff =
      quittingPureTimeHazard (some quitTime) := by
    funext time
    by_cases htime : time < cutoff
    · rw [quittingTruncatedHazard_of_lt _ htime]
    · rw [quittingTruncatedHazard_of_le _ (Nat.not_lt.mp htime),
        quittingPureTimeHazard_some_of_ne (show time ≠ quitTime by omega)]
  have hupdate := quittingRootSequenceUpdate_quittingTruncatedRoots plan who
    (quittingPureTimeHazard (some quitTime)) cutoff
  rw [htruncated] at hupdate
  have hdecomp := quittingRootSequenceTerminalValue_eq_truncated_add_jointSurvival_mul
    reward (quittingRootSequenceUpdate plan who (quittingPureTimeHazard (some quitTime)))
    who cutoff
  rw [← hupdate,
    quittingJointSurvivalWeight_quittingRootSequenceUpdate_pureTime_eq_zero plan who hquit,
    zero_mul, add_zero] at hdecomp
  rw [quittingRootSequencePureTimeTerminalValue, quittingRootSequencePureTimeTerminalValue,
    quittingRootSequenceHazardTerminalValue, quittingRootSequenceHazardTerminalValue]
  exact hdecomp.symm

/-- **A quit date at or past the cutoff is the always-Continue deviation plus
one reach-weighted term.**  Before the cutoff such a deviation continues, so
its truncation is the always-Continue one; the whole of its quitting happens
inside the reach-weighted tail. -/
theorem quittingRootSequencePureTimeTerminalValue_quittingTruncatedRoots_of_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan : ℕ → ι → PMF Bool) (who : ι) {cutoff quitTime : ℕ} (hquit : cutoff ≤ quitTime) :
    quittingRootSequencePureTimeTerminalValue reward
        (quittingTruncatedRoots plan cutoff) who (some quitTime) 0 =
      quittingRootSequenceHazardTerminalValue reward
          (quittingTruncatedRoots plan cutoff) who quittingAlwaysContinueHazard 0 +
        quittingOpponentSurvivalWeight plan who 0 cutoff *
          quittingRootSequenceTerminalValue reward
            (quittingRootSequenceUpdate (quittingTruncatedRoots plan cutoff) who
              (quittingPureTimeHazard (some quitTime))) who cutoff := by
  have hprefix : ∀ time, time < cutoff →
      quittingRootSequenceUpdate (quittingTruncatedRoots plan cutoff) who
          (quittingPureTimeHazard (some quitTime)) time =
        quittingRootSequenceUpdate (quittingTruncatedRoots plan cutoff) who
          quittingAlwaysContinueHazard time := by
    intro time htime
    rw [quittingRootSequenceUpdate, quittingRootSequenceUpdate,
      quittingPureTimeHazard_some_of_ne (show time ≠ quitTime by omega)]
    rfl
  have htruncated : quittingTruncatedRoots
      (quittingRootSequenceUpdate (quittingTruncatedRoots plan cutoff) who
        (quittingPureTimeHazard (some quitTime))) cutoff =
      quittingRootSequenceUpdate (quittingTruncatedRoots plan cutoff) who
        quittingAlwaysContinueHazard := by
    funext time
    by_cases htime : time < cutoff
    · rw [quittingTruncatedRoots_of_lt _ htime]
      exact hprefix time htime
    · rw [quittingTruncatedRoots_of_le _ (Nat.not_lt.mp htime), quittingRootSequenceUpdate,
        quittingTruncatedRoots_of_le plan (Nat.not_lt.mp htime)]
      exact (Function.update_eq_self who (quittingAllContinueRoot : ι → PMF Bool)).symm
  have hsurvival : quittingJointSurvivalWeight
      (quittingRootSequenceUpdate (quittingTruncatedRoots plan cutoff) who
        (quittingPureTimeHazard (some quitTime))) 0 cutoff =
      quittingOpponentSurvivalWeight plan who 0 cutoff := by
    rw [quittingJointSurvivalWeight_eq_prod]
    unfold quittingOpponentSurvivalWeight quittingFixedOpponentsContinueMass
    refine Finset.prod_congr rfl fun offset hoffset => ?_
    have hlt : offset < cutoff := Finset.mem_range.mp hoffset
    rw [Nat.zero_add, quittingRootSequenceUpdate,
      quittingPureTimeHazard_some_of_ne (show offset ≠ quitTime by omega),
      quittingTruncatedRoots_of_lt plan hlt]
  have hdecomp := quittingRootSequenceTerminalValue_eq_truncated_add_jointSurvival_mul
    reward (quittingRootSequenceUpdate (quittingTruncatedRoots plan cutoff) who
      (quittingPureTimeHazard (some quitTime))) who cutoff
  rw [htruncated, hsurvival] at hdecomp
  rw [quittingRootSequencePureTimeTerminalValue, quittingRootSequenceHazardTerminalValue,
    quittingRootSequenceHazardTerminalValue]
  exact hdecomp

/-! ## The folded plan-phase cap -/

/-- **Hypothesis (a) from the plan's own ledger.**  The clock bounds the
*plan's* ledger, not the truncated plan's; folding the truncation correction
into the reach probability turns that bound into the plan-phase hypothesis of
`quittingTerminalPayoff_update_quittingPhaseSwitchProfile_le`, at the cost of
`reach · (5 · bound)`.

The three hypotheses are exactly the three quantities the clocks and the
survival wiring produce: the ledger cap up to the switch, the quit regret
before it, and the reach probability at it.  The last is Case 2's; in Case 1
it is the open crossing estimate and stays a hypothesis here. -/
theorem quittingRootSequenceHazardTerminalValue_quittingTruncatedRoots_le_of_plan_ledger_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan : ℕ → ι → PMF Bool) (who : ι) (cutoff : ℕ)
    {ε δ reach bound : ℝ} (hbound : 0 ≤ bound) (hδ : 0 ≤ δ)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hledger : ∀ index, index ≤ cutoff → quittingLedger reward plan who index ≤ ε)
    (hregret : ∀ stage, stage < cutoff →
      quittingLedgerQuitRegret reward plan who stage ≤ δ)
    (hreach : quittingOpponentSurvivalWeight plan who 0 cutoff ≤ reach)
    (hazard : ℕ → PMF Bool) :
    quittingRootSequenceHazardTerminalValue reward
        (quittingTruncatedRoots plan cutoff) who hazard 0 ≤
      quittingRootSequenceTerminalValue reward (quittingTruncatedRoots plan cutoff) who 0 +
        (ε + δ + reach * (5 * bound)) := by
  set survival := quittingOpponentSurvivalWeight plan who 0 cutoff with hsurvivalDef
  set truncatedValue := quittingRootSequenceTerminalValue reward
    (quittingTruncatedRoots plan cutoff) who 0 with htruncatedValue
  have hsurvivalNonneg : 0 ≤ survival :=
    quittingOpponentSurvivalWeight_nonneg plan who 0 cutoff
  have hslackScale : 5 * (survival * bound) ≤ reach * (5 * bound) := by
    nlinarith [mul_nonneg hbound (sub_nonneg.mpr hreach)]
  -- The plan's own value against the truncated plan's.
  have hjoint : quittingJointSurvivalWeight plan 0 cutoff ≤ survival :=
    quittingJointSurvivalWeight_le_quittingOpponentSurvivalWeight plan who 0 cutoff
  have hjointNonneg := quittingJointSurvivalWeight_nonneg plan 0 cutoff
  have hcutoffValue : |quittingRootSequenceTerminalValue reward plan who cutoff| ≤ bound :=
    abs_quittingRootSequenceTerminalValue_le reward plan who cutoff hbound hreward
  have hplanValue : quittingRootSequenceTerminalValue reward plan who 0 ≤
      truncatedValue + survival * bound := by
    have hdecomp := quittingRootSequenceTerminalValue_eq_truncated_add_jointSurvival_mul
      reward plan who cutoff
    rw [abs_le] at hcutoffValue
    have h1 : quittingJointSurvivalWeight plan 0 cutoff *
        quittingRootSequenceTerminalValue reward plan who cutoff ≤
        quittingJointSurvivalWeight plan 0 cutoff * bound :=
      mul_le_mul_of_nonneg_left hcutoffValue.2 hjointNonneg
    have h2 : quittingJointSurvivalWeight plan 0 cutoff * bound ≤ survival * bound :=
      mul_le_mul_of_nonneg_right hjoint hbound
    rw [htruncatedValue]
    linarith [hdecomp]
  -- The always-Continue branch.
  have halwaysContinue : quittingRootSequenceHazardTerminalValue reward
      (quittingTruncatedRoots plan cutoff) who quittingAlwaysContinueHazard 0 ≤
      truncatedValue + (ε + 4 * (survival * bound)) := by
    have hplanCap :=
      quittingRootSequenceHazardTerminalValue_quittingAlwaysContinueHazard_le_of_ledger_le
        reward plan who cutoff hbound hreward hledger
    have hidentity :=
      quittingRootSequenceHazardTerminalValue_quittingTruncatedRoots_alwaysContinue_eq_sub
        reward plan who cutoff
    have hdeviated : |quittingRootSequenceTerminalValue reward
        (quittingRootSequenceUpdate plan who quittingAlwaysContinueHazard) who cutoff| ≤
        bound :=
      abs_quittingRootSequenceTerminalValue_le reward _ who cutoff hbound hreward
    rw [abs_le] at hdeviated
    have hcorrection : -(survival * quittingRootSequenceTerminalValue reward
        (quittingRootSequenceUpdate plan who quittingAlwaysContinueHazard) who cutoff) ≤
        survival * bound := by
      nlinarith [hdeviated.1]
    have hexpand : survival * (2 * bound) = 2 * (survival * bound) := by ring
    rw [hexpand] at hplanCap
    linarith [hidentity, hplanCap, hplanValue, hcorrection]
  -- The late-quit branch.
  have hlate : ∀ quitTime : ℕ, cutoff ≤ quitTime →
      quittingRootSequencePureTimeTerminalValue reward
          (quittingTruncatedRoots plan cutoff) who (some quitTime) 0 ≤
        truncatedValue + (ε + 5 * (survival * bound)) := by
    intro quitTime hquitTime
    have hidentity := quittingRootSequencePureTimeTerminalValue_quittingTruncatedRoots_of_le
      reward plan who hquitTime
    have htail : |quittingRootSequenceTerminalValue reward
        (quittingRootSequenceUpdate (quittingTruncatedRoots plan cutoff) who
          (quittingPureTimeHazard (some quitTime))) who cutoff| ≤ bound :=
      abs_quittingRootSequenceTerminalValue_le reward _ who cutoff hbound hreward
    rw [abs_le] at htail
    have hcorrection : survival * quittingRootSequenceTerminalValue reward
        (quittingRootSequenceUpdate (quittingTruncatedRoots plan cutoff) who
          (quittingPureTimeHazard (some quitTime))) who cutoff ≤ survival * bound :=
      mul_le_mul_of_nonneg_left htail.2 hsurvivalNonneg
    linarith [hidentity, halwaysContinue, hcorrection]
  -- The early-quit branch.
  have hearly : ∀ quitTime : ℕ, quitTime < cutoff →
      quittingRootSequencePureTimeTerminalValue reward
          (quittingTruncatedRoots plan cutoff) who (some quitTime) 0 ≤
        truncatedValue + (ε + δ + survival * bound) := by
    intro quitTime hquitTime
    have hidentity := quittingRootSequencePureTimeTerminalValue_quittingTruncatedRoots_of_lt
      reward plan who hquitTime
    have hplanCap := quittingRootSequencePureTimeTerminalValue_some_le_of_ledger_le
      reward plan who quitTime hδ
      (fun index hindex => hledger index (le_trans hindex hquitTime.le))
      (hregret quitTime hquitTime)
    linarith [hidentity, hplanCap, hplanValue]
  -- The reduction to the pure shapes.
  refine le_of_forall_pos_le_add fun slack hslack => ?_
  obtain ⟨quitTime, hquitTime⟩ := exists_quittingRootSequencePureTimeTerminalValue_ge_sub
    reward (quittingTruncatedRoots plan cutoff) who hazard hslack
  cases quitTime with
  | none =>
      rw [quittingRootSequencePureTimeTerminalValue,
        quittingPureTimeHazard_none_eq_quittingAlwaysContinueHazard] at hquitTime
      linarith [hquitTime, halwaysContinue, hslackScale, hsurvivalNonneg,
        mul_nonneg hsurvivalNonneg hbound]
  | some delay =>
      rcases lt_or_ge delay cutoff with hlt | hge
      · linarith [hquitTime, hearly delay hlt, hslackScale,
          mul_nonneg hsurvivalNonneg hbound]
      · linarith [hquitTime, hlate delay hge, hslackScale, hδ]

/-- **The assembled cap, fed by the clocks alone.**  The phase-switch
deviation cap whose plan phase is discharged by the *plan's* ledger, the
plan's quit regret before the switch, and the reach probability at the
switch -- the three quantities `QuittingLedgerPunishClock.lean`'s clocks and
`QuittingPhaseSwitchResiduals.lean`'s Case-2 wiring produce.  Hypothesis (b),
the punishment cap, is unchanged and remains hypothesised. -/
theorem quittingTerminalPayoff_update_quittingPhaseSwitchProfile_le_of_plan_ledger_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan punish : ℕ → ι → PMF Bool) (switch : ℕ) (who : ι)
    {ε δ reach punishError punishCap bound : ℝ}
    (hbound : 0 ≤ bound) (hδ : 0 ≤ δ)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hledger : ∀ index, index ≤ switch → quittingLedger reward plan who index ≤ ε)
    (hregret : ∀ stage, stage < switch →
      quittingLedgerQuitRegret reward plan who stage ≤ δ)
    (hreach : quittingOpponentSurvivalWeight plan who 0 switch ≤ reach)
    (hpunish : ∀ g : ℕ → PMF Bool,
      quittingRootSequenceHazardTerminalValue reward punish who g 0 ≤
        punishCap + punishError)
    (deviation : (quittingGame reward).BehaviorStrategy who) :
    quittingTerminalPayoff reward
        (Function.update (quittingPhaseSwitchProfile reward plan punish switch)
          who deviation) who ≤
      quittingTerminalPayoff reward
          (quittingPhaseSwitchProfile reward plan punish switch) who +
        (ε + δ + reach * (5 * bound)) +
        reach * (max (punishCap + punishError) 0 + bound) :=
  quittingTerminalPayoff_update_quittingPhaseSwitchProfile_le reward plan punish switch
    who hbound hreward
    (quittingRootSequenceHazardTerminalValue_quittingTruncatedRoots_le_of_plan_ledger_le
      reward plan who switch hbound hδ hreward hledger hregret hreach)
    hpunish hreach deviation

end GameTheory
