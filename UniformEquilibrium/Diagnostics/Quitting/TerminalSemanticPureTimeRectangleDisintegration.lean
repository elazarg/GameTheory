/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveSlopeCausalRegression

/-!
# Causal disintegration of a pure-time stopping-law rectangle

The cap branch of the positive stopping-law slope decoder selects one
deterministic response time for the debt recipient.  This file disintegrates
the resulting signed terminal-law rectangle without changing any of its
profiles.

For a finite recipient stop, a terminal coalition excluding the recipient is
preemption strictly before that stop, while a coalition containing the
recipient occurs at the stop itself.  A `Never` response leaves only finite
preemption.  At every selected stage the reset mover's factor is exactly
either a difference of stopping masses (when it belongs to the coalition) or
a difference of next-date survival masses (when it does not).

The stage certificate is signed.  In particular, positivity after weighting
by the recipient's reward is not called positive incidence and is not
silently relabelled as a same-row coalition toggle.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The literal signed payoff contribution of one chronological coalition
when only `mover` changes from `source` to `target`. -/
def quittingStoppingLawRectangleStageAtom
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : (quittingGame reward).BehaviorProfile) (mover : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (observer : ι) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) : ℝ :=
  (quittingStageCoalitionMass reward (Function.update base mover target)
      time terminal -
    quittingStageCoalitionMass reward (Function.update base mover source)
      time terminal) * reward terminal observer

/-- The mover's signed stopping-law factor at one chronological coalition.
Membership selects stopping mass; nonmembership selects survival through the
stage. -/
def quittingStoppingLawChronologicalFactorDifference
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (mover : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (time : ℕ) (terminal : {S : Finset ι // S.Nonempty}) : ℝ :=
  if mover ∈ terminal.val then
    quittingHazardStopMass (quittingBehaviorLiveHazard reward target) time -
      quittingHazardStopMass (quittingBehaviorLiveHazard reward source) time
  else
    quittingHazardSurvival (quittingBehaviorLiveHazard reward target)
        (time + 1) -
      quittingHazardSurvival (quittingBehaviorLiveHazard reward source)
        (time + 1)

/-- The cumulative stopping-probability difference `target - source` through
one date, written as the opposite difference of their surviving masses. -/
def quittingStoppingLawCumulativeDifference
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (mover : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (time : ℕ) : ℝ :=
  quittingHazardSurvival (quittingBehaviorLiveHazard reward source)
      (time + 1) -
    quittingHazardSurvival (quittingBehaviorLiveHazard reward target)
      (time + 1)

/-- Add one player to a nonempty terminal coalition. -/
def quittingInsertTerminal (mover : ι)
    (terminal : {S : Finset ι // S.Nonempty}) :
    {S : Finset ι // S.Nonempty} :=
  ⟨insert mover terminal.val, Finset.insert_nonempty mover terminal.val⟩

/-- The singleton terminal of one mover. -/
def quittingSoloTerminal (mover : ι) :
    {S : Finset ι // S.Nonempty} :=
  ⟨{mover}, Finset.singleton_nonempty mover⟩

/-- Reward change when the mover joins one nonempty opponent coalition. -/
def quittingStoppingLawInsertionGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mover observer : ι)
    (terminal : {S : Finset ι // S.Nonempty}) : ℝ :=
  reward (quittingInsertTerminal mover terminal) observer -
    reward terminal observer

/-- Reward change between mover-solo preemption and collision with one
opponent coalition. -/
def quittingStoppingLawPreemptionGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mover observer : ι)
    (terminal : {S : Finset ι // S.Nonempty}) : ℝ :=
  reward (quittingSoloTerminal mover) observer -
    reward (quittingInsertTerminal mover terminal) observer

/-- Conditional payoff change at one fixed opponents' first-stop row.  The
three terms are respectively mover preemption, collision, and later stopping
or `Never`. -/
def quittingStoppingLawConditionalFirstStopDifference
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mover observer : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (time : ℕ) (terminal : {S : Finset ι // S.Nonempty}) : ℝ :=
  (quittingHazardSurvival (quittingBehaviorLiveHazard reward source) time -
      quittingHazardSurvival (quittingBehaviorLiveHazard reward target) time) *
      reward (quittingSoloTerminal mover) observer +
    (quittingHazardStopMass (quittingBehaviorLiveHazard reward target) time -
      quittingHazardStopMass (quittingBehaviorLiveHazard reward source) time) *
      reward (quittingInsertTerminal mover terminal) observer +
    (quittingHazardSurvival (quittingBehaviorLiveHazard reward target)
          (time + 1) -
      quittingHazardSurvival (quittingBehaviorLiveHazard reward source)
          (time + 1)) * reward terminal observer

/-- **Exact local `H(t), H(t-1)` identity.**  Conditional on opponents first
stopping as `terminal` at `time`, the target-minus-source payoff change is
the cumulative stopping difference through `time` times the insertion gap,
plus the cumulative difference through `time-1` times the solo-versus-
collision gap.  At `time = 0` the latter coefficient vanishes because both
survivals at zero equal one. -/
theorem quittingStoppingLawConditionalFirstStopDifference_eq_gapCombination
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mover observer : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (time : ℕ) (terminal : {S : Finset ι // S.Nonempty}) :
    quittingStoppingLawConditionalFirstStopDifference reward mover observer
        source target time terminal =
      quittingStoppingLawCumulativeDifference reward mover source target time *
          quittingStoppingLawInsertionGap reward mover observer terminal +
        (quittingHazardSurvival
              (quittingBehaviorLiveHazard reward source) time -
            quittingHazardSurvival
              (quittingBehaviorLiveHazard reward target) time) *
          quittingStoppingLawPreemptionGap reward mover observer terminal := by
  unfold quittingStoppingLawConditionalFirstStopDifference
    quittingStoppingLawCumulativeDifference quittingStoppingLawInsertionGap
    quittingStoppingLawPreemptionGap
  rw [quittingHazardStopMass_eq_survival_sub_succ,
    quittingHazardStopMass_eq_survival_sub_succ]
  ring

theorem quittingStageCoalitionOpponentFactor_nonneg
    (roots : ℕ → ι → PMF Bool) (mover : ι) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) :
    0 ≤ quittingStageCoalitionOpponentFactor roots mover time terminal := by
  unfold quittingStageCoalitionOpponentFactor
  exact mul_nonneg (quittingOpponentSurvivalWeight_nonneg roots mover 0 time)
    (MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg _ _)

/-- For a coalition not containing the mover, forcing the mover to join it
does not change the opponents' first-stop factor. -/
theorem quittingStageCoalitionOpponentFactor_insert_eq
    (roots : ℕ → ι → PMF Bool) (mover : ι) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty})
    (hmover : mover ∉ terminal.val) :
    quittingStageCoalitionOpponentFactor roots mover time
        (quittingInsertTerminal mover terminal) =
      quittingStageCoalitionOpponentFactor roots mover time terminal := by
  unfold quittingStageCoalitionOpponentFactor
  apply congrArg (fun value =>
    quittingOpponentSurvivalWeight roots mover 0 time * value)
  unfold quittingInsertTerminal quittingRootCoalitionMass
    Math.PMFProduct.coalitionMass quittingRootQuitRates
  have hmemTrue :
      (∏ x ∈ terminal.val,
        ((Function.update (roots time) mover (PMF.pure true) x) true).toReal) =
        ∏ x ∈ terminal.val, ((roots time x) true).toReal := by
    apply Finset.prod_congr rfl
    intro x hx
    have hxne : x ≠ mover := by
      intro heq
      subst x
      exact hmover hx
    simp [Function.update_of_ne hxne]
  have hmemFalse :
      (∏ x ∈ terminal.val,
        ((Function.update (roots time) mover (PMF.pure false) x) true).toReal) =
        ∏ x ∈ terminal.val, ((roots time x) true).toReal := by
    apply Finset.prod_congr rfl
    intro x hx
    have hxne : x ≠ mover := by
      intro heq
      subst x
      exact hmover hx
    simp [Function.update_of_ne hxne]
  have hcomplementTrue :
      (∏ x ∈ terminal.valᶜ.erase mover,
        (1 - ((Function.update (roots time) mover
          (PMF.pure true) x) true).toReal)) =
        ∏ x ∈ terminal.valᶜ.erase mover,
          (1 - ((roots time x) true).toReal) := by
    apply Finset.prod_congr rfl
    intro x hx
    have hxne : x ≠ mover := Finset.ne_of_mem_erase hx
    simp [Function.update_of_ne hxne]
  have hcomplementFalse :
      (∏ x ∈ terminal.valᶜ,
        (1 - ((Function.update (roots time) mover
          (PMF.pure false) x) true).toReal)) =
        ∏ x ∈ terminal.valᶜ.erase mover,
          (1 - ((roots time x) true).toReal) := by
    have hmoverComplement : mover ∈ terminal.valᶜ := by simp [hmover]
    have hsplit := Finset.prod_erase_mul terminal.valᶜ
      (fun x => 1 - ((Function.update (roots time) mover
        (PMF.pure false) x) true).toReal) hmoverComplement
    have herased :
        (∏ x ∈ terminal.valᶜ.erase mover,
          (1 - ((Function.update (roots time) mover
            (PMF.pure false) x) true).toReal)) =
          ∏ x ∈ terminal.valᶜ.erase mover,
            (1 - ((roots time x) true).toReal) := by
      apply Finset.prod_congr rfl
      intro x hx
      have hxne : x ≠ mover := Finset.ne_of_mem_erase hx
      simp [Function.update_of_ne hxne]
    rw [← hsplit, herased]
    simp
  simp only [Finset.prod_insert, hmover, not_false_eq_true,
    Finset.compl_insert]
  simp only [decide_false]
  simp
  rw [hmemTrue, hmemFalse, hcomplementTrue, hcomplementFalse]

omit [DecidableEq ι] in
/-- The positive part of a cumulative `target - source` stopping excess is
dominated by the source survival which it consumes. -/
theorem max_cumulativeDifference_le_sourceSurvival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (mover : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (time : ℕ) :
    max (quittingStoppingLawCumulativeDifference reward mover source target
      time) 0 ≤
      quittingHazardSurvival (quittingBehaviorLiveHazard reward source)
        (time + 1) := by
  unfold quittingStoppingLawCumulativeDifference
  apply max_le
  · exact sub_le_self _ (quittingHazardSurvival_nonneg _ _)
  · exact quittingHazardSurvival_nonneg _ _

omit [DecidableEq ι] in
/-- The opposite orientation is dominated by target survival. -/
theorem max_neg_cumulativeDifference_le_targetSurvival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (mover : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (time : ℕ) :
    max (-quittingStoppingLawCumulativeDifference reward mover source target
      time) 0 ≤
      quittingHazardSurvival (quittingBehaviorLiveHazard reward target)
        (time + 1) := by
  unfold quittingStoppingLawCumulativeDifference
  apply max_le
  · rw [neg_sub]
    exact sub_le_self _ (quittingHazardSurvival_nonneg _ _)
  · exact quittingHazardSurvival_nonneg _ _

/-- A positive cumulative clock on a mover-free opponent coalition is
dominated by that coalition's actual chronological mass under the source
law. -/
theorem opponentFactor_mul_max_cumulativeDifference_le_sourceStageMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : (quittingGame reward).BehaviorProfile) (mover : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (time : ℕ) (terminal : {S : Finset ι // S.Nonempty})
    (hmover : mover ∉ terminal.val) :
    quittingStageCoalitionOpponentFactor
        (quittingProfileLiveRoot reward base) mover time terminal *
      max (quittingStoppingLawCumulativeDifference reward mover source target
        time) 0 ≤
      quittingStageCoalitionMass reward (Function.update base mover source)
        time terminal := by
  rw [quittingStageCoalitionMass_update_eq_opponentFactor_mul]
  simp only [hmover, if_false]
  exact mul_le_mul_of_nonneg_left
    (max_cumulativeDifference_le_sourceSurvival reward mover source target time)
    (quittingStageCoalitionOpponentFactor_nonneg
      (quittingProfileLiveRoot reward base) mover time terminal)

/-- The negatively oriented cumulative clock is likewise dominated by the
target endpoint's actual stage mass. -/
theorem opponentFactor_mul_max_neg_cumulativeDifference_le_targetStageMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : (quittingGame reward).BehaviorProfile) (mover : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (time : ℕ) (terminal : {S : Finset ι // S.Nonempty})
    (hmover : mover ∉ terminal.val) :
    quittingStageCoalitionOpponentFactor
        (quittingProfileLiveRoot reward base) mover time terminal *
      max (-quittingStoppingLawCumulativeDifference reward mover source target
        time) 0 ≤
      quittingStageCoalitionMass reward (Function.update base mover target)
        time terminal := by
  rw [quittingStageCoalitionMass_update_eq_opponentFactor_mul]
  simp only [hmover, if_false]
  exact mul_le_mul_of_nonneg_left
    (max_neg_cumulativeDifference_le_targetSurvival reward mover source target
      time)
    (quittingStageCoalitionOpponentFactor_nonneg
      (quittingProfileLiveRoot reward base) mover time terminal)

/-- Opponent first-stop mass times the mover's survival into a row is exactly
the sum of the two actual row atoms `S` and `S ∪ {mover}`. -/
theorem opponentFactor_mul_survival_eq_stageMass_add_insertStageMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : (quittingGame reward).BehaviorProfile) (mover : ι)
    (strategy : (quittingGame reward).BehaviorStrategy mover)
    (time : ℕ) (terminal : {S : Finset ι // S.Nonempty})
    (hmover : mover ∉ terminal.val) :
    quittingStageCoalitionOpponentFactor
        (quittingProfileLiveRoot reward base) mover time terminal *
      quittingHazardSurvival (quittingBehaviorLiveHazard reward strategy)
        time =
      quittingStageCoalitionMass reward (Function.update base mover strategy)
          time terminal +
        quittingStageCoalitionMass reward (Function.update base mover strategy)
          time (quittingInsertTerminal mover terminal) := by
  rw [quittingStageCoalitionMass_update_eq_opponentFactor_mul,
    quittingStageCoalitionMass_update_eq_opponentFactor_mul,
    quittingStageCoalitionOpponentFactor_insert_eq
      (quittingProfileLiveRoot reward base) mover time terminal hmover]
  simp only [hmover, if_false, quittingInsertTerminal,
    Finset.mem_insert, true_or, if_true]
  rw [quittingHazardStopMass_eq_survival_sub_succ]
  ring

/-- The `H(t-1)` positive clock from the first-stop identity is dominated by
the combined actual `S`/`S ∪ {mover}` stage mass under the source law. -/
theorem opponentFactor_mul_max_previousCumulative_le_sourceStagePair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : (quittingGame reward).BehaviorProfile) (mover : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (time : ℕ) (terminal : {S : Finset ι // S.Nonempty})
    (hmover : mover ∉ terminal.val) :
    quittingStageCoalitionOpponentFactor
        (quittingProfileLiveRoot reward base) mover time terminal *
      max
        (quittingHazardSurvival (quittingBehaviorLiveHazard reward source) time -
          quittingHazardSurvival (quittingBehaviorLiveHazard reward target) time)
        0 ≤
      quittingStageCoalitionMass reward (Function.update base mover source)
          time terminal +
        quittingStageCoalitionMass reward (Function.update base mover source)
          time (quittingInsertTerminal mover terminal) := by
  rw [← opponentFactor_mul_survival_eq_stageMass_add_insertStageMass reward
    base mover source time terminal hmover]
  apply mul_le_mul_of_nonneg_left
  · apply max_le
    · exact sub_le_self _ (quittingHazardSurvival_nonneg _ _)
    · exact quittingHazardSurvival_nonneg _ _
  · exact quittingStageCoalitionOpponentFactor_nonneg
      (quittingProfileLiveRoot reward base) mover time terminal

/-- The opposite `H(t-1)` orientation is dominated by the corresponding
target endpoint stage pair. -/
theorem opponentFactor_mul_max_neg_previousCumulative_le_targetStagePair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : (quittingGame reward).BehaviorProfile) (mover : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (time : ℕ) (terminal : {S : Finset ι // S.Nonempty})
    (hmover : mover ∉ terminal.val) :
    quittingStageCoalitionOpponentFactor
        (quittingProfileLiveRoot reward base) mover time terminal *
      max
        (-(quittingHazardSurvival (quittingBehaviorLiveHazard reward source)
              time -
            quittingHazardSurvival (quittingBehaviorLiveHazard reward target)
              time)) 0 ≤
      quittingStageCoalitionMass reward (Function.update base mover target)
          time terminal +
        quittingStageCoalitionMass reward (Function.update base mover target)
          time (quittingInsertTerminal mover terminal) := by
  rw [← opponentFactor_mul_survival_eq_stageMass_add_insertStageMass reward
    base mover target time terminal hmover]
  apply mul_le_mul_of_nonneg_left
  · apply max_le
    · rw [neg_sub]
      exact sub_le_self _ (quittingHazardSurvival_nonneg _ _)
    · exact quittingHazardSurvival_nonneg _ _
  · exact quittingStageCoalitionOpponentFactor_nonneg
      (quittingProfileLiveRoot reward base) mover time terminal

/-- A positive weighted sum of two signed gap terms exposes one of the four
positive-part clock orientations. -/
private theorem positive_weighted_twoGap_exposes_orientedClock
    (mass H previous insertionGap preemptionGap : ℝ)
    (hmass : 0 ≤ mass)
    (hpositive : 0 < mass *
      (H * insertionGap + previous * preemptionGap)) :
    (0 < mass * max H 0 ∧ 0 < insertionGap) ∨
      (0 < mass * max (-H) 0 ∧ 0 < -insertionGap) ∨
      (0 < mass * max previous 0 ∧ 0 < preemptionGap) ∨
      (0 < mass * max (-previous) 0 ∧ 0 < -preemptionGap) := by
  have hsplit : 0 < mass * H * insertionGap ∨
      0 < mass * previous * preemptionGap := by
    by_contra hnone
    push Not at hnone
    nlinarith
  rcases hsplit with hinsertion | hpreemption
  · rcases (mul_pos_iff.mp hinsertion) with
      ⟨hmassHPositive, hinsertionPositive⟩ |
      ⟨hmassHNegative, hinsertionNegative⟩
    · have hHPositive : 0 < H := by
        rcases (mul_pos_iff.mp hmassHPositive) with hsame | hopposite
        · exact hsame.2
        · exact False.elim ((not_lt_of_ge hmass) hopposite.1)
      left
      simpa [max_eq_left hHPositive.le] using
        And.intro hmassHPositive hinsertionPositive
    · have hHNegative : H < 0 := by
        rcases (mul_neg_iff.mp hmassHNegative) with hsign | hsign
        · exact hsign.2
        · exact False.elim ((not_lt_of_ge hmass) hsign.1)
      right
      left
      refine ⟨?_, neg_pos.mpr hinsertionNegative⟩
      rw [max_eq_left (neg_nonneg.mpr hHNegative.le)]
      nlinarith
  · rcases (mul_pos_iff.mp hpreemption) with
      ⟨hmassPreviousPositive, hpreemptionPositive⟩ |
      ⟨hmassPreviousNegative, hpreemptionNegative⟩
    · have hpreviousPositive : 0 < previous := by
        rcases (mul_pos_iff.mp hmassPreviousPositive) with hsame | hopposite
        · exact hsame.2
        · exact False.elim ((not_lt_of_ge hmass) hopposite.1)
      right
      right
      left
      simpa [max_eq_left hpreviousPositive.le] using
        And.intro hmassPreviousPositive hpreemptionPositive
    · have hpreviousNegative : previous < 0 := by
        rcases (mul_neg_iff.mp hmassPreviousNegative) with hsign | hsign
        · exact hsign.2
        · exact False.elim ((not_lt_of_ge hmass) hsign.1)
      right
      right
      right
      refine ⟨?_, neg_pos.mpr hpreemptionNegative⟩
      rw [max_eq_left (neg_nonneg.mpr hpreviousNegative.le)]
      nlinarith

/-- **Positive-clock label extraction at one co-realized first-stop row.**

If the target-minus-source conditional payoff change is positive after
weighting by the actual opponents' first-stop mass, one of four fixed reward
labels is positive: insertion, reverse insertion, solo-over-collision, or
collision-over-solo.  Its clock is a nonnegative positive part of the actual
mover stopping-law difference.  The preceding domination theorems bound
that clock by one literal endpoint stage atom (insertion labels) or by the
literal `S`/`S ∪ {mover}` endpoint pair (preemption labels). -/
theorem positive_firstStopDifference_exposes_orientedGapClock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : (quittingGame reward).BehaviorProfile) (mover observer : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (time : ℕ) (terminal : {S : Finset ι // S.Nonempty})
    (_hmover : mover ∉ terminal.val)
    (hpositive : 0 <
      quittingStageCoalitionOpponentFactor
          (quittingProfileLiveRoot reward base) mover time terminal *
        quittingStoppingLawConditionalFirstStopDifference reward mover
          observer source target time terminal) :
    let mass := quittingStageCoalitionOpponentFactor
      (quittingProfileLiveRoot reward base) mover time terminal
    let H := quittingStoppingLawCumulativeDifference reward mover source target
      time
    let previous :=
      quittingHazardSurvival (quittingBehaviorLiveHazard reward source) time -
        quittingHazardSurvival (quittingBehaviorLiveHazard reward target) time
    let J := quittingStoppingLawInsertionGap reward mover observer terminal
    let K := quittingStoppingLawPreemptionGap reward mover observer terminal
    (0 < mass * max H 0 ∧ 0 < J) ∨
      (0 < mass * max (-H) 0 ∧ 0 < -J) ∨
      (0 < mass * max previous 0 ∧ 0 < K) ∨
      (0 < mass * max (-previous) 0 ∧ 0 < -K) := by
  dsimp only
  rw [quittingStoppingLawConditionalFirstStopDifference_eq_gapCombination]
    at hpositive
  exact positive_weighted_twoGap_exposes_orientedClock _ _ _ _ _
    (quittingStageCoalitionOpponentFactor_nonneg
      (quittingProfileLiveRoot reward base) mover time terminal) hpositive

/-- Exact causal factorization of a signed rectangle stage.  The opponent
factor is common to the two co-realized profiles; all of their difference is
in the mover's stopping-time law. -/
theorem quittingStoppingLawRectangleStageAtom_eq_causalFactor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : (quittingGame reward).BehaviorProfile) (mover : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (observer : ι) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingStoppingLawRectangleStageAtom reward base mover source target
        observer time terminal =
      quittingStageCoalitionOpponentFactor
          (quittingProfileLiveRoot reward base) mover time terminal *
        quittingStoppingLawChronologicalFactorDifference reward mover source
          target time terminal * reward terminal observer := by
  rw [quittingStoppingLawRectangleStageAtom,
    quittingStageCoalitionMass_update_eq_opponentFactor_mul,
    quittingStageCoalitionMass_update_eq_opponentFactor_mul]
  unfold quittingStoppingLawChronologicalFactorDifference
  by_cases hmover : mover ∈ terminal.val
  · simp only [hmover, if_true]
    ring
  · simp only [hmover, if_false]
    ring

/-- The chronological rectangle atoms form a summable signed series. -/
theorem summable_quittingStoppingLawRectangleStageAtom
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : (quittingGame reward).BehaviorProfile) (mover : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (observer : ι) (terminal : {S : Finset ι // S.Nonempty}) :
    Summable (fun time =>
      quittingStoppingLawRectangleStageAtom reward base mover source target
        observer time terminal) := by
  unfold quittingStoppingLawRectangleStageAtom
  exact ((hasSum_quittingStageCoalitionMass reward
      (Function.update base mover target) terminal).summable.sub
        (hasSum_quittingStageCoalitionMass reward
          (Function.update base mover source) terminal).summable).mul_right
            (reward terminal observer)

/-- Every chronological coalition atom is dominated by the matching actual
terminal-law atom of the same profile. -/
theorem quittingStageCoalitionMass_le_terminalOutcomeMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingStageCoalitionMass reward profile time terminal ≤
      quittingTerminalOutcomeMass reward profile (some terminal) := by
  change quittingStageCoalitionMass reward profile time terminal ≤
    quittingAbsorbedMassLimit reward profile terminal
  rw [← tsum_quittingStageCoalitionMass reward profile terminal]
  exact (hasSum_quittingStageCoalitionMass reward profile terminal).summable.le_tsum
    time (fun other _hne =>
      quittingStageCoalitionMass_nonneg reward profile other terminal)

/-- Positivity of a signed chronological rectangle is carried by positive
mass in at least one of its two literal endpoint profiles.  Consequently the
same terminal coalition has positive mass in that actual endpoint terminal
law. -/
theorem positive_actualTerminalMass_of_positive_stoppingLawRectangleStageAtom
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : (quittingGame reward).BehaviorProfile) (mover : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (observer : ι) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty})
    (hpositive : 0 < quittingStoppingLawRectangleStageAtom reward base mover
      source target observer time terminal) :
    (0 < quittingStageCoalitionMass reward
        (Function.update base mover target) time terminal ∧
      0 < quittingTerminalOutcomeMass reward
        (Function.update base mover target) (some terminal)) ∨
    (0 < quittingStageCoalitionMass reward
        (Function.update base mover source) time terminal ∧
      0 < quittingTerminalOutcomeMass reward
        (Function.update base mover source) (some terminal)) := by
  let targetMass := quittingStageCoalitionMass reward
    (Function.update base mover target) time terminal
  let sourceMass := quittingStageCoalitionMass reward
    (Function.update base mover source) time terminal
  have htargetNonneg : 0 ≤ targetMass :=
    quittingStageCoalitionMass_nonneg reward
      (Function.update base mover target) time terminal
  have hsourceNonneg : 0 ≤ sourceMass :=
    quittingStageCoalitionMass_nonneg reward
      (Function.update base mover source) time terminal
  have honePositive : 0 < targetMass ∨ 0 < sourceMass := by
    by_contra hnone
    push Not at hnone
    have htargetZero : targetMass = 0 := le_antisymm hnone.1 htargetNonneg
    have hsourceZero : sourceMass = 0 := le_antisymm hnone.2 hsourceNonneg
    dsimp only [quittingStoppingLawRectangleStageAtom, targetMass,
      sourceMass] at hpositive htargetZero hsourceZero
    rw [htargetZero, hsourceZero] at hpositive
    simp at hpositive
  rcases honePositive with htarget | hsource
  · left
    refine ⟨htarget, htarget.trans_le ?_⟩
    exact quittingStageCoalitionMass_le_terminalOutcomeMass reward
      (Function.update base mover target) time terminal
  · right
    refine ⟨hsource, hsource.trans_le ?_⟩
    exact quittingStageCoalitionMass_le_terminalOutcomeMass reward
      (Function.update base mover source) time terminal

/-! ## Exact pure-time rectangle formulas -/

/-- If a finite pure-time recipient is absent from the terminal coalition,
the complete terminal rectangle is the finite sum of preemption stages
strictly before its stop. -/
theorem quittingTerminalPayoffDifferenceAtom_pureTime_some_notMem_eq_before
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (hmoverObserver : mover ≠ observer)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (stop : ℕ) (terminal : {S : Finset ι // S.Nonempty})
    (hobserver : observer ∉ terminal.val) :
    quittingTerminalPayoffDifferenceAtom reward
        (Function.update (Function.update profile mover target) observer
          (quittingPureTimeBehaviorStrategy reward observer (some stop)))
        (Function.update (Function.update profile mover source) observer
          (quittingPureTimeBehaviorStrategy reward observer (some stop)))
        observer (some terminal) =
      ∑ time ∈ Finset.range stop,
        quittingStoppingLawRectangleStageAtom reward
          (Function.update profile observer
            (quittingPureTimeBehaviorStrategy reward observer (some stop)))
          mover source target observer time terminal := by
  rw [quittingTerminalPayoffDifferenceAtom,
    quittingTerminalOutcomeMass_update_pureTime_some_notMem_eq_before
      reward (Function.update profile mover target) observer stop terminal
        hobserver,
    quittingTerminalOutcomeMass_update_pureTime_some_notMem_eq_before
      reward (Function.update profile mover source) observer stop terminal
        hobserver,
    ← Finset.sum_sub_distrib]
  simp only [quittingTerminalOutcomeReward]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro time _htime
  rw [Function.update_comm hmoverObserver,
    Function.update_comm hmoverObserver]
  rfl

/-- If a finite pure-time recipient belongs to the terminal coalition, the
complete rectangle is the single collision row at its selected stop.  When
the mover is absent, the same formula is the `mover later or Never` survival
boundary at that row. -/
theorem quittingTerminalPayoffDifferenceAtom_pureTime_some_mem_eq_at
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (hmoverObserver : mover ≠ observer)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (stop : ℕ) (terminal : {S : Finset ι // S.Nonempty})
    (hobserver : observer ∈ terminal.val) :
    quittingTerminalPayoffDifferenceAtom reward
        (Function.update (Function.update profile mover target) observer
          (quittingPureTimeBehaviorStrategy reward observer (some stop)))
        (Function.update (Function.update profile mover source) observer
          (quittingPureTimeBehaviorStrategy reward observer (some stop)))
        observer (some terminal) =
      quittingStoppingLawRectangleStageAtom reward
        (Function.update profile observer
          (quittingPureTimeBehaviorStrategy reward observer (some stop)))
        mover source target observer stop terminal := by
  rw [quittingTerminalPayoffDifferenceAtom,
    quittingTerminalOutcomeMass_update_pureTime_some_mem_eq_at
      reward (Function.update profile mover target) observer stop terminal
        hobserver,
    quittingTerminalOutcomeMass_update_pureTime_some_mem_eq_at
      reward (Function.update profile mover source) observer stop terminal
        hobserver,
    Function.update_comm hmoverObserver,
    Function.update_comm hmoverObserver]
  rfl

/-- Under a pure `Never` response, an absorbing terminal rectangle is the
summable series of its finite chronological preemption rows. -/
theorem quittingTerminalPayoffDifferenceAtom_pureTime_none_eq_tsum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (hmoverObserver : mover ≠ observer)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingTerminalPayoffDifferenceAtom reward
        (Function.update (Function.update profile mover target) observer
          (quittingPureTimeBehaviorStrategy reward observer none))
        (Function.update (Function.update profile mover source) observer
          (quittingPureTimeBehaviorStrategy reward observer none))
        observer (some terminal) =
      ∑' time,
        quittingStoppingLawRectangleStageAtom reward
          (Function.update profile observer
            (quittingPureTimeBehaviorStrategy reward observer none))
          mover source target observer time terminal := by
  let targetProfile := Function.update (Function.update profile mover target)
    observer (quittingPureTimeBehaviorStrategy reward observer none)
  let sourceProfile := Function.update (Function.update profile mover source)
    observer (quittingPureTimeBehaviorStrategy reward observer none)
  have htarget : HasSum
      (fun time => quittingStageCoalitionMass reward targetProfile time terminal)
      (quittingAbsorbedMassLimit reward targetProfile terminal) :=
    hasSum_quittingStageCoalitionMass reward targetProfile terminal
  have hsource : HasSum
      (fun time => quittingStageCoalitionMass reward sourceProfile time terminal)
      (quittingAbsorbedMassLimit reward sourceProfile terminal) :=
    hasSum_quittingStageCoalitionMass reward sourceProfile terminal
  have hrectangle := (htarget.sub hsource).mul_right (reward terminal observer)
  unfold quittingTerminalPayoffDifferenceAtom
  simp only [quittingTerminalOutcomeMass,
    quittingTerminalOutcomeReward]
  change
    (quittingAbsorbedMassLimit reward targetProfile terminal -
        quittingAbsorbedMassLimit reward sourceProfile terminal) *
          reward terminal observer = _
  rw [← hrectangle.tsum_eq]
  apply tsum_congr
  intro time
  dsimp only [targetProfile, sourceProfile]
  rw [Function.update_comm hmoverObserver,
    Function.update_comm hmoverObserver]
  rfl

/-! ## Positive signed atom localization -/

/-- Chronological location of a terminal atom under a deterministic
pure-time response. -/
def IsQuittingPureTimeRectangleStage
    (observer : ι) (terminal : {S : Finset ι // S.Nonempty})
    (quitTime : Option ℕ) (time : ℕ) : Prop :=
  match quitTime with
  | some stop =>
      (time < stop ∧ observer ∉ terminal.val) ∨
        (time = stop ∧ observer ∈ terminal.val)
  | none => observer ∉ terminal.val

/-- A positive signed pure-time rectangle has a positive signed causal
stage.  The accompanying alternative records its exact chronology:

* a finite stop gives either preemption before the stop or the unique
  at-stop coalition;
* `Never` gives a finite preemption row and excludes the recipient from the
  terminal coalition.

The returned stage atom has the exact stopping-mass/survival factorization
above. -/
theorem exists_positive_causalStage_of_positive_pureTimeRectangleAtom
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (hmoverObserver : mover ≠ observer)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (quitTime : Option ℕ)
    (terminal : {S : Finset ι // S.Nonempty})
    (hpositive : 0 < quittingTerminalPayoffDifferenceAtom reward
      (Function.update (Function.update profile mover target) observer
        (quittingPureTimeBehaviorStrategy reward observer quitTime))
      (Function.update (Function.update profile mover source) observer
        (quittingPureTimeBehaviorStrategy reward observer quitTime))
      observer (some terminal)) :
    ∃ time,
      0 < quittingStoppingLawRectangleStageAtom reward
        (Function.update profile observer
          (quittingPureTimeBehaviorStrategy reward observer quitTime))
        mover source target observer time terminal ∧
      IsQuittingPureTimeRectangleStage observer terminal quitTime time := by
  cases quitTime with
  | some stop =>
      by_cases hobserver : observer ∈ terminal.val
      · refine ⟨stop, ?_, Or.inr ⟨rfl, hobserver⟩⟩
        rw [quittingTerminalPayoffDifferenceAtom_pureTime_some_mem_eq_at
          reward profile mover observer hmoverObserver source target stop
            terminal hobserver] at hpositive
        exact hpositive
      · rw [quittingTerminalPayoffDifferenceAtom_pureTime_some_notMem_eq_before
          reward profile mover observer hmoverObserver source target stop
            terminal hobserver] at hpositive
        have hexists : ∃ time ∈ Finset.range stop,
            0 < quittingStoppingLawRectangleStageAtom reward
              (Function.update profile observer
                (quittingPureTimeBehaviorStrategy reward observer
                  (some stop))) mover source target observer time terminal := by
          by_contra hnone
          push Not at hnone
          have hsumNonpos :
              (∑ time ∈ Finset.range stop,
                quittingStoppingLawRectangleStageAtom reward
                  (Function.update profile observer
                    (quittingPureTimeBehaviorStrategy reward observer
                      (some stop))) mover source target observer time terminal) ≤
                0 := by
            apply Finset.sum_nonpos
            intro time htime
            exact hnone time htime
          linarith
        obtain ⟨time, htime, htimePositive⟩ := hexists
        exact ⟨time, htimePositive,
          Or.inl ⟨Finset.mem_range.mp htime, hobserver⟩⟩
  | none =>
      have hobserver : observer ∉ terminal.val := by
        intro hobserver
        have htargetZero :=
          quittingTerminalOutcomeMass_update_pureTime_none_mem_eq_zero reward
            (Function.update profile mover target) observer terminal hobserver
        have hsourceZero :=
          quittingTerminalOutcomeMass_update_pureTime_none_mem_eq_zero reward
            (Function.update profile mover source) observer terminal hobserver
        unfold quittingTerminalPayoffDifferenceAtom at hpositive
        rw [htargetZero, hsourceZero] at hpositive
        simp at hpositive
      rw [quittingTerminalPayoffDifferenceAtom_pureTime_none_eq_tsum reward
        profile mover observer hmoverObserver source target terminal] at hpositive
      have hexists : ∃ time,
          0 < quittingStoppingLawRectangleStageAtom reward
            (Function.update profile observer
              (quittingPureTimeBehaviorStrategy reward observer none))
            mover source target observer time terminal := by
        by_contra hnone
        push Not at hnone
        have hsumNonpos :
            (∑' time,
              quittingStoppingLawRectangleStageAtom reward
                (Function.update profile observer
                  (quittingPureTimeBehaviorStrategy reward observer none))
                mover source target observer time terminal) ≤ 0 :=
          tsum_nonpos hnone
        linarith
      obtain ⟨time, htimePositive⟩ := hexists
      exact ⟨time, htimePositive, hobserver⟩

/-- Quantitative entry point matching the pure-time cap branch: a positive
charge bounded by the finite-outcome multiple of one rectangle atom yields a
positive causal stage, its exact chronology, and positive mass for the same
terminal coalition in one literal endpoint law. -/
theorem exists_positive_causalStage_and_actualTerminalMass_of_rectangleCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (hmoverObserver : mover ≠ observer)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (quitTime : Option ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) (charge : ℝ)
    (hcharge : 0 < charge)
    (hbound : charge ≤
      (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
        quittingTerminalPayoffDifferenceAtom reward
          (Function.update (Function.update profile mover target) observer
            (quittingPureTimeBehaviorStrategy reward observer quitTime))
          (Function.update (Function.update profile mover source) observer
            (quittingPureTimeBehaviorStrategy reward observer quitTime))
          observer (some terminal)) :
    ∃ time,
      0 < quittingStoppingLawRectangleStageAtom reward
        (Function.update profile observer
          (quittingPureTimeBehaviorStrategy reward observer quitTime))
        mover source target observer time terminal ∧
      IsQuittingPureTimeRectangleStage observer terminal quitTime time ∧
      ((0 < quittingTerminalOutcomeMass reward
          (Function.update
            (Function.update profile observer
              (quittingPureTimeBehaviorStrategy reward observer quitTime))
            mover target) (some terminal)) ∨
        (0 < quittingTerminalOutcomeMass reward
          (Function.update
            (Function.update profile observer
              (quittingPureTimeBehaviorStrategy reward observer quitTime))
            mover source) (some terminal))) := by
  let atom := quittingTerminalPayoffDifferenceAtom reward
    (Function.update (Function.update profile mover target) observer
      (quittingPureTimeBehaviorStrategy reward observer quitTime))
    (Function.update (Function.update profile mover source) observer
      (quittingPureTimeBehaviorStrategy reward observer quitTime))
    observer (some terminal)
  have hcard : 0 ≤ (Fintype.card (QuittingTerminalOutcome ι) : ℝ) := by
    positivity
  have hatom : 0 < atom := by
    dsimp only [atom] at hbound ⊢
    nlinarith
  obtain ⟨time, htimePositive, hchronology⟩ :=
    exists_positive_causalStage_of_positive_pureTimeRectangleAtom reward
      profile mover observer hmoverObserver source target quitTime terminal
        hatom
  have hactual :=
    positive_actualTerminalMass_of_positive_stoppingLawRectangleStageAtom
      reward
        (Function.update profile observer
          (quittingPureTimeBehaviorStrategy reward observer quitTime))
        mover source target observer time terminal htimePositive
  refine ⟨time, htimePositive, hchronology, ?_⟩
  rcases hactual with htarget | hsource
  · exact Or.inl htarget.2
  · exact Or.inr hsource.2

end GameTheory
