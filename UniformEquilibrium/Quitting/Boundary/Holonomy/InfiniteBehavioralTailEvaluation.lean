/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Holonomy.BehavioralTailEvaluation
import UniformEquilibrium.Quitting.Boundary.Holonomy.BehavioralTailRepairValue
import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality
import UniformEquilibrium.Quitting.Cycles.PhaseSwitchDeviationCap

/-!
# Infinite behavioral tails through a finite holonomy

This module closes the semantic seam left open by finite boundary evaluation.
For one actual punishment root sequence, its prescribed boundary and its
all-behavior best-response boundary are kept together.  Attaching that tail
after a nonempty finite plan prefix makes the prefix max-affine holonomy equal
to the literal all-behavior best-response value of the phase-switch profile.

The proof does not truncate the tail.  It uses the exact phase-switch
decomposition for arbitrary live-path hazards.  The upper bound inserts the
tail best-response supremum into the finite Bellman recursion.  For the lower
bound, an early Bellman maximizer is realized by an actual deterministic quit
date, while the Continue-through alternative is approached by an actual tail
behavior deviation.  Uniform boundedness of rewards is used only for the
real-valued suprema and their approximation; no absorption or survival-limit
hypothesis is required.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Elementary realization lemmas -/

/-- Any live-path hazard is bounded by the literal all-behavior
best-response value against the same root sequence. -/
theorem quittingRootSequenceHazardTerminalValue_le_continuationBestResponse
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (hazard : ℕ → PMF Bool)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    quittingRootSequenceHazardTerminalValue reward roots who hazard 0 ≤
      quittingContinuationBestResponseValue reward
        (quittingRootSequenceProfile reward roots 0) who := by
  rw [quittingRootSequenceHazardTerminalValue_eq_terminalPayoff_update]
  exact quittingTerminalPayoff_update_le_continuationBestResponseValue
    reward (quittingRootSequenceProfile reward roots 0) who
      (fun time _history => hazard time) hM hreward

private theorem exists_finiteEarlyBestResponse_pureTime
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (terminalValue : ℝ) :
    ∀ start extra,
      ∃ choice : Fin (extra + 1),
        quittingFiniteTerminalPureTimeValue reward roots who terminalValue
            start (extra + 1) choice.castSucc =
          quittingFiniteEarlyBestResponseValue reward roots who start extra := by
  intro start extra
  induction extra generalizing start with
  | zero =>
      refine ⟨0, ?_⟩
      rfl
  | succ extra ih =>
      obtain ⟨later, hlater⟩ := ih (start + 1)
      by_cases hquit :
          quittingFixedOpponentsQuitValue reward roots who start ≤
            quittingFixedOpponentsContinueReward reward roots who start +
              quittingFixedOpponentsContinueMass roots who start *
                quittingFiniteEarlyBestResponseValue reward roots who
                  (start + 1) extra
      · refine ⟨Fin.succ later, ?_⟩
        rw [quittingFiniteEarlyBestResponseValue, max_eq_right hquit]
        change
          quittingFixedOpponentsContinueReward reward roots who start +
                quittingFixedOpponentsContinueMass roots who start *
                  quittingFiniteTerminalPureTimeValue reward roots who
                    terminalValue (start + 1) (extra + 1) later.castSucc = _
        rw [hlater]
      · refine ⟨0, ?_⟩
        rw [quittingFiniteEarlyBestResponseValue,
          max_eq_left (le_of_not_ge hquit)]
        rfl

private theorem quittingFiniteTerminalPureTimeValue_castSucc_terminal_congr
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (first second : ℝ) :
    ∀ (start fuel : ℕ) (choice : Fin fuel),
      quittingFiniteTerminalPureTimeValue reward roots who first
          start fuel choice.castSucc =
        quittingFiniteTerminalPureTimeValue reward roots who second
          start fuel choice.castSucc := by
  intro start fuel
  induction fuel generalizing start with
  | zero => exact fun choice => Fin.elim0 choice
  | succ fuel ih =>
      intro choice
      refine Fin.cases ?_ (fun later => ?_) choice
      · rfl
      · change
          quittingFixedOpponentsContinueReward reward roots who start +
                quittingFixedOpponentsContinueMass roots who start *
                  quittingFiniteTerminalPureTimeValue reward roots who first
                    (start + 1) fuel later.castSucc =
            quittingFixedOpponentsContinueReward reward roots who start +
                quittingFixedOpponentsContinueMass roots who start *
                  quittingFiniteTerminalPureTimeValue reward roots who second
                    (start + 1) fuel later.castSucc
        rw [ih (start + 1) later]

private theorem exists_finiteEarlyBestResponse_pureTime_of_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (terminalValue : ℝ)
    (start fuel : ℕ) (hfuel : 0 < fuel) :
    ∃ choice : Fin fuel,
      quittingFiniteTerminalPureTimeValue reward roots who terminalValue
          start fuel choice.castSucc =
        quittingFiniteEarlyBestResponseValue reward roots who start
          (fuel - 1) := by
  cases fuel with
  | zero => omega
  | succ extra =>
      simpa using exists_finiteEarlyBestResponse_pureTime
        reward roots who terminalValue start extra

private theorem quittingFiniteTerminalHazardValue_pureContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (terminalValue : ℝ) :
    ∀ start fuel,
      quittingFiniteTerminalHazardValue reward roots who
          (fun _ => PMF.pure false) terminalValue start fuel =
        quittingFiniteContinueToBoundaryValue reward roots who terminalValue
          start fuel := by
  intro start fuel
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      rw [quittingFiniteTerminalHazardValue,
        quittingFiniteContinueToBoundaryValue, ih (start + 1)]
      simp

/-- A scalar phase switch: Continue throughout the finite prefix, then use
the supplied tail hazard from its own time zero. -/
def quittingContinueUntilThenHazard
    (switch : ℕ) (tailHazard : ℕ → PMF Bool) : ℕ → PMF Bool :=
  fun time => if time < switch then PMF.pure false
    else tailHazard (time - switch)

@[simp] theorem quittingContinueUntilThenHazard_of_lt
    (switch : ℕ) (tailHazard : ℕ → PMF Bool) {time : ℕ}
    (htime : time < switch) :
    quittingContinueUntilThenHazard switch tailHazard time = PMF.pure false := by
  simp [quittingContinueUntilThenHazard, htime]

@[simp] theorem quittingContinueUntilThenHazard_add
    (switch offset : ℕ) (tailHazard : ℕ → PMF Bool) :
    quittingContinueUntilThenHazard switch tailHazard (switch + offset) =
      tailHazard offset := by
  simp [quittingContinueUntilThenHazard]

private theorem quittingFiniteTerminalHazardValue_continueThenHazard_prefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (terminalValue : ℝ)
    (switch : ℕ) (tailHazard : ℕ → PMF Bool) :
    quittingFiniteTerminalHazardValue reward roots who
        (quittingContinueUntilThenHazard switch tailHazard) terminalValue 0 switch =
      quittingFiniteContinueToBoundaryValue reward roots who terminalValue
        0 switch := by
  have hprefix : ∀ start fuel, start + fuel ≤ switch →
      quittingFiniteTerminalHazardValue reward roots who
          (quittingContinueUntilThenHazard switch tailHazard) terminalValue
          start fuel =
        quittingFiniteTerminalHazardValue reward roots who
          (fun _ => PMF.pure false) terminalValue start fuel := by
    intro start fuel hwindow
    induction fuel generalizing start with
    | zero => rfl
    | succ fuel ih =>
        have hstart : start < switch := by omega
        have htail : start + 1 + fuel ≤ switch := by omega
        rw [quittingFiniteTerminalHazardValue,
          quittingFiniteTerminalHazardValue,
          quittingContinueUntilThenHazard_of_lt switch tailHazard hstart,
          ih (start + 1) htail]
  rw [hprefix 0 switch (by omega)]
  exact quittingFiniteTerminalHazardValue_pureContinue
    reward roots who terminalValue 0 switch

/-! ## Exact infinite-tail best-response evaluation -/

/-- Attaching one actual behavioral tail after a positive finite prefix:
the finite Bellman envelope evaluated at that tail's literal best-response
boundary is exactly the literal all-behavior best-response value of the
phase-switch profile. -/
theorem quittingPhaseSwitch_bestResponseAt_eq_continuationBestResponse
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan punish : ℕ → ι → PMF Bool) (switch : ℕ) (hswitch : 0 < switch)
    (who : ι) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    (quittingFiniteBoundaryHolonomy reward plan 0 (switch - 1)).boundaryEnvelopeAt
        (QuittingBoundaryHolonomy.behavioralTailEnvelopeBoundary reward punish)
        who =
      quittingContinuationBestResponseValue reward
        (quittingPhaseSwitchProfile reward plan punish switch) who := by
  let phase := quittingPhaseSwitchRoots plan punish switch
  let phaseProfile := quittingPhaseSwitchProfile reward plan punish switch
  let tailProfile := quittingRootSequenceProfile reward punish 0
  let tailBest := quittingContinuationBestResponseValue reward tailProfile who
  let prefixBest := quittingFiniteTerminalBestResponseValue reward plan who
    tailBest 0 switch
  have hlength : switch - 1 + 1 = switch := Nat.sub_add_cancel
    (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hswitch))
  have hholonomy :
      (quittingFiniteBoundaryHolonomy reward plan 0 (switch - 1)).boundaryEnvelopeAt
          (QuittingBoundaryHolonomy.behavioralTailEnvelopeBoundary reward punish)
          who = prefixBest := by
    change QuittingMaxAffineSummary.eval
        ((quittingFiniteBoundaryHolonomy reward plan 0 (switch - 1)).bestResponse who)
        tailBest = prefixBest
    rw [quittingFiniteBoundaryHolonomy_bestResponse_eval, hlength]
  rw [hholonomy]
  apply le_antisymm
  · change quittingFiniteTerminalBestResponseValue reward plan who tailBest
        0 switch ≤ _
    have hprefixSplit :
        quittingFiniteTerminalBestResponseValue reward plan who tailBest
            0 switch =
          max (quittingFiniteEarlyBestResponseValue reward plan who 0
              (switch - 1))
            (quittingFiniteContinueToBoundaryValue reward plan who tailBest
              0 switch) := by
      rw [← hlength]
      exact quittingFiniteTerminalBestResponseValue_eq_max_early_boundary
        reward plan who tailBest 0 (switch - 1)
    rw [hprefixSplit]
    apply max_le
    · obtain ⟨choice, hchoice⟩ :=
        exists_finiteEarlyBestResponse_pureTime_of_pos reward plan who tailBest
          0 switch hswitch
      let quitTime := choice.val
      let hazard := quittingPureTimeHazard (some quitTime)
      have hphaseValue :
          quittingRootSequenceHazardTerminalValue reward phase who hazard 0 =
            quittingFiniteEarlyBestResponseValue reward plan who 0
              (switch - 1) := by
        rw [quittingRootSequenceHazardTerminalValue_phaseSwitch_eq_finite]
        let boundary := quittingRootSequenceHazardTerminalValue reward punish who
          (fun offset => hazard (switch + offset)) 0
        change quittingFiniteTerminalHazardValue reward plan who
            (quittingPureTimeHazard (some choice.val)) boundary 0 switch = _
        have hrealize :=
          quittingFiniteTerminalPureTimeValue_castSucc_eq_hazard
            reward plan who boundary 0 switch choice
        simp only [Nat.zero_add] at hrealize
        rw [← hrealize]
        calc
          quittingFiniteTerminalPureTimeValue reward plan who boundary
                0 switch choice.castSucc =
              quittingFiniteTerminalPureTimeValue reward plan who tailBest
                0 switch choice.castSucc :=
            quittingFiniteTerminalPureTimeValue_castSucc_terminal_congr
              reward plan who boundary tailBest 0 switch choice
          _ = _ := hchoice
      rw [← hphaseValue]
      dsimp [phase, phaseProfile]
      exact quittingRootSequenceHazardTerminalValue_le_continuationBestResponse
        reward (quittingPhaseSwitchRoots plan punish switch) who hazard hM hreward
    · apply le_of_forall_pos_le_add
      intro ε hε
      obtain ⟨tailDeviation, htailApprox⟩ :=
        exists_quittingContinuation_deviation_ge_sub reward tailProfile who
          hε hM hreward
      let tailHazard := quittingBehaviorLiveHazard reward tailDeviation
      let hazard := quittingContinueUntilThenHazard switch tailHazard
      let tailValue := quittingTerminalPayoff reward
        (Function.update tailProfile who tailDeviation) who
      have htailValue : tailValue ≤ tailBest := by
        exact quittingTerminalPayoff_update_le_continuationBestResponseValue
          reward tailProfile who tailDeviation hM hreward
      have htailGap : 0 ≤ tailBest - tailValue := sub_nonneg.mpr htailValue
      have htailGapLe : tailBest - tailValue ≤ ε := by
        dsimp [tailBest, tailValue] at htailApprox ⊢
        linarith
      have htailRoot :
          quittingRootSequenceHazardTerminalValue reward punish who tailHazard 0 =
            tailValue := by
        dsimp [tailHazard, tailValue, tailProfile]
        rw [quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue,
          quittingProfileLiveRoot_quittingRootSequenceProfile_zero]
      have hphaseValue :
          quittingRootSequenceHazardTerminalValue reward phase who hazard 0 =
            quittingFiniteContinueToBoundaryValue reward plan who tailValue
              0 switch := by
        rw [quittingRootSequenceHazardTerminalValue_phaseSwitch_eq_finite]
        have hsuffix : (fun offset => hazard (switch + offset)) = tailHazard := by
          funext offset
          exact quittingContinueUntilThenHazard_add switch offset tailHazard
        rw [hsuffix, htailRoot]
        exact quittingFiniteTerminalHazardValue_continueThenHazard_prefix
          reward plan who tailValue switch tailHazard
      have hsurvival1 := quittingOpponentSurvivalWeight_le_one plan who 0 switch
      have hboundary :
          quittingFiniteContinueToBoundaryValue reward plan who tailBest 0 switch =
            quittingFiniteContinueToBoundaryValue reward plan who tailValue 0 switch +
              quittingOpponentSurvivalWeight plan who 0 switch *
                (tailBest - tailValue) := by
        calc
          quittingFiniteContinueToBoundaryValue reward plan who tailBest
              0 switch =
            quittingFiniteContinueToBoundaryValue reward plan who
              (tailValue + (tailBest - tailValue)) 0 switch := by
                congr 2
                ring
          _ = _ := quittingFiniteContinueToBoundaryValue_add
            reward plan who tailValue (tailBest - tailValue) 0 switch
      have hscaled :
          quittingOpponentSurvivalWeight plan who 0 switch *
              (tailBest - tailValue) ≤ ε := by
        calc
          _ ≤ 1 * (tailBest - tailValue) :=
            mul_le_mul_of_nonneg_right hsurvival1 htailGap
          _ ≤ ε := by simpa using htailGapLe
      rw [hboundary]
      calc
        quittingFiniteContinueToBoundaryValue reward plan who tailValue 0 switch +
              quittingOpponentSurvivalWeight plan who 0 switch *
                (tailBest - tailValue) ≤
            quittingRootSequenceHazardTerminalValue reward phase who hazard 0 + ε := by
          rw [hphaseValue]
          linarith
        _ ≤ quittingContinuationBestResponseValue reward phaseProfile who + ε := by
          gcongr
          dsimp [phase, phaseProfile]
          exact quittingRootSequenceHazardTerminalValue_le_continuationBestResponse
            reward (quittingPhaseSwitchRoots plan punish switch) who hazard hM hreward
  · unfold quittingContinuationBestResponseValue
    apply csSup_le
    · refine ⟨_, ⟨phaseProfile who, rfl⟩⟩
    · rintro _ ⟨deviation, rfl⟩
      let hazard := quittingBehaviorLiveHazard reward deviation
      have hcollapse :
          quittingTerminalPayoff reward
              (Function.update phaseProfile who deviation) who =
            quittingRootSequenceHazardTerminalValue reward phase who hazard 0 := by
        dsimp [phase, phaseProfile, hazard]
        rw [quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue,
          quittingProfileLiveRoot_quittingPhaseSwitchProfile]
      change quittingTerminalPayoff reward
          (Function.update phaseProfile who deviation) who ≤ prefixBest
      rw [hcollapse,
        quittingRootSequenceHazardTerminalValue_phaseSwitch_eq_finite]
      have htail :
          quittingRootSequenceHazardTerminalValue reward punish who
              (fun offset => hazard (switch + offset)) 0 ≤ tailBest := by
        dsimp [tailBest, tailProfile]
        exact quittingRootSequenceHazardTerminalValue_le_continuationBestResponse
          reward punish who (fun offset => hazard (switch + offset)) hM hreward
      calc
        quittingFiniteTerminalHazardValue reward plan who hazard
              (quittingRootSequenceHazardTerminalValue reward punish who
                (fun offset => hazard (switch + offset)) 0) 0 switch ≤
            quittingFiniteTerminalBestResponseValue reward plan who
              (quittingRootSequenceHazardTerminalValue reward punish who
                (fun offset => hazard (switch + offset)) 0) 0 switch :=
          quittingFiniteTerminalHazardValue_le_bestResponse
            reward plan who hazard _ 0 switch
        _ ≤ prefixBest :=
          quittingFiniteTerminalBestResponseValue_mono_terminal
            reward plan who htail 0 switch

/-! ## Literal terminal exploitability -/

/-- Maximum positive unilateral terminal gain of one behavioral profile.
This is a literal all-behavior quantity: each best-response coordinate is the
supremum over all unilateral behavior strategies against the displayed
profile. -/
def quittingTerminalExploitability [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) : ℝ :=
  QuittingBoundaryHolonomy.finitePlayerMax fun who =>
    max 0 (quittingContinuationBestResponseValue reward profile who -
      quittingTerminalPayoff reward profile who)

/-- The holonomy gain at the co-realized prescribed/best-response boundary
of one actual tail is playerwise the literal terminal deviation gain of the
attached phase-switch profile. -/
theorem quittingPhaseSwitch_coRealizedGain_eq_terminalGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan punish : ℕ → ι → PMF Bool) (switch : ℕ) (hswitch : 0 < switch)
    (who : ι) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    (quittingFiniteBoundaryHolonomy reward plan 0 (switch - 1)).coRealizedGain
        (QuittingBoundaryHolonomy.behavioralTailPrescribedBoundary reward punish)
        (QuittingBoundaryHolonomy.behavioralTailEnvelopeBoundary reward punish)
        who =
      quittingContinuationBestResponseValue reward
          (quittingPhaseSwitchProfile reward plan punish switch) who -
        quittingTerminalPayoff reward
          (quittingPhaseSwitchProfile reward plan punish switch) who := by
  unfold QuittingBoundaryHolonomy.coRealizedGain
  rw [quittingPhaseSwitch_bestResponseAt_eq_continuationBestResponse
    reward plan punish switch hswitch who hM hreward]
  change _ - (quittingFiniteBoundaryHolonomy reward plan 0
      (switch - 1)).prescribedAt
        (phaseSwitchPrescribedBoundary reward punish) who = _
  rw [quittingPhaseSwitch_prescribedAt_eq_terminalValue
      reward plan punish switch hswitch who,
    quittingTerminalPayoff_eq_rootSequence_profileLiveRoot,
    quittingProfileLiveRoot_quittingPhaseSwitchProfile]

/-- Consequently the max-affine holonomy's maximum co-realized gain is
exactly the literal maximum positive terminal exploitability of the
concatenated profile. -/
theorem quittingPhaseSwitch_behavioralTailGain_eq_terminalExploitability
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan punish : ℕ → ι → PMF Bool) (switch : ℕ) (hswitch : 0 < switch)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    QuittingBoundaryHolonomy.behavioralTailGain reward
        (quittingFiniteBoundaryHolonomy reward plan 0 (switch - 1)) punish =
      quittingTerminalExploitability reward
        (quittingPhaseSwitchProfile reward plan punish switch) := by
  unfold QuittingBoundaryHolonomy.behavioralTailGain
    QuittingBoundaryHolonomy.maxCoRealizedGain
    quittingTerminalExploitability
  congr 1
  funext who
  rw [quittingPhaseSwitch_coRealizedGain_eq_terminalGain
    reward plan punish switch hswitch who hM hreward]

/-- The named fixed-prefix repair value is exactly the infimum of literal
terminal exploitability over all behavioral tails attached after that prefix.
-/
theorem behavioralTailRepairValue_eq_sInf_phaseSwitch_terminalExploitability
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan : ℕ → ι → PMF Bool) (switch : ℕ) (hswitch : 0 < switch)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    QuittingBoundaryHolonomy.behavioralTailRepairValue reward
        (quittingFiniteBoundaryHolonomy reward plan 0 (switch - 1)) =
      sInf (Set.range fun punish : ℕ → ι → PMF Bool =>
        quittingTerminalExploitability reward
          (quittingPhaseSwitchProfile reward plan punish switch)) := by
  unfold QuittingBoundaryHolonomy.behavioralTailRepairValue
  apply congrArg sInf
  ext value
  constructor
  · rintro ⟨punish, rfl⟩
    refine ⟨punish, ?_⟩
    exact (quittingPhaseSwitch_behavioralTailGain_eq_terminalExploitability
      reward plan punish switch hswitch hM hreward).symm
  · rintro ⟨punish, rfl⟩
    refine ⟨punish, ?_⟩
    exact quittingPhaseSwitch_behavioralTailGain_eq_terminalExploitability
      reward plan punish switch hswitch hM hreward

end GameTheory
