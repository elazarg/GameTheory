/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import experiments.quitting.PositiveRectangleResetFaceLawCausalDispatch
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeNegativeCollisionAtomicDispatch

/-!
# Negative rectangles compensate on the zero-debt endpoint

A negative-reward rectangle stores the displayed terminal mass on the source
endpoint, while the observer's vanishing debt belongs to the target endpoint.
This looks like a fatal endpoint mismatch.  Conservation of total probability
shows that it has an exact dual form: every fixed loss of the displayed source
atom forces a fixed gain of some *other* outcome on the target endpoint.

After finite-label extraction, the compensating target outcome is either
`Never` or one fixed absorbing coalition.  Hence the sign asymmetry produces
an exact harmonic/finite dichotomy on the correct zero-debt endpoint.  This
does not assert that the compensating absorbing coalition has the original
label or strategic sign.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Losing one coordinate between two finite probability vectors forces
compensating mass on another coordinate of the first vector. -/
theorem exists_compensating_probability_coordinate
    {α : Type} [Fintype α] [DecidableEq α]
    (first second : α → ℝ) (target other : α) (hother : other ≠ target)
    (hfirst0 : ∀ x, 0 ≤ first x) (hsecond0 : ∀ x, 0 ≤ second x)
    (hfirstSum : ∑ x, first x = 1) (hsecondSum : ∑ x, second x = 1)
    (lower : ℝ) (hloss : lower ≤ second target - first target) :
    ∃ outcome, outcome ≠ target ∧
      lower ≤ (Fintype.card α : ℝ) * first outcome := by
  classical
  let candidates := (Finset.univ : Finset α).erase target
  have hcandidates : candidates.Nonempty := by
    refine ⟨other, ?_⟩
    simp [candidates, hother]
  have hsumDifference :
      (∑ x ∈ candidates, (first x - second x)) =
        second target - first target := by
    have hfirstErase : ∑ x ∈ candidates, first x = 1 - first target := by
      rw [show ∑ x ∈ candidates, first x =
          (∑ x, first x) - first target by
        dsimp only [candidates]
        linarith [Finset.sum_erase_add Finset.univ first
          (Finset.mem_univ target)] , hfirstSum]
    have hsecondErase : ∑ x ∈ candidates, second x = 1 - second target := by
      rw [show ∑ x ∈ candidates, second x =
          (∑ x, second x) - second target by
        dsimp only [candidates]
        linarith [Finset.sum_erase_add Finset.univ second
          (Finset.mem_univ target)] , hsecondSum]
    rw [Finset.sum_sub_distrib, hfirstErase, hsecondErase]
    ring
  have hlowerSum : lower ≤ ∑ x ∈ candidates, first x := by
    calc
      lower ≤ second target - first target := hloss
      _ = ∑ x ∈ candidates, (first x - second x) := hsumDifference.symm
      _ ≤ ∑ x ∈ candidates, first x := by
        apply Finset.sum_le_sum
        intro x _
        linarith [hsecond0 x]
  obtain ⟨outcome, houtcome, hmax⟩ :=
    Finset.exists_max_image candidates first hcandidates
  have hsumMax : (∑ x ∈ candidates, first x) ≤
      (candidates.card : ℝ) * first outcome := by
    have h := candidates.sum_le_card_nsmul first (first outcome)
      (fun x hx => hmax x hx)
    simpa [nsmul_eq_mul] using h
  have hcardLe : (candidates.card : ℝ) ≤ Fintype.card α := by
    exact_mod_cast Finset.card_le_univ candidates
  have houtcome0 : 0 ≤ first outcome := hfirst0 outcome
  refine ⟨outcome, (Finset.mem_erase.mp houtcome).1, ?_⟩
  exact hlowerSum.trans (hcardLe |> fun hcard =>
    hsumMax.trans (mul_le_mul_of_nonneg_right hcard houtcome0))

/-- The quantitative target-endpoint compensation scale. -/
def quittingStoppingLawNegativeCompensationLower
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier) : ℝ :=
  quittingStoppingLawNegativeCollisionMassLower packet /
    (Fintype.card (QuittingTerminalOutcome ι) : ℝ)

/-- **One negative rectangle has compensating target mass.** -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.exists_negativeObserver_targetCompensation
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (hnegative : reward packet.terminal packet.observer < 0) (n : ℕ) :
    ∃ outcome : QuittingTerminalOutcome ι,
      outcome ≠ some packet.terminal ∧
      quittingStoppingLawNegativeCompensationLower packet ≤
        quittingTerminalOutcomeMass reward
          (quittingStoppingLawRectangleTargetObserverProfile packet n)
          outcome := by
  classical
  let card : ℝ := Fintype.card (QuittingTerminalOutcome ι)
  let M := quittingRewardBound reward
  let targetProfile := quittingStoppingLawRectangleTargetObserverProfile packet n
  let sourceProfile := quittingStoppingLawRectangleSourceProfile packet n
  let targetMass := quittingTerminalOutcomeMass reward targetProfile
  let sourceMass := quittingTerminalOutcomeMass reward sourceProfile
  let selected : QuittingTerminalOutcome ι := some packet.terminal
  have hcard : 0 < card := by
    dsimp only [card]
    exact_mod_cast Fintype.card_pos
  have hMpos : 0 < M := packet.rewardBound_pos_of_negativeCollision hnegative
  have hbound := packet.atom_bound n
  have hsourceUpdate : Function.update
      (frontier.profiles (frontier.subseq (packet.rank n))) packet.mover.1
      (frontier.profiles (frontier.subseq (packet.rank n)) packet.mover.1) =
        frontier.profiles (frontier.subseq (packet.rank n)) :=
    Function.update_eq_self _ _
  rw [hsourceUpdate] at hbound
  change packet.charge / 4 ≤ card *
      ((targetMass selected - sourceMass selected) *
        reward packet.terminal packet.observer) at hbound
  have hreversal :
      (targetMass selected - sourceMass selected) *
          reward packet.terminal packet.observer =
        (sourceMass selected - targetMass selected) *
          (-reward packet.terminal packet.observer) := by ring
  rw [hreversal] at hbound
  have hrewardLe : -reward packet.terminal packet.observer ≤ M := by
    rw [← abs_of_neg hnegative]
    exact abs_reward_le_quittingRewardBound reward packet.terminal
      packet.observer
  have hdiff0 : 0 ≤ sourceMass selected - targetMass selected := by
    by_contra hnot
    have hneg : sourceMass selected - targetMass selected < 0 :=
      lt_of_not_ge hnot
    have hproductNeg :
        (sourceMass selected - targetMass selected) *
            (-reward packet.terminal packet.observer) < 0 :=
      mul_neg_of_neg_of_pos hneg (neg_pos.mpr hnegative)
    have hchargePos : 0 < packet.charge / 4 :=
      div_pos packet.charge_pos (by norm_num)
    nlinarith
  have hscaled : packet.charge / 4 ≤ card *
      ((sourceMass selected - targetMass selected) * M) := by
    exact hbound.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hrewardLe hdiff0) hcard.le)
  have hloss : quittingStoppingLawNegativeCollisionMassLower packet ≤
      sourceMass selected - targetMass selected := by
    unfold quittingStoppingLawNegativeCollisionMassLower
    apply (div_le_iff₀ (mul_pos hcard hMpos)).2
    calc
      packet.charge / 4 ≤ card *
          ((sourceMass selected - targetMass selected) * M) := hscaled
      _ = (sourceMass selected - targetMass selected) * (card * M) := by ring
  have htargetSimplex :=
    quittingTerminalOutcomeMass_mem_stdSimplex reward targetProfile
  have hsourceSimplex :=
    quittingTerminalOutcomeMass_mem_stdSimplex reward sourceProfile
  obtain ⟨outcome, houtcome, hcompensation⟩ :=
    exists_compensating_probability_coordinate
      targetMass sourceMass selected none (by simp)
      htargetSimplex.1 hsourceSimplex.1 htargetSimplex.2 hsourceSimplex.2
      (quittingStoppingLawNegativeCollisionMassLower packet) hloss
  refine ⟨outcome, houtcome, ?_⟩
  unfold quittingStoppingLawNegativeCompensationLower
  exact (div_le_iff₀ hcard).2 (by
    simpa only [targetProfile, targetMass, card, mul_comm] using hcompensation)

/-- **Fixed compensating outcome.**  Along a subsequence, one outcome
different from the lost terminal label carries a uniform amount of target
mass. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.exists_fixed_negativeObserver_targetCompensation
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (hnegative : reward packet.terminal packet.observer < 0) :
    ∃ outcome : QuittingTerminalOutcome ι,
      outcome ≠ some packet.terminal ∧
      ∃ subseq : ℕ → ℕ,
        StrictMono subseq ∧
        ∀ rank,
          quittingStoppingLawNegativeCompensationLower packet ≤
            quittingTerminalOutcomeMass reward
              (quittingStoppingLawRectangleTargetObserverProfile packet
                (subseq rank)) outcome := by
  classical
  choose outcome houtcome hmass using
    fun n => packet.exists_negativeObserver_targetCompensation hnegative n
  have hfrequent : ∃ fixed : QuittingTerminalOutcome ι,
      ∃ᶠ n in atTop, outcome n = fixed := by
    by_contra hnot
    push Not at hnot
    have hall : ∀ᶠ n in atTop, ∀ fixed : QuittingTerminalOutcome ι,
        outcome n ≠ fixed := by
      rw [eventually_all]
      exact hnot
    obtain ⟨n, hn⟩ := hall.exists
    exact hn (outcome n) rfl
  obtain ⟨fixed, hfixed⟩ := hfrequent
  obtain ⟨subseq, hsubseq, hfixedEq⟩ :=
    extraction_of_frequently_atTop hfixed
  refine ⟨fixed, ?_, subseq, hsubseq, ?_⟩
  · rw [← hfixedEq 0]
    exact houtcome (subseq 0)
  · intro rank
    rw [← hfixedEq rank]
    exact hmass (subseq rank)

/-- **Negative orientation = harmonic or finite reset-face law.**  The
compensating target outcome either is `Never`, or it is one fixed absorbing
coalition.  In both cases it occurs on literal target endpoints whose observer
debt tends to zero. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.negativeObserver_harmonic_or_absorbingResetFaceCompensation
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (hnegative : reward packet.terminal packet.observer < 0) :
    (∃ subseq : ℕ → ℕ,
      StrictMono subseq ∧
      (∀ rank, packet.quitTime (subseq rank) = none) ∧
      ∀ rank,
        quittingStoppingLawNegativeCompensationLower packet ≤
          quittingTerminalOutcomeMass reward
            (quittingStoppingLawRectangleTargetObserverProfile packet
              (subseq rank)) none) ∨
    ∃ terminal : {S : Finset ι // S.Nonempty},
      terminal ≠ packet.terminal ∧
      ∃ subseq : ℕ → ℕ,
        StrictMono subseq ∧
        (∀ rank,
          quittingStoppingLawNegativeCompensationLower packet ≤
            quittingTerminalOutcomeMass reward
              (quittingStoppingLawRectangleTargetObserverProfile packet
                (subseq rank)) (some terminal)) ∧
        Tendsto (fun rank ↦
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (quittingStoppingLawRectangleTargetObserverProfile packet
                (subseq rank))) packet.observer) atTop (nhds 0) := by
  obtain ⟨outcome, houtcome, subseq, hsubseq, hmass⟩ :=
    packet.exists_fixed_negativeObserver_targetCompensation hnegative
  cases outcome with
  | none =>
      left
      refine ⟨subseq, hsubseq, ?_, hmass⟩
      intro rank
      cases htime : packet.quitTime (subseq rank) with
      | none => rfl
      | some time =>
          have hzero : quittingTerminalOutcomeMass reward
              (quittingStoppingLawRectangleTargetObserverProfile packet
                (subseq rank)) none = 0 := by
            change quittingLiveMassLimit reward _ = 0
            rw [quittingStoppingLawRectangleTargetObserverProfile, htime]
            exact quittingLiveMassLimit_update_pureTimeBehaviorStrategy_some_eq_zero
              reward (quittingStoppingLawRectangleTargetProfile packet
                (subseq rank)) packet.observer time
          have hlowerPos : 0 <
              quittingStoppingLawNegativeCompensationLower packet := by
            unfold quittingStoppingLawNegativeCompensationLower
            exact div_pos (packet.negativeCollisionMassLower_pos hnegative)
              (by positivity)
          have hmassRank := hmass rank
          rw [hzero] at hmassRank
          exact False.elim ((not_lt_of_ge hmassRank) hlowerPos)
  | some terminal =>
      right
      have hterminalNe : terminal ≠ packet.terminal := by
        intro heq
        subst terminal
        exact houtcome rfl
      refine ⟨terminal, hterminalNe, subseq, hsubseq, hmass, ?_⟩
      exact packet.observer_debt_tendsto_zero.comp hsubseq.tendsto_atTop

/-- **Absorbing compensation has a law-preserving reset-face limit.** -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.exists_negativeObserver_absorbingCompensationResetFaceLawPoint
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (terminal : {S : Finset ι // S.Nonempty})
    (subseq : ℕ → ℕ)
    (hmass : ∀ rank,
      quittingStoppingLawNegativeCompensationLower packet ≤
        quittingTerminalOutcomeMass reward
          (quittingStoppingLawRectangleTargetObserverProfile packet
            (subseq rank)) (some terminal))
    (hdebt : Tendsto (fun rank ↦
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingStoppingLawRectangleTargetObserverProfile packet
            (subseq rank))) packet.observer) atTop (nhds 0)) :
    ∃ point : QuittingTerminalSemanticLawPoint ι,
      point ∈ quittingTerminalSemanticLawCarrier reward ∧
      quittingTerminalSemanticDebt point.1 packet.observer = 0 ∧
      quittingStoppingLawNegativeCompensationLower packet ≤
        point.2 (some terminal) := by
  let endpoint : ℕ → QuittingTerminalSemanticLawPoint ι := fun rank ↦
    (quittingTerminalSemanticPair reward
        (quittingStoppingLawRectangleTargetObserverProfile packet
          (subseq rank)),
      quittingTerminalOutcomeMass reward
        (quittingStoppingLawRectangleTargetObserverProfile packet
          (subseq rank)))
  have hendpointMem : ∀ rank,
      endpoint rank ∈ quittingTerminalSemanticLawCarrier reward := by
    intro rank
    exact quittingTerminalSemanticLawPoint_mem_carrier reward _
  obtain ⟨point, hpoint, selected, hselected, hlimit⟩ :=
    (quittingTerminalSemanticLawCarrier_isCompact reward
      (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward)).tendsto_subseq hendpointMem
  have hdebtLimit :=
    ((continuous_quittingTerminalSemanticDebt packet.observer).comp
      continuous_fst).tendsto point |>.comp hlimit
  have hdebtSub := hdebt.comp hselected.tendsto_atTop
  have hreset : quittingTerminalSemanticDebt point.1 packet.observer = 0 := by
    change Tendsto (fun rank ↦
      quittingTerminalSemanticDebt (endpoint (selected rank)).1
        packet.observer) atTop
      (nhds (quittingTerminalSemanticDebt point.1 packet.observer))
      at hdebtLimit
    exact tendsto_nhds_unique hdebtLimit hdebtSub
  have hmassLimit : Tendsto (fun rank ↦
      (endpoint (selected rank)).2 (some terminal)) atTop
      (nhds (point.2 (some terminal))) :=
    ((continuous_apply (some terminal)).comp continuous_snd).tendsto point
      |>.comp hlimit
  have hpointMass : quittingStoppingLawNegativeCompensationLower packet ≤
      point.2 (some terminal) := by
    apply ge_of_tendsto hmassLimit
    exact Eventually.of_forall fun rank ↦ by
      simpa only [endpoint] using hmass (selected rank)
  exact ⟨point, hpoint, hreset, hpointMass⟩

/-- **Negative absorbing collisions concentrate on the reset face.**  Once
the compensating outcome is a nonsingleton coalition, its zero-debt endpoint
law has recurrent same-profile stage representatives; the diffuse branch is
impossible. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.exists_negativeObserver_absorbingCompensationConcentratedPacket
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (hnegative : reward packet.terminal packet.observer < 0)
    (terminal : {S : Finset ι // S.Nonempty})
    (hcollision : 1 < terminal.val.card)
    (subseq : ℕ → ℕ) (hsubseq : StrictMono subseq)
    (hmass : ∀ rank,
      quittingStoppingLawNegativeCompensationLower packet ≤
        quittingTerminalOutcomeMass reward
          (quittingStoppingLawRectangleTargetObserverProfile packet
            (subseq rank)) (some terminal)) :
    ∃ point : QuittingTerminalSemanticLawPoint ι,
      point ∈ quittingTerminalSemanticLawCarrier reward ∧
      quittingTerminalSemanticDebt point.1 packet.observer = 0 ∧
      0 < point.2 (some terminal) ∧
      ∃ profiles : ℕ → (quittingGame reward).BehaviorProfile,
      ∃ cutoff : ℕ → ℕ, ∃ scale : ℕ → ℝ,
      ∃ fixedOther : ι,
      ∃ exact : {S : Finset ι // S.Nonempty},
        Tendsto (fun n ↦
          (quittingTerminalSemanticPair reward (profiles n),
            quittingTerminalOutcomeMass reward (profiles n)))
          atTop (nhds point) ∧
        (∀ n, 0 < scale n) ∧
        Tendsto scale atTop (nhds 0) ∧
        fixedOther ≠ packet.observer ∧ fixedOther ∈ exact.val ∧
        Nonempty (QuittingReprojectionConcentratedPacket
          reward profiles packet.observer exact cutoff scale) := by
  have hdebt := packet.observer_debt_tendsto_zero.comp hsubseq.tendsto_atTop
  obtain ⟨point, hpoint, hreset, hpointMass⟩ :=
    packet.exists_negativeObserver_absorbingCompensationResetFaceLawPoint
      terminal subseq hmass hdebt
  have hlowerPos : 0 < quittingStoppingLawNegativeCompensationLower packet := by
    unfold quittingStoppingLawNegativeCompensationLower
    exact div_pos (packet.negativeCollisionMassLower_pos hnegative)
      (by positivity)
  have hpointMassPos : 0 < point.2 (some terminal) :=
    hlowerPos.trans_le hpointMass
  obtain ⟨profiles, cutoff, scale, fixedOther, exact, hprofiles,
      hscalePos, hscaleZero, hfixedNe, hfixedMem, hconcentrated⟩ :=
    exists_resetFaceLaw_concentratedPacket_of_collision
      reward point packet.observer terminal
        (quittingRewardBound_nonneg reward)
        (abs_reward_le_quittingRewardBound reward) hpoint hreset
          hpointMassPos hcollision
  exact ⟨point, hpoint, hreset, hpointMassPos, profiles, cutoff, scale,
    fixedOther, exact, hprofiles, hscalePos, hscaleZero, hfixedNe,
    hfixedMem, hconcentrated⟩

end GameTheory
