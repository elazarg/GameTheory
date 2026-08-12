/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeObserverAbsentDefectPolarityDispatch

/-!
# Observer-absent rectangle occupation versus its source baseline

A fixed positive owner/outsider rectangle is not itself a unilateral gain.
Writing `q` for the owner's actual Quit probability and `g`, `gC` for the
same outsider action's gain at the actual and owner-forced-Continue rows, the
affine two-face identity gives exactly

`q * rectangle = g - gC`.

The terminal cylinder already contains the missing owner-Quit factor.
Consequently its rectangle occupation is paid either by the positive part of
the outsider's actual source-row gain or by the negative part of `gC`.  The
first term has a named strategic consumer: pure Continue uses the legal
multi-date Continue collector, while pure Quit uses the fixed coalition-atom
decoder.  The second term is the precise remaining baseline sign.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Positive source-row gain occupation of one fixed pure outsider action. -/
def quittingFinitePureActionSourceGainOccupation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (action : Bool) (cutoff : ℕ) : ℝ :=
  ∑ time ∈ Finset.range cutoff,
    let root := quittingProfileLiveRoot reward profile time
    let tail := (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (time + 1))).1
    quittingLiveMass reward profile time *
      max (quittingRootDeviationGain reward tail root who
        (PMF.pure action)) 0

/-- The sole signed loss left by the affine rectangle identity: the fixed
outsider action is worse than the prescribed marginal on the face where the
owner is forced to Continue. -/
def quittingFiniteForcedOwnerContinueFaceLossOccupation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner who : ι) (action : Bool) (cutoff : ℕ) : ℝ :=
  ∑ time ∈ Finset.range cutoff,
    let root := quittingProfileLiveRoot reward profile time
    let tail := (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (time + 1))).1
    quittingLiveMass reward profile time * (root owner false).toReal *
      max (-quittingRootDeviationGain reward tail
        (Function.update root owner (PMF.pure false)) who
          (PMF.pure action)) 0

/-- The owner-face rectangle identity in the form used by the chronological
account: owner-Quit probability times the rectangle is actual gain minus the
owner-Continue-face gain. -/
theorem ownerQuit_mul_quittingOwnerOutsiderDeviationRectangle_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (owner who : ι) (hne : owner ≠ who) (action : Bool) :
    (root owner true).toReal *
        quittingOwnerOutsiderDeviationRectangle
          reward tail root owner who action =
      quittingRootDeviationGain reward tail root who (PMF.pure action) -
        quittingRootDeviationGain reward tail
          (Function.update root owner (PMF.pure false)) who
            (PMF.pure action) := by
  have haffine := quittingRootDeviationGain_eq_ownerEndpointMix
    reward tail root owner who hne (PMF.pure action)
  have hsum := quittingRoot_continueProbability_add_quitProbability root owner
  unfold quittingOwnerOutsiderDeviationRectangle
  have hcontinue : (root owner false).toReal =
      1 - (root owner true).toReal := by linarith
  rw [haffine, hcontinue]
  ring

/-- **One-row source/baseline split.**  The exact terminal cylinder contains
the owner-Quit factor needed by the affine identity.  A positive rectangle
charge is therefore bounded by the actual positive source gain plus the
negative owner-Continue-face baseline, with no division by a hazard. -/
theorem stageRectangleCharge_le_sourceGain_add_continueFaceLoss
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (hne : owner ≠ who) (howner : owner ∈ terminal.val)
    (action : Bool) (time : ℕ) :
    let root := quittingProfileLiveRoot reward profile time
    let tail := (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (time + 1))).1
    quittingStageCoalitionMass reward profile time terminal *
          (root owner false).toReal *
          max (quittingOwnerOutsiderDeviationRectangle
            reward tail root owner who action) 0 ≤
      quittingLiveMass reward profile time *
          max (quittingRootDeviationGain reward tail root who
            (PMF.pure action)) 0 +
        quittingLiveMass reward profile time * (root owner false).toReal *
          max (-quittingRootDeviationGain reward tail
            (Function.update root owner (PMF.pure false)) who
              (PMF.pure action)) 0 := by
  dsimp only
  let root := quittingProfileLiveRoot reward profile time
  let tail := (quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (time + 1))).1
  let mass := quittingStageCoalitionMass reward profile time terminal
  let live := quittingLiveMass reward profile time
  let rectangle := quittingOwnerOutsiderDeviationRectangle
    reward tail root owner who action
  let actual := quittingRootDeviationGain reward tail root who
    (PMF.pure action)
  let continueFace := quittingRootDeviationGain reward tail
    (Function.update root owner (PMF.pure false)) who (PMF.pure action)
  have hmass : mass ≤ live * (root owner true).toReal := by
    dsimp only [mass, live, root]
    rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass]
    exact mul_le_mul_of_nonneg_left
      (quittingRootCoalitionMass_le_quitProbability_of_mem
        root terminal.val owner howner)
      (quittingLiveMass_nonneg reward profile time)
  have hlive0 : 0 ≤ live := quittingLiveMass_nonneg reward profile time
  have hcontinue0 : 0 ≤ (root owner false).toReal := ENNReal.toReal_nonneg
  have hrectangle0 : 0 ≤ max rectangle 0 := le_max_right _ _
  have hscaled := mul_le_mul_of_nonneg_right hmass
    (mul_nonneg hcontinue0 hrectangle0)
  have hid : (root owner true).toReal * rectangle = actual - continueFace := by
    exact ownerQuit_mul_quittingOwnerOutsiderDeviationRectangle_eq
      reward tail root owner who hne action
  have hpositiveDifference : (root owner true).toReal * max rectangle 0 ≤
      max actual 0 + max (-continueFace) 0 := by
    by_cases hrect : rectangle ≤ 0
    · rw [max_eq_right hrect, mul_zero]
      exact add_nonneg (le_max_right _ _) (le_max_right _ _)
    · rw [max_eq_left (le_of_not_ge hrect), hid]
      rw [sub_eq_add_neg]
      exact add_le_add (le_max_left _ _) (le_max_left _ _)
  change mass * (root owner false).toReal * max rectangle 0 ≤
    live * max actual 0 + live * (root owner false).toReal *
      max (-continueFace) 0
  calc
    mass * (root owner false).toReal * max rectangle 0 ≤
        (live * (root owner true).toReal) *
          ((root owner false).toReal * max rectangle 0) := by
      simpa only [mul_assoc] using hscaled
    _ = live * (root owner false).toReal *
        ((root owner true).toReal * max rectangle 0) := by ring
    _ ≤ live * (root owner false).toReal *
        (max actual 0 + max (-continueFace) 0) :=
      mul_le_mul_of_nonneg_left hpositiveDifference
        (mul_nonneg hlive0 hcontinue0)
    _ ≤ live * max actual 0 +
        live * (root owner false).toReal * max (-continueFace) 0 := by
      have hc1 : (root owner false).toReal ≤ 1 := by
        have hsum := quittingRoot_continueProbability_add_quitProbability
          root owner
        have hq0 : 0 ≤ (root owner true).toReal := ENNReal.toReal_nonneg
        linarith
      have hactual0 : 0 ≤ max actual 0 := le_max_right _ _
      have hactualScaled : live * (root owner false).toReal *
          max actual 0 ≤ live * max actual 0 := by
        calc
          live * (root owner false).toReal * max actual 0 =
              live * ((root owner false).toReal * max actual 0) := by ring
          _ ≤ live * max actual 0 :=
            mul_le_mul_of_nonneg_left
              (mul_le_of_le_one_left hactual0 hc1) hlive0
      calc
        live * (root owner false).toReal *
            (max actual 0 + max (-continueFace) 0) =
          live * (root owner false).toReal * max actual 0 +
            live * (root owner false).toReal *
              max (-continueFace) 0 := by ring
        _ ≤ _ := add_le_add hactualScaled (le_refl _)

/-- Summing the exact row account produces the promised sharp finite-window
split. -/
theorem quittingFiniteForcedOwnerRectangleOccupation_le_sourceGain_add_faceLoss
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (hne : owner ≠ who) (howner : owner ∈ terminal.val)
    (action : Bool) (cutoff : ℕ) :
    quittingFiniteForcedOwnerRectangleOccupation reward profile terminal
        owner who action cutoff ≤
      quittingFinitePureActionSourceGainOccupation reward profile who action
          cutoff +
        quittingFiniteForcedOwnerContinueFaceLossOccupation reward profile
          owner who action cutoff := by
  unfold quittingFiniteForcedOwnerRectangleOccupation
    quittingFinitePureActionSourceGainOccupation
    quittingFiniteForcedOwnerContinueFaceLossOccupation
  simp only [if_neg hne.symm]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun time _ =>
    stageRectangleCharge_le_sourceGain_add_continueFaceLoss reward profile
      terminal owner who hne howner action time

theorem max_quittingRootDeviationGain_pure_false_eq_continueDirectedDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    max (quittingRootDeviationGain reward tail root who (PMF.pure false)) 0 =
      quittingRootContinueDirectedDefect reward tail root who := by
  rw [quittingRootDeviationGain_pure_false_eq]
  unfold quittingRootContinueDirectedDefect
  have h := mul_max_of_nonneg
    (-quittingRootEndpointDifference reward tail root who) 0
    (ENNReal.toReal_nonneg : 0 ≤ (root who true).toReal)
  simpa [mul_neg] using h.symm

theorem max_quittingRootDeviationGain_pure_true_eq_quitDirectedDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    max (quittingRootDeviationGain reward tail root who (PMF.pure true)) 0 =
      quittingRootQuitDirectedDefect reward tail root who := by
  rw [quittingRootDeviationGain_pure_true_eq]
  unfold quittingRootQuitDirectedDefect
  have h := mul_max_of_nonneg
    (quittingRootEndpointDifference reward tail root who) 0
    (ENNReal.toReal_nonneg : 0 ≤ (root who false).toReal)
  simpa using h.symm

/-- A fixed pure-Continue source occupation is exactly the existing legal
Continue collector's source-live occupation. -/
theorem exists_behaviorDeviation_gain_ge_pureFalseSourceOccupation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (cutoff : ℕ) :
    ∃ deviation : (quittingGame reward).BehaviorStrategy who,
      quittingFinitePureActionSourceGainOccupation reward profile who false
          cutoff ≤
        quittingTerminalPayoff reward
            (Function.update profile who deviation) who -
          quittingTerminalPayoff reward profile who := by
  obtain ⟨deviation, hgain⟩ :=
    exists_behaviorDeviation_gain_ge_sum_live_continueDirectedDefect
      reward profile who cutoff
  refine ⟨deviation, ?_⟩
  unfold quittingFinitePureActionSourceGainOccupation
  simpa only [quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot,
    quittingTerminalSemanticSpinePayoff_eq_rootSequenceTailVector,
    max_quittingRootDeviationGain_pure_false_eq_continueDirectedDefect] using
    hgain

/-- A fixed pure-Quit source occupation freezes only the opponent-coalition
label; the player label is already supplied by the rectangle. -/
theorem exists_fixedCoalition_of_pureTrueSourceOccupation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (cutoff : ℕ) :
    ∃ coalition ∈ (Finset.univ.erase who).powerset,
      quittingFinitePureActionSourceGainOccupation reward profile who true
          cutoff ≤
        (((Finset.univ.erase who).powerset.card : ℝ) *
          quittingFiniteQuitDefectAtomOccupationAt reward
            (fun time => (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile
                (time + 1))).1)
            (quittingProfileLiveRoot reward profile)
            (quittingLiveMass reward profile) cutoff who coalition) := by
  let tail : ℕ → Payoff ι := fun time =>
    (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (time + 1))).1
  let root := quittingProfileLiveRoot reward profile
  let live := quittingLiveMass reward profile
  let coalitions := (Finset.univ.erase who).powerset
  let atom : Finset ι → ℝ := fun coalition =>
    quittingFiniteQuitDefectAtomOccupationAt reward tail root live cutoff who
      coalition
  have hsource : quittingFinitePureActionSourceGainOccupation reward profile
      who true cutoff ≤ ∑ coalition ∈ coalitions, atom coalition := by
    unfold quittingFinitePureActionSourceGainOccupation atom
      quittingFiniteQuitDefectAtomOccupationAt coalitions tail root live
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro time htime
    dsimp only
    rw [max_quittingRootDeviationGain_pure_true_eq_quitDirectedDefect]
    have hscaled := mul_le_mul_of_nonneg_left
      (quittingRootQuitDirectedDefect_le_sum_atoms reward
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward profile (time + 1))).1
        (quittingProfileLiveRoot reward profile time) who)
      (quittingLiveMass_nonneg reward profile time)
    rw [Finset.mul_sum] at hscaled
    exact hscaled
  obtain ⟨coalition, hcoalition, hmax⟩ := Finset.exists_max_image coalitions
    atom ⟨∅, Finset.empty_mem_powerset _⟩
  have hsum : (∑ candidate ∈ coalitions, atom candidate) ≤
      (coalitions.card : ℝ) * atom coalition := by
    have h := coalitions.sum_le_card_nsmul atom (atom coalition)
      (fun candidate hcandidate => hmax candidate hcandidate)
    simpa [nsmul_eq_mul] using h
  exact ⟨coalition, hcoalition, hsource.trans hsum⟩

/-- **Sharp fixed-rectangle dispatch.**  A quantitative fixed-label rectangle
occupation yields the matching legal Continue deviation, the matching
player's fixed Quit atom, or half of its mass remains in the explicit
owner-Continue-face loss.  No source-matched gain is claimed in the last
branch. -/
theorem exists_sourceConsumer_or_continueFaceLoss_of_rectangleOccupation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (hne : owner ≠ who) (howner : owner ∈ terminal.val)
    (action : Bool) (cutoff : ℕ) (lower : ℝ)
    (hrectangle : lower ≤
      quittingFiniteForcedOwnerRectangleOccupation reward profile terminal
        owner who action cutoff) :
    (action = false ∧
      ∃ deviation : (quittingGame reward).BehaviorStrategy who,
        lower / 2 ≤
          quittingTerminalPayoff reward
              (Function.update profile who deviation) who -
            quittingTerminalPayoff reward profile who) ∨
    (action = true ∧ ∃ coalition ∈ (Finset.univ.erase who).powerset,
      lower / 2 ≤ (((Finset.univ.erase who).powerset.card : ℝ) *
        quittingFiniteQuitDefectAtomOccupationAt reward
          (fun time => (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile
              (time + 1))).1)
          (quittingProfileLiveRoot reward profile)
          (quittingLiveMass reward profile) cutoff who coalition)) ∨
    lower / 2 ≤ quittingFiniteForcedOwnerContinueFaceLossOccupation reward
      profile owner who action cutoff := by
  have haccount :=
    quittingFiniteForcedOwnerRectangleOccupation_le_sourceGain_add_faceLoss
      reward profile terminal owner who hne howner action cutoff
  let source := quittingFinitePureActionSourceGainOccupation reward profile
    who action cutoff
  let loss := quittingFiniteForcedOwnerContinueFaceLossOccupation reward
    profile owner who action cutoff
  have hlowerAccount : lower ≤ source + loss :=
    hrectangle.trans (by simpa only [source, loss] using haccount)
  by_cases hloss : lower / 2 ≤ loss
  · exact Or.inr (Or.inr hloss)
  · have hsource : lower / 2 ≤ source := by linarith
    cases action with
    | false =>
        left
        obtain ⟨deviation, hgain⟩ :=
          exists_behaviorDeviation_gain_ge_pureFalseSourceOccupation
            reward profile who cutoff
        exact ⟨rfl, deviation, hsource.trans (by
          simpa only [source] using hgain)⟩
    | true =>
        right; left
        obtain ⟨coalition, hcoalition, hatom⟩ :=
          exists_fixedCoalition_of_pureTrueSourceOccupation reward profile who
            cutoff
        exact ⟨rfl, coalition, hcoalition, hsource.trans (by
          simpa only [source] using hatom)⟩

/-- **Complete finite-clock baseline dispatch.**  This composes directly with
the observer-absent polarity theorem.  Its former fixed-rectangle alternative
is replaced by a source-matched action consumer or one explicit signed
owner-Continue-face loss.  Thus the last line, not a vague rectangle, is the
sole residual of the observer-absent finite clock. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.observerAbsent_finiteClock_faceLoss
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (habsent : packet.observer ∉ packet.terminal.val)
    (n stop : ℕ) (hstop : packet.quitTime n = some stop)
    (δ : ℝ) (hδ : 0 < δ) :
    let profile := quittingStoppingLawObserverAbsentCarrierProfile packet n
    let owner := quittingStoppingLawObserverAbsentOwner packet
    let charge := quittingStoppingLawObserverAbsentMassLower packet *
      regime.terminalGap
    (∃ deviation : (quittingGame reward).BehaviorStrategy owner,
      charge / 2 - δ ≤
        quittingTerminalPayoff reward
            (Function.update profile owner deviation) owner -
          quittingTerminalPayoff reward profile owner) ∨
    (∃ who : ι, ∃ deviation : (quittingGame reward).BehaviorStrategy who,
      charge / 12 ≤ (Fintype.card ι : ℝ) *
        (quittingTerminalPayoff reward
            (Function.update profile who deviation) who -
          quittingTerminalPayoff reward profile who)) ∨
    (∃ who coalition,
      coalition ∈ (Finset.univ.erase who).powerset ∧
      charge / 12 ≤
        (Fintype.card ι : ℝ) *
          (((Finset.univ.erase who).powerset.card : ℝ) *
            quittingFiniteQuitDefectAtomOccupationAt reward
              (fun time => (quittingTerminalSemanticPair reward
                (quittingAllContinueProfileSpine reward profile
                  (time + 1))).1)
              (quittingProfileLiveRoot reward profile)
              (quittingLiveMass reward profile) stop who coalition)) ∨
    (∃ who action, who ≠ owner ∧
      ((action = false ∧
        ∃ deviation : (quittingGame reward).BehaviorStrategy who,
          charge / (24 * (Fintype.card (ι × Bool) : ℝ)) ≤
            quittingTerminalPayoff reward
                (Function.update profile who deviation) who -
              quittingTerminalPayoff reward profile who) ∨
       (action = true ∧
        ∃ coalition ∈ (Finset.univ.erase who).powerset,
          charge / (24 * (Fintype.card (ι × Bool) : ℝ)) ≤
            (((Finset.univ.erase who).powerset.card : ℝ) *
              quittingFiniteQuitDefectAtomOccupationAt reward
                (fun time => (quittingTerminalSemanticPair reward
                  (quittingAllContinueProfileSpine reward profile
                    (time + 1))).1)
                (quittingProfileLiveRoot reward profile)
                (quittingLiveMass reward profile) stop who coalition)) ∨
       charge / (24 * (Fintype.card (ι × Bool) : ℝ)) ≤
        quittingFiniteForcedOwnerContinueFaceLossOccupation reward profile
          owner who action stop)) := by
  classical
  dsimp only
  let profile := quittingStoppingLawObserverAbsentCarrierProfile packet n
  let owner := quittingStoppingLawObserverAbsentOwner packet
  let charge := quittingStoppingLawObserverAbsentMassLower packet *
    regime.terminalGap
  have hdispatch := packet.observerAbsent_finiteClock_defectPolarity habsent
    n stop hstop δ hδ
  rcases hdispatch with hrefusal | hcontinue | hquit | hrectangle
  · exact Or.inl hrefusal
  · exact Or.inr (Or.inl hcontinue)
  · exact Or.inr (Or.inr (Or.inl hquit))
  · rcases hrectangle with ⟨who, action, hwho, hcharge⟩
    have hlabelCard : 0 < (Fintype.card (ι × Bool) : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr ⟨(owner, false)⟩
    have hrectangleLower :
        charge / (12 * (Fintype.card (ι × Bool) : ℝ)) ≤
          quittingFiniteForcedOwnerRectangleOccupation reward profile
            packet.terminal owner who action stop := by
      apply (div_le_iff₀ (mul_pos (by norm_num) hlabelCard)).2
      calc
        charge = 12 * (charge / 12) := by ring
        _ ≤ 12 * ((Fintype.card (ι × Bool) : ℝ) *
            quittingFiniteForcedOwnerRectangleOccupation reward profile
              packet.terminal owner who action stop) :=
          mul_le_mul_of_nonneg_left hcharge (by norm_num)
        _ = quittingFiniteForcedOwnerRectangleOccupation reward profile
              packet.terminal owner who action stop *
            (12 * (Fintype.card (ι × Bool) : ℝ)) := by ring
    have hrefined :=
      exists_sourceConsumer_or_continueFaceLoss_of_rectangleOccupation
        reward profile packet.terminal owner who hwho.symm
        (quittingStoppingLawObserverAbsentOwner_mem packet) action stop
        (charge / (12 * (Fintype.card (ι × Bool) : ℝ))) hrectangleLower
    right; right; right
    refine ⟨who, action, hwho, ?_⟩
    simpa only [show
      (charge / (12 * (Fintype.card (ι × Bool) : ℝ))) / 2 =
        charge / (24 * (Fintype.card (ι × Bool) : ℝ)) by ring] using hrefined

end GameTheory
