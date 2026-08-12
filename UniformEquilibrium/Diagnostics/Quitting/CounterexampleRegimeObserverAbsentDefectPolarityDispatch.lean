/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticForcedOwnerRefusalCollector
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticForcedOwnerWallRectangleCurvature
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticEndpointDefectPolarity

/-!
# Observer-absent forced-owner defect polarity dispatch

The finite observer-absent wall has one residual after forced-owner refusal is
collected: the aggregate Nash defect seen after counterfactually forcing a
fixed terminal owner to Quit.  The forced-owner rectangle identity moves half
of this charge to the actual literal row or to a positive same-witness square.

Actual-row defect is then split by endpoint polarity.  Continue-directed
occupation is collected by one legal behavioral deviation after freezing the
player.  Quit-directed occupation is atomized into one fixed player/coalition
label.  The only new residual is one fixed outsider/action rectangle
occupation, with its exact chronological mass and owner-Continue factor.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The prescribed payoff of the shifted literal profile is exactly the tail
vector of the original profile's canonical live-root sequence. -/
theorem quittingTerminalSemanticSpinePayoff_eq_rootSequenceTailVector
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (start : ℕ) :
    (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile start)).1 =
      quittingRootSequenceTailVector reward
        (quittingProfileLiveRoot reward profile) start := by
  funext who
  unfold quittingTerminalSemanticPair quittingRootSequenceTailVector
  change quittingTerminalPayoff reward
      (quittingAllContinueProfileSpine reward profile start) who = _
  rw [quittingTerminalPayoff_eq_rootSequence_profileLiveRoot]
  have hroots : quittingProfileLiveRoot reward
        (quittingAllContinueProfileSpine reward profile start) =
      fun time => quittingProfileLiveRoot reward profile (start + time) := by
    funext time player
    unfold quittingProfileLiveRoot
    exact quittingAllContinueProfileSpine_apply_liveHist
      reward profile start player time
  rw [hroots]
  exact (quittingRootSequenceTerminalValue_eq_shift reward
    (quittingProfileLiveRoot reward profile) who start).symm

/-- Actual live-row total coordinate-defect occupation on a finite window. -/
def quittingFiniteActualDefectOccupation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (cutoff : ℕ) : ℝ :=
  ∑ time ∈ Finset.range cutoff,
    quittingLiveMass reward profile time *
      ∑ who,
        quittingRootCoordinateNashDefect reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile (time + 1))).1
          (quittingProfileLiveRoot reward profile time) who

/-- Continue-directed part of the actual finite defect occupation. -/
def quittingFiniteActualContinueDefectOccupation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (cutoff : ℕ) : ℝ :=
  ∑ time ∈ Finset.range cutoff,
    quittingLiveMass reward profile time *
      ∑ who,
        quittingRootContinueDirectedDefect reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile (time + 1))).1
          (quittingProfileLiveRoot reward profile time) who

/-- Continue-directed occupation of one fixed player. -/
def quittingFiniteActualContinueDefectOccupationAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (cutoff : ℕ) : ℝ :=
  ∑ time ∈ Finset.range cutoff,
    quittingLiveMass reward profile time *
      quittingRootContinueDirectedDefect reward
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward profile (time + 1))).1
        (quittingProfileLiveRoot reward profile time) who

/-- Quit-directed part of the actual finite defect occupation. -/
def quittingFiniteActualQuitDefectOccupation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (cutoff : ℕ) : ℝ :=
  quittingFiniteQuitDirectedDefectOccupation reward
    (fun time =>
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (time + 1))).1)
    (quittingProfileLiveRoot reward profile)
    (quittingLiveMass reward profile) cutoff

/-- One fixed outsider/action same-witness rectangle occupation. -/
def quittingFiniteForcedOwnerRectangleOccupation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (action : Bool) (cutoff : ℕ) : ℝ :=
  ∑ time ∈ Finset.range cutoff,
    if who = owner then 0 else
      let root := quittingProfileLiveRoot reward profile time
      let tail := (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (time + 1))).1
      quittingStageCoalitionMass reward profile time terminal *
        (root owner false).toReal *
          max (quittingOwnerOutsiderDeviationRectangle
            reward tail root owner who action) 0

/-- The sum of all positive owner/outsider rectangles at one literal row. -/
def quittingForcedOwnerRectangleRowTotal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner : ι) (time : ℕ) : ℝ :=
  ∑ label : ι × Bool,
    if label.1 = owner then 0 else
      let root := quittingProfileLiveRoot reward profile time
      let tail := (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (time + 1))).1
      quittingStageCoalitionMass reward profile time terminal *
        (root owner false).toReal *
          max (quittingOwnerOutsiderDeviationRectangle
            reward tail root owner label.1 label.2) 0

/-- Total positive same-witness rectangle occupation, before freezing its
outsider and pure action labels. -/
def quittingFiniteForcedOwnerRectangleTotal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner : ι) (cutoff : ℕ) : ℝ :=
  ∑ label : ι × Bool,
    quittingFiniteForcedOwnerRectangleOccupation reward profile terminal
      owner label.1 label.2 cutoff

/-- The actual defect occupation is exactly the sum of its two endpoint
polarities. -/
theorem quittingFiniteActualDefectOccupation_eq_polaritySum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (cutoff : ℕ) :
    quittingFiniteActualDefectOccupation reward profile cutoff =
      quittingFiniteActualContinueDefectOccupation reward profile cutoff +
        quittingFiniteActualQuitDefectOccupation reward profile cutoff := by
  unfold quittingFiniteActualDefectOccupation
    quittingFiniteActualContinueDefectOccupation
    quittingFiniteActualQuitDefectOccupation
    quittingFiniteQuitDirectedDefectOccupation
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro time _
  rw [← mul_add, ← Finset.sum_add_distrib]
  apply congrArg (fun value : ℝ =>
    quittingLiveMass reward profile time * value)
  apply Finset.sum_congr rfl
  intro who _
  exact quittingRootCoordinateNashDefect_eq_polaritySum reward
    (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (time + 1))).1
    (quittingProfileLiveRoot reward profile time) who

/-- The rectangle row totals sum to the fixed-label rectangle occupation. -/
theorem sum_quittingForcedOwnerRectangleRowTotal_eq_total
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner : ι) (cutoff : ℕ) :
    (∑ time ∈ Finset.range cutoff,
        quittingForcedOwnerRectangleRowTotal reward profile terminal owner time) =
      quittingFiniteForcedOwnerRectangleTotal reward profile terminal owner
        cutoff := by
  unfold quittingForcedOwnerRectangleRowTotal
    quittingFiniteForcedOwnerRectangleTotal
    quittingFiniteForcedOwnerRectangleOccupation
  rw [Finset.sum_comm]

/-- Freeze one player in a positive Continue-directed occupation.  The
selected player's full occupation is collected by one legal deviation. -/
theorem exists_fixedPlayer_behaviorDeviation_of_continueOccupation
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (cutoff : ℕ) :
    ∃ who : ι, ∃ deviation : (quittingGame reward).BehaviorStrategy who,
      quittingFiniteActualContinueDefectOccupation reward profile cutoff ≤
        (Fintype.card ι : ℝ) *
          (quittingTerminalPayoff reward
              (Function.update profile who deviation) who -
            quittingTerminalPayoff reward profile who) := by
  let occupation : ι → ℝ := fun who =>
    quittingFiniteActualContinueDefectOccupationAt reward profile who cutoff
  obtain ⟨who, _hwho, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset ι) occupation Finset.univ_nonempty
  obtain ⟨deviation, hcollect⟩ :=
    exists_behaviorDeviation_gain_ge_sum_live_continueDirectedDefect
      reward profile who cutoff
  have hoccupation : occupation who ≤
      quittingTerminalPayoff reward
          (Function.update profile who deviation) who -
        quittingTerminalPayoff reward profile who := by
    unfold occupation quittingFiniteActualContinueDefectOccupationAt
    simpa only [quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot,
      quittingTerminalSemanticSpinePayoff_eq_rootSequenceTailVector] using
      hcollect
  have hsum : quittingFiniteActualContinueDefectOccupation reward profile cutoff =
      ∑ player, occupation player := by
    unfold quittingFiniteActualContinueDefectOccupation occupation
      quittingFiniteActualContinueDefectOccupationAt
    rw [Finset.sum_comm]
    simp_rw [Finset.mul_sum]
  have hsumLe : (∑ player, occupation player) ≤
      (Fintype.card ι : ℝ) * occupation who := by
    have h := (Finset.univ : Finset ι).sum_le_card_nsmul occupation
      (occupation who) (fun player hplayer => hmax player hplayer)
    simpa [nsmul_eq_mul] using h
  refine ⟨who, deviation, ?_⟩
  rw [hsum]
  exact hsumLe.trans (mul_le_mul_of_nonneg_left hoccupation (by positivity))

/-- Freeze one outsider/action label in the positive rectangle occupation. -/
theorem exists_fixed_forcedOwnerRectangleOccupation
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner : ι) (cutoff : ℕ)
    (hpositive : 0 < quittingFiniteForcedOwnerRectangleTotal reward profile
      terminal owner cutoff) :
    ∃ who action, who ≠ owner ∧
      quittingFiniteForcedOwnerRectangleTotal reward profile terminal owner
          cutoff ≤
        (Fintype.card (ι × Bool) : ℝ) *
          quittingFiniteForcedOwnerRectangleOccupation reward profile terminal
            owner who action cutoff := by
  let occupation : ι × Bool → ℝ := fun label =>
    quittingFiniteForcedOwnerRectangleOccupation reward profile terminal
      owner label.1 label.2 cutoff
  obtain ⟨label, _hlabel, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (ι × Bool)) occupation Finset.univ_nonempty
  have hsumLe : (∑ candidate, occupation candidate) ≤
      (Fintype.card (ι × Bool) : ℝ) * occupation label := by
    have h := (Finset.univ : Finset (ι × Bool)).sum_le_card_nsmul occupation
      (occupation label) (fun candidate hcandidate => hmax candidate hcandidate)
    simpa [nsmul_eq_mul] using h
  have hne : label.1 ≠ owner := by
    intro heq
    have hzero : occupation label = 0 := by
      unfold occupation quittingFiniteForcedOwnerRectangleOccupation
      simp [heq]
    have hallZero : ∀ candidate, occupation candidate ≤ 0 := by
      intro candidate
      simpa only [hzero] using hmax candidate (Finset.mem_univ candidate)
    have htotalNonneg : 0 ≤ ∑ candidate, occupation candidate := by
      apply Finset.sum_nonneg
      intro candidate _
      unfold occupation quittingFiniteForcedOwnerRectangleOccupation
      apply Finset.sum_nonneg
      intro time _
      split_ifs
      · exact le_rfl
      · exact mul_nonneg
          (mul_nonneg
            (quittingStageCoalitionMass_nonneg reward profile time terminal)
            ENNReal.toReal_nonneg)
          (le_max_right _ 0)
    have htotalZero : (∑ candidate, occupation candidate) = 0 :=
      le_antisymm (Finset.sum_nonpos fun candidate _ => hallZero candidate)
        htotalNonneg
    have : (∑ candidate, occupation candidate) =
        quittingFiniteForcedOwnerRectangleTotal reward profile terminal owner
          cutoff := by rfl
    have hbad : 0 < ∑ candidate, occupation candidate := by
      rw [this]
      exact hpositive
    rw [htotalZero] at hbad
    exact (lt_irrefl 0) hbad
  refine ⟨label.1, label.2, hne, ?_⟩
  simpa [quittingFiniteForcedOwnerRectangleTotal, occupation] using hsumLe

/-- **One-row curvature consumption.**  Half of the actual terminal-cylinder
mass times the forced-owner outsider defect is already actual-row defect or
positive same-witness rectangle mass on that same cylinder. -/
theorem stageCoalitionMass_mul_forcedOwnerDefect_half_le_actual_add_rectangle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner : ι) (howner : owner ∈ terminal.val) (time : ℕ) :
    let root := quittingProfileLiveRoot reward profile time
    let tail := (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (time + 1))).1
    quittingStageCoalitionMass reward profile time terminal *
          quittingForcedOwnerOutsiderDefect reward
            (Function.update root owner (PMF.pure true)) owner / 2 ≤
      quittingLiveMass reward profile time *
          ∑ who, quittingRootCoordinateNashDefect reward tail root who +
        quittingForcedOwnerRectangleRowTotal reward profile terminal owner time := by
  dsimp only
  let root := quittingProfileLiveRoot reward profile time
  let tail := (quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (time + 1))).1
  let forcedRoot := Function.update root owner (PMF.pure true)
  let forcedDefect := quittingForcedOwnerOutsiderDefect reward forcedRoot owner
  let mass := quittingStageCoalitionMass reward profile time terminal
  have hforced0 : 0 ≤ forcedDefect :=
    quittingForcedOwnerOutsiderDefect_nonneg reward forcedRoot owner
  have hmass0 : 0 ≤ mass :=
    quittingStageCoalitionMass_nonneg reward profile time terminal
  have hlive0 : 0 ≤ quittingLiveMass reward profile time :=
    quittingLiveMass_nonneg reward profile time
  have hactual0 : 0 ≤ quittingLiveMass reward profile time *
      ∑ who, quittingRootCoordinateNashDefect reward tail root who := by
    exact mul_nonneg hlive0 (Finset.sum_nonneg fun who _ =>
      quittingRootCoordinateNashDefect_nonneg reward tail root who)
  have hrectangle0 : 0 ≤
      quittingForcedOwnerRectangleRowTotal reward profile terminal owner time := by
    unfold quittingForcedOwnerRectangleRowTotal
    apply Finset.sum_nonneg
    intro label _
    split_ifs
    · exact le_rfl
    · exact mul_nonneg
        (mul_nonneg hmass0 ENNReal.toReal_nonneg)
        (le_max_right _ 0)
  change mass * forcedDefect / 2 ≤
    quittingLiveMass reward profile time *
        ∑ who, quittingRootCoordinateNashDefect reward tail root who +
      quittingForcedOwnerRectangleRowTotal reward profile terminal owner time
  rcases hforced0.eq_or_lt with hzero | hpositive
  · rw [← hzero, mul_zero, zero_div]
    exact add_nonneg hactual0 hrectangle0
  · have hownerForced : forcedRoot owner = PMF.pure true := by
      simp [forcedRoot]
    obtain ⟨who, hwho, hcoordinate⟩ :=
      exists_outsider_coordinateNashDefect_ge_of_forcedOwnerDefect_ge
        reward tail forcedRoot owner hownerForced hpositive (le_refl forcedDefect)
    have hweighted : mass * forcedDefect ≤ mass *
        quittingRootCoordinateNashDefect reward tail forcedRoot who :=
      mul_le_mul_of_nonneg_left hcoordinate hmass0
    obtain ⟨action, _hrealize, halt⟩ :=
      stageCoalitionMass_gap_actualDefect_or_rectangle reward profile tail time
        owner who hwho.symm terminal howner forcedDefect hweighted
    rcases halt with hactual | hrectangle
    · have hsingle : quittingRootCoordinateNashDefect reward tail root who ≤
          ∑ player, quittingRootCoordinateNashDefect reward tail root player :=
        Finset.single_le_sum
          (fun player _ =>
            quittingRootCoordinateNashDefect_nonneg reward tail root player)
          (Finset.mem_univ who)
      have hscaled := mul_le_mul_of_nonneg_left hsingle hlive0
      exact hactual.trans (hscaled.trans (le_add_of_nonneg_right hrectangle0))
    · let rectangle := quittingOwnerOutsiderDeviationRectangle
        reward tail root owner who action
      have hrectangleDef : rectangle =
          quittingRootDeviationGain reward tail
              (Function.update root owner (PMF.pure true)) who
                (PMF.pure action) -
            quittingRootDeviationGain reward tail
              (Function.update root owner (PMF.pure false)) who
                (PMF.pure action) := rfl
      have hfactor0 : 0 ≤ mass * (root owner false).toReal :=
        mul_nonneg hmass0 ENNReal.toReal_nonneg
      have hpositivePart : mass * (root owner false).toReal * rectangle ≤
          mass * (root owner false).toReal * max rectangle 0 :=
        mul_le_mul_of_nonneg_left (le_max_left rectangle 0) hfactor0
      have hlabel : mass * (root owner false).toReal * max rectangle 0 ≤
          quittingForcedOwnerRectangleRowTotal reward profile terminal owner
            time := by
        unfold quittingForcedOwnerRectangleRowTotal
        have hterm0 : ∀ label : ι × Bool, 0 ≤
            (if label.1 = owner then 0 else
              mass * (root owner false).toReal *
                max (quittingOwnerOutsiderDeviationRectangle reward tail root
                  owner label.1 label.2) 0) := by
          intro label
          split_ifs
          · exact le_rfl
          · exact mul_nonneg hfactor0 (le_max_right _ 0)
        have hsingle := Finset.single_le_sum
          (fun label _ => hterm0 label)
          (Finset.mem_univ (who, action))
        simpa [hwho, mass, root, tail, rectangle] using hsingle
      have hrect : mass * forcedDefect / 2 ≤
          mass * (root owner false).toReal * rectangle := by
        simpa only [hrectangleDef, mass, forcedDefect, root, tail] using hrectangle
      exact hrect.trans (hpositivePart.trans
        (hlabel.trans (le_add_of_nonneg_left hactual0)))

/-- Sum the pointwise curvature consumption over a finite literal window. -/
theorem sum_stageCoalitionMass_mul_forcedOwnerDefect_half_le_actual_add_rectangle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner : ι) (howner : owner ∈ terminal.val) (cutoff : ℕ) :
    (∑ time ∈ Finset.range cutoff,
        quittingStageCoalitionMass reward profile time terminal *
          quittingForcedOwnerOutsiderDefect reward
            (Function.update
              (quittingProfileLiveRoot reward profile time) owner
              (PMF.pure true)) owner) / 2 ≤
      quittingFiniteActualDefectOccupation reward profile cutoff +
        quittingFiniteForcedOwnerRectangleTotal reward profile terminal owner
          cutoff := by
  have hsum := Finset.sum_le_sum fun time
      (_htime : time ∈ Finset.range cutoff) =>
    stageCoalitionMass_mul_forcedOwnerDefect_half_le_actual_add_rectangle
      reward profile terminal owner howner time
  rw [← Finset.sum_div] at hsum
  calc
    _ ≤ (∑ time ∈ Finset.range cutoff,
          quittingLiveMass reward profile time *
            ∑ who, quittingRootCoordinateNashDefect reward
              (quittingTerminalSemanticPair reward
                (quittingAllContinueProfileSpine reward profile
                  (time + 1))).1
              (quittingProfileLiveRoot reward profile time) who) +
        ∑ time ∈ Finset.range cutoff,
          quittingForcedOwnerRectangleRowTotal reward profile terminal owner
            time := by
      simpa only [Finset.sum_add_distrib] using hsum
    _ = _ := by
      rw [sum_quittingForcedOwnerRectangleRowTotal_eq_total]
      rfl

/-- **Finite-window exhaustive strategic dispatch.**  A positive aggregate
forced-owner outsider charge has exactly three consumers after the universal
factor six: one legal Continue deviation, one fixed Quit atom label, or one
fixed positive same-witness rectangle label.  Every object uses the original
literal carrier and finite chronological window. -/
theorem exists_continueDeviation_or_fixedQuitAtom_or_fixedRectangle_of_forcedOwnerOccupation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner : ι) (howner : owner ∈ terminal.val) (cutoff : ℕ)
    (lower : ℝ) (hlower : 0 < lower)
    (hcharge : lower ≤
      ∑ time ∈ Finset.range cutoff,
        quittingStageCoalitionMass reward profile time terminal *
          quittingForcedOwnerOutsiderDefect reward
            (Function.update
              (quittingProfileLiveRoot reward profile time) owner
              (PMF.pure true)) owner) :
    (∃ who : ι, ∃ deviation : (quittingGame reward).BehaviorStrategy who,
      lower / 6 ≤ (Fintype.card ι : ℝ) *
        (quittingTerminalPayoff reward
            (Function.update profile who deviation) who -
          quittingTerminalPayoff reward profile who)) ∨
    (∃ who coalition,
      coalition ∈ (Finset.univ.erase who).powerset ∧
      lower / 6 ≤
        (Fintype.card ι : ℝ) *
          (((Finset.univ.erase who).powerset.card : ℝ) *
            quittingFiniteQuitDefectAtomOccupationAt reward
              (fun time => (quittingTerminalSemanticPair reward
                (quittingAllContinueProfileSpine reward profile
                  (time + 1))).1)
              (quittingProfileLiveRoot reward profile)
              (quittingLiveMass reward profile) cutoff who coalition)) ∨
    (∃ who action, who ≠ owner ∧
      lower / 6 ≤ (Fintype.card (ι × Bool) : ℝ) *
        quittingFiniteForcedOwnerRectangleOccupation reward profile terminal
          owner who action cutoff) := by
  let actual := quittingFiniteActualDefectOccupation reward profile cutoff
  let continueCharge :=
    quittingFiniteActualContinueDefectOccupation reward profile cutoff
  let quit := quittingFiniteActualQuitDefectOccupation reward profile cutoff
  let rectangle := quittingFiniteForcedOwnerRectangleTotal reward profile
    terminal owner cutoff
  have hcurvature :=
    sum_stageCoalitionMass_mul_forcedOwnerDefect_half_le_actual_add_rectangle
      reward profile terminal owner howner cutoff
  have hlowerHalf : lower / 2 ≤ actual + rectangle := by
    exact (div_le_div_of_nonneg_right hcharge (by norm_num)).trans
      (by simpa only [actual, rectangle] using hcurvature)
  have hpolarity : actual = continueCharge + quit := by
    simpa only [actual, continueCharge, quit] using
      quittingFiniteActualDefectOccupation_eq_polaritySum reward profile cutoff
  rw [hpolarity] at hlowerHalf
  have hnonempty : Nonempty ι := ⟨owner⟩
  letI : Nonempty ι := hnonempty
  by_cases hcontinue : lower / 6 ≤ continueCharge
  · left
    obtain ⟨who, deviation, hgain⟩ :=
      exists_fixedPlayer_behaviorDeviation_of_continueOccupation
        reward profile cutoff
    exact ⟨who, deviation, hcontinue.trans hgain⟩
  · have hquitRectangle : lower / 3 ≤ quit + rectangle := by linarith
    by_cases hquit : lower / 6 ≤ quit
    · right; left
      obtain ⟨who, coalition, hcoalition, hatom⟩ :=
        exists_fixed_valid_quittingQuitDefectAtom reward
          (fun time => (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile (time + 1))).1)
          (quittingProfileLiveRoot reward profile)
          (quittingLiveMass reward profile) cutoff
          (quittingLiveMass_nonneg reward profile)
      refine ⟨who, coalition, hcoalition, hquit.trans ?_⟩
      simpa only [quit, quittingFiniteActualQuitDefectOccupation,
        mul_assoc] using hatom
    · have hrectangleLower : lower / 6 ≤ rectangle := by linarith
      have hrectanglePos : 0 < rectangle :=
        lt_of_lt_of_le (div_pos hlower (by norm_num)) hrectangleLower
      right; right
      obtain ⟨who, action, hwho, hfixed⟩ :=
        exists_fixed_forcedOwnerRectangleOccupation reward profile terminal
          owner cutoff (by simpa only [rectangle] using hrectanglePos)
      exact ⟨who, action, hwho, hrectangleLower.trans hfixed⟩

/-- **Complete finite observer-absent consumer.**  On a finite preemption
clock the observer-absent wall reaches, with literal-profile provenance,
either the fixed owner's refusal deviation, a fixed-player Continue
deviation, a fixed Quit-directed coalition atom, or a fixed outsider/action
same-witness rectangle.  The last alternative is the sole uncompiled term. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.observerAbsent_finiteClock_defectPolarity
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
      charge / 12 ≤ (Fintype.card (ι × Bool) : ℝ) *
        quittingFiniteForcedOwnerRectangleOccupation reward profile
          packet.terminal owner who action stop) := by
  classical
  dsimp only
  let profile := quittingStoppingLawObserverAbsentCarrierProfile packet n
  let owner := quittingStoppingLawObserverAbsentOwner packet
  let charge := quittingStoppingLawObserverAbsentMassLower packet *
    regime.terminalGap
  have hchargePos : 0 < charge := mul_pos
    packet.observerAbsentMassLower_pos regime.terminalGap_pos
  have hsplit := packet.observerAbsent_finiteClock_strategicSplit habsent
    n stop hstop δ hδ
  rcases hsplit with houtside | ⟨deviation, hdeviation⟩
  · have hdispatch :=
      exists_continueDeviation_or_fixedQuitAtom_or_fixedRectangle_of_forcedOwnerOccupation
        reward profile packet.terminal owner
        (quittingStoppingLawObserverAbsentOwner_mem packet) stop
        (charge / 2) (div_pos hchargePos (by norm_num))
        (by simpa only [profile, owner, charge] using houtside)
    rcases hdispatch with hcontinue | hquit | hrectangle
    · right; left
      simpa only [show (charge / 2) / 6 = charge / 12 by ring] using hcontinue
    · right; right; left
      simpa only [show (charge / 2) / 6 = charge / 12 by ring] using hquit
    · right; right; right
      simpa only [show (charge / 2) / 6 = charge / 12 by ring] using hrectangle
  · left
    exact ⟨deviation, by simpa only [profile, owner, charge] using hdeviation⟩

end GameTheory
