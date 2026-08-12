/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAtomicBlockerResetAdapter
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDefectCharge
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawMixture

/-!
# Forced-owner gain versus actual rectangle curvature

Fix an owner and an outsider deviation.  The outsider's one-root deviation
gain is affine in the owner's Quit marginal.  A gain visible after forcing
the owner to Quit can therefore disappear at the actual mixed root only by
creating a positive owner-action / outsider-deviation rectangle.

Quantitatively, half of the forced gain weighted by the owner's actual Quit
probability is found either in the outsider's actual root Nash defect or in
the weighted two-action rectangle curvature.  This is the exact
no-cancellation interface needed by a forced-owner wall.  It makes no claim
that the positive rectangle has already been integrated into a compatible
chronological reset path.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Gain of one fixed root marginal deviation over the prescribed product
root value. -/
def quittingRootDeviationGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (who : ι) (deviation : PMF Bool) : ℝ :=
  quittingRootExpectedPayoff reward tail
      (Function.update root who deviation) who -
    quittingRootSuccessorPayoff reward tail root who

/-- Pure Quit gain is the Continue probability times Quit-minus-Continue. -/
theorem quittingRootDeviationGain_pure_true_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootDeviationGain reward tail root who (PMF.pure true) =
      (root who false).toReal *
        quittingRootEndpointDifference reward tail root who := by
  unfold quittingRootDeviationGain
  rw [show quittingRootExpectedPayoff reward tail
      (Function.update root who (PMF.pure true)) who =
        quittingRootQuitPayoff reward tail root who by
      simp [quittingRootQuitPayoff]]
  rw [quittingRootSuccessorPayoff_eq_endpointMix]
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  have htrue : (root who true).toReal = 1 - (root who false).toReal := by
    linarith
  rw [htrue]
  unfold quittingRootEndpointDifference
  ring

/-- Pure Continue gain is minus the Quit probability times
Quit-minus-Continue. -/
theorem quittingRootDeviationGain_pure_false_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootDeviationGain reward tail root who (PMF.pure false) =
      -(root who true).toReal *
        quittingRootEndpointDifference reward tail root who := by
  unfold quittingRootDeviationGain
  rw [show quittingRootExpectedPayoff reward tail
      (Function.update root who (PMF.pure false)) who =
        quittingRootContinuePayoff reward tail root who by
      simp [quittingRootContinuePayoff]]
  rw [quittingRootSuccessorPayoff_eq_endpointMix]
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  have hfalse : (root who false).toReal = 1 - (root who true).toReal := by
    linarith
  rw [hfalse]
  unfold quittingRootEndpointDifference
  ring

/-- The gain of one fixed outsider deviation is exactly affine in a distinct
owner's marginal. -/
theorem quittingRootDeviationGain_eq_ownerEndpointMix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (owner who : ι) (hne : owner ≠ who) (deviation : PMF Bool) :
    quittingRootDeviationGain reward tail root who deviation =
      (root owner true).toReal *
          quittingRootDeviationGain reward tail
            (Function.update root owner (PMF.pure true)) who deviation +
        (root owner false).toReal *
          quittingRootDeviationGain reward tail
            (Function.update root owner (PMF.pure false)) who deviation := by
  have hdeviated := quittingRootExpectedPayoff_updateCoordinate_eq_endpointMix
    reward tail (Function.update root who deviation) owner who (root owner)
  have hbase := quittingRootExpectedPayoff_updateCoordinate_eq_endpointMix
    reward tail root owner who (root owner)
  rw [Function.update_eq_self] at hbase
  have hdeviatedSource : Function.update
      (Function.update root who deviation) owner (root owner) =
      Function.update root who deviation := by
    funext player
    by_cases hplayer : player = owner
    · subst player
      simp [hne]
    · simp [hplayer]
  rw [hdeviatedSource] at hdeviated
  unfold quittingRootDeviationGain quittingRootSuccessorPayoff
  rw [hdeviated, hbase]
  rw [Function.update_comm hne, Function.update_comm hne]
  ring

/-- Change in `who`'s Quit-minus-Continue advantage when `owner` is toggled
from Continue to Quit.  This is the two-coordinate discrete derivative seen
by the outsider. -/
def quittingOwnerInfluenceOnEndpointDifference
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (owner who : ι) : ℝ :=
  quittingRootEndpointDifference reward tail
      (Function.update root owner (PMF.pure true)) who -
    quittingRootEndpointDifference reward tail
      (Function.update root owner (PMF.pure false)) who

/-- Same-witness gain rectangle between the owner's endpoint and one pure
outsider deviation. -/
def quittingOwnerOutsiderDeviationRectangle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (owner who : ι) (action : Bool) : ℝ :=
  quittingRootDeviationGain reward tail
      (Function.update root owner (PMF.pure true)) who (PMF.pure action) -
    quittingRootDeviationGain reward tail
      (Function.update root owner (PMF.pure false)) who (PMF.pure action)

/-- **Boolean-character formula for the owner/outsider square.**  The two
pure outsider endpoints are the two opposite characters of the same scalar
owner influence. -/
theorem quittingOwnerOutsiderDeviationRectangle_eq_polarity
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (owner who : ι) (hne : owner ≠ who) (action : Bool) :
    quittingOwnerOutsiderDeviationRectangle reward tail root owner who action =
      if action then
        (root who false).toReal *
          quittingOwnerInfluenceOnEndpointDifference
            reward tail root owner who
      else
        -(root who true).toReal *
          quittingOwnerInfluenceOnEndpointDifference
            reward tail root owner who := by
  cases action with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      unfold quittingOwnerOutsiderDeviationRectangle
        quittingOwnerInfluenceOnEndpointDifference
      rw [quittingRootDeviationGain_pure_false_eq,
        quittingRootDeviationGain_pure_false_eq]
      simp only [Function.update_of_ne hne.symm]
      ring
  | true =>
      simp only [↓reduceIte]
      unfold quittingOwnerOutsiderDeviationRectangle
        quittingOwnerInfluenceOnEndpointDifference
      rw [quittingRootDeviationGain_pure_true_eq,
        quittingRootDeviationGain_pure_true_eq]
      simp only [Function.update_of_ne hne.symm]
      ring

/-- A positive square has exactly one of two orientations: pure Quit sees a
positive owner influence, or pure Continue sees a negative owner influence.
The orientations are disjoint. -/
theorem positive_quittingOwnerOutsiderDeviationRectangle_orientation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (owner who : ι) (hne : owner ≠ who) (action : Bool)
    (hpositive : 0 < quittingOwnerOutsiderDeviationRectangle
      reward tail root owner who action) :
    (action = true ∧ 0 < quittingOwnerInfluenceOnEndpointDifference
        reward tail root owner who) ∨
      (action = false ∧ quittingOwnerInfluenceOnEndpointDifference
        reward tail root owner who < 0) := by
  rw [quittingOwnerOutsiderDeviationRectangle_eq_polarity
    reward tail root owner who hne action] at hpositive
  cases action with
  | false =>
      right
      refine ⟨rfl, ?_⟩
      by_contra hnot
      have hinfluence : 0 ≤ quittingOwnerInfluenceOnEndpointDifference
          reward tail root owner who := le_of_not_gt hnot
      have hproduct : 0 ≤ (root who true).toReal *
          quittingOwnerInfluenceOnEndpointDifference
            reward tail root owner who :=
        mul_nonneg ENNReal.toReal_nonneg hinfluence
      simp only [Bool.false_eq_true, ↓reduceIte] at hpositive
      linarith
  | true =>
      left
      refine ⟨rfl, ?_⟩
      by_contra hnot
      have hinfluence : quittingOwnerInfluenceOnEndpointDifference
          reward tail root owner who ≤ 0 := le_of_not_gt hnot
      have hproduct : (root who false).toReal *
          quittingOwnerInfluenceOnEndpointDifference
            reward tail root owner who ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg hinfluence
      simp only [↓reduceIte] at hpositive
      linarith

/-- **Exact `Z₂` rectangle circulation.**  The two pure outsider endpoint
rectangles are the opposite characters of one scalar influence, and their
weights under the prescribed outsider marginal cancel exactly. -/
theorem quittingOwnerOutsiderDeviationRectangle_weighted_circulation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (owner who : ι) (hne : owner ≠ who) :
    (root who true).toReal *
        quittingOwnerOutsiderDeviationRectangle
          reward tail root owner who true +
      (root who false).toReal *
        quittingOwnerOutsiderDeviationRectangle
          reward tail root owner who false = 0 := by
  rw [quittingOwnerOutsiderDeviationRectangle_eq_polarity
      reward tail root owner who hne true,
    quittingOwnerOutsiderDeviationRectangle_eq_polarity
      reward tail root owner who hne false]
  simp only [↓reduceIte, Bool.false_eq_true]
  ring

/-- If both outsider actions occur with positive probability, a positive
rectangle on either pure endpoint forces a strictly negative rectangle on
the other. -/
theorem positive_rectangle_forces_negative_opposite_of_fullyMixed
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (owner who : ι) (hne : owner ≠ who)
    (hquit : 0 < (root who true).toReal)
    (hcontinue : 0 < (root who false).toReal) (action : Bool)
    (hpositive : 0 < quittingOwnerOutsiderDeviationRectangle
      reward tail root owner who action) :
    quittingOwnerOutsiderDeviationRectangle
      reward tail root owner who (!action) < 0 := by
  have horientation :=
    positive_quittingOwnerOutsiderDeviationRectangle_orientation
      reward tail root owner who hne action hpositive
  rcases horientation with ⟨haction, hinfluence⟩ |
      ⟨haction, hinfluence⟩
  · subst action
    change quittingOwnerOutsiderDeviationRectangle
      reward tail root owner who false < 0
    rw [quittingOwnerOutsiderDeviationRectangle_eq_polarity
      reward tail root owner who hne false]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hquit) hinfluence
  · subst action
    change quittingOwnerOutsiderDeviationRectangle
      reward tail root owner who true < 0
    rw [quittingOwnerOutsiderDeviationRectangle_eq_polarity
      reward tail root owner who hne true]
    simp only [↓reduceIte]
    exact mul_neg_of_pos_of_neg hcontinue hinfluence

/-- If the owner belongs to a coalition, the coalition's actual root mass is
its owner-Quit probability times its mass on the owner-forced-Quit face. -/
theorem quittingRootCoalitionMass_eq_ownerQuit_mul_forced
    (root : ι → PMF Bool) (owner : ι) (coalition : Finset ι)
    (howner : owner ∈ coalition) :
    quittingRootCoalitionMass root coalition =
      (root owner true).toReal *
        quittingRootCoalitionMass
          (Function.update root owner (PMF.pure true)) coalition := by
  have hfactor := quittingRootCoalitionMass_update_eq_actionProbability_mul_forced
    root owner (root owner) coalition
  rw [Function.update_eq_self] at hfactor
  simpa [howner] using hfactor

/-- Every root coordinate Nash defect is realized by one of the two pure
endpoint deviations. -/
theorem exists_pureEndpointDeviationGain_eq_coordinateNashDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    ∃ action : Bool,
      quittingRootDeviationGain reward tail root who (PMF.pure action) =
        quittingRootCoordinateNashDefect reward tail root who := by
  unfold quittingRootCoordinateNashDefect
  by_cases hquit : quittingRootContinuePayoff reward tail root who ≤
      quittingRootQuitPayoff reward tail root who
  · refine ⟨true, ?_⟩
    rw [max_eq_left hquit]
    simp [quittingRootDeviationGain, quittingRootQuitPayoff]
  · have hcontinue : quittingRootQuitPayoff reward tail root who ≤
        quittingRootContinuePayoff reward tail root who := le_of_not_ge hquit
    refine ⟨false, ?_⟩
    rw [max_eq_right hcontinue]
    simp [quittingRootDeviationGain, quittingRootContinuePayoff]

/-- The gain of either pure endpoint is bounded by the coordinate Nash
defect. -/
theorem pureEndpointDeviationGain_le_coordinateNashDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (action : Bool) :
    quittingRootDeviationGain reward tail root who (PMF.pure action) ≤
      quittingRootCoordinateNashDefect reward tail root who := by
  cases action with
  | false =>
      unfold quittingRootDeviationGain quittingRootCoordinateNashDefect
      simp [quittingRootContinuePayoff]
  | true =>
      unfold quittingRootDeviationGain quittingRootCoordinateNashDefect
      simp [quittingRootQuitPayoff]

/-- Scalar no-cancellation lemma.  If `actual` is the affine mixture of the
Quit and Continue faces, half of the Quit-face contribution lies either in
the positive actual gain or in the weighted face rectangle. -/
theorem half_quitContribution_le_actual_or_rectangle
    (q quitGain continueGain actualGain : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (haffine : actualGain = q * quitGain + (1 - q) * continueGain) :
    q * quitGain / 2 ≤ max actualGain 0 ∨
      q * quitGain / 2 ≤
        q * (1 - q) * (quitGain - continueGain) := by
  by_cases hactual : q * quitGain / 2 ≤ max actualGain 0
  · exact Or.inl hactual
  · right
    have hpositiveContribution : 0 < q * quitGain := by
      by_contra hnonpos
      have hle : q * quitGain ≤ 0 := le_of_not_gt hnonpos
      have : q * quitGain / 2 ≤ max actualGain 0 := by
        have hdiv : q * quitGain / 2 ≤ 0 := by nlinarith
        exact hdiv.trans (le_max_right _ 0)
      exact hactual this
    have hactualLt : actualGain < q * quitGain / 2 := by
      have hmaxLt : max actualGain 0 < q * quitGain / 2 :=
        lt_of_not_ge hactual
      exact (le_max_left actualGain 0).trans_lt hmaxLt
    rw [haffine] at hactualLt
    nlinarith

/-- **Forced-owner defect localization.**  Choose a pure outsider endpoint
which realizes its defect at the owner-forced-Quit row.  Half of that defect,
weighted by the owner's actual Quit probability, is either already an actual
outsider Nash defect or is stored in a positive owner/outsider rectangle.

The rectangle uses the same outsider endpoint on both owner faces; no witness
switch is hidden in the statement. -/
theorem forcedOwner_coordinateDefect_actual_or_rectangle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (owner who : ι) (hne : owner ≠ who) :
    ∃ action : Bool,
      let quitGain := quittingRootDeviationGain reward tail
        (Function.update root owner (PMF.pure true)) who (PMF.pure action)
      let continueGain := quittingRootDeviationGain reward tail
        (Function.update root owner (PMF.pure false)) who (PMF.pure action)
      quitGain = quittingRootCoordinateNashDefect reward tail
          (Function.update root owner (PMF.pure true)) who ∧
        ((root owner true).toReal * quitGain / 2 ≤
            quittingRootCoordinateNashDefect reward tail root who ∨
          (root owner true).toReal * quitGain / 2 ≤
            (root owner true).toReal * (root owner false).toReal *
              (quitGain - continueGain)) := by
  obtain ⟨action, haction⟩ :=
    exists_pureEndpointDeviationGain_eq_coordinateNashDefect reward tail
      (Function.update root owner (PMF.pure true)) who
  refine ⟨action, haction, ?_⟩
  let actualGain := quittingRootDeviationGain reward tail root who
    (PMF.pure action)
  let quitGain := quittingRootDeviationGain reward tail
    (Function.update root owner (PMF.pure true)) who (PMF.pure action)
  let continueGain := quittingRootDeviationGain reward tail
    (Function.update root owner (PMF.pure false)) who (PMF.pure action)
  have haffine : actualGain =
      (root owner true).toReal * quitGain +
        (root owner false).toReal * continueGain := by
    exact quittingRootDeviationGain_eq_ownerEndpointMix reward tail root owner
      who hne (PMF.pure action)
  have hsum := quittingRoot_continueProbability_add_quitProbability root owner
  have hfalse : (root owner false).toReal =
      1 - (root owner true).toReal := by linarith
  have hq0 : 0 ≤ (root owner true).toReal := ENNReal.toReal_nonneg
  have hq1 : (root owner true).toReal ≤ 1 := by
    have hfalse0 : 0 ≤ (root owner false).toReal := ENNReal.toReal_nonneg
    linarith
  have halt := half_quitContribution_le_actual_or_rectangle
    (root owner true).toReal quitGain continueGain actualGain hq0 hq1
    (by rw [haffine, hfalse])
  rcases halt with hactual | hrectangle
  · left
    have hgainLe := pureEndpointDeviationGain_le_coordinateNashDefect
      reward tail root who action
    have hdefectNonneg := quittingRootCoordinateNashDefect_nonneg
      reward tail root who
    exact hactual.trans (max_le hgainLe hdefectNonneg)
  · right
    simpa only [hfalse] using hrectangle

/-- **Coalition-weighted forced-owner localization.**  When the forced owner
belongs to a displayed coalition, the owner's Quit probability in the
pointwise localization is exactly the factor already present in that
coalition's actual mass.  Thus half of the mass-weighted forced defect is
charged either to the actual outsider defect, with no extra coefficient, or
to a same-deviation rectangle carried by that very coalition mass. -/
theorem coalitionMass_mul_forcedOwnerDefect_actual_or_rectangle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (owner who : ι) (hne : owner ≠ who)
    (coalition : Finset ι) (howner : owner ∈ coalition) :
    ∃ action : Bool,
      let quitGain := quittingRootDeviationGain reward tail
        (Function.update root owner (PMF.pure true)) who (PMF.pure action)
      let continueGain := quittingRootDeviationGain reward tail
        (Function.update root owner (PMF.pure false)) who (PMF.pure action)
      let mass := quittingRootCoalitionMass root coalition
      quitGain = quittingRootCoordinateNashDefect reward tail
          (Function.update root owner (PMF.pure true)) who ∧
        (mass * quitGain / 2 ≤
            quittingRootCoordinateNashDefect reward tail root who ∨
          mass * quitGain / 2 ≤
            mass * (root owner false).toReal *
              (quitGain - continueGain)) := by
  obtain ⟨action, hrealize, halt⟩ :=
    forcedOwner_coordinateDefect_actual_or_rectangle reward tail root owner
      who hne
  refine ⟨action, hrealize, ?_⟩
  let quitGain := quittingRootDeviationGain reward tail
    (Function.update root owner (PMF.pure true)) who (PMF.pure action)
  let continueGain := quittingRootDeviationGain reward tail
    (Function.update root owner (PMF.pure false)) who (PMF.pure action)
  let mass := quittingRootCoalitionMass root coalition
  let forcedMass := quittingRootCoalitionMass
    (Function.update root owner (PMF.pure true)) coalition
  have hmass : mass = (root owner true).toReal * forcedMass := by
    exact quittingRootCoalitionMass_eq_ownerQuit_mul_forced root owner
      coalition howner
  have hforcedMass0 : 0 ≤ forcedMass :=
    MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg _ _
  have hforcedMass1 : forcedMass ≤ 1 := by
    have hle := quittingRootCoalitionMass_le_quitProbability_of_mem
      (Function.update root owner (PMF.pure true)) coalition owner howner
    simpa [forcedMass] using hle
  have hactualDefect0 :
      0 ≤ quittingRootCoordinateNashDefect reward tail root who :=
    quittingRootCoordinateNashDefect_nonneg reward tail root who
  rcases halt with hactual | hrectangle
  · left
    calc
      mass * quitGain / 2 =
          forcedMass * ((root owner true).toReal * quitGain / 2) := by
            rw [hmass]
            ring
      _ ≤ forcedMass *
          quittingRootCoordinateNashDefect reward tail root who :=
        mul_le_mul_of_nonneg_left hactual hforcedMass0
      _ ≤ quittingRootCoordinateNashDefect reward tail root who :=
        mul_le_of_le_one_left hactualDefect0 hforcedMass1
  · right
    calc
      mass * quitGain / 2 =
          forcedMass * ((root owner true).toReal * quitGain / 2) := by
            rw [hmass]
            ring
      _ ≤ forcedMass *
          ((root owner true).toReal * (root owner false).toReal *
            (quitGain - continueGain)) :=
        mul_le_mul_of_nonneg_left hrectangle hforcedMass0
      _ = mass * (root owner false).toReal *
          (quitGain - continueGain) := by
        rw [hmass]
        ring

/-- Chronological form of the coalition-weighted localization.  The first
branch is exactly the usual live Nash-defect occupation.  The second branch
is a new signed rectangle charge carried by the original stage cylinder. -/
theorem stageCoalitionMass_mul_forcedOwnerDefect_actual_or_rectangle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (tail : Payoff ι) (time : ℕ)
    (owner who : ι) (hne : owner ≠ who)
    (terminal : {S : Finset ι // S.Nonempty})
    (howner : owner ∈ terminal.val) :
    ∃ action : Bool,
      let root := quittingProfileLiveRoot reward profile time
      let quitGain := quittingRootDeviationGain reward tail
        (Function.update root owner (PMF.pure true)) who (PMF.pure action)
      let continueGain := quittingRootDeviationGain reward tail
        (Function.update root owner (PMF.pure false)) who (PMF.pure action)
      let mass := quittingStageCoalitionMass reward profile time terminal
      quitGain = quittingRootCoordinateNashDefect reward tail
          (Function.update root owner (PMF.pure true)) who ∧
        (mass * quitGain / 2 ≤
            quittingLiveMass reward profile time *
              quittingRootCoordinateNashDefect reward tail root who ∨
          mass * quitGain / 2 ≤
            mass * (root owner false).toReal *
              (quitGain - continueGain)) := by
  let root := quittingProfileLiveRoot reward profile time
  obtain ⟨action, hrealize, halt⟩ :=
    coalitionMass_mul_forcedOwnerDefect_actual_or_rectangle reward tail root
      owner who hne terminal.val howner
  refine ⟨action, hrealize, ?_⟩
  let quitGain := quittingRootDeviationGain reward tail
    (Function.update root owner (PMF.pure true)) who (PMF.pure action)
  let continueGain := quittingRootDeviationGain reward tail
    (Function.update root owner (PMF.pure false)) who (PMF.pure action)
  let rootMass := quittingRootCoalitionMass root terminal.val
  let mass := quittingStageCoalitionMass reward profile time terminal
  have hmass : mass = quittingLiveMass reward profile time * rootMass := by
    exact quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass
      reward profile time terminal
  have hlive0 : 0 ≤ quittingLiveMass reward profile time :=
    quittingLiveMass_nonneg reward profile time
  rcases halt with hactual | hrectangle
  · left
    calc
      mass * quitGain / 2 = quittingLiveMass reward profile time *
          (rootMass * quitGain / 2) := by
        rw [hmass]
        ring
      _ ≤ quittingLiveMass reward profile time *
          quittingRootCoordinateNashDefect reward tail root who :=
        mul_le_mul_of_nonneg_left hactual hlive0
  · right
    calc
      mass * quitGain / 2 = quittingLiveMass reward profile time *
          (rootMass * quitGain / 2) := by
        rw [hmass]
        ring
      _ ≤ quittingLiveMass reward profile time *
          (rootMass * (root owner false).toReal *
            (quitGain - continueGain)) :=
        mul_le_mul_of_nonneg_left hrectangle hlive0
      _ = mass * (root owner false).toReal *
          (quitGain - continueGain) := by
        rw [hmass]
        ring

/-- A mass-weighted lower bound already charged to the counterfactual defect
inherits the same actual-defect/rectangle localization, at the sole cost of
the universal factor two. -/
theorem stageCoalitionMass_gap_actualDefect_or_rectangle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (tail : Payoff ι) (time : ℕ)
    (owner who : ι) (hne : owner ≠ who)
    (terminal : {S : Finset ι // S.Nonempty})
    (howner : owner ∈ terminal.val) (gap : ℝ)
    (hgap : quittingStageCoalitionMass reward profile time terminal * gap ≤
      quittingStageCoalitionMass reward profile time terminal *
        quittingRootCoordinateNashDefect reward tail
          (Function.update (quittingProfileLiveRoot reward profile time)
            owner (PMF.pure true)) who) :
    ∃ action : Bool,
      let root := quittingProfileLiveRoot reward profile time
      let quitGain := quittingRootDeviationGain reward tail
        (Function.update root owner (PMF.pure true)) who (PMF.pure action)
      let continueGain := quittingRootDeviationGain reward tail
        (Function.update root owner (PMF.pure false)) who (PMF.pure action)
      let mass := quittingStageCoalitionMass reward profile time terminal
      quitGain = quittingRootCoordinateNashDefect reward tail
          (Function.update root owner (PMF.pure true)) who ∧
        (mass * gap / 2 ≤
            quittingLiveMass reward profile time *
              quittingRootCoordinateNashDefect reward tail root who ∨
          mass * gap / 2 ≤
            mass * (root owner false).toReal *
              (quitGain - continueGain)) := by
  obtain ⟨action, hrealize, halt⟩ :=
    stageCoalitionMass_mul_forcedOwnerDefect_actual_or_rectangle reward
      profile tail time owner who hne terminal howner
  refine ⟨action, hrealize, ?_⟩
  let root := quittingProfileLiveRoot reward profile time
  let quitGain := quittingRootDeviationGain reward tail
    (Function.update root owner (PMF.pure true)) who (PMF.pure action)
  let mass := quittingStageCoalitionMass reward profile time terminal
  have hmassGap : mass * gap ≤ mass * quitGain := by
    dsimp only [mass, quitGain, root]
    rw [hrealize]
    exact hgap
  have hhalf : mass * gap / 2 ≤ mass * quitGain / 2 := by
    exact div_le_div_of_nonneg_right hmassGap (by norm_num)
  exact halt.imp hhalf.trans hhalf.trans

/-! ## Witness-free positive-square account -/

/-- Positive part of one mass-weighted owner/outsider square.  Keeping the
mass inside the definition lets chronological sums use the literal cylinder
weight without dividing by a possibly vanishing probability. -/
def quittingPositiveOwnerOutsiderRectangleCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (mass : ℝ) (owner who : ι) (action : Bool) : ℝ :=
  max 0 (mass * (root owner false).toReal *
    quittingOwnerOutsiderDeviationRectangle
      reward tail root owner who action)

theorem quittingPositiveOwnerOutsiderRectangleCharge_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (mass : ℝ) (owner who : ι) (action : Bool) :
    0 ≤ quittingPositiveOwnerOutsiderRectangleCharge
      reward tail root mass owner who action := by
  exact le_max_left _ _

/-- A single coordinate defect is bounded by the total root defect. -/
theorem quittingRootCoordinateNashDefect_le_total
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootCoordinateNashDefect reward tail root who ≤
      quittingRootTotalNashDefect reward tail root := by
  unfold quittingRootTotalNashDefect
  exact Finset.single_le_sum
    (fun player _ =>
      quittingRootCoordinateNashDefect_nonneg reward tail root player)
    (Finset.mem_univ who)

/-- **Witness-free row account.**  The largest outsider defect at the
owner-forced-Quit face is paid, without a cardinality loss, by the actual
total root Nash defect plus the sum of positive same-witness Boolean
squares.  The maximizing outsider and its better endpoint may vary from row
to row, but have disappeared behind finite nonnegative sums.

The displayed coalition must contain the owner.  This is exactly what turns
the owner's actual Quit probability into the coalition mass already carried
by the clock. -/
theorem stageCoalitionMass_mul_forcedOwnerOutsiderDefect_le_actual_add_squares
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (tail : Payoff ι) (time : ℕ) (owner : ι)
    (terminal : {S : Finset ι // S.Nonempty})
    (howner : owner ∈ terminal.val) :
    let root := quittingProfileLiveRoot reward profile time
    let mass := quittingStageCoalitionMass reward profile time terminal
    mass * quittingForcedOwnerOutsiderDefect reward
          (Function.update root owner (PMF.pure true)) owner / 2 ≤
      quittingLiveMass reward profile time *
          quittingRootTotalNashDefect reward tail root +
        ∑ who, ∑ action,
          quittingPositiveOwnerOutsiderRectangleCharge
            reward tail root mass owner who action := by
  classical
  dsimp only
  let root := quittingProfileLiveRoot reward profile time
  let mass := quittingStageCoalitionMass reward profile time terminal
  let forcedRoot := Function.update root owner (PMF.pure true)
  let forcedDefect :=
    quittingForcedOwnerOutsiderDefect reward forcedRoot owner
  change mass * forcedDefect / 2 ≤
    quittingLiveMass reward profile time *
        quittingRootTotalNashDefect reward tail root +
      ∑ who, ∑ action,
        quittingPositiveOwnerOutsiderRectangleCharge
          reward tail root mass owner who action
  have hmass0 : 0 ≤ mass :=
    quittingStageCoalitionMass_nonneg reward profile time terminal
  have hlive0 : 0 ≤ quittingLiveMass reward profile time :=
    quittingLiveMass_nonneg reward profile time
  have htotal0 : 0 ≤ quittingRootTotalNashDefect reward tail root :=
    quittingRootTotalNashDefect_nonneg reward tail root
  have hsquares0 : 0 ≤ ∑ who, ∑ action,
      quittingPositiveOwnerOutsiderRectangleCharge
        reward tail root mass owner who action := by
    exact Finset.sum_nonneg fun who _ =>
      Finset.sum_nonneg fun action _ =>
        quittingPositiveOwnerOutsiderRectangleCharge_nonneg
          reward tail root mass owner who action
  by_cases hpositive : 0 < forcedDefect
  · obtain ⟨who, hwho, hcoordinate⟩ :=
      exists_outsider_coordinateNashDefect_ge_of_forcedOwnerDefect_ge
        reward tail forcedRoot owner (by simp [forcedRoot]) hpositive le_rfl
    have hgap : mass * forcedDefect ≤ mass *
        quittingRootCoordinateNashDefect reward tail forcedRoot who :=
      mul_le_mul_of_nonneg_left hcoordinate hmass0
    obtain ⟨action, _hrealize, halt⟩ :=
      stageCoalitionMass_gap_actualDefect_or_rectangle reward profile tail
        time owner who hwho.symm terminal howner forcedDefect hgap
    rcases halt with hactual | hrectangle
    · have hcoordinateTotal :=
        quittingRootCoordinateNashDefect_le_total reward tail root who
      have hactualTotal :
          quittingLiveMass reward profile time *
              quittingRootCoordinateNashDefect reward tail root who ≤
            quittingLiveMass reward profile time *
              quittingRootTotalNashDefect reward tail root :=
        mul_le_mul_of_nonneg_left hcoordinateTotal hlive0
      exact hactual.trans <|
        hactualTotal.trans (le_add_of_nonneg_right hsquares0)
    · have hrectanglePositive : mass * (root owner false).toReal *
          (quittingRootDeviationGain reward tail forcedRoot who
              (PMF.pure action) -
            quittingRootDeviationGain reward tail
              (Function.update root owner (PMF.pure false)) who
              (PMF.pure action)) ≤
          quittingPositiveOwnerOutsiderRectangleCharge
            reward tail root mass owner who action := by
        unfold quittingPositiveOwnerOutsiderRectangleCharge
          quittingOwnerOutsiderDeviationRectangle
        exact le_max_right _ _
      have hselectedLe :
          quittingPositiveOwnerOutsiderRectangleCharge
              reward tail root mass owner who action ≤
            ∑ player, ∑ endpoint,
              quittingPositiveOwnerOutsiderRectangleCharge
                reward tail root mass owner player endpoint := by
        have hactionLe :
            quittingPositiveOwnerOutsiderRectangleCharge
                reward tail root mass owner who action ≤
              ∑ endpoint,
                quittingPositiveOwnerOutsiderRectangleCharge
                  reward tail root mass owner who endpoint := by
          exact Finset.single_le_sum
            (fun endpoint _ =>
              quittingPositiveOwnerOutsiderRectangleCharge_nonneg
                reward tail root mass owner who endpoint)
            (Finset.mem_univ action)
        have hwhoLe :
            (∑ endpoint,
                quittingPositiveOwnerOutsiderRectangleCharge
                  reward tail root mass owner who endpoint) ≤
              ∑ player, ∑ endpoint,
                quittingPositiveOwnerOutsiderRectangleCharge
                  reward tail root mass owner player endpoint := by
          exact Finset.single_le_sum
            (fun player _ => Finset.sum_nonneg fun endpoint _ =>
            quittingPositiveOwnerOutsiderRectangleCharge_nonneg
              reward tail root mass owner player endpoint)
            (Finset.mem_univ who)
        exact hactionLe.trans hwhoLe
      have hrectangles := hrectangle.trans
        (hrectanglePositive.trans hselectedLe)
      exact hrectangles.trans (le_add_of_nonneg_left (mul_nonneg hlive0 htotal0))
  · have hforced0 : 0 ≤ forcedDefect :=
      quittingForcedOwnerOutsiderDefect_nonneg reward forcedRoot owner
    have hforced : forcedDefect = 0 := le_antisymm (le_of_not_gt hpositive) hforced0
    rw [hforced, mul_zero, zero_div]
    exact add_nonneg (mul_nonneg hlive0 htotal0) hsquares0

end GameTheory
