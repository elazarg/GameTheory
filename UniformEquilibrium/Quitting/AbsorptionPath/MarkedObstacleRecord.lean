/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.RealizedMarkedAbsorptionCylinder

/-!
# Source-forgetting marked obstacle records

`MarkedObstacleRecord` is the one-row semantic primitive needed before a
chronological completed graph can be built.  It retains the current product
root and the pre/post full and player-deleted survival factors, together with
the local Bellman data and its obstacle ordinate.  It intentionally contains
no realized block, source root function, literal offset, or horizon.

The encoder below is the finite realization adapter: its bounded `Fin` stage
is used only while constructing a record.  No compactness, list construction,
seam pullback, or generalized-path claim is made here.

Arbitrary records are raw finite coordinates.  The encoder image carries the
recurrence, product, and local Bellman coherence proved below.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Finite-coordinate/source-forgetting semantic data for one chronological
marked obstacle sample. -/
structure MarkedObstacleRecord (ι : Type) [Fintype ι] where
  player : ι
  root : ι → PMF Bool
  preFactor : ι → ℝ
  postFactor : ι → ℝ
  preFull : ℝ
  postFull : ℝ
  preDeleted : ℝ
  postDeleted : ℝ
  quitValue : ℝ
  continueReward : ℝ
  continueMass : ℝ
  continuation : ℝ
  obstacle : ℝ
  obstacle_pin : obstacle = preDeleted * quitValue

namespace MarkedObstacleRecord

/-- The local obstacle ordinate represented by a record. -/
def literalObstacle (record : MarkedObstacleRecord ι) : ℝ :=
  record.preDeleted * record.quitValue

omit [DecidableEq ι] in
theorem obstacle_eq_literal (record : MarkedObstacleRecord ι) :
    record.obstacle = record.literalObstacle := by
  exact record.obstacle_pin

/-! ## Vector-factor identities -/

/-- One coordinate's continue factor over a finite chronological prefix. -/
def playerContinueFactor (roots : ℕ → ι → PMF Bool)
    (player : ι) (start fuel : ℕ) : ℝ :=
  Math.survivalProduct (fun time => (roots time player false).toReal) start fuel

omit [Fintype ι] [DecidableEq ι] in
theorem playerContinueFactor_succ
    (roots : ℕ → ι → PMF Bool) (player : ι) (start fuel : ℕ) :
    playerContinueFactor roots player start (fuel + 1) =
      playerContinueFactor roots player start fuel *
        (roots (start + fuel) player false).toReal := by
  exact Math.survivalProduct_succ _ start fuel

omit [DecidableEq ι] in
theorem prod_playerContinueFactor_eq_survival
    (roots : ℕ → ι → PMF Bool) (start fuel : ℕ) :
    (∏ player, playerContinueFactor roots player start fuel) =
      Math.survivalProduct
        (fun time => quittingStationaryContinueMass (roots time)) start fuel := by
  induction fuel with
  | zero => simp [playerContinueFactor]
  | succ fuel ih =>
      calc
        (∏ player, playerContinueFactor roots player start (fuel + 1)) =
            ∏ player, (playerContinueFactor roots player start fuel *
              (roots (start + fuel) player false).toReal) := by
          apply Finset.prod_congr rfl
          intro player _
          exact playerContinueFactor_succ roots player start fuel
        _ = (∏ player, playerContinueFactor roots player start fuel) *
            (∏ player, (roots (start + fuel) player false).toReal) := by
          exact Finset.prod_mul_distrib
        _ = Math.survivalProduct
              (fun time => quittingStationaryContinueMass (roots time)) start fuel *
            quittingStationaryContinueMass (roots (start + fuel)) := by
          rw [ih, quittingStationaryContinueMass_eq_prod_continueProbability]
        _ = Math.survivalProduct
              (fun time => quittingStationaryContinueMass (roots time))
              start (fuel + 1) := by
          exact (Math.survivalProduct_succ _ start fuel).symm

theorem prod_playerContinueFactor_erase_eq_opponentSurvivalWeight
    (roots : ℕ → ι → PMF Bool) (who : ι) (start fuel : ℕ) :
    (∏ player ∈ Finset.univ.erase who,
      playerContinueFactor roots player start fuel) =
      quittingOpponentSurvivalWeight roots who start fuel := by
  classical
  induction fuel with
  | zero => simp [playerContinueFactor, quittingOpponentSurvivalWeight]
  | succ fuel ih =>
      have hpoint (time : ℕ) :
          (∏ player ∈ Finset.univ.erase who,
            (roots time player false).toReal) =
            quittingFixedOpponentsContinueMass roots who time := by
        rw [quittingFixedOpponentsContinueMass,
          quittingStationaryContinueMass_eq_prod_continueProbability,
          ← Finset.mul_prod_erase Finset.univ
            (fun player =>
              (Function.update (roots time) who (PMF.pure false) player false).toReal)
            (Finset.mem_univ who)]
        have hown :
            (Function.update (roots time) who (PMF.pure false) who false).toReal =
              1 := by simp
        rw [hown, one_mul]
        refine Finset.prod_congr rfl ?_
        intro player hplayer
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hplayer)]
      calc
        (∏ player ∈ Finset.univ.erase who,
            playerContinueFactor roots player start (fuel + 1)) =
            ∏ player ∈ Finset.univ.erase who,
              (playerContinueFactor roots player start fuel *
                (roots (start + fuel) player false).toReal) := by
          apply Finset.prod_congr rfl
          intro player hplayer
          exact playerContinueFactor_succ roots player start fuel
        _ = (∏ player ∈ Finset.univ.erase who,
              playerContinueFactor roots player start fuel) *
            (∏ player ∈ Finset.univ.erase who,
              (roots (start + fuel) player false).toReal) := by
          exact Finset.prod_mul_distrib
        _ = quittingOpponentSurvivalWeight roots who start fuel *
              quittingFixedOpponentsContinueMass roots who (start + fuel) := by
          rw [ih, hpoint]
        _ = quittingOpponentSurvivalWeight roots who start (fuel + 1) := by
          change
            (∏ offset ∈ Finset.range fuel,
              quittingFixedOpponentsContinueMass roots who (start + offset)) *
                quittingFixedOpponentsContinueMass roots who (start + fuel) =
              ∏ offset ∈ Finset.range (fuel + 1),
                quittingFixedOpponentsContinueMass roots who (start + offset)
          rw [Finset.prod_range_succ]

/-! ## Finite realization encoder -/

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Encode one bounded stage of a realized cylinder as source-free data. -/
def ofRealizedStage [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor)
    (who : ι) (offset : Fin c.block.length) : MarkedObstacleRecord ι :=
  let time := c.block.start + offset.val
  let remaining := c.block.extra - offset.val
  { player := who
    root := anchor.roots time
    preFactor := fun player =>
      playerContinueFactor anchor.roots player c.block.start offset.val
    postFactor := fun player =>
      playerContinueFactor anchor.roots player c.block.start (offset.val + 1)
    preFull := realizedBlockFullSurvival c.block offset.val (by omega)
    postFull := realizedBlockFullSurvival c.block (offset.val + 1) (by omega)
    preDeleted := quittingOpponentSurvivalWeight anchor.roots who
      c.block.start offset.val
    postDeleted := quittingOpponentSurvivalWeight anchor.roots who
      c.block.start (offset.val + 1)
    quitValue := quittingFixedOpponentsQuitValue reward anchor.roots who time
    continueReward :=
      quittingFixedOpponentsContinueReward reward anchor.roots who time
    continueMass := quittingFixedOpponentsContinueMass anchor.roots who time
    continuation := quittingFiniteContinueToBoundaryValue reward anchor.roots
      who 0 (time + 1) remaining
    obstacle :=
      (quittingOpponentSurvivalWeight anchor.roots who c.block.start offset.val) *
        quittingFixedOpponentsQuitValue reward anchor.roots who time
    obstacle_pin := rfl }

@[simp] theorem ofRealizedStage_player [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor)
    (who : ι) (offset : Fin c.block.length) :
    (ofRealizedStage c who offset).player = who := rfl

@[simp] theorem ofRealizedStage_root [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor)
    (who : ι) (offset : Fin c.block.length) :
    (ofRealizedStage c who offset).root =
      anchor.roots (c.block.start + offset.val) := rfl

@[simp] theorem ofRealizedStage_preFactor [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor)
    (who : ι) (offset : Fin c.block.length) (j : ι) :
    (ofRealizedStage c who offset).preFactor j =
      playerContinueFactor anchor.roots j c.block.start offset.val := rfl

@[simp] theorem ofRealizedStage_postFactor [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor)
    (who : ι) (offset : Fin c.block.length) (j : ι) :
    (ofRealizedStage c who offset).postFactor j =
      playerContinueFactor anchor.roots j c.block.start (offset.val + 1) := rfl

theorem ofRealizedStage_postFactor_eq_preFactor_mul_root
    [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor)
    (who : ι) (offset : Fin c.block.length) (j : ι) :
    (ofRealizedStage c who offset).postFactor j =
      (ofRealizedStage c who offset).preFactor j *
        ((ofRealizedStage c who offset).root j false).toReal := by
  simp [ofRealizedStage, playerContinueFactor, Math.survivalProduct_succ]

theorem ofRealizedStage_preFactor_prod_eq_preFull [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor)
    (who : ι) (offset : Fin c.block.length) :
    (∏ j, (ofRealizedStage c who offset).preFactor j) =
      (ofRealizedStage c who offset).preFull := by
  simpa [ofRealizedStage, realizedBlockFullSurvival] using
    (prod_playerContinueFactor_eq_survival anchor.roots c.block.start offset.val)

theorem ofRealizedStage_postFactor_prod_eq_postFull [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor)
    (who : ι) (offset : Fin c.block.length) :
    (∏ j, (ofRealizedStage c who offset).postFactor j) =
      (ofRealizedStage c who offset).postFull := by
  simpa [ofRealizedStage, realizedBlockFullSurvival] using
    (prod_playerContinueFactor_eq_survival anchor.roots c.block.start
      (offset.val + 1))

theorem ofRealizedStage_preFull [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor)
    (who : ι) (offset : Fin c.block.length) :
    (ofRealizedStage c who offset).preFull =
      realizedBlockFullSurvival c.block offset.val (by omega) := rfl

theorem ofRealizedStage_postFull [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor)
    (who : ι) (offset : Fin c.block.length) :
    (ofRealizedStage c who offset).postFull =
      realizedBlockFullSurvival c.block (offset.val + 1) (by omega) := rfl

theorem ofRealizedStage_preDeleted [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor)
    (who : ι) (offset : Fin c.block.length) :
    (ofRealizedStage c who offset).preDeleted =
      quittingOpponentSurvivalWeight anchor.roots who c.block.start offset.val := rfl

theorem ofRealizedStage_postDeleted [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor)
    (who : ι) (offset : Fin c.block.length) :
    (ofRealizedStage c who offset).postDeleted =
      quittingOpponentSurvivalWeight anchor.roots who c.block.start
        (offset.val + 1) := rfl

theorem ofRealizedStage_preDeleted_eq_erase_preFactor [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor)
    (who : ι) (offset : Fin c.block.length) :
    (ofRealizedStage c who offset).preDeleted =
      (∏ j ∈ Finset.univ.erase who,
        (ofRealizedStage c who offset).preFactor j) := by
  simpa [ofRealizedStage] using
    (prod_playerContinueFactor_erase_eq_opponentSurvivalWeight
      anchor.roots who c.block.start offset.val).symm

theorem ofRealizedStage_postDeleted_eq_erase_postFactor [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor)
    (who : ι) (offset : Fin c.block.length) :
    (ofRealizedStage c who offset).postDeleted =
      (∏ j ∈ Finset.univ.erase who,
        (ofRealizedStage c who offset).postFactor j) := by
  simpa [ofRealizedStage] using
      (prod_playerContinueFactor_erase_eq_opponentSurvivalWeight
      anchor.roots who c.block.start (offset.val + 1)).symm

theorem ofRealizedStage_postDeleted_eq_preDeleted_mul_continueMass [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor)
    (who : ι) (offset : Fin c.block.length) :
    (ofRealizedStage c who offset).postDeleted =
      (ofRealizedStage c who offset).preDeleted *
        (ofRealizedStage c who offset).continueMass := by
  change quittingOpponentSurvivalWeight anchor.roots who c.block.start
      (offset.val + 1) =
    quittingOpponentSurvivalWeight anchor.roots who c.block.start offset.val *
      quittingFixedOpponentsContinueMass anchor.roots who
        (c.block.start + offset.val)
  rw [quittingOpponentSurvivalWeight_eq_survivalProduct,
    quittingOpponentSurvivalWeight_eq_survivalProduct]
  exact Math.survivalProduct_succ _ c.block.start offset.val

theorem ofRealizedStage_postFull_eq_preFull_mul_rootMass [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor)
    (who : ι) (offset : Fin c.block.length) :
    (ofRealizedStage c who offset).postFull =
      (ofRealizedStage c who offset).preFull *
        quittingStationaryContinueMass
          ((ofRealizedStage c who offset).root) := by
  change realizedBlockFullSurvival c.block (offset.val + 1) (by omega) =
    realizedBlockFullSurvival c.block offset.val (by omega) *
      quittingStationaryContinueMass
        (anchor.roots (c.block.start + offset.val))
  exact realizedBlockFullSurvival_succ c.block offset.val (by omega)

theorem ofRealizedStage_continueBellman [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor)
    (who : ι) (offset : Fin c.block.length) :
    (ofRealizedStage c who offset).continueReward +
        (ofRealizedStage c who offset).continueMass *
          (ofRealizedStage c who offset).continuation =
      quittingFiniteContinueToBoundaryValue reward anchor.roots who 0
        (c.block.start + offset.val)
        ((c.block.extra - offset.val) + 1) := by
  rfl

theorem ofRealizedStage_quitValue [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor)
    (who : ι) (offset : Fin c.block.length) :
    (ofRealizedStage c who offset).quitValue =
      quittingFixedOpponentsQuitValue reward anchor.roots who
        (c.block.start + offset.val) := rfl

theorem ofRealizedStage_continueReward [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor)
    (who : ι) (offset : Fin c.block.length) :
    (ofRealizedStage c who offset).continueReward =
      quittingFixedOpponentsContinueReward reward anchor.roots who
        (c.block.start + offset.val) := rfl

theorem ofRealizedStage_continueMass [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor)
    (who : ι) (offset : Fin c.block.length) :
    (ofRealizedStage c who offset).continueMass =
      quittingFixedOpponentsContinueMass anchor.roots who
        (c.block.start + offset.val) := rfl

theorem ofRealizedStage_continuation [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor)
    (who : ι) (offset : Fin c.block.length) :
    (ofRealizedStage c who offset).continuation =
      quittingFiniteContinueToBoundaryValue reward anchor.roots who 0
        (c.block.start + offset.val + 1) (c.block.extra - offset.val) := rfl

theorem ofRealizedStage_obstacle_eq_literal [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor)
    (who : ι) (offset : Fin c.block.length) :
    (ofRealizedStage c who offset).obstacle =
      quittingOpponentSurvivalWeight anchor.roots who c.block.start offset.val *
        quittingFixedOpponentsQuitValue reward anchor.roots who
          (c.block.start + offset.val) := by
  rfl

theorem ofRealizedStage_obstacle_eq_literalObstacle [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor)
    (who : ι) (offset : Fin c.block.length) :
    (ofRealizedStage c who offset).obstacle =
      (ofRealizedStage c who offset).literalObstacle := by
  exact obstacle_eq_literal _

end MarkedObstacleRecord

end GameTheory
