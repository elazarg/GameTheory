/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Examples.BlockPair.K11LocalValue

/-!
# Scalar opponent summaries for the block-pair K11 system

This module evaluates the three one-phase opponent summaries without
materializing gradients.  Its projection and lifting theorems identify those
scalar computations exactly with both the phase-local cached-dual evaluator
and the canonical rational-polynomial expressions.
-/

namespace GameTheory.BlockPairK11

open Math.Interval
open LocalInterval

namespace LocalValue

variable {precision : ℕ}

/-- Payoff interval from quitting against the opponents at a specialized
phase root. -/
def opponentQuitValueFromRoot
    (root : Vector (Value precision) 4) (who : Player) :
    Value precision :=
  sum fun mask : QuitterMask ↦
    if maskHasPlayer mask who then DyadicInterval.ofRat 0
    else
      (DyadicInterval.ofRat
          (terminalTable (maskWithPlayer mask who) who)).mul
        (maskProbability root mask (some who))

/-- Absorbing payoff interval produced by the opponents while the selected
player continues. -/
def opponentAbsorbingContributionFromRoot
    (root : Vector (Value precision) 4) (who : Player) :
    Value precision :=
  sum fun mask : QuitterMask ↦
    if mask.val = 0 || maskHasPlayer mask who then DyadicInterval.ofRat 0
    else
      (DyadicInterval.ofRat (terminalTable mask who)).mul
        (maskProbability root mask (some who))

/-- Probability interval that every opponent continues at a specialized
phase root. -/
def opponentSurvivalFromRoot
    (root : Vector (Value precision) 4) (who : Player) :
    Value precision :=
  maskProbability root 0 (some who)

def opponentQuitValue (box : HazardIndex → Value precision)
    (phase : Phase) (who : Player) : Value precision :=
  opponentQuitValueFromRoot (buildRoot box phase) who

def opponentAbsorbingContribution
    (box : HazardIndex → Value precision)
    (phase : Phase) (who : Player) : Value precision :=
  opponentAbsorbingContributionFromRoot (buildRoot box phase) who

def opponentSurvival (box : HazardIndex → Value precision)
    (phase : Phase) (who : Player) : Value precision :=
  opponentSurvivalFromRoot (buildRoot box phase) who

/-- Value projection of the four phase-local cached-dual roots. -/
def valueRoot (data : LocalPhaseData precision) :
    Vector (Value precision) 4 :=
  Vector.ofFn fun player ↦ (data.root.get player).value

/-- The scalar quitting payoff is the value projection of its phase-local
cached-dual computation. -/
theorem localOpponentQuitValue_value
    (data : LocalPhaseData precision) (who : Player) :
    (LocalInterval.localOpponentQuitValue data who).value =
      opponentQuitValueFromRoot (valueRoot data) who := by
  unfold LocalInterval.localOpponentQuitValue opponentQuitValueFromRoot
  rw [cachedSum_value]
  apply sum_congr
  intro mask
  have hprob := localMaskProbability_value data.root (valueRoot data)
    (fun player ↦ by simp [valueRoot]) mask (some who)
  by_cases hmask : maskHasPlayer mask who = true
  · simp [hmask, RationalPolynomial.CachedDyadicDual.constant]
  · simpa [hmask, LocalInterval.CachedDual.ofRat,
      RationalPolynomial.CachedDyadicDual.mul,
      RationalPolynomial.CachedDyadicDual.constant] using
      congrArg
        (fun value ↦
          (DyadicInterval.ofRat
            (terminalTable (maskWithPlayer mask who) who)).mul value)
        hprob

/-- The scalar opponent-absorption payoff is the value projection of its
phase-local cached-dual computation. -/
theorem localOpponentAbsorbingContribution_value
    (data : LocalPhaseData precision) (who : Player) :
    (LocalInterval.localOpponentAbsorbingContribution data who).value =
      opponentAbsorbingContributionFromRoot (valueRoot data) who := by
  unfold LocalInterval.localOpponentAbsorbingContribution
    opponentAbsorbingContributionFromRoot
  rw [cachedSum_value]
  apply sum_congr
  intro mask
  have hprob := localMaskProbability_value data.root (valueRoot data)
    (fun player ↦ by simp [valueRoot]) mask (some who)
  by_cases hzero : mask.val = 0
  · simp [hzero, RationalPolynomial.CachedDyadicDual.constant]
  · by_cases hwho : maskHasPlayer mask who = true
    · simp [hzero, hwho, RationalPolynomial.CachedDyadicDual.constant]
    · simpa [hzero, hwho, LocalInterval.CachedDual.ofRat,
        RationalPolynomial.CachedDyadicDual.mul,
        RationalPolynomial.CachedDyadicDual.constant] using
        congrArg
          (fun value ↦
            (DyadicInterval.ofRat (terminalTable mask who)).mul value)
          hprob

/-- Scalar opponent survival is the value projection of its phase-local
cached-dual computation. -/
theorem localOpponentSurvival_value
    (data : LocalPhaseData precision) (who : Player) :
    (LocalInterval.localOpponentSurvival data who).value =
      opponentSurvivalFromRoot (valueRoot data) who := by
  unfold LocalInterval.localOpponentSurvival opponentSurvivalFromRoot
  apply localMaskProbability_value
  intro player
  simp [valueRoot]

@[simp] theorem buildLocalPhaseData_valueRoot
    (box : HazardIndex → Value precision) (phase : Phase) :
    valueRoot (buildLocalPhaseData box phase) = buildRoot box phase := by
  apply Vector.ext
  intro player hplayer
  simp [valueRoot, buildLocalPhaseData, buildRoot, localRoot_value]

theorem buildLocalOpponentQuitValue_value
    (box : HazardIndex → Value precision)
    (phase : Phase) (who : Player) :
    (LocalInterval.localOpponentQuitValue
        (buildLocalPhaseData box phase) who).value =
      opponentQuitValue box phase who := by
  rw [localOpponentQuitValue_value]
  simp [opponentQuitValue]

theorem buildLocalOpponentAbsorbingContribution_value
    (box : HazardIndex → Value precision)
    (phase : Phase) (who : Player) :
    (LocalInterval.localOpponentAbsorbingContribution
        (buildLocalPhaseData box phase) who).value =
      opponentAbsorbingContribution box phase who := by
  rw [localOpponentAbsorbingContribution_value]
  simp [opponentAbsorbingContribution]

theorem buildLocalOpponentSurvival_value
    (box : HazardIndex → Value precision)
    (phase : Phase) (who : Player) :
    (LocalInterval.localOpponentSurvival
        (buildLocalPhaseData box phase) who).value =
      opponentSurvival box phase who := by
  rw [localOpponentSurvival_value]
  simp [opponentSurvival]

end LocalValue

namespace LocalInterval

variable {precision : ℕ}

/-- The lifted local quitting-payoff node agrees exactly with canonical
cached evaluation. -/
theorem lift_buildLocalOpponentQuitValue_eq_evalCachedDyadic
    (box : HazardIndex → DyadicInterval precision)
    (phase : Phase) (who : Player) :
    liftLocalDual phase
        (localOpponentQuitValue (buildLocalPhaseData box phase) who) =
      RationalPolynomial.evalCachedDyadic box
        (BlockPairK11.opponentQuitValue phase who) := by
  unfold localOpponentQuitValue BlockPairK11.opponentQuitValue
  rw [liftLocalDual_cachedSum, evalCachedDyadic_expressionSum]
  apply congrArg cachedSum
  funext mask
  have hprob := liftLocalMaskProbability_eq_evalCachedDyadic box phase
    (Vector.ofFn fun player ↦ localRoot box phase player)
    (fun player ↦ by
      simp only [Vector.get_ofFn]
      exact liftLocalRoot_eq_evalCachedDyadic box phase player)
    mask (some who)
  by_cases hmask : maskHasPlayer mask who = true
  · simp [hmask, RationalPolynomial.evalCachedDyadic]
  · simpa [hmask, buildLocalPhaseData, CachedDual.ofRat,
      RationalPolynomial.evalCachedDyadic] using
      congrArg
        (fun dual : RationalPolynomial.CachedDyadicDual precision 31 ↦
          (RationalPolynomial.CachedDyadicDual.constant
            (terminalTable (maskWithPlayer mask who) who)).mul dual)
        hprob

/-- The lifted local opponent-absorption node agrees exactly with canonical
cached evaluation. -/
theorem lift_buildLocalOpponentAbsorbingContribution_eq_evalCachedDyadic
    (box : HazardIndex → DyadicInterval precision)
    (phase : Phase) (who : Player) :
    liftLocalDual phase
        (localOpponentAbsorbingContribution
          (buildLocalPhaseData box phase) who) =
      RationalPolynomial.evalCachedDyadic box
        (BlockPairK11.opponentAbsorbingContribution phase who) := by
  unfold localOpponentAbsorbingContribution
    BlockPairK11.opponentAbsorbingContribution
  rw [liftLocalDual_cachedSum, evalCachedDyadic_expressionSum]
  apply congrArg cachedSum
  funext mask
  have hprob := liftLocalMaskProbability_eq_evalCachedDyadic box phase
    (Vector.ofFn fun player ↦ localRoot box phase player)
    (fun player ↦ by
      simp only [Vector.get_ofFn]
      exact liftLocalRoot_eq_evalCachedDyadic box phase player)
    mask (some who)
  by_cases hzero : mask.val = 0
  · simp [hzero, RationalPolynomial.evalCachedDyadic]
  · by_cases hwho : maskHasPlayer mask who = true
    · simp [hzero, hwho, RationalPolynomial.evalCachedDyadic]
    · simpa [hzero, hwho, buildLocalPhaseData, CachedDual.ofRat,
        RationalPolynomial.evalCachedDyadic] using
        congrArg
          (fun dual : RationalPolynomial.CachedDyadicDual precision 31 ↦
            (RationalPolynomial.CachedDyadicDual.constant
              (terminalTable mask who)).mul dual)
          hprob

/-- The lifted local opponent-survival node agrees exactly with canonical
cached evaluation. -/
theorem lift_buildLocalOpponentSurvival_eq_evalCachedDyadic
    (box : HazardIndex → DyadicInterval precision)
    (phase : Phase) (who : Player) :
    liftLocalDual phase
        (localOpponentSurvival (buildLocalPhaseData box phase) who) =
      RationalPolynomial.evalCachedDyadic box
        (BlockPairK11.opponentSurvival phase who) := by
  unfold localOpponentSurvival BlockPairK11.opponentSurvival
    buildLocalPhaseData
  apply liftLocalMaskProbability_eq_evalCachedDyadic
  intro player
  simp only [Vector.get_ofFn]
  exact liftLocalRoot_eq_evalCachedDyadic box phase player

end LocalInterval

end GameTheory.BlockPairK11
