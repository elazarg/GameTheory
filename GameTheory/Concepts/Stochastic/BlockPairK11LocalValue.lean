/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.BlockPairK11LocalInterval

/-!
# Scalar phase-local dyadic evaluation for the block-pair K11 system

This evaluator computes interval values without materializing any gradient.
Its operations mirror the phase-local cached-dual evaluator, and the
projection theorems below prove that it is exactly the value component of
that already-sound evaluator.
-/

set_option autoImplicit false

namespace GameTheory.BlockPairK11.LocalValue

open LocalInterval Math.Interval

variable {precision : ℕ}

abbrev Value (precision : ℕ) := DyadicInterval precision

def sum : {count : ℕ} → (Fin count → Value precision) → Value precision
  | 0, _ => DyadicInterval.ofRat 0
  | count + 1, term =>
      sum (fun index ↦ term index.castSucc) |>.add
        (term (Fin.last count))

def product : {count : ℕ} →
    (Fin count → Value precision) → Value precision
  | 0, _ => DyadicInterval.ofRat 1
  | count + 1, factor =>
      product (fun index ↦ factor index.castSucc) |>.mul
        (factor (Fin.last count))

def root (box : HazardIndex → Value precision)
    (phase : Phase) (player : Player) : Value precision :=
  LocalInterval.localBox box phase player

def actionFactor (root : Vector (Value precision) 4)
    (mask : QuitterMask) (omitted : Option Player)
    (player : Player) : Value precision :=
  if omitted = some player then DyadicInterval.ofRat 1
  else if maskHasPlayer mask player then root.get player
  else (DyadicInterval.ofRat 1).add (root.get player).neg

def maskProbability (root : Vector (Value precision) 4)
    (mask : QuitterMask) (omitted : Option Player := none) :
    Value precision :=
  product fun player : Player ↦ actionFactor root mask omitted player

def buildRoot (box : HazardIndex → Value precision)
    (phase : Phase) : Vector (Value precision) 4 :=
  Vector.ofFn fun player ↦ root box phase player

def buildMaskProbabilities (root : Vector (Value precision) 4) :
    Vector (Value precision) 16 :=
  Vector.ofFn fun mask ↦ maskProbability root mask

/-- Compute one immediate-reward interval from four already-specialized root
intervals, without any derivative data. -/
def immediateFromRoot (root : Vector (Value precision) 4)
    (who : Player) : Value precision :=
  let probabilities := buildMaskProbabilities root
  sum fun mask : QuitterMask ↦
    (DyadicInterval.ofRat (terminalTable mask who)).mul
      (probabilities.get mask)

/-- Compute one immediate-reward interval without any derivative data. -/
def immediate (box : HazardIndex → Value precision)
    (phase : Phase) (who : Player) : Value precision :=
  immediateFromRoot (buildRoot box phase) who

/-- Compute one all-continue interval from specialized roots. -/
def survivalFromRoot (root : Vector (Value precision) 4) :
    Value precision :=
  maskProbability root 0

/-- Compute one all-continue interval without any derivative data. -/
def survival (box : HazardIndex → Value precision)
    (phase : Phase) : Value precision :=
  survivalFromRoot (buildRoot box phase)

theorem cachedSum_value {count : ℕ}
    (term : Fin count → LocalDual precision) :
    (cachedSum term).value = sum fun index ↦ (term index).value := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      simp only [cachedSum, sum,
        RationalPolynomial.CachedDyadicDual.add]
      rw [inductionHypothesis]

theorem cachedProduct_value {count : ℕ}
    (factor : Fin count → LocalDual precision) :
    (cachedProduct factor).value =
      product fun index ↦ (factor index).value := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      simp only [cachedProduct, product,
        RationalPolynomial.CachedDyadicDual.mul]
      rw [inductionHypothesis]

@[simp] theorem localRoot_value
    (box : HazardIndex → Value precision)
    (phase : Phase) (player : Player) :
    (localRoot box phase player).value = root box phase player := by
  unfold localRoot root LocalInterval.localBox
  cases hindex : fastActiveHazardIndex? phase player <;>
    simp [hindex, RationalPolynomial.CachedDyadicDual.constant,
      RationalPolynomial.CachedDyadicDual.ofVariable]

theorem localActionFactor_value
    (dualRoot : Vector (LocalDual precision) 4)
    (valueRoot : Vector (Value precision) 4)
    (hroot : ∀ player,
      (dualRoot.get player).value = valueRoot.get player)
    (mask : QuitterMask) (omitted : Option Player) (player : Player) :
    (localActionFactor dualRoot mask omitted player).value =
      actionFactor valueRoot mask omitted player := by
  by_cases homitted : omitted = some player
  · simp [localActionFactor, actionFactor, homitted,
      RationalPolynomial.CachedDyadicDual.constant]
  · by_cases hmask : maskHasPlayer mask player
    · simpa [localActionFactor, actionFactor, homitted, hmask] using
        hroot player
    · simp [localActionFactor, actionFactor, homitted, hmask,
        LocalInterval.CachedDual.sub,
        RationalPolynomial.CachedDyadicDual.constant,
        RationalPolynomial.CachedDyadicDual.add,
        RationalPolynomial.CachedDyadicDual.neg, hroot]

theorem localMaskProbability_value
    (dualRoot : Vector (LocalDual precision) 4)
    (valueRoot : Vector (Value precision) 4)
    (hroot : ∀ player,
      (dualRoot.get player).value = valueRoot.get player)
    (mask : QuitterMask) (omitted : Option Player := none) :
    (localMaskProbability dualRoot mask omitted).value =
      maskProbability valueRoot mask omitted := by
  rw [localMaskProbability, maskProbability, cachedProduct_value]
  apply congrArg product
  funext player
  exact localActionFactor_value dualRoot valueRoot hroot
    mask omitted player

/-- Scalar evaluation is exactly the value projection of the cached local
immediate evaluator. -/
theorem buildLocalImmediate_value
    (box : HazardIndex → Value precision)
    (phase : Phase) (who : Player) :
    (buildLocalImmediate box phase who).value =
      immediate box phase who := by
  simp only [buildLocalImmediate, localImmediateFromMaskProbabilities,
    buildLocalMaskProbabilities, LocalInterval.buildLocalRoot,
    immediate, immediateFromRoot, buildMaskProbabilities, buildRoot,
    Vector.get_ofFn]
  rw [cachedSum_value]
  apply congrArg sum
  funext mask
  simp only [LocalInterval.CachedDual.ofRat,
    RationalPolynomial.CachedDyadicDual.mul,
    RationalPolynomial.CachedDyadicDual.constant]
  rw [localMaskProbability_value]
  intro player
  simp only [Vector.get_ofFn, localRoot_value]

/-- Scalar survival is exactly the value projection of the cached local
survival evaluator. -/
theorem buildLocalSurvival_value
    (box : HazardIndex → Value precision) (phase : Phase) :
    (buildLocalSurvival box phase).value = survival box phase := by
  simp only [buildLocalSurvival, LocalInterval.buildLocalRoot, survival,
    survivalFromRoot, buildRoot]
  rw [localMaskProbability_value]
  intro player
  simp only [Vector.get_ofFn, localRoot_value]

end GameTheory.BlockPairK11.LocalValue
