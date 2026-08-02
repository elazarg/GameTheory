/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.BlockPairK11System
import GameTheory.Concepts.Stochastic.QuittingCachedDyadicDual
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-!
# Phase-local sparse interval evaluation for the block-pair K11 system

Every one-phase formula depends on at most four hazards (in fact at most
three on the public support).  This evaluator differentiates those formulas
in four local coordinates, caches the sixteen mask probabilities, and only
then lifts the five phase summaries into the 31-dimensional global gradient.
-/

set_option autoImplicit false

namespace GameTheory

namespace BlockPairK11

namespace LocalInterval

variable {precision variableCount : ℕ}

abbrev GlobalDual (precision : ℕ) :=
  RationalPolynomial.CachedDyadicDual precision 31

abbrev LocalDual (precision : ℕ) :=
  RationalPolynomial.CachedDyadicDual precision 4

namespace CachedDual

def zero : RationalPolynomial.CachedDyadicDual precision variableCount :=
  .constant 0

def one : RationalPolynomial.CachedDyadicDual precision variableCount :=
  .constant 1

def ofRat (value : ℚ) :
    RationalPolynomial.CachedDyadicDual precision variableCount :=
  .constant value

def sub
    (first second :
      RationalPolynomial.CachedDyadicDual precision variableCount) :
    RationalPolynomial.CachedDyadicDual precision variableCount :=
  first.add second.neg

end CachedDual

def cachedSum : {count : ℕ} →
    (Fin count →
      RationalPolynomial.CachedDyadicDual precision variableCount) →
    RationalPolynomial.CachedDyadicDual precision variableCount
  | 0, _ => .constant 0
  | count + 1, term =>
      cachedSum (fun index ↦ term index.castSucc) |>.add
        (term (Fin.last count))

def cachedProduct : {count : ℕ} →
    (Fin count →
      RationalPolynomial.CachedDyadicDual precision variableCount) →
    RationalPolynomial.CachedDyadicDual precision variableCount
  | 0, _ => .constant 1
  | count + 1, factor =>
      cachedProduct (fun index ↦ factor index.castSucc) |>.mul
        (factor (Fin.last count))

/-- Number of active bits among players `0,...,fuel-1`. -/
def activePlayersBefore (mask : QuitterMask) : ℕ → ℕ
  | 0 => 0
  | fuel + 1 =>
      activePlayersBefore mask fuel +
        if maskHasPlayer mask (Fin.ofNat 4 fuel) then 1 else 0

def activePlayerCount (mask : QuitterMask) : ℕ :=
  activePlayersBefore mask 4

/-- Number of active hazards in phases `0,...,fuel-1`, computed from the
public support word. -/
def activePhasesBefore : ℕ → ℕ
  | 0 => 0
  | fuel + 1 =>
      activePhasesBefore fuel +
        activePlayerCount (supportMask (Fin.ofNat 11 fuel))

/-- Coordinate lookup computed directly from the public support word and its
lexicographic active-variable convention. -/
def activeHazardIndex? (phase : Phase) (player : Player) :
    Option HazardIndex :=
  let mask := supportMask phase
  if maskHasPlayer mask player then
    some (Fin.ofNat 31
      (activePhasesBefore phase.val +
        activePlayersBefore mask player.val))
  else none

private theorem activeHazardIndex?_sound_finite :
    ∀ phase player,
      match activeHazardIndex? phase player with
      | none => True
      | some index => activeSlot index = (phase, player) := by
  intro phase player
  fin_cases phase <;> fin_cases player <;>
    simp +decide [activeHazardIndex?, activePhasesBefore, activePlayerCount,
      activePlayersBefore]

private theorem activeHazardIndex?_roundtrip_finite :
    ∀ index,
      activeHazardIndex? (activeSlot index).1 (activeSlot index).2 =
        some index := by
  intro index
  fin_cases index <;> simp +decide

/-- The support-derived coordinate calculation is exactly inverse to the
public active-slot order. -/
theorem activeHazardIndex?_eq_some_iff
    (phase : Phase) (player : Player) (index : HazardIndex) :
    activeHazardIndex? phase player = some index ↔
      activeSlot index = (phase, player) := by
  constructor
  · intro hindex
    have hsound := activeHazardIndex?_sound_finite phase player
    rw [hindex] at hsound
    exact hsound
  · intro hslot
    simpa only [hslot] using activeHazardIndex?_roundtrip_finite index

theorem activeSlot_injective : Function.Injective activeSlot := by
  intro first second hslots
  have hfirst := activeHazardIndex?_roundtrip_finite first
  have hsecond := activeHazardIndex?_roundtrip_finite second
  have hlookup := congrArg
    (fun slot : Phase × Player ↦ activeHazardIndex? slot.1 slot.2) hslots
  rw [hfirst, hsecond] at hlookup
  exact Option.some.inj hlookup

theorem hazardExpression_activeSlot (index : HazardIndex) :
    hazardExpression (activeSlot index).1 (activeSlot index).2 =
      .var index := by
  fin_cases index <;> rfl

private theorem activeHazardIndex?_none_hazardExpression_zero_finite :
    ∀ phase player,
      activeHazardIndex? phase player = none →
        hazardExpression phase player = 0 := by
  intro phase player
  fin_cases phase <;> fin_cases player <;> simp +decide

theorem hazardExpression_eq_zero_of_activeHazardIndex?_eq_none
    {phase : Phase} {player : Player}
    (hindex : activeHazardIndex? phase player = none) :
    hazardExpression phase player = 0 :=
  activeHazardIndex?_none_hazardExpression_zero_finite phase player hindex

def localBox (box : HazardIndex → DyadicInterval precision)
    (phase : Phase) (player : Player) : DyadicInterval precision :=
  match activeHazardIndex? phase player with
  | some index => box index
  | none => DyadicInterval.ofRat 0

def localRoot (box : HazardIndex → DyadicInterval precision)
    (phase : Phase) (player : Player) : LocalDual precision :=
  match activeHazardIndex? phase player with
  | some _ =>
      RationalPolynomial.CachedDyadicDual.ofVariable
        (localBox box phase) player
  | none => .constant 0

def localActionFactor (root : Vector (LocalDual precision) 4)
    (mask : QuitterMask) (omitted : Option Player)
    (player : Player) : LocalDual precision :=
  if omitted = some player then .constant 1
  else if maskHasPlayer mask player then root.get player
  else CachedDual.sub (.constant 1) (root.get player)

def localMaskProbability (root : Vector (LocalDual precision) 4)
    (mask : QuitterMask) (omitted : Option Player := none) :
    LocalDual precision :=
  cachedProduct fun player : Player =>
    localActionFactor root mask omitted player

structure LocalPhaseData (precision : ℕ) where
  root : Vector (LocalDual precision) 4
  maskProbabilities : Vector (LocalDual precision) 16
  immediate : Vector (LocalDual precision) 4
  survival : LocalDual precision

def buildLocalPhaseData
    (box : HazardIndex → DyadicInterval precision) (phase : Phase) :
    LocalPhaseData precision :=
  let root : Vector (LocalDual precision) 4 :=
    Vector.ofFn fun player => localRoot box phase player
  let maskProbabilities : Vector (LocalDual precision) 16 :=
    Vector.ofFn fun mask => localMaskProbability root mask
  let immediate : Vector (LocalDual precision) 4 :=
    Vector.ofFn fun who =>
      cachedSum fun mask : QuitterMask =>
        (CachedDual.ofRat (terminalTable mask who)).mul
          (maskProbabilities.get mask)
  ⟨root, maskProbabilities, immediate, maskProbabilities.get 0⟩

/-- Embed a four-coordinate phase derivative into the public 31-coordinate
active-slot order. -/
def liftLocalDual (phase : Phase) (dual : LocalDual precision) :
    GlobalDual precision :=
  ⟨dual.value, Vector.ofFn fun index =>
    if (activeSlot index).1 = phase then
      dual.derivative.get (activeSlot index).2
    else DyadicInterval.ofInt 0⟩

private theorem cachedDual_ext
    {first second : GlobalDual precision}
    (hvalue : first.value = second.value)
    (hderivative : ∀ coordinate,
      first.derivative.get coordinate = second.derivative.get coordinate) :
    first = second := by
  cases first
  cases second
  simp only [RationalPolynomial.CachedDyadicDual.mk.injEq]
  exact ⟨hvalue, Vector.ext fun index hindex =>
    hderivative ⟨index, hindex⟩⟩

@[simp] theorem liftLocalDual_constant (phase : Phase) (value : ℚ) :
    liftLocalDual phase
        (RationalPolynomial.CachedDyadicDual.constant value :
          LocalDual precision) =
      (RationalPolynomial.CachedDyadicDual.constant value :
        GlobalDual precision) := by
  apply cachedDual_ext
  · rfl
  · intro coordinate
    simp [liftLocalDual,
      RationalPolynomial.CachedDyadicDual.constant]

@[simp] theorem liftLocalDual_add (phase : Phase)
    (first second : LocalDual precision) :
    liftLocalDual phase (first.add second) =
      (liftLocalDual phase first).add (liftLocalDual phase second) := by
  apply cachedDual_ext
  · rfl
  · intro coordinate
    by_cases hphase : (activeSlot coordinate).1 = phase
    · simp [liftLocalDual, RationalPolynomial.CachedDyadicDual.add, hphase]
    · simp [liftLocalDual, RationalPolynomial.CachedDyadicDual.add, hphase]

@[simp] theorem liftLocalDual_neg (phase : Phase)
    (dual : LocalDual precision) :
    liftLocalDual phase dual.neg = (liftLocalDual phase dual).neg := by
  apply cachedDual_ext
  · rfl
  · intro coordinate
    by_cases hphase : (activeSlot coordinate).1 = phase
    · simp [liftLocalDual, RationalPolynomial.CachedDyadicDual.neg, hphase]
    · simp [liftLocalDual, RationalPolynomial.CachedDyadicDual.neg, hphase]

@[simp] theorem liftLocalDual_mul (phase : Phase)
    (first second : LocalDual precision) :
    liftLocalDual phase (first.mul second) =
      (liftLocalDual phase first).mul (liftLocalDual phase second) := by
  apply cachedDual_ext
  · rfl
  · intro coordinate
    by_cases hphase : (activeSlot coordinate).1 = phase
    · simp [liftLocalDual, RationalPolynomial.CachedDyadicDual.mul, hphase]
    · simp [liftLocalDual, RationalPolynomial.CachedDyadicDual.mul, hphase]

@[simp] theorem liftLocalDual_sub (phase : Phase)
    (first second : LocalDual precision) :
    liftLocalDual phase (CachedDual.sub first second) =
      CachedDual.sub (liftLocalDual phase first)
        (liftLocalDual phase second) := by
  simp only [CachedDual.sub, liftLocalDual_add, liftLocalDual_neg]

theorem liftLocalDual_cachedSum (phase : Phase) {count : ℕ}
    (term : Fin count → LocalDual precision) :
    liftLocalDual phase (cachedSum term) =
      cachedSum fun index ↦ liftLocalDual phase (term index) := by
  induction count with
  | zero => simp [cachedSum]
  | succ count inductionHypothesis =>
      simp only [cachedSum, liftLocalDual_add]
      rw [inductionHypothesis]

theorem liftLocalDual_cachedProduct (phase : Phase) {count : ℕ}
    (factor : Fin count → LocalDual precision) :
    liftLocalDual phase (cachedProduct factor) =
      cachedProduct fun index ↦ liftLocalDual phase (factor index) := by
  induction count with
  | zero => simp [cachedProduct]
  | succ count inductionHypothesis =>
      simp only [cachedProduct, liftLocalDual_mul]
      rw [inductionHypothesis]

theorem evalCachedDyadic_expressionSum
    (box : HazardIndex → DyadicInterval precision) {count : ℕ}
    (term : Fin count → Expression) :
    RationalPolynomial.evalCachedDyadic box (expressionSum term) =
      cachedSum fun index ↦
        RationalPolynomial.evalCachedDyadic box (term index) := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      simp only [expressionSum, cachedSum,
        RationalPolynomial.evalCachedDyadic]
      rw [inductionHypothesis]

theorem evalCachedDyadic_expressionProduct
    (box : HazardIndex → DyadicInterval precision) {count : ℕ}
    (factor : Fin count → Expression) :
    RationalPolynomial.evalCachedDyadic box (expressionProduct factor) =
      cachedProduct fun index ↦
        RationalPolynomial.evalCachedDyadic box (factor index) := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      simp only [expressionProduct, cachedProduct,
        RationalPolynomial.evalCachedDyadic]
      rw [inductionHypothesis]

private theorem dyadicDual_ext
    {first second : RationalPolynomial.DyadicDual precision 31}
    (hvalue : first.value = second.value)
    (hderivative : ∀ coordinate,
      first.derivative coordinate = second.derivative coordinate) :
    first = second := by
  cases first
  cases second
  simp only [RationalPolynomial.DyadicDual.mk.injEq]
  exact ⟨hvalue, funext hderivative⟩

/-- The local root and the global reflected hazard have exactly the same
dyadic value and global derivative after lifting. -/
theorem liftLocalRoot_toDyadicDual
    (box : HazardIndex → DyadicInterval precision)
    (phase : Phase) (player : Player) :
    (liftLocalDual phase (localRoot box phase player)).toDyadicDual =
      RationalPolynomial.evalDualDyadic box
        (hazardExpression phase player) := by
  cases hindex : activeHazardIndex? phase player with
  | none =>
      have hexpression :=
        hazardExpression_eq_zero_of_activeHazardIndex?_eq_none hindex
      apply dyadicDual_ext
      · simp [liftLocalDual, localRoot, hindex, hexpression,
          RationalPolynomial.CachedDyadicDual.toDyadicDual,
          RationalPolynomial.evalDualDyadic,
          RationalPolynomial.CachedDyadicDual.constant,
          RationalPolynomial.DyadicDual.constant]
      · intro coordinate
        simp [liftLocalDual, localRoot, hindex, hexpression,
          RationalPolynomial.CachedDyadicDual.toDyadicDual,
          RationalPolynomial.evalDualDyadic,
          RationalPolynomial.CachedDyadicDual.constant,
          RationalPolynomial.DyadicDual.constant]
  | some index =>
      have hslot :=
        (activeHazardIndex?_eq_some_iff phase player index).1 hindex
      have hexpression : hazardExpression phase player = .var index := by
        have hphaseSlot : (activeSlot index).1 = phase := by
          simpa using congrArg Prod.fst hslot
        have hplayerSlot : (activeSlot index).2 = player := by
          simpa using congrArg Prod.snd hslot
        rw [← hphaseSlot, ← hplayerSlot]
        exact hazardExpression_activeSlot index
      apply dyadicDual_ext
      · simp [liftLocalDual, localRoot, localBox, hindex, hexpression,
          RationalPolynomial.CachedDyadicDual.toDyadicDual,
          RationalPolynomial.evalDualDyadic,
          RationalPolynomial.CachedDyadicDual.ofVariable,
          RationalPolynomial.DyadicDual.ofVariable]
      · intro coordinate
        by_cases hcoordinate : coordinate = index
        · subst coordinate
          simp [liftLocalDual, localRoot, localBox, hindex, hexpression,
            hslot, RationalPolynomial.CachedDyadicDual.toDyadicDual,
            RationalPolynomial.evalDualDyadic,
            RationalPolynomial.CachedDyadicDual.ofVariable,
            RationalPolynomial.DyadicDual.ofVariable]
        · by_cases hphase : (activeSlot coordinate).1 = phase
          · have hplayer : (activeSlot coordinate).2 ≠ player := by
              intro hplayer
              apply hcoordinate
              apply activeSlot_injective
              rw [hslot]
              exact Prod.ext hphase hplayer
            simp [liftLocalDual, localRoot, localBox, hindex, hexpression,
              hcoordinate, hphase, hplayer,
              RationalPolynomial.CachedDyadicDual.toDyadicDual,
              RationalPolynomial.evalDualDyadic,
              RationalPolynomial.CachedDyadicDual.ofVariable,
              RationalPolynomial.DyadicDual.ofVariable]
          · simp [liftLocalDual, localRoot, localBox, hindex, hexpression,
              hcoordinate, hphase,
              RationalPolynomial.CachedDyadicDual.toDyadicDual,
              RationalPolynomial.evalDualDyadic,
              RationalPolynomial.CachedDyadicDual.ofVariable,
              RationalPolynomial.DyadicDual.ofVariable]

/-- Cached local roots are literally the eager reflected evaluator after
lifting, not merely interval enclosures with matching semantics. -/
theorem liftLocalRoot_eq_evalCachedDyadic
    (box : HazardIndex → DyadicInterval precision)
    (phase : Phase) (player : Player) :
    liftLocalDual phase (localRoot box phase player) =
      RationalPolynomial.evalCachedDyadic box
        (hazardExpression phase player) := by
  apply RationalPolynomial.CachedDyadicDual.toDyadicDual_injective
  rw [liftLocalRoot_toDyadicDual,
    RationalPolynomial.toDyadicDual_evalCachedDyadic]

theorem liftLocalActionFactor_eq_evalCachedDyadic
    (box : HazardIndex → DyadicInterval precision) (phase : Phase)
    (root : Vector (LocalDual precision) 4)
    (hroot : ∀ player,
      liftLocalDual phase (root.get player) =
        RationalPolynomial.evalCachedDyadic box
          (hazardExpression phase player))
    (mask : QuitterMask) (omitted : Option Player) (player : Player) :
    liftLocalDual phase
        (localActionFactor root mask omitted player) =
      RationalPolynomial.evalCachedDyadic box
        (actionFactor phase mask omitted player) := by
  by_cases homitted : omitted = some player
  · simp [localActionFactor, actionFactor, homitted,
      RationalPolynomial.evalCachedDyadic]
  · by_cases hmask : maskHasPlayer mask player
    · simpa [localActionFactor, actionFactor, homitted, hmask] using
        hroot player
    · simp [localActionFactor, actionFactor, homitted, hmask,
        CachedDual.sub, hroot]
      rfl

theorem liftLocalMaskProbability_eq_evalCachedDyadic
    (box : HazardIndex → DyadicInterval precision) (phase : Phase)
    (root : Vector (LocalDual precision) 4)
    (hroot : ∀ player,
      liftLocalDual phase (root.get player) =
        RationalPolynomial.evalCachedDyadic box
          (hazardExpression phase player))
    (mask : QuitterMask) (omitted : Option Player := none) :
    liftLocalDual phase (localMaskProbability root mask omitted) =
      RationalPolynomial.evalCachedDyadic box
        (maskProbability phase mask omitted) := by
  rw [localMaskProbability, maskProbability,
    liftLocalDual_cachedProduct,
    evalCachedDyadic_expressionProduct]
  apply congrArg cachedProduct
  funext player
  exact liftLocalActionFactor_eq_evalCachedDyadic
    box phase root hroot mask omitted player

theorem lift_buildLocalPhaseData_maskProbability
    (box : HazardIndex → DyadicInterval precision)
    (phase : Phase) (mask : QuitterMask) :
    liftLocalDual phase
        ((buildLocalPhaseData box phase).maskProbabilities.get mask) =
      RationalPolynomial.evalCachedDyadic box
        (maskProbability phase mask) := by
  simp only [buildLocalPhaseData, Vector.get_ofFn]
  apply liftLocalMaskProbability_eq_evalCachedDyadic
  intro player
  simp only [Vector.get_ofFn]
  exact liftLocalRoot_eq_evalCachedDyadic box phase player

theorem lift_buildLocalPhaseData_immediate
    (box : HazardIndex → DyadicInterval precision)
    (phase : Phase) (who : Player) :
    liftLocalDual phase
        ((buildLocalPhaseData box phase).immediate.get who) =
      RationalPolynomial.evalCachedDyadic box
        (immediateReward phase who) := by
  simp only [buildLocalPhaseData, Vector.get_ofFn]
  rw [immediateReward, liftLocalDual_cachedSum,
    evalCachedDyadic_expressionSum]
  apply congrArg cachedSum
  funext mask
  simp only [liftLocalDual_mul, CachedDual.ofRat,
    liftLocalDual_constant, RationalPolynomial.evalCachedDyadic]
  rw [liftLocalMaskProbability_eq_evalCachedDyadic]
  intro player
  simp only [Vector.get_ofFn]
  exact liftLocalRoot_eq_evalCachedDyadic box phase player

theorem lift_buildLocalPhaseData_survival
    (box : HazardIndex → DyadicInterval precision)
    (phase : Phase) :
    liftLocalDual phase (buildLocalPhaseData box phase).survival =
      RationalPolynomial.evalCachedDyadic box
        (phaseSurvival phase) := by
  simp only [buildLocalPhaseData, Vector.get_ofFn]
  simpa only [phaseSurvival] using
    liftLocalMaskProbability_eq_evalCachedDyadic box phase
      (Vector.ofFn fun player ↦ localRoot box phase player)
      (fun player ↦ by
        simp only [Vector.get_ofFn]
        exact liftLocalRoot_eq_evalCachedDyadic box phase player)
      0

structure GlobalPhaseData (precision : ℕ) where
  immediate : Vector (GlobalDual precision) 4
  survival : GlobalDual precision

def liftPhaseData (phase : Phase) (data : LocalPhaseData precision) :
    GlobalPhaseData precision :=
  ⟨Vector.ofFn fun who => liftLocalDual phase (data.immediate.get who),
    liftLocalDual phase data.survival⟩

structure CycleData (precision : ℕ) where
  localPhases : Vector (LocalPhaseData precision) 11
  phases : Vector (GlobalPhaseData precision) 11
  jointSurvival : GlobalDual precision

def buildCycleData (box : HazardIndex → DyadicInterval precision) :
    CycleData precision :=
  let localPhases : Vector (LocalPhaseData precision) 11 :=
    Vector.ofFn fun phase => buildLocalPhaseData box phase
  let phases : Vector (GlobalPhaseData precision) 11 :=
    Vector.ofFn fun phase => liftPhaseData phase (localPhases.get phase)
  let jointSurvival := cachedProduct fun phase : Phase =>
    (phases.get phase).survival
  ⟨localPhases, phases, jointSurvival⟩

def numeratorAux (data : CycleData precision)
    (phase : Phase) (who : Player) :
    ℕ → GlobalDual precision × GlobalDual precision
  | 0 => (.constant 0, .constant 1)
  | fuel + 1 =>
      let previous := numeratorAux data phase who fuel
      let cyclePhase := phaseAdd phase fuel
      let phaseData := data.phases.get cyclePhase
      (previous.1.add
          (previous.2.mul (phaseData.immediate.get who)),
        previous.2.mul phaseData.survival)

def cyclicValueNumerator (data : CycleData precision)
    (phase : Phase) (who : Player) : GlobalDual precision :=
  (numeratorAux data phase who 11).1

def localOpponentQuitValue (data : LocalPhaseData precision)
    (who : Player) : LocalDual precision :=
  cachedSum fun mask : QuitterMask =>
    if maskHasPlayer mask who then .constant 0
    else
      (CachedDual.ofRat (terminalTable (maskWithPlayer mask who) who)).mul
        (localMaskProbability data.root mask (some who))

def localOpponentAbsorbingContribution
    (data : LocalPhaseData precision) (who : Player) :
    LocalDual precision :=
  cachedSum fun mask : QuitterMask =>
    if mask.val = 0 || maskHasPlayer mask who then .constant 0
    else
      (CachedDual.ofRat (terminalTable mask who)).mul
        (localMaskProbability data.root mask (some who))

def localOpponentSurvival (data : LocalPhaseData precision)
    (who : Player) : LocalDual precision :=
  localMaskProbability data.root 0 (some who)

def opponentQuitValue (data : CycleData precision)
    (phase : Phase) (who : Player) : GlobalDual precision :=
  liftLocalDual phase
    (localOpponentQuitValue (data.localPhases.get phase) who)

def opponentAbsorbingContribution (data : CycleData precision)
    (phase : Phase) (who : Player) : GlobalDual precision :=
  liftLocalDual phase
    (localOpponentAbsorbingContribution
      (data.localPhases.get phase) who)

def opponentSurvival (data : CycleData precision)
    (phase : Phase) (who : Player) : GlobalDual precision :=
  liftLocalDual phase
    (localOpponentSurvival (data.localPhases.get phase) who)

def activeEquationAt (data : CycleData precision)
    (phase : Phase) (who : Player) : GlobalDual precision :=
  CachedDual.sub
    ((CachedDual.sub (.constant 1) data.jointSurvival).mul
      (CachedDual.sub (opponentQuitValue data phase who)
        (opponentAbsorbingContribution data phase who)))
    ((opponentSurvival data phase who).mul
      (cyclicValueNumerator data (nextPhase phase) who))

end LocalInterval

end BlockPairK11

end GameTheory
