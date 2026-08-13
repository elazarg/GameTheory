/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Interval.RationalPolynomial
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic.Ring

/-!
# The reduced 31-variable block-pair period-eleven system

This file contains mathematical data, not a numerical witness: the integer
terminal table, the public support word, the active-variable order, and the
31 factored active-indifference equations.  The equations eliminate cyclic
continuation values using `V = N / (1 - ρ)` and clear the common positive
denominator.
-/

namespace GameTheory

namespace BlockPairK11

open Math.Interval
open scoped BigOperators

abbrev Player := Fin 4
abbrev Phase := Fin 11
abbrev HazardIndex := Fin 31
abbrev QuitterMask := Fin 16
abbrev Expression := RationalPolynomial 31

/-- The block-pair terminal table, with a harmless zero row at the empty
mask.  Rows `1,...,15` are the actual terminal rewards. -/
def terminalTable : QuitterMask → Player → ℚ := ![
  ![0, 0, 0, 0],
  ![-2, 8, 0, 0],
  ![4, 2, 0, 0],
  ![-5, -1, -1, 2],
  ![-4, 0, 2, 8],
  ![0, 4, 0, -4],
  ![-7, 0, 6, 3],
  ![-6, 1, -1, -3],
  ![-4, 0, 8, 2],
  ![-6, 3, 5, 6],
  ![-2, 6, 1, 2],
  ![-8, 3, 1, 4],
  ![1, 0, 3, 2],
  ![-7, -3, 0, 0],
  ![-2, 0, 6, 0],
  ![-10, -6, 1, -1]
]

/-- Public support word `[7,7,14,14,11,11,9,9,13,13,7]`. -/
def supportMask : Phase → QuitterMask :=
  ![7, 7, 14, 14, 11, 11, 9, 9, 13, 13, 7]

/-- Lexicographic phase/player order of the 31 active hazards. -/
def activeSlot : HazardIndex → Phase × Player := ![
  (0, 0), (0, 1), (0, 2),
  (1, 0), (1, 1), (1, 2),
  (2, 1), (2, 2), (2, 3),
  (3, 1), (3, 2), (3, 3),
  (4, 0), (4, 1), (4, 3),
  (5, 0), (5, 1), (5, 3),
  (6, 0), (6, 3),
  (7, 0), (7, 3),
  (8, 0), (8, 2), (8, 3),
  (9, 0), (9, 2), (9, 3),
  (10, 0), (10, 1), (10, 2)
]

/-- Sparse phase/player hazard matrix in the same active-variable order. -/
def hazardExpression : Phase → Player → Expression := ![
  ![.var 0, .var 1, .var 2, 0],
  ![.var 3, .var 4, .var 5, 0],
  ![0, .var 6, .var 7, .var 8],
  ![0, .var 9, .var 10, .var 11],
  ![.var 12, .var 13, 0, .var 14],
  ![.var 15, .var 16, 0, .var 17],
  ![.var 18, 0, 0, .var 19],
  ![.var 20, 0, 0, .var 21],
  ![.var 22, 0, .var 23, .var 24],
  ![.var 25, 0, .var 26, .var 27],
  ![.var 28, .var 29, .var 30, 0]
]

/-- An ordered finite sum that does not require quotienting expression trees
by commutative-monoid laws. -/
def expressionSum : {count : ℕ} → (Fin count → Expression) → Expression
  | 0, _ => 0
  | count + 1, term =>
      expressionSum (fun index ↦ term index.castSucc) + term (Fin.last count)

/-- An ordered finite product for factored expression trees. -/
def expressionProduct : {count : ℕ} →
    (Fin count → Expression) → Expression
  | 0, _ => 1
  | count + 1, factor =>
      expressionProduct (fun index ↦ factor index.castSucc) *
        factor (Fin.last count)

def maskHasPlayer (mask : QuitterMask) (player : Player) : Bool :=
  mask.val.testBit player.val

def phaseAdd (phase : Phase) (offset : ℕ) : Phase :=
  Fin.ofNat 11 (phase.val + offset)

def nextPhase (phase : Phase) : Phase :=
  phaseAdd phase 1

def actionFactor (phase : Phase) (mask : QuitterMask)
    (omitted : Option Player) (player : Player) : Expression :=
  if omitted = some player then 1
  else if maskHasPlayer mask player then hazardExpression phase player
  else 1 - hazardExpression phase player

/-- Product probability of a quitter mask, optionally omitting one player's
coordinate. -/
def maskProbability (phase : Phase) (mask : QuitterMask)
    (omitted : Option Player := none) : Expression :=
  expressionProduct fun player : Player =>
    actionFactor phase mask omitted player

/-- Expected absorbing reward contributed at one phase. -/
def immediateReward (phase : Phase) (who : Player) : Expression :=
  expressionSum fun mask : QuitterMask =>
    .constant (terminalTable mask who) * maskProbability phase mask

/-- Joint all-continue probability at one phase. -/
def phaseSurvival (phase : Phase) : Expression :=
  maskProbability phase 0

/-- Joint survival through one full public cycle. -/
def jointCycleSurvival : Expression :=
  expressionProduct phaseSurvival

/-- Accumulate the cyclic payoff numerator and the current survival prefix. -/
def numeratorAux (phase : Phase) (who : Player) :
    ℕ → Expression × Expression
  | 0 => (0, 1)
  | fuel + 1 =>
      let previous := numeratorAux phase who fuel
      let cyclePhase := phaseAdd phase fuel
      (previous.1 + previous.2 * immediateReward cyclePhase who,
        previous.2 * phaseSurvival cyclePhase)

/-- Numerator `N_i^k` of the exact cyclic value
`V_i^k = N_i^k / (1 - ρ)`. -/
def cyclicValueNumerator (phase : Phase) (who : Player) : Expression :=
  (numeratorAux phase who 11).1

/-! ## Real semantics of the named numerator recurrence -/

/-- Real scalar version of the canonical ordered numerator recurrence. -/
def realNumeratorAux (immediate survival : ℕ → ℝ) : ℕ → ℝ × ℝ
  | 0 => (0, 1)
  | fuel + 1 =>
      let previous := realNumeratorAux immediate survival fuel
      (previous.1 + previous.2 * immediate fuel,
        previous.2 * survival fuel)

@[simp] theorem realNumeratorAux_succ
    (immediate survival : ℕ → ℝ) (fuel : ℕ) :
    realNumeratorAux immediate survival (fuel + 1) =
      let previous := realNumeratorAux immediate survival fuel
      (previous.1 + previous.2 * immediate fuel,
        previous.2 * survival fuel) := by
  rfl

/-- An ordered scalar numerator fold decomposes at its first phase without
expanding the remaining prefix. -/
theorem realNumeratorAux_prepend
    (immediate survival : ℕ → ℝ) (fuel : ℕ) :
    realNumeratorAux immediate survival (fuel + 1) =
      let tail := realNumeratorAux
        (fun offset ↦ immediate (offset + 1))
        (fun offset ↦ survival (offset + 1)) fuel
      (immediate 0 + survival 0 * tail.1,
        survival 0 * tail.2) := by
  induction fuel with
  | zero => simp [realNumeratorAux]
  | succ fuel inductionHypothesis =>
      rw [realNumeratorAux_succ, inductionHypothesis]
      simp only [realNumeratorAux]
      ring_nf

/-- The survival component of an ordered scalar numerator is the ordered
product of its survival inputs. -/
theorem realNumeratorAux_survival_eq_prod
    (immediate survival : ℕ → ℝ) (fuel : ℕ) :
    (realNumeratorAux immediate survival fuel).2 =
      ∏ index : Fin fuel, survival index.val := by
  induction fuel with
  | zero => simp [realNumeratorAux]
  | succ fuel inductionHypothesis =>
      rw [realNumeratorAux_succ]
      simp only
      rw [Fin.prod_univ_castSucc, inductionHypothesis]
      rfl

/-- Real evaluation commutes with the canonical expression product. -/
theorem evalReal_expressionProduct_eq_prod {count : ℕ}
    (x : HazardIndex → ℝ) (factor : Fin count → Expression) :
    RationalPolynomial.evalReal x (expressionProduct factor) =
      ∏ index, RationalPolynomial.evalReal x (factor index) := by
  induction count with
  | zero => simp [expressionProduct, RationalPolynomial.evalReal]
  | succ count inductionHypothesis =>
      simp only [expressionProduct, RationalPolynomial.evalReal]
      rw [inductionHypothesis, Fin.prod_univ_castSucc]

/-- Evaluating the canonical expression numerator yields the matching named
scalar recurrence at every ordered prefix. -/
theorem evalReal_numeratorAux_eq_realNumeratorAux
    (x : HazardIndex → ℝ) (phase : Phase) (who : Player) (fuel : ℕ) :
    (RationalPolynomial.evalReal x (numeratorAux phase who fuel).1,
      RationalPolynomial.evalReal x (numeratorAux phase who fuel).2) =
      realNumeratorAux
        (fun offset ↦ RationalPolynomial.evalReal x
          (immediateReward (phaseAdd phase offset) who))
        (fun offset ↦ RationalPolynomial.evalReal x
          (phaseSurvival (phaseAdd phase offset))) fuel := by
  induction fuel with
  | zero =>
      norm_num [numeratorAux, realNumeratorAux,
        RationalPolynomial.evalReal]
  | succ fuel inductionHypothesis =>
      simp only [numeratorAux, realNumeratorAux]
      change
        (RationalPolynomial.evalReal x (numeratorAux phase who fuel).1 +
            RationalPolynomial.evalReal x (numeratorAux phase who fuel).2 *
              RationalPolynomial.evalReal x
                (immediateReward (phaseAdd phase fuel) who),
          RationalPolynomial.evalReal x (numeratorAux phase who fuel).2 *
            RationalPolynomial.evalReal x
              (phaseSurvival (phaseAdd phase fuel))) = _
      have hfirst := congrArg Prod.fst inductionHypothesis
      have hsecond := congrArg Prod.snd inductionHypothesis
      simp only at hfirst hsecond
      rw [hfirst, hsecond]

theorem phaseAdd_nextPhase (phase : Phase) (offset : ℕ) :
    phaseAdd (nextPhase phase) offset = phaseAdd phase (offset + 1) := by
  apply Fin.ext
  simp [phaseAdd, nextPhase, Fin.ofNat, Nat.add_mod]
  omega

theorem phaseAdd_nextPhase_ten (phase : Phase) :
    phaseAdd (nextPhase phase) 10 = phase := by
  apply Fin.ext
  simp [phaseAdd, nextPhase, Fin.ofNat, Nat.add_mod]
  omega

theorem phaseAdd_eq_addLeft (phase offset : Phase) :
    phaseAdd phase offset.val = Equiv.addLeft phase offset := by
  apply Fin.ext
  simp [phaseAdd, Fin.ofNat, Fin.add_def]

/-- Eleven-step scalar numerator fold beginning at a named phase. -/
def realCycleNumerator (immediate survival : Phase → ℝ)
    (phase : Phase) : ℝ × ℝ :=
  realNumeratorAux (fun offset ↦ immediate (phaseAdd phase offset))
    (fun offset ↦ survival (phaseAdd phase offset)) 11

/-- Rotation identity for the named eleven-step numerator fold.  The proof
uses only the first and last recurrence nodes. -/
theorem realCycleNumerator_recurrence
    (immediate survival : Phase → ℝ) (phase : Phase) :
    (realCycleNumerator immediate survival phase).1 =
      (1 - (realCycleNumerator immediate survival phase).2) *
          immediate phase +
        survival phase *
          (realCycleNumerator immediate survival (nextPhase phase)).1 := by
  let tail := realNumeratorAux
    (fun offset ↦ immediate (phaseAdd phase (offset + 1)))
    (fun offset ↦ survival (phaseAdd phase (offset + 1))) 10
  have hphase := realNumeratorAux_prepend
    (fun offset ↦ immediate (phaseAdd phase offset))
    (fun offset ↦ survival (phaseAdd phase offset)) 10
  have hnext := realNumeratorAux_succ
    (fun offset ↦ immediate (phaseAdd (nextPhase phase) offset))
    (fun offset ↦ survival (phaseAdd (nextPhase phase) offset)) 10
  have htailNext :
      realNumeratorAux
          (fun offset ↦ immediate (phaseAdd (nextPhase phase) offset))
          (fun offset ↦ survival (phaseAdd (nextPhase phase) offset)) 10 =
        tail := by
    apply congrArg₂ (fun first second ↦
      realNumeratorAux first second 10)
    · funext offset
      rw [phaseAdd_nextPhase]
    · funext offset
      rw [phaseAdd_nextPhase]
  simp only [realCycleNumerator]
  rw [hphase]
  change
    immediate (phaseAdd phase 0) + survival (phaseAdd phase 0) * tail.1 =
      (1 - survival (phaseAdd phase 0) * tail.2) * immediate phase +
        survival phase *
          (realNumeratorAux
            (fun offset ↦ immediate (phaseAdd (nextPhase phase) offset))
            (fun offset ↦ survival (phaseAdd (nextPhase phase) offset))
            11).1
  rw [hnext, htailNext]
  simp only [phaseAdd_nextPhase_ten]
  have hzero : phaseAdd phase 0 = phase := by
    apply Fin.ext
    simp [phaseAdd, Fin.ofNat]
  rw [hzero]
  ring_nf

/-- The survival component of every rotated real cycle numerator is the
evaluation of the canonical full-cycle survival expression. -/
theorem realCycleNumerator_survival_eq_evalReal_jointCycleSurvival
    (x : HazardIndex → ℝ) (immediate : Phase → ℝ) (phase : Phase) :
    (realCycleNumerator immediate
      (fun current ↦ RationalPolynomial.evalReal x
        (phaseSurvival current)) phase).2 =
      RationalPolynomial.evalReal x jointCycleSurvival := by
  unfold realCycleNumerator jointCycleSurvival
  rw [realNumeratorAux_survival_eq_prod,
    evalReal_expressionProduct_eq_prod]
  have hrotate := Equiv.prod_comp (Equiv.addLeft phase)
    (fun current : Phase ↦ RationalPolynomial.evalReal x
      (phaseSurvival current))
  simpa only [phaseAdd_eq_addLeft] using hrotate

/-- Real evaluation of a canonical cyclic numerator is the corresponding
named scalar cycle fold. -/
theorem evalReal_cyclicValueNumerator_eq_realCycleNumerator
    (x : HazardIndex → ℝ) (phase : Phase) (who : Player) :
    RationalPolynomial.evalReal x (cyclicValueNumerator phase who) =
      (realCycleNumerator
        (fun current ↦ RationalPolynomial.evalReal x
          (immediateReward current who))
        (fun current ↦ RationalPolynomial.evalReal x
          (phaseSurvival current)) phase).1 := by
  unfold cyclicValueNumerator realCycleNumerator
  exact congrArg Prod.fst
    (evalReal_numeratorAux_eq_realNumeratorAux x phase who 11)

/-- The evaluated canonical cyclic numerator satisfies its one-phase
denominator-cleared Bellman recurrence. -/
theorem evalReal_cyclicValueNumerator_recurrence
    (x : HazardIndex → ℝ) (phase : Phase) (who : Player) :
    RationalPolynomial.evalReal x (cyclicValueNumerator phase who) =
      (1 - RationalPolynomial.evalReal x jointCycleSurvival) *
          RationalPolynomial.evalReal x (immediateReward phase who) +
        RationalPolynomial.evalReal x (phaseSurvival phase) *
          RationalPolynomial.evalReal x
            (cyclicValueNumerator (nextPhase phase) who) := by
  rw [evalReal_cyclicValueNumerator_eq_realCycleNumerator,
    evalReal_cyclicValueNumerator_eq_realCycleNumerator]
  have hrecurrence := realCycleNumerator_recurrence
    (fun current ↦ RationalPolynomial.evalReal x
      (immediateReward current who))
    (fun current ↦ RationalPolynomial.evalReal x
      (phaseSurvival current)) phase
  rw [realCycleNumerator_survival_eq_evalReal_jointCycleSurvival]
    at hrecurrence
  exact hrecurrence

def maskWithPlayer (mask : QuitterMask) (who : Player) : QuitterMask :=
  Fin.ofNat 16 (mask.val + 2 ^ who.val)

/-- Payoff from quitting now against the phase's fixed opponent hazards. -/
def opponentQuitValue (phase : Phase) (who : Player) : Expression :=
  expressionSum fun mask : QuitterMask =>
    if maskHasPlayer mask who then 0
    else
      .constant (terminalTable (maskWithPlayer mask who) who) *
        maskProbability phase mask (some who)

/-- Absorbing payoff produced by the opponents when `who` continues. -/
def opponentAbsorbingContribution
    (phase : Phase) (who : Player) : Expression :=
  expressionSum fun mask : QuitterMask =>
    if mask.val = 0 || maskHasPlayer mask who then 0
    else
      .constant (terminalTable mask who) *
        maskProbability phase mask (some who)

/-- Probability that all opponents of `who` continue at one phase. -/
def opponentSurvival (phase : Phase) (who : Player) : Expression :=
  maskProbability phase 0 (some who)

/-- Denominator-cleared active indifference equation

`H_i^k = (1 - ρ) (Q_i^k - A_i^k) - c_i^k N_i^(k+1)`.
-/
def activeEquationAt (phase : Phase) (who : Player) : Expression :=
  (1 - jointCycleSurvival) *
      (opponentQuitValue phase who -
        opponentAbsorbingContribution phase who) -
    opponentSurvival phase who *
      cyclicValueNumerator (nextPhase phase) who

/-- The reduced 31-equation system in `activeSlot` order. -/
def activeEquation (equation : HazardIndex) : Expression :=
  activeEquationAt (activeSlot equation).1 (activeSlot equation).2

end BlockPairK11

end GameTheory
