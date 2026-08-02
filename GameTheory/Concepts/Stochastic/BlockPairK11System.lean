/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingRationalPolynomial
import Mathlib.Data.Fin.VecNotation

/-!
# The reduced 31-variable block-pair period-eleven system

This file contains mathematical data, not a numerical witness: the integer
terminal table, the public support word, the active-variable order, and the
31 factored active-indifference equations.  The equations eliminate cyclic
continuation values using `V = N / (1 - ρ)` and clear the common positive
denominator.
-/

set_option autoImplicit false

namespace GameTheory

namespace BlockPairK11

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
