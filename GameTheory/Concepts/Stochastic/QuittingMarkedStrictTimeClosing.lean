/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Tactic

/-!
# Closing strict-time marked cycles

This file isolates the endpoint-charge bookkeeping needed when a cycle is
cut from a strictly time-advancing sequence of marked quitting-game suffixes.

An internal marked macro-step gives an opponent-survival product at most
`1 - β/4`.  The final macro-step includes the first root *after* the cut, so
its endpoint factor is absent from the repeated block.  Replacing that factor
by the recurrent start-root factor loses at most `nδ`, where in the quitting
application `n = |I|-1` and `δ` is the sup-coordinate distance between the
two endpoint roots.  Thus `nδ ≤ β/8` leaves a seam charge of `β/8`.

Two consecutive-distinct target labels suffice for playerwise contraction:
every player differs from either the internal target or the seam target.
The theorem below therefore gives every player's repeated-block opponent
product the common bound `1 - β/8`.

This is the finite scalar contraction theorem only.  The marked selection,
strict calendar-time advancement, near-return extraction, and game-facing
periodic closing hypotheses remain separate inputs.
-/

namespace GameTheory

namespace QuittingMarkedStrictTimeClosing

/-- Replacing the omitted endpoint factor by the recurrent start factor costs
at most their distance, because the preceding survival product lies in
`[0,1]`. -/
theorem seamCycleProduct_le
    {macroPrefix endpointFactor startFactor cycleProduct β loss : ℝ}
    (hprefix0 : 0 ≤ macroPrefix) (hprefix1 : macroPrefix ≤ 1)
    (hmacro : macroPrefix * endpointFactor ≤ 1 - β / 4)
    (hcycle : cycleProduct ≤ macroPrefix * startFactor)
    (hclose : |startFactor - endpointFactor| ≤ loss) :
    cycleProduct ≤ 1 - β / 4 + loss := by
  have hreplace :
      macroPrefix * startFactor ≤ macroPrefix * endpointFactor + loss := by
    have hlinear :
      macroPrefix * startFactor =
          macroPrefix * endpointFactor +
            macroPrefix * (startFactor - endpointFactor) := by
      ring
    have hterm : macroPrefix * (startFactor - endpointFactor) ≤ loss := by
      calc
      macroPrefix * (startFactor - endpointFactor) ≤
          |macroPrefix * (startFactor - endpointFactor)| := le_abs_self _
      _ = macroPrefix * |startFactor - endpointFactor| := by
        rw [abs_mul, abs_of_nonneg hprefix0]
      _ ≤ 1 * |startFactor - endpointFactor| := by
        exact mul_le_mul_of_nonneg_right hprefix1 (abs_nonneg _)
      _ ≤ loss := by simpa using hclose
    rw [hlinear]
    linarith
  linarith

/-- The quantitative endpoint replacement used by the marked strict-time
cycle: an inclusive `β/4` macro-charge leaves a `β/8` cyclic charge when
the endpoint-factor loss is at most `β/8`. -/
theorem seamCycleProduct_le_one_sub_eighth
    {macroPrefix endpointFactor startFactor cycleProduct β loss : ℝ}
    (hprefix0 : 0 ≤ macroPrefix) (hprefix1 : macroPrefix ≤ 1)
    (hmacro : macroPrefix * endpointFactor ≤ 1 - β / 4)
    (hcycle : cycleProduct ≤ macroPrefix * startFactor)
    (hclose : |startFactor - endpointFactor| ≤ loss)
    (hloss : loss ≤ β / 8) :
    cycleProduct ≤ 1 - β / 8 := by
  have hseam := seamCycleProduct_le
    hprefix0 hprefix1 hmacro hcycle hclose
  linarith

/-- **Strict-time marked-cycle contraction.**

`internalTarget` is the target label of one macro-step wholly inside the
cut block.  `seamTarget` is the target label of the final macro-step, whose
last root lies just beyond the cut.  The labels are distinct.  An internal
charge contracts every player other than `internalTarget`; the seam charge,
after endpoint replacement, contracts every player other than `seamTarget`.
Those two families cover all players.

In the quitting-game instantiation, `cycleProduct who` is the complete
opponent-continuation product of the repeated block for `who`, `prefix who`
is the final macro-product without its endpoint, and `startFactor` and
`endpointFactor` are the opponent-continuation masses at the recurrent start
and omitted endpoint roots. -/
theorem markedStrictTime_cycleProduct_le_one_sub_eighth
    {I : Type*}
    (internalTarget seamTarget : I)
    (cycleProduct macroPrefix endpointFactor startFactor : I → ℝ)
    (β loss : ℝ)
    (htargets : internalTarget ≠ seamTarget)
    (hβ0 : 0 ≤ β)
    (hinternal : ∀ who, who ≠ internalTarget →
      cycleProduct who ≤ 1 - β / 4)
    (hprefix0 : ∀ who, 0 ≤ macroPrefix who)
    (hprefix1 : ∀ who, macroPrefix who ≤ 1)
    (hseamMacro : ∀ who, who ≠ seamTarget →
      macroPrefix who * endpointFactor who ≤ 1 - β / 4)
    (hcycle : ∀ who, cycleProduct who ≤
      macroPrefix who * startFactor who)
    (hclose : ∀ who,
      |startFactor who - endpointFactor who| ≤ loss)
    (hloss : loss ≤ β / 8) :
    ∀ who, cycleProduct who ≤ 1 - β / 8 := by
  intro who
  by_cases hinternalTarget : who = internalTarget
  · subst who
    apply seamCycleProduct_le_one_sub_eighth
      (hprefix0 internalTarget) (hprefix1 internalTarget)
      (hseamMacro internalTarget htargets)
      (hcycle internalTarget) (hclose internalTarget) hloss
  · have hstrong := hinternal who hinternalTarget
    linarith

/-- Positive marked charge makes every opponent-survival product strictly
contracting, in the exact form consumed by periodic closing. -/
theorem markedStrictTime_cycleProduct_lt_one
    {I : Type*}
    (internalTarget seamTarget : I)
    (cycleProduct macroPrefix endpointFactor startFactor : I → ℝ)
    (β loss : ℝ)
    (htargets : internalTarget ≠ seamTarget)
    (hβ : 0 < β)
    (hinternal : ∀ who, who ≠ internalTarget →
      cycleProduct who ≤ 1 - β / 4)
    (hprefix0 : ∀ who, 0 ≤ macroPrefix who)
    (hprefix1 : ∀ who, macroPrefix who ≤ 1)
    (hseamMacro : ∀ who, who ≠ seamTarget →
      macroPrefix who * endpointFactor who ≤ 1 - β / 4)
    (hcycle : ∀ who, cycleProduct who ≤
      macroPrefix who * startFactor who)
    (hclose : ∀ who,
      |startFactor who - endpointFactor who| ≤ loss)
    (hloss : loss ≤ β / 8) :
    ∀ who, cycleProduct who < 1 := by
  have hbound := markedStrictTime_cycleProduct_le_one_sub_eighth
    internalTarget seamTarget cycleProduct macroPrefix endpointFactor startFactor
      β loss htargets hβ.le hinternal hprefix0 hprefix1 hseamMacro hcycle
      hclose hloss
  intro who
  have := hbound who
  linarith

/-- The corresponding denominator has the explicit common lower bound
`β/8`, so every `O(δ)` seam residual is amplified by at most `8/β`. -/
theorem eighth_le_cycleDenominator
    {I : Type*} (cycleProduct : I → ℝ) (β : ℝ)
    (hbound : ∀ who, cycleProduct who ≤ 1 - β / 8) :
    ∀ who, β / 8 ≤ 1 - cycleProduct who := by
  intro who
  linarith [hbound who]

end QuittingMarkedStrictTimeClosing

end GameTheory
