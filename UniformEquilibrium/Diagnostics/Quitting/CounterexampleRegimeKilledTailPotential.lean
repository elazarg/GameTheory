/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.KilledTailPotential
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeDebtConservation

/-!
# Killed-potential accounting on a counterexample debt tail

This module specializes the scalar killed-potential API to the canonical
optimized exact dynamic-debt tail of a quitting counterexample.  For each
player, joint Continue mass is the survival coefficient, the diagonal debt
seam is the source, and exact dynamic debt is an exact reference potential.

The specialization also isolates the boundary premise needed to compare this
reference with any excessive account having the same source and initial
value.  If the excessive account's surviving terminal boundary dominates the
exact debt boundary, every positively weighted local dissipation in the
window vanishes.  Conversely, one strict positively weighted dissipation
forces the excessive account's boundary strictly below the debt boundary.

The boundary premise is not derived from the counterexample regime.  In
particular, the prescribed value and its dynamic-debt augmented cap do not
have the same initial value: their difference is exactly the (positive, for
the selected owner) dynamic debt.  Thus the results below retain the phantom
boundary explicitly and do not rule out the positive all-Continue plateau.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingCounterexampleSeamWitness

variable {regime : QuittingCounterexampleRegime reward}

/-- Joint Continue mass, viewed as the one-step survival coefficient on the
canonical counterexample tail. -/
def killedDebtSurvival
    (seam : QuittingCounterexampleSeamWitness regime) (time : ℕ) : ℝ :=
  quittingStationaryContinueMass
    (quittingDynamicDebtTailRoots seam.tail time)

/-- The diagonal debt seam, viewed as the source in scalar killed
accounting. -/
def killedDebtSource
    (seam : QuittingCounterexampleSeamWitness regime)
    (who : ι) (time : ℕ) : ℝ :=
  quittingDynamicDebtSeam (seam.tail time) who

/-- One coordinate of exact dynamic debt, viewed as the reference potential
in scalar killed accounting. -/
def killedDebtReference
    (seam : QuittingCounterexampleSeamWitness regime)
    (who : ι) (time : ℕ) : ℝ :=
  (seam.tail time).2 who

theorem killedDebtSurvival_nonneg
    (seam : QuittingCounterexampleSeamWitness regime) (time : ℕ) :
    0 ≤ seam.killedDebtSurvival time :=
  quittingStationaryContinueMass_nonneg _

/-- Exact dynamic-debt conservation is precisely the one-step killed
reference recursion. -/
theorem killedDebtReference_step
    (seam : QuittingCounterexampleSeamWitness regime)
    (who : ι) (time : ℕ) :
    seam.killedDebtReference who time =
      seam.killedDebtSource who time +
        seam.killedDebtSurvival time *
          seam.killedDebtReference who (time + 1) := by
  have hstep := quittingDynamicDebt_eq_continueMass_mul_add_seam
    (reward := reward) (seam.tail time) (seam.tail (time + 1))
      (seam.tail_edge time) (seam.tail_mem (time + 1)).2.1 who
  simpa only [killedDebtReference, killedDebtSource, killedDebtSurvival,
    quittingDynamicDebtTailRoots, add_comm] using hstep

/-- Playerwise exact dynamic debt is the exact killed reference account over
every finite counterexample-tail window.  The terminal debt boundary is not
dropped. -/
theorem killedDebtReference_eq_killedTailAccount
    (seam : QuittingCounterexampleSeamWitness regime)
    (who : ι) (start fuel : ℕ) :
    seam.killedDebtReference who start =
      killedTailAccount seam.killedDebtSurvival
        (seam.killedDebtSource who) (seam.killedDebtReference who)
          start fuel :=
  potential_eq_killedTailAccount seam.killedDebtSurvival
    (seam.killedDebtSource who) (seam.killedDebtReference who)
      (seam.killedDebtReference_step who) start fuel

/-- With the initial value pinned to exact debt, the debt boundary is exactly
the proposed account's boundary plus all of its killed dissipation.  Thus a
boundary comparison in the opposite direction has no hidden slack: it can
hold for an excessive account only when the whole dissipation sum vanishes. -/
theorem debtBoundary_eq_dissipationSum_add_potentialBoundary
    (seam : QuittingCounterexampleSeamWitness regime)
    (who : ι) (potential : ℕ → ℝ) (start fuel : ℕ)
    (hinitial : potential start = seam.killedDebtReference who start) :
    killedBoundaryRemainder seam.killedDebtSurvival
        (seam.killedDebtReference who) start fuel =
      killedSourceSum seam.killedDebtSurvival
          (killedDissipation seam.killedDebtSurvival
            (seam.killedDebtSource who) potential) start fuel +
        killedBoundaryRemainder seam.killedDebtSurvival potential
          start fuel := by
  have href := seam.killedDebtReference_eq_killedTailAccount who start fuel
  have hpotential := potential_eq_source_add_dissipationSum_add_boundary
    seam.killedDebtSurvival (seam.killedDebtSource who) potential start fuel
  unfold killedTailAccount at href
  linarith

/-- If an excessive account starts from the exact debt reference and its
surviving boundary dominates the exact debt boundary, its total killed
dissipation on the window is zero.  The displayed boundary comparison is the
model-specific premise not supplied by counterexample-tail extraction. -/
theorem killedDissipationSum_eq_zero_of_debtBoundary_le
    (seam : QuittingCounterexampleSeamWitness regime)
    (who : ι) (potential : ℕ → ℝ)
    (hexcessive : IsKilledExcessive seam.killedDebtSurvival
      (seam.killedDebtSource who) potential)
    (start fuel : ℕ)
    (hinitial : potential start = seam.killedDebtReference who start)
    (hboundary :
      killedBoundaryRemainder seam.killedDebtSurvival
          (seam.killedDebtReference who) start fuel ≤
        killedBoundaryRemainder seam.killedDebtSurvival potential
          start fuel) :
    killedSourceSum seam.killedDebtSurvival
        (killedDissipation seam.killedDebtSurvival
          (seam.killedDebtSource who) potential) start fuel = 0 := by
  exact killedDissipationSum_eq_zero_of_referenceBoundary_le
    seam.killedDebtSurvival (seam.killedDebtSource who) potential
      (seam.killedDebtReference who) seam.killedDebtSurvival_nonneg
      hexcessive (seam.killedDebtReference_step who) start fuel
      hinitial hboundary

/-- For an excessive account initialized at exact debt, domination of the
exact debt boundary is equivalent to vanishing of the full killed
dissipation sum.  This exposes why boundary domination cannot be obtained by
mere reanchoring: it is already the desired no-dissipation conclusion. -/
theorem debtBoundary_le_potentialBoundary_iff_dissipationSum_eq_zero
    (seam : QuittingCounterexampleSeamWitness regime)
    (who : ι) (potential : ℕ → ℝ)
    (hexcessive : IsKilledExcessive seam.killedDebtSurvival
      (seam.killedDebtSource who) potential)
    (start fuel : ℕ)
    (hinitial : potential start = seam.killedDebtReference who start) :
    (killedBoundaryRemainder seam.killedDebtSurvival
          (seam.killedDebtReference who) start fuel ≤
        killedBoundaryRemainder seam.killedDebtSurvival potential
          start fuel) ↔
      killedSourceSum seam.killedDebtSurvival
          (killedDissipation seam.killedDebtSurvival
            (seam.killedDebtSource who) potential) start fuel = 0 := by
  constructor
  · exact seam.killedDissipationSum_eq_zero_of_debtBoundary_le who
      potential hexcessive start fuel hinitial
  · intro hdissipation
    have hidentity :=
      seam.debtBoundary_eq_dissipationSum_add_potentialBoundary
        who potential start fuel hinitial
    linarith

/-- Under the same minimal boundary comparison, every local dissipation that
is reached with positive prefix survival vanishes. -/
theorem killedDissipation_eq_zero_of_debtBoundary_le
    (seam : QuittingCounterexampleSeamWitness regime)
    (who : ι) (potential : ℕ → ℝ)
    (hexcessive : IsKilledExcessive seam.killedDebtSurvival
      (seam.killedDebtSource who) potential)
    (start fuel offset : ℕ)
    (hoffset : offset ∈ Finset.range fuel)
    (hweight :
      0 < killedPrefixWeight seam.killedDebtSurvival start offset)
    (hinitial : potential start = seam.killedDebtReference who start)
    (hboundary :
      killedBoundaryRemainder seam.killedDebtSurvival
          (seam.killedDebtReference who) start fuel ≤
        killedBoundaryRemainder seam.killedDebtSurvival potential
          start fuel) :
    killedDissipation seam.killedDebtSurvival
        (seam.killedDebtSource who) potential (start + offset) = 0 := by
  apply killedDissipation_eq_zero_of_boundaryExhausts
    seam.killedDebtSurvival (seam.killedDebtSource who) potential
      seam.killedDebtSurvival_nonneg hexcessive start fuel offset
      hoffset hweight
  unfold BoundaryExhaustsSourceResidual
  have href := seam.killedDebtReference_eq_killedTailAccount who start fuel
  unfold killedTailAccount at href
  rw [hinitial, href]
  linarith

/-- One strict dissipation reached with positive prefix survival forces the
excessive account's surviving terminal boundary strictly below the exact debt
boundary.  This is the useful alternative when boundary dominance cannot be
proved. -/
theorem potentialBoundary_lt_debtBoundary_of_strictDissipation
    (seam : QuittingCounterexampleSeamWitness regime)
    (who : ι) (potential : ℕ → ℝ)
    (hexcessive : IsKilledExcessive seam.killedDebtSurvival
      (seam.killedDebtSource who) potential)
    (start fuel offset : ℕ)
    (hoffset : offset ∈ Finset.range fuel)
    (hweight :
      0 < killedPrefixWeight seam.killedDebtSurvival start offset)
    (hinitial : potential start = seam.killedDebtReference who start)
    (hstrict :
      seam.killedDebtSource who (start + offset) +
          seam.killedDebtSurvival (start + offset) *
            potential (start + offset + 1) <
        potential (start + offset)) :
    killedBoundaryRemainder seam.killedDebtSurvival potential start fuel <
      killedBoundaryRemainder seam.killedDebtSurvival
        (seam.killedDebtReference who) start fuel := by
  have hshortfall := boundary_lt_sourceResidual_of_strictDissipation
    seam.killedDebtSurvival (seam.killedDebtSource who) potential
      seam.killedDebtSurvival_nonneg hexcessive start fuel offset
      hoffset hweight hstrict
  have href := seam.killedDebtReference_eq_killedTailAccount who start fuel
  unfold killedTailAccount at href
  rw [hinitial, href] at hshortfall
  linarith

end QuittingCounterexampleSeamWitness

end GameTheory
