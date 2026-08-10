/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeCapCarrier
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeKilledTailPotential
import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorAdmissibleChargedRelation

/-!
# A killed debt account from the canonical prefix capacity

The unaugmented optimized counterexample tail lies in the full
punishment-floor-admissible carrier.  Its chronological Nash--Bellman edge is
oriented backward in the charged predecessor relation, so the canonical
budget-to-go potential increases by at least the one-stage absorption charge
along chronological time.  Subtracting it from the canonical prefix-charge
bound gives a nonnegative remaining capacity which decreases by at least that
charge.

For player `who`, scale this remaining capacity by the positive singleton
debt cap.  The diagonal dynamic-debt seam is at most that cap times the
absorption charge, so the scaled capacity is an excessive account for the
exact killed debt source.  The result supplies a natural source-compatible
account; it does not show that its initial value equals exact debt or that its
surviving boundary dominates the exact debt boundary.  The final definition
records the initial mismatch explicitly.
-/

noncomputable section

namespace GameTheory

open Math.ChargedPathBudget Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {regime : QuittingCounterexampleRegime reward}

namespace QuittingCounterexampleSeamWitness

/-- The unaugmented counterexample-tail point, with its box and punishment-
floor certificates, as a state of the full admissible charged relation. -/
def killedCapacityAdmissibleState
    (seam : QuittingCounterexampleSeamWitness regime) (time : ℕ) :
    QuittingPunishmentFloorAdmissibleState reward :=
  ⟨⟨(seam.tail time).1, (seam.tail_mem time).1⟩,
    seam.punishmentValue_le_tailValue time⟩

/-- One chronological tail step, represented in the reverse orientation of
the charged predecessor relation. -/
def killedCapacityAdmissibleEdge
    (seam : QuittingCounterexampleSeamWitness regime) (time : ℕ) :
    QuittingPunishmentFloorAdmissibleEdge reward where
  tail := seam.killedCapacityAdmissibleState (time + 1)
  current := seam.killedCapacityAdmissibleState time
  exactEdge := (seam.tail_edge time).1

/-- The canonical admissible budget-to-go evaluated on the chronological
counterexample tail. -/
def killedCapacityPotential
    (seam : QuittingCounterexampleSeamWitness regime) (time : ℕ) : ℝ :=
  quittingPunishmentFloorAdmissiblePotential reward
    (seam.killedCapacityAdmissibleState time)

/-- The canonical prefix-charge bound bounds the admissible potential at
every counterexample-tail state. -/
theorem killedCapacityPotential_le_prefixChargeBound
    (seam : QuittingCounterexampleSeamWitness regime) (time : ℕ) :
    seam.killedCapacityPotential time ≤
      quittingPunishmentFloorPrefixChargeBound reward := by
  apply
    (quittingPunishmentFloorAdmissibleChargedRelation reward).value_le
      (quittingPunishmentFloorPrefixChargeBound_nonneg reward)
  intro target path
  rw [← QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix_charge
    path]
  exact regime.prefixCharge_le _

/-- Along chronological time, the canonical admissible potential increases
by at least the literal joint absorption charge. -/
theorem killedCapacityPotential_add_absorption_le_succ
    (seam : QuittingCounterexampleSeamWitness regime) (time : ℕ) :
    seam.killedCapacityPotential time +
        quittingDynamicDebtTailAbsorptionCharge seam.tail time ≤
      seam.killedCapacityPotential (time + 1) := by
  simpa [killedCapacityPotential, killedCapacityAdmissibleEdge,
    killedCapacityAdmissibleState,
    QuittingPunishmentFloorAdmissibleEdge.toBoxEdge,
    QuittingPunishmentFloorBoxEdge.absorptionCharge,
    QuittingPunishmentFloorBoxEdge.root,
    quittingDynamicDebtTailAbsorptionCharge] using
    quittingPunishmentFloorAdmissiblePotential_predecessor_decrement
      (hbound := regime.prefixCharge_le)
      (seam.killedCapacityAdmissibleEdge time)

/-- Capacity still available beyond the selected chronological tail state. -/
def killedRemainingCapacity
    (seam : QuittingCounterexampleSeamWitness regime) (time : ℕ) : ℝ :=
  quittingPunishmentFloorPrefixChargeBound reward -
    seam.killedCapacityPotential time

theorem killedRemainingCapacity_nonneg
    (seam : QuittingCounterexampleSeamWitness regime) (time : ℕ) :
    0 ≤ seam.killedRemainingCapacity time := by
  unfold killedRemainingCapacity
  linarith [seam.killedCapacityPotential_le_prefixChargeBound time]

/-- The remaining capacity pays the current absorption charge before passing
to the next chronological state. -/
theorem absorption_add_killedRemainingCapacity_succ_le
    (seam : QuittingCounterexampleSeamWitness regime) (time : ℕ) :
    quittingDynamicDebtTailAbsorptionCharge seam.tail time +
        seam.killedRemainingCapacity (time + 1) ≤
      seam.killedRemainingCapacity time := by
  unfold killedRemainingCapacity
  linarith [seam.killedCapacityPotential_add_absorption_le_succ time]

/-- The remaining capacity scaled by one player's singleton debt cap. -/
def killedCapacityDebtAccount
    (seam : QuittingCounterexampleSeamWitness regime)
    (who : ι) (time : ℕ) : ℝ :=
  quittingPositiveSingletonDebtCap reward who *
    seam.killedRemainingCapacity time

theorem killedCapacityDebtAccount_nonneg
    (seam : QuittingCounterexampleSeamWitness regime)
    (who : ι) (time : ℕ) :
    0 ≤ seam.killedCapacityDebtAccount who time :=
  mul_nonneg (le_max_left _ _) (seam.killedRemainingCapacity_nonneg time)

/-- The scaled remaining capacity pays the full diagonal debt source and
still dominates its un-killed successor account. -/
theorem killedDebtSource_add_capacityDebtAccount_succ_le
    (seam : QuittingCounterexampleSeamWitness regime)
    (who : ι) (time : ℕ) :
    seam.killedDebtSource who time +
        seam.killedCapacityDebtAccount who (time + 1) ≤
      seam.killedCapacityDebtAccount who time := by
  have hsource := quittingDynamicDebtSeam_le_cap_mul_absorptionMass
    (state := seam.tail time) (seam.tail_mem time) who
  have hremaining :=
    seam.absorption_add_killedRemainingCapacity_succ_le time
  have hcapNonneg :
      0 ≤ quittingPositiveSingletonDebtCap reward who := le_max_left _ _
  calc
    seam.killedDebtSource who time +
        seam.killedCapacityDebtAccount who (time + 1) ≤
      quittingPositiveSingletonDebtCap reward who *
          quittingDynamicDebtTailAbsorptionCharge seam.tail time +
        seam.killedCapacityDebtAccount who (time + 1) :=
      add_le_add (by
        simpa [killedDebtSource, quittingDynamicDebtTailAbsorptionCharge]
          using hsource) le_rfl
    _ = quittingPositiveSingletonDebtCap reward who *
        (quittingDynamicDebtTailAbsorptionCharge seam.tail time +
          seam.killedRemainingCapacity (time + 1)) := by
      simp [killedCapacityDebtAccount]
      ring
    _ ≤ quittingPositiveSingletonDebtCap reward who *
        seam.killedRemainingCapacity time :=
      mul_le_mul_of_nonneg_left hremaining hcapNonneg
    _ = seam.killedCapacityDebtAccount who time := rfl

/-- The capacity-derived account is excessive for the exact killed debt
source.  The proof weakens its stronger additive successor inequality by the
fact that joint Continue mass is at most one. -/
theorem killedCapacityDebtAccount_isKilledExcessive
    (seam : QuittingCounterexampleSeamWitness regime) (who : ι) :
    IsKilledExcessive seam.killedDebtSurvival
      (seam.killedDebtSource who) (seam.killedCapacityDebtAccount who) := by
  intro time
  have hadditive :=
    seam.killedDebtSource_add_capacityDebtAccount_succ_le who time
  have hcontinue : seam.killedDebtSurvival time ≤ 1 :=
    quittingStationaryContinueMass_le_one _
  have haccountNonneg := seam.killedCapacityDebtAccount_nonneg who (time + 1)
  calc
    seam.killedDebtSource who time +
        seam.killedDebtSurvival time *
          seam.killedCapacityDebtAccount who (time + 1) ≤
      seam.killedDebtSource who time +
        seam.killedCapacityDebtAccount who (time + 1) := by
      apply add_le_add le_rfl
      exact mul_le_of_le_one_left haccountNonneg hcontinue
    _ ≤ seam.killedCapacityDebtAccount who time := hadditive

/-- Exact initial normalization defect of the capacity-derived account
relative to the playerwise dynamic-debt reference. -/
def killedCapacityInitialMismatch
    (seam : QuittingCounterexampleSeamWitness regime)
    (who : ι) (start : ℕ) : ℝ :=
  seam.killedDebtReference who start -
    seam.killedCapacityDebtAccount who start

/-- Vanishing initial mismatch is exactly the missing equal-initial-value
hypothesis.  No sign or vanishing theorem for this quantity follows from the
landed capacity bounds. -/
theorem killedCapacityInitialMismatch_eq_zero_iff
    (seam : QuittingCounterexampleSeamWitness regime)
    (who : ι) (start : ℕ) :
    seam.killedCapacityInitialMismatch who start = 0 ↔
      seam.killedDebtReference who start =
        seam.killedCapacityDebtAccount who start := by
  simp [killedCapacityInitialMismatch, sub_eq_zero]

/-- Adding the exact mismatch arithmetically reanchors the capacity account
at the selected start.  This equality alone does not assert that the shifted
account remains excessive. -/
theorem killedCapacityDebtAccount_add_initialMismatch
    (seam : QuittingCounterexampleSeamWitness regime)
    (who : ι) (start : ℕ) :
    seam.killedCapacityDebtAccount who start +
        seam.killedCapacityInitialMismatch who start =
      seam.killedDebtReference who start := by
  unfold killedCapacityInitialMismatch
  ring

end QuittingCounterexampleSeamWitness

end GameTheory
