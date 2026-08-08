/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Holonomy.AllTailRepairValue
import UniformEquilibrium.Quitting.Boundary.Holonomy.Basic
import UniformEquilibrium.Quitting.Cycles.PhaseSwitchProfile
import UniformEquilibrium.Quitting.Terminal.TargetTail.DiagonalTargetTailSemantics

/-!
# Behavioral tail evaluation through a fixed finite prefix

This file is the semantic adapter between an actual phase-switch root
sequence and the coefficient-level boundary holonomy.  The prescribed
identity is an infinite-tail identity: the boundary is the actual terminal
value of the punishment root sequence.  The best-response identity below is
deliberately stated at the finite behavioral horizon, where the terminal
boundary is an arbitrary scalar.  Its Bellman maximum is the exact envelope
over all time-dependent unilateral hazards.

An unrestricted infinite-tail best-response identity would additionally need
an interchange theorem between the finite-prefix Bellman envelope and the
supremum over deviations in the attached tail.  This module does not silently
assume that theorem.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Actual tail boundary -/

/-- The prescribed boundary vector supplied by an actual punishment root
sequence. -/
def phaseSwitchPrescribedBoundary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (punish : ℕ → ι → PMF Bool) : ι → ℝ :=
  fun who => quittingRootSequenceTerminalValue reward punish who 0

omit [DecidableEq ι] in
@[simp] theorem phaseSwitchPrescribedBoundary_apply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (punish : ℕ → ι → PMF Bool) (who : ι) :
    phaseSwitchPrescribedBoundary reward punish who =
      quittingRootSequenceTerminalValue reward punish who 0 := rfl

/-! ## Exact prefix identities -/

/-- The finite-prefix affine map applied to the actual punishment payoff is
the prescribed payoff of the attached phase-switch profile. -/
theorem quittingPhaseSwitch_prescribedAt_eq_terminalValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan punish : ℕ → ι → PMF Bool) (switch : ℕ) (hswitch : 0 < switch)
    (who : ι) :
    (quittingFiniteBoundaryHolonomy reward plan 0 (switch - 1)).prescribedAt
        (phaseSwitchPrescribedBoundary reward punish) who =
      quittingRootSequenceTerminalValue reward
        (quittingPhaseSwitchRoots plan punish switch) who 0 := by
  have hlen : switch - 1 + 1 = switch := Nat.sub_add_cancel
    (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hswitch))
  change QuittingAffineSummary.eval
      ((quittingFiniteBoundaryHolonomy reward plan 0 (switch - 1)).prescribed who)
      (phaseSwitchPrescribedBoundary reward punish who) = _
  rw [quittingFiniteBoundaryHolonomy_prescribed_eval]
  simpa [phaseSwitchPrescribedBoundary, hlen] using
    (quittingRootSequenceTerminalValue_phaseSwitch_eq_finite
      reward plan punish switch who).symm

/-!
The following theorem is the exact finite behavioral counterpart.  The
finite best-response recursion is the unrestricted mixed-hazard envelope, so
this is the strongest identity available without an infinite-tail
prefix/supremum interchange.
-/

/-- The finite-prefix max-affine map applied to a terminal behavioral
boundary is the exact finite all-behavior best-response envelope. -/
theorem quittingPhaseSwitch_bestResponseAt_eq_finiteBehavioralEnvelope
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan : ℕ → ι → PMF Bool) (switch : ℕ) (hswitch : 0 < switch)
    (who : ι)
    (boundary : ℝ) :
    (quittingFiniteBoundaryHolonomy reward plan 0 (switch - 1)).boundaryEnvelopeAt
        (fun _ => boundary) who =
      quittingFiniteTerminalBestResponseValue reward plan who boundary
        0 switch := by
  change QuittingMaxAffineSummary.eval
      ((quittingFiniteBoundaryHolonomy reward plan 0 (switch - 1)).bestResponse who)
      boundary = _
  have hlen : switch - 1 + 1 = switch := Nat.sub_add_cancel
    (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hswitch))
  rw [quittingFiniteBoundaryHolonomy_bestResponse_eval]
  rw [hlen]

end GameTheory
