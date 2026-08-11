/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentTwoOwnerPacketDichotomy

/-!
# Collapse of auxiliary physical gates for exact two-owner packet edges

The strict-cell theorem for a compatible two-owner tangent packet asks for a
continuation floor and a scalar upper box.  Those bounds are useful when the
edge must remain inside a prescribed viable carrier, but neither bound appears
in the theorem's exact Nash--Bellman edge conclusion.

For bare exact-edge existence they can therefore be recentered around the
packet boundary: use the artificial floor `boundary - 1` and enlarge any weak
boundary upper bound from `upper` to `upper + 1`.  The punishment-floor and
upper-box equality branches disappear completely.  The only remaining local
gate on the exact two-owner ray is a tight inactive singleton row, whose
higher coalition regression still has an uncontrolled sign.

This does not make the resulting continuation punishment-admissible for the
original floor, and it does not construct a return or chronological splice.
It isolates the exact-edge producer from those later viability obligations.
-/

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingChargeTangentPacket

/-- Strict inactive singleton slack alone produces nearby positive-charge
exact Nash--Bellman edges.  The continuation floor and upper box used by the
strict-cell theorem are auxiliary and may be recentered away. -/
theorem eventually_exists_positiveChargeExactEdge_of_outsideSolo_lt_boundary
    (packet : QuittingChargeTangentPacket reward)
    (upper : ℝ) (first second : ι)
    (hne : first ≠ second)
    (hfirst : 0 < packet.mass first) (hsecond : 0 < packet.mass second)
    (houtsideMass : ∀ owner, owner ≠ first → owner ≠ second →
      packet.mass owner = 0)
    (hcompatFirst : quittingActivePairCompatibilityResidual packet first = 0)
    (hcompatSecond : quittingActivePairCompatibilityResidual packet second = 0)
    (hboundaryUpper : ∀ who, packet.boundary who ≤ upper)
    (houtsideSolo : ∀ who, who ≠ first → who ≠ second →
      reward (quittingSingletonTerminal who) who < packet.boundary who) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ∃ root : ι → PMF Bool, ∃ continuation : Payoff ι,
        hazardOfRoot root = packet.twoOwnerHazardAt first second t ∧
        0 < quittingRootAbsorptionMass root ∧
        ∀ tailRoot : QuittingRootSimplex ι,
          IsQuittingNashBellmanEdge reward
            (packet.boundary, quittingFrozenRootLiftSimplex root)
            (continuation, tailRoot) := by
  have hfloor : ∀ who, packet.boundary who - 1 < packet.boundary who := by
    intro who
    linarith
  have hupper : ∀ who, packet.boundary who < upper + 1 := by
    intro who
    linarith [hboundaryUpper who]
  exact packet.eventually_exists_positiveChargeExactEdge_of_strictPhysicalCell
    (fun who => packet.boundary who - 1) (upper + 1) first second
    hne hfirst hsecond houtsideMass hcompatFirst hcompatSecond
    hfloor hupper houtsideSolo

/-- **Exact-edge gate collapse.**  On a compatible literal two-owner packet,
either every sufficiently small positive scale supplies a positive-charge
exact Nash--Bellman edge, or an inactive owner is singleton-tight at the
packet boundary.

In particular, punishment-floor tightness and upper-box tightness are not
exact-edge obstructions.  They belong only to a later viability or attachment
problem. -/
theorem positiveChargeExactEdge_or_tightOutsiderSingletonGate
    (packet : QuittingChargeTangentPacket reward)
    (upper : ℝ) (first second : ι)
    (hne : first ≠ second)
    (hfirst : 0 < packet.mass first) (hsecond : 0 < packet.mass second)
    (houtsideMass : ∀ owner, owner ≠ first → owner ≠ second →
      packet.mass owner = 0)
    (hcompatFirst : quittingActivePairCompatibilityResidual packet first = 0)
    (hcompatSecond : quittingActivePairCompatibilityResidual packet second = 0)
    (hboundaryUpper : ∀ who, packet.boundary who ≤ upper) :
    (∀ᶠ t in 𝓝[>] (0 : ℝ),
      ∃ root : ι → PMF Bool, ∃ continuation : Payoff ι,
        hazardOfRoot root = packet.twoOwnerHazardAt first second t ∧
        0 < quittingRootAbsorptionMass root ∧
        ∀ tailRoot : QuittingRootSimplex ι,
          IsQuittingNashBellmanEdge reward
            (packet.boundary, quittingFrozenRootLiftSimplex root)
            (continuation, tailRoot)) ∨
      ∃ who, who ≠ first ∧ who ≠ second ∧
        reward (quittingSingletonTerminal who) who = packet.boundary who := by
  by_cases houtsideStrict : ∀ who, who ≠ first → who ≠ second →
      reward (quittingSingletonTerminal who) who < packet.boundary who
  · exact Or.inl <|
      packet.eventually_exists_positiveChargeExactEdge_of_outsideSolo_lt_boundary
        upper first second hne hfirst hsecond houtsideMass
        hcompatFirst hcompatSecond hboundaryUpper houtsideStrict
  · push Not at houtsideStrict
    obtain ⟨who, hwhoFirst, hwhoSecond, hnot⟩ := houtsideStrict
    have hle := packet.solo_le_boundary who
    have heq : reward (quittingSingletonTerminal who) who =
        packet.boundary who := le_antisymm hle hnot
    exact Or.inr ⟨who, hwhoFirst, hwhoSecond, heq⟩

end QuittingChargeTangentPacket

end GameTheory
