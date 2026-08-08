/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Analytic.PlayerNeutral.ResidualOccupation
import Math.FiniteDeflationIteration

/-!
# Finite rank for iterated player-neutral deflation

The first strict player-neutral deletion can be flattened into a node over
the original finite occupation-index type.  Its active subtype is equivalent
to the existing `ZeroDriftIndex`, while its exceptional set is exactly the
strict set already equipped with an occupation budget.

`Math.FiniteDeflationIteration` proves that any continuation expressed by
properly shrinking these ambient active sets is well founded and provides an
additive support calculus for exceptional accounts.

This resolves the combinatorial termination issue, but not yet the
dependent analytic iteration issue.  The current
`PlayerNeutralStrictLeadingDrift` structure is specialized to a potential
over the original full `PlayerNeutralOccupationIndex`.  By contrast, the
next potential in `ZeroDriftAnalyticPotentialJet` is over the restricted
`ZeroDriftIndex`.  It therefore cannot be supplied definitionally to the
same strict-drift constructor.  Repeated analytic iteration needs either:

* a strict-leading-drift structure parameterized by an arbitrary ambient
  active finset and its restricted column family; or
* an explicit extension of each residual potential back to the fixed
  ambient type, with all missing-column drift charged to the accumulated
  exceptional account.

No public strategy or recurrent-child claim is made here.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math Math.Probability
open Math.Probability.AnalyticScaledChargedOccupationPotential

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

namespace AnalyticBellmanGerm
namespace PlayerNeutralStrictLeadingDrift

local instance finiteDeflationIndexDecidableEq
    (germ : G.AnalyticBellmanGerm) (who : ι) :
    DecidableEq (germ.PlayerNeutralOccupationIndex who) :=
  Classical.decEq _

variable
    {germ : G.AnalyticBellmanGerm}
    {B : G.State → Payoff ι} {who : ι}
    {P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)}
    {anchor : G.State}
    {jet : GaugeFixedPotentialJet P anchor}

/-- The initial finite-deflation node containing every player-neutral
occupation index. -/
def fullDeflationState :
    FiniteDeflationState (germ.PlayerNeutralOccupationIndex who) where
  active := Finset.univ

/-- The ambient active set after deleting the complete strict set selected
by one leading potential. -/
def zeroDriftDeflationState
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet) :
    FiniteDeflationState (germ.PlayerNeutralOccupationIndex who) :=
  fullDeflationState.delete C.strictIndexSet

/-- The first zero-drift restriction is a genuine finite deflation. -/
theorem zeroDriftDeflationState_deflates
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet) :
    C.zeroDriftDeflationState.Deflates
      (fullDeflationState (germ := germ) (who := who)) := by
  apply FiniteDeflationState.delete_deflates
  · exact Finset.subset_univ _
  · exact C.strictIndexSet_nonempty

/-- The accumulated exceptional set after the first deflation is exactly
the strict set deleted at that step. -/
theorem zeroDriftDeflationState_exceptional
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet) :
    C.zeroDriftDeflationState.exceptional = C.strictIndexSet := by
  change Finset.univ \ (Finset.univ \ C.strictIndexSet) =
    C.strictIndexSet
  exact Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)

/-- Membership in the flattened active set is the existing zero-drift
predicate. -/
theorem mem_zeroDriftDeflationState_active_iff
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet)
    (index : germ.PlayerNeutralOccupationIndex who) :
    index ∈ C.zeroDriftDeflationState.active ↔
      index ∉ C.strictIndexSet := by
  simp [zeroDriftDeflationState, fullDeflationState,
    FiniteDeflationState.delete]

/-- The nested subtype used by the analytic restriction is equivalent to the
active subtype of the fixed ambient finite-deflation node. -/
def zeroDriftIndexEquivActive
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet) :
    C.ZeroDriftIndex ≃
      {index //
        index ∈ C.zeroDriftDeflationState.active} where
  toFun index :=
    ⟨index.1,
      (C.mem_zeroDriftDeflationState_active_iff index.1).mpr
        index.2⟩
  invFun index :=
    ⟨index.1,
      (C.mem_zeroDriftDeflationState_active_iff index.1).mp
        index.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The flattened first step spends exactly the same cardinal rank as the
existing subtype calculation. -/
theorem card_zeroDriftDeflationState_lt_full
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet) :
    C.zeroDriftDeflationState.rank <
      (fullDeflationState (germ := germ) (who := who)).rank :=
  FiniteDeflationState.rankLt_of_deflates
    C.zeroDriftDeflationState_deflates

end PlayerNeutralStrictLeadingDrift
end AnalyticBellmanGerm
end StochasticGame
end GameTheory
