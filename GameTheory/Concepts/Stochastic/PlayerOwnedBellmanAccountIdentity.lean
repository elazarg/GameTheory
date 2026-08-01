/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.AnalyticPlayerOwnedOccupationAlternative
import GameTheory.Concepts.Stochastic.OccupationBellmanAccountIdentity

/-!
# Player-owned charge as an exact Bellman account

The full player-owned occupation charge is exactly the difference between
the actual stage-plus-continuation value of an owned transition and the
prescribed stage-plus-continuation value at the same source.  This identity
is the semantic bridge needed to use a full-family charged-flow potential
against arbitrary unilateral behavior.

Both statements are the player-owned instance of the generic oriented
account of `OccupationBellmanAccountIdentity`, whose orientation is the
pair of projections of an owned state/action row.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm

open Math Math.Probability Set

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

/-- Stage payoff associated with one moving player-owned occupation row.
Baseline rows use prescribed play; action rows use the actual pure
unilateral deviation. -/
def playerOwnedOccupationStageEUAt
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι) :
    OwnerOccupationIndex G who → ℝ :=
  germ.occupationRowStageEUAt ht who
    (fun response : G.State × G.Act who => response.1)
    (fun response => response.2)

omit [DecidableEq G.State] in
/-- The full player-owned raw charge is exactly the excess of actual
stage-plus-`B` continuation over its prescribed counterpart. -/
theorem playerOwnedOccupation_bellmanAccount_eq
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι) (index : OwnerOccupationIndex G who) :
    germ.playerOwnedOccupationStageEUAt ht who index +
          expect
            (germ.finkOwnerActualOccupationKernelAt ht who index)
            (fun state => B state who) =
      G.finkStageEU (germ.finkPointAt ht)
          (ownerActualOccupationSource who index) who +
        G.finkContinuationEU B (germ.finkPointAt ht)
          (ownerActualOccupationSource who index) who +
        germ.rawPlayerOwnedOccupationCharge B who t index := by
  have account :=
    germ.occupationRow_bellmanAccount_eq B ht who
      (fun response : G.State × G.Act who => response.1)
      (fun response => response.2) index
  cases index <;> exact account

omit [DecidableEq G.State] in
/-- Rearranged form: the prescribed Bellman residual plus the player-owned
raw charge is the whole payoff residual for the selected row. -/
theorem playerOwnedOccupation_payoffResidual_eq
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι) (target : ℝ)
    (index : OwnerOccupationIndex G who) :
    germ.playerOwnedOccupationStageEUAt ht who index +
          expect
            (germ.finkOwnerActualOccupationKernelAt ht who index)
            (fun state => B state who) -
          B (ownerActualOccupationSource who index) who -
          target =
      (G.finkStageEU (germ.finkPointAt ht)
            (ownerActualOccupationSource who index) who +
          G.finkContinuationEU B (germ.finkPointAt ht)
            (ownerActualOccupationSource who index) who -
          B (ownerActualOccupationSource who index) who -
          target) +
        germ.rawPlayerOwnedOccupationCharge B who t index := by
  have residual :=
    germ.occupationRow_payoffResidual_eq B ht who target
      (fun response : G.State × G.Act who => response.1)
      (fun response => response.2) index
  cases index <;> exact residual

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
