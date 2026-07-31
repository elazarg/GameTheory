/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.OwnedAnalyticOccupationResponse
import Math.Probability.AnalyticOwnerChargedOccupationFlow

/-!
# Analytic player-owned occupation alternative

For one player, consider the full operational family consisting of every
prescribed baseline transition and every pure action of that player.  A
deviation column carries its moving stage-plus-continuation gain against a
fixed bias, while a baseline column has zero charge.

The generic analytic charged-flow alternative then gives an exhaustive
choice:

* a positive charged circulation using only transitions available to that
  player; or
* a pole-cleared analytic potential controlling every one of that player's
  actual actions.

Unlike the player-neutral restriction, the potential branch has no
strict-action shadow or restart seam.  This file records the analytic
alternative and its pointwise game semantics.  It does not yet compile the
potential into a calendar account or the circulation into a punishment.
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

/-- Moving Bellman charge on the full operational family of one player.
Baseline transitions have zero charge.  A pure action carries its raw stage
gain plus its raw continuation gain against `B`. -/
def rawPlayerOwnedOccupationCharge
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι) :
    ℝ → OwnerOccupationIndex G who → ℝ
  | _, .inl _ => 0
  | t, .inr response =>
      germ.rawPureDeviationStageGainCurve
          t response.1 who response.2 +
        germ.rawPureDeviationContinuationGainCurve
          B t response.1 who response.2

omit [DecidableEq G.State] in
/-- Every player-owned moving charge coordinate is analytic at the
endpoint. -/
theorem analytic_rawPlayerOwnedOccupationCharge
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι) :
    ∀ index,
      AnalyticAt ℝ
        (fun t =>
          germ.rawPlayerOwnedOccupationCharge B who t index) 0 := by
  intro index
  cases index with
  | inl source =>
      exact analyticAt_const
  | inr response =>
      exact
        (analyticAt_pi_iff.mp
          ((analyticAt_pi_iff.mp
            ((analyticAt_pi_iff.mp
              germ.analytic_rawPureDeviationStageGainCurve)
                response.1)) who) response.2).add
        (analyticAt_pi_iff.mp
          ((analyticAt_pi_iff.mp
            ((analyticAt_pi_iff.mp
              (germ.analytic_rawPureDeviationContinuationGainCurve B))
                response.1)) who) response.2)

omit [DecidableEq G.State] in
/-- At a valid positive parameter, the raw player-owned charge is exactly
the semantic stage gain plus continuation gain against the fixed bias. -/
theorem rawPlayerOwnedOccupationCharge_eq_finkPointAt
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι) (index : OwnerOccupationIndex G who) :
    germ.rawPlayerOwnedOccupationCharge B who t index =
      match index with
      | .inl _ => 0
      | .inr response =>
          G.finkStageGain (germ.finkPointAt ht)
              response.1 who response.2 +
            G.finkContinuationGain B (germ.finkPointAt ht)
              response.1 who response.2 := by
  cases index with
  | inl source => rfl
  | inr response =>
      simp only [rawPlayerOwnedOccupationCharge]
      rw [germ.rawPureDeviationStageGainCurve_eq_finkPointAt ht,
        germ.rawPureDeviationContinuationGainCurve_eq_finkPointAt B ht]

/-- **Full player-owned analytic charged-flow alternative.**

Either the prescribed transitions and pure actions of `who` contain a
pole-cleared analytic positive charged circulation, or one analytic scaled
potential controls that entire operational family. -/
theorem rawPlayerOwnedPositiveChargedCirculation_xor_scaledPotential
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι) :
    Xor
      (Nonempty
        (AnalyticPositiveChargedCirculation
          (germ.rawOwnerAnalyticOccupationColumn who)
          (germ.rawPlayerOwnedOccupationCharge B who)))
      (Nonempty
        (AnalyticScaledChargedOccupationPotential
          (germ.rawOwnerAnalyticOccupationColumn who)
          (germ.rawPlayerOwnedOccupationCharge B who))) := by
  exact
    analyticPositiveChargedCirculation_xor_scaledPotential
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who)
      (germ.analytic_rawOwnerAnalyticOccupationColumn who)
      (germ.analytic_rawPlayerOwnedOccupationCharge B who)

/-- Run the full player-owned charged-flow alternative simultaneously over
the finite player set.  The potential branch synchronizes all pole-clearing
orders. -/
theorem
    exists_playerOwnedPositiveChargedCirculation_or_commonScaledPotential
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) :
    (∃ who,
      Nonempty
        (AnalyticPositiveChargedCirculation
          (germ.rawOwnerAnalyticOccupationColumn who)
          (germ.rawPlayerOwnedOccupationCharge B who))) ∨
    Nonempty
      (AnalyticOwnerScaledChargedOccupationPotential
        (fun who => OwnerOccupationIndex G who)
        (fun who => germ.rawOwnerAnalyticOccupationColumn who)
        (fun who => germ.rawPlayerOwnedOccupationCharge B who)) := by
  exact
    exists_owner_analyticPositiveChargedCirculation_or_commonScaledPotential
      (fun who => OwnerOccupationIndex G who)
      (fun who => germ.rawOwnerAnalyticOccupationColumn who)
      (fun who => germ.rawPlayerOwnedOccupationCharge B who)
      (fun who => germ.analytic_rawOwnerAnalyticOccupationColumn who)
      (fun who => germ.analytic_rawPlayerOwnedOccupationCharge B who)

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
