/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Analytic.PlayerNeutral.PotentialJet
import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Analytic.Accounting.AnalyticBellmanHierarchy

/-!
# Harmonic response from a player-neutral potential jet

The leading scalar coefficient of a gauge-fixed player-neutral potential is
embedded in the selected player's payoff coordinate.  It is nonzero because
the scalar coefficient is nonzero.  If every endpoint player-neutral
occupation column annihilates that coefficient, the embedded payoff vector
is harmonic under the endpoint prescribed kernel.

Relative to the endpoint-harmonic directions already processed, this yields
exactly the honest finite alternative: the payoff vector is already in the
processed span, or adjoining it strictly lowers the remaining harmonic rank.
No strict-drift strategy or public punishment is constructed here.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Filter Math Math.Probability Set
open Math.Probability.AnalyticScaledChargedOccupationPotential

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

namespace AnalyticBellmanGerm

/-- Embed the leading scalar player-neutral potential coefficient in its
owner's payoff coordinate. -/
def playerNeutralPotentialJetLeadingPayoff
    (germ : G.AnalyticBellmanGerm)
    (who : ι)
    {B : G.State → Payoff ι}
    {P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)}
    {anchor : G.State}
    (jet : GaugeFixedPotentialJet P anchor) :
    G.State → Payoff ι :=
  G.finkPlayerPotential who (jet.factor 0)

@[simp]
theorem playerNeutralPotentialJetLeadingPayoff_apply_self
    (germ : G.AnalyticBellmanGerm)
    (who : ι)
    {B : G.State → Payoff ι}
    {P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)}
    {anchor : G.State}
    (jet : GaugeFixedPotentialJet P anchor)
    (state : G.State) :
    germ.playerNeutralPotentialJetLeadingPayoff who jet
        state who =
      jet.factor 0 state := by
  simp [playerNeutralPotentialJetLeadingPayoff]

@[simp]
theorem playerNeutralPotentialJetLeadingPayoff_apply_of_ne
    (germ : G.AnalyticBellmanGerm)
    (who other : ι)
    {B : G.State → Payoff ι}
    {P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)}
    {anchor : G.State}
    (jet : GaugeFixedPotentialJet P anchor)
    (state : G.State)
    (other_ne : other ≠ who) :
    germ.playerNeutralPotentialJetLeadingPayoff who jet
        state other = 0 := by
  exact G.finkPlayerPotential_apply_of_ne
    who other (jet.factor 0) state other_ne

/-- The embedded leading payoff vector is nonzero. -/
theorem playerNeutralPotentialJetLeadingPayoff_ne_zero
    (germ : G.AnalyticBellmanGerm)
    (who : ι)
    {B : G.State → Payoff ι}
    {P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)}
    {anchor : G.State}
    (jet : GaugeFixedPotentialJet P anchor) :
    germ.playerNeutralPotentialJetLeadingPayoff who jet ≠ 0 := by
  intro payoff_zero
  apply jet.leading_ne_zero
  funext state
  have coordinate_zero :=
    congrFun (congrFun payoff_zero state) who
  simpa using coordinate_zero

/-- The leading scalar coefficient retains the gauge normalization at the
chosen anchor. In particular, together with `leading_ne_zero`, it is a
genuinely nonconstant state potential. -/
theorem playerNeutralPotentialJet_leading_anchor_eq_zero
    (germ : G.AnalyticBellmanGerm)
    (who : ι)
    {B : G.State → Payoff ι}
    {P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)}
    {anchor : G.State}
    (jet : GaugeFixedPotentialJet P anchor) :
    jet.factor 0 anchor = 0 := by
  have factor_eventually_zero :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        jet.factor t anchor = 0 := by
    filter_upwards [
      jet.gauge_eq.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t gauge_eq t_pos
    have coordinate_eq := congrFun gauge_eq anchor
    have product_zero :
        t ^ jet.order * jet.factor t anchor = 0 := by
      simpa [gaugeFixAt] using coordinate_eq.symm
    exact
      (mul_eq_zero.mp product_zero).resolve_left
        (pow_ne_zero _ (ne_of_gt (mem_Ioi.mp t_pos)))
  have factor_tendsto :
      Tendsto (fun t => jet.factor t anchor)
        (nhdsWithin 0 (Ioi 0))
        (nhds (jet.factor 0 anchor)) :=
    (analyticAt_pi_iff.mp jet.analytic_factor anchor).continuousAt
      |>.tendsto
      |>.mono_left nhdsWithin_le_nhds
  have zero_tendsto :
      Tendsto (fun _ : ℝ => (0 : ℝ))
        (nhdsWithin 0 (Ioi 0)) (nhds (0 : ℝ)) :=
    tendsto_const_nhds
  haveI : NeBot (nhdsWithin (0 : ℝ) (Ioi 0)) :=
    nhdsWithin_Ioi_neBot le_rfl
  exact tendsto_nhds_unique_of_eventuallyEq
    factor_tendsto zero_tendsto factor_eventually_zero

/-- If all endpoint player-neutral columns annihilate the leading scalar
coefficient, its selected-player payoff embedding is endpoint harmonic. -/
theorem playerNeutralPotentialJetLeadingPayoff_mem_harmonic
    (germ : G.AnalyticBellmanGerm)
    (who : ι)
    {B : G.State → Payoff ι}
    {P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)}
    {anchor : G.State}
    (jet : GaugeFixedPotentialJet P anchor)
    (pairing_zero :
      ∀ index : germ.PlayerNeutralOccupationIndex who,
        (∑ state,
          jet.factor 0 state *
            actualOccupationColumn
              (germ.playerNeutralOccupationKernel who)
              (germ.playerNeutralOccupationSource who)
              index state) = 0) :
    germ.playerNeutralPotentialJetLeadingPayoff who jet ∈
      germ.endpointHarmonicSubmodule := by
  apply
    (germ.mem_endpointHarmonicSubmodule_iff
      (germ.playerNeutralPotentialJetLeadingPayoff
        who jet)).2
  funext source other
  by_cases other_eq : other = who
  · subst other
    have baseline_pair := pairing_zero (Sum.inl source)
    rw [potential_pair_actualOccupationColumn] at baseline_pair
    dsimp only [playerNeutralOccupationKernel,
      playerNeutralOccupationSource] at baseline_pair
    unfold finkContinuationResidualVector
      finkContinuationResidual finkContinuationEU
    rw [← G.expect_finkStateKernel_eq]
    simpa using baseline_pair
  · unfold finkContinuationResidualVector
      finkContinuationResidual finkContinuationEU
    rw [← G.expect_finkStateKernel_eq]
    simp [playerNeutralPotentialJetLeadingPayoff, other_eq]

/-- Harmonic-side finite progress: the leading player-neutral payoff vector
is already processed, or adjoining it strictly lowers harmonic rank. -/
theorem
    playerNeutralPotentialJetLeadingPayoff_processed_or_rankDecrease
    (germ : G.AnalyticBellmanGerm)
    (who : ι)
    {B : G.State → Payoff ι}
    {P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)}
    {anchor : G.State}
    (jet : GaugeFixedPotentialJet P anchor)
    (span : germ.EndpointHarmonicJetSpan)
    (pairing_zero :
      ∀ index : germ.PlayerNeutralOccupationIndex who,
        (∑ state,
          jet.factor 0 state *
            actualOccupationColumn
              (germ.playerNeutralOccupationKernel who)
              (germ.playerNeutralOccupationSource who)
              index state) = 0) :
    germ.playerNeutralPotentialJetLeadingPayoff who jet ∈
        span.carrier ∨
      ∃ harmonic :
          germ.playerNeutralPotentialJetLeadingPayoff who jet ∈
            germ.endpointHarmonicSubmodule,
        (span.extend
          (germ.playerNeutralPotentialJetLeadingPayoff who jet)
          harmonic).rank < span.rank := by
  let leading :=
    germ.playerNeutralPotentialJetLeadingPayoff who jet
  have harmonic :
      leading ∈ germ.endpointHarmonicSubmodule :=
    germ.playerNeutralPotentialJetLeadingPayoff_mem_harmonic
      who jet pairing_zero
  by_cases processed : leading ∈ span.carrier
  · exact Or.inl processed
  · exact Or.inr
      ⟨harmonic,
        span.rank_extend_lt leading harmonic processed⟩

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
