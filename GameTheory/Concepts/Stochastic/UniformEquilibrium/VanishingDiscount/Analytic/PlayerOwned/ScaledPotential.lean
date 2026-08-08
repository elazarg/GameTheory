/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Analytic.PlayerOwned.BellmanAccountIdentity

/-!
# Semantic meaning of full player-owned scaled potentials

A charged-occupation potential for the full player-owned operational family
is exactly a moving Bellman correction for every pure action of that player.
After dividing an analytic scaled potential by its positive clearing power,
this interpretation holds eventually on the punctured analytic germ.

This is the key advantage of the full operational family: no endpoint-strict
action is discarded, shadowed, or charged a restart bill.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm

open Filter Math Math.Probability Set

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

/-- A moving correction for one player which controls the prescribed
transition and every pure action available to that player. -/
def IsPlayerOwnedBiasCorrectionAt
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (C : G.State → ℝ) : Prop :=
  (∀ source,
      0 ≤ G.finkContinuationResidual
        (fun state owner => if owner = who then C state else 0)
        (germ.finkPointAt ht) source who) ∧
    ∀ source (action : G.Act who),
      G.finkStageGain (germ.finkPointAt ht)
            source who action +
          G.finkContinuationGain
            (B - fun state owner => if owner = who then C state else 0)
            (germ.finkPointAt ht) source who action ≤
        G.finkContinuationResidual
          (fun state owner => if owner = who then C state else 0)
          (germ.finkPointAt ht) source who

omit [DecidableEq G.State] in
/-- A continuation gain plus the prescribed residual is the source-based
drift of the corresponding actual pure-deviation kernel. -/
theorem playerOwnedContinuationGain_add_residual_eq_deviationDriftAt
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (C : G.State → ℝ) (who : ι)
    (source : G.State) (action : G.Act who) :
    G.finkContinuationGain
          (fun state owner => if owner = who then C state else 0)
          (germ.finkPointAt ht) source who action +
        G.finkContinuationResidual
          (fun state owner => if owner = who then C state else 0)
          (germ.finkPointAt ht) source who =
      expect
          (germ.finkOwnerActualOccupationKernelAt
            ht who (.inr (source, action)))
          C -
        C source := by
  rw [G.finkContinuationGain_eq_expect_stateKernels]
  unfold finkContinuationResidual finkContinuationEU
  rw [← G.expect_finkStateKernel_eq]
  simp only [if_pos]
  change
    (expect
          (G.finkPureDeviationStateKernel
            (germ.finkPointAt ht) source who action) C -
        expect
          (G.finkStateKernel
            (germ.finkPointAt ht) source) C) +
      (expect
          (G.finkStateKernel
            (germ.finkPointAt ht) source) C -
        C source) =
      expect
          (G.finkPureDeviationStateKernel
            (germ.finkPointAt ht) source who action) C -
        C source
  ring

/-- On the full player-owned family, an ordinary charged-occupation
potential is exactly a moving all-action bias correction. -/
theorem chargedOccupationPotential_iff_playerOwnedBiasCorrectionAt
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι) (C : G.State → ℝ) :
    IsChargedOccupationPotential
        (germ.rawOwnerAnalyticOccupationColumn who t)
        (germ.rawPlayerOwnedOccupationCharge B who t) C ↔
      germ.IsPlayerOwnedBiasCorrectionAt B who ht C := by
  constructor
  · intro h
    constructor
    · intro source
      have hsource := h (.inl source)
      rw [germ.potential_pair_rawOwnerAnalyticOccupationColumn_eq
        ht who C (.inl source)] at hsource
      change
        0 ≤
          expect (G.finkStateKernel
            (germ.finkPointAt ht) source) C - C source at hsource
      unfold finkContinuationResidual finkContinuationEU
      rw [← G.expect_finkStateKernel_eq]
      simp only [if_pos]
      exact hsource
    · intro source action
      have hresponse := h (.inr (source, action))
      rw [germ.potential_pair_rawOwnerAnalyticOccupationColumn_eq
        ht who C (.inr (source, action))] at hresponse
      rw [germ.rawPlayerOwnedOccupationCharge_eq_finkPointAt
        B ht who (.inr (source, action))] at hresponse
      rw [G.finkContinuationGain_sub]
      have hid :=
        germ.playerOwnedContinuationGain_add_residual_eq_deviationDriftAt
          ht C who source action
      change
        G.finkStageGain (germ.finkPointAt ht) source who action +
            G.finkContinuationGain B (germ.finkPointAt ht)
              source who action ≤
          expect
              (germ.finkOwnerActualOccupationKernelAt
                ht who (.inr (source, action))) C -
            C source at hresponse
      linarith
  · rintro ⟨hbaseline, hresponse⟩ index
    cases index with
    | inl source =>
        rw [germ.potential_pair_rawOwnerAnalyticOccupationColumn_eq
          ht who C (.inl source)]
        rw [germ.rawPlayerOwnedOccupationCharge_eq_finkPointAt
          B ht who (.inl source)]
        have hsource := hbaseline source
        unfold finkContinuationResidual finkContinuationEU at hsource
        rw [← G.expect_finkStateKernel_eq] at hsource
        simp only [if_pos] at hsource
        exact hsource
    | inr response =>
        rw [germ.potential_pair_rawOwnerAnalyticOccupationColumn_eq
          ht who C (.inr response)]
        rw [germ.rawPlayerOwnedOccupationCharge_eq_finkPointAt
          B ht who (.inr response)]
        have hcorrected := hresponse response.1 response.2
        rw [G.finkContinuationGain_sub] at hcorrected
        have hid :=
          germ.playerOwnedContinuationGain_add_residual_eq_deviationDriftAt
            ht C who response.1 response.2
        change
          G.finkStageGain (germ.finkPointAt ht)
                response.1 who response.2 +
              G.finkContinuationGain B (germ.finkPointAt ht)
                response.1 who response.2 ≤
            expect
                (germ.finkOwnerActualOccupationKernelAt
                  ht who (.inr response)) C -
              C response.1
        linarith

/-- Undo the clearing power in a full player-owned scaled potential. -/
def puncturedPlayerOwnedPotentialAt
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who))
    (t : ℝ) : G.State → ℝ :=
  fun state => P.potential t state / t ^ P.poleOrder

/-- After dividing by the positive clearing power, a full player-owned
scaled potential eventually controls every pure action of the player. -/
theorem
    AnalyticScaledChargedOccupationPotential.eventually_playerOwnedBiasCorrectionAt
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who)) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
        germ.IsPlayerOwnedBiasCorrectionAt B who ht
          (germ.puncturedPlayerOwnedPotentialAt B who P t) := by
  filter_upwards [P.eventual, self_mem_nhdsWithin] with
    t hscaled htpos htvalid
  apply
    (germ.chargedOccupationPotential_iff_playerOwnedBiasCorrectionAt
      B htvalid who
        (germ.puncturedPlayerOwnedPotentialAt B who P t)).1
  intro index
  have hpow : 0 < t ^ P.poleOrder :=
    pow_pos (mem_Ioi.mp htpos) _
  have hsum :
      (∑ destination,
          germ.puncturedPlayerOwnedPotentialAt B who P t destination *
            germ.rawOwnerAnalyticOccupationColumn
              who t index destination) =
        (∑ destination,
            P.potential t destination *
              germ.rawOwnerAnalyticOccupationColumn
                who t index destination) /
          t ^ P.poleOrder := by
    simp only [puncturedPlayerOwnedPotentialAt, div_mul_eq_mul_div]
    rw [Finset.sum_div]
  rw [hsum]
  apply (le_div_iff₀ hpow).2
  simpa only [mul_comm] using hscaled index

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
