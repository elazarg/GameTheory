/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.AnalyticPlayerNeutralOccupationAlternative

/-!
# Semantic Meaning of Analytic Player-Neutral Scaled Potentials

The scaled-potential branch of the analytic charged occupation alternative is
an affine Farkas certificate. On every positive germ parameter, dividing by
the clearing power turns it into an ordinary state potential. For the raw
player-neutral family, its inequalities are exactly:

* nonnegative drift under every prescribed transition;
* the corrected Bellman gain inequality for every endpoint-neutral pure
  action of the fixed player.

If the static endpoint admits a positive charged circulation, the clearing
order of such a scaled potential must be positive. This is only a statement
about the clearing exponent: the analytic numerator may also vanish, so no
divergence or boundedness claim about the punctured correction is made.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Filter Math Math.Probability Set
open Math.PMFProduct

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

namespace AnalyticBellmanGerm

/-- The actual moving kernel represented by one player-neutral raw
occupation column. -/
def finkPlayerNeutralOccupationKernelAt
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι) :
    germ.PlayerNeutralOccupationIndex who → PMF G.State :=
  fun index =>
    germ.finkActualOccupationKernelAt ht
      (playerNeutralOccupationIndexEmbedding who index)

/-- Pairing a raw player-neutral column with a potential is the expected
one-step drift of its actual moving kernel. -/
theorem potential_pair_rawPlayerNeutralOccupationColumn_eq
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι) (potential : G.State → ℝ)
    (index : germ.PlayerNeutralOccupationIndex who) :
    (∑ destination,
      potential destination *
        germ.rawPlayerNeutralOccupationColumn
          who t index destination) =
      expect (germ.finkPlayerNeutralOccupationKernelAt ht who index)
          potential -
        potential (germ.playerNeutralOccupationSource who index) := by
  cases index with
  | inl source =>
      simpa [rawPlayerNeutralOccupationColumn,
        finkPlayerNeutralOccupationKernelAt,
        playerNeutralOccupationIndexEmbedding,
        playerNeutralOccupationSource, finkActualOccupationSource,
        occupationSource] using
        germ.potential_pair_rawAnalyticOccupationColumn_eq
          ht potential
            (playerNeutralOccupationIndexEmbedding
              (germ := germ) who (.inl source))
  | inr response =>
      simpa [rawPlayerNeutralOccupationColumn,
        finkPlayerNeutralOccupationKernelAt,
        playerNeutralOccupationIndexEmbedding,
        playerNeutralOccupationSource, finkActualOccupationSource,
        occupationSource] using
        germ.potential_pair_rawAnalyticOccupationColumn_eq
          ht potential
            (playerNeutralOccupationIndexEmbedding
              (germ := germ) who (.inr response))

omit [DecidableEq G.State] in
/-- At a positive parameter, the raw player-neutral charge is the semantic
stage gain plus continuation gain against the fixed bias. -/
theorem rawPlayerNeutralOccupationCharge_eq_finkPointAt
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι) (index : germ.PlayerNeutralOccupationIndex who) :
    germ.rawPlayerNeutralOccupationCharge B who t index =
      match index with
      | .inl _ => 0
      | .inr response =>
          G.finkStageGain (germ.finkPointAt ht)
              response.source who response.1.2 +
            G.finkContinuationGain B (germ.finkPointAt ht)
              response.source who response.1.2 := by
  cases index with
  | inl source => rfl
  | inr response =>
      simp only [rawPlayerNeutralOccupationCharge]
      rw [germ.rawPureDeviationStageGainCurve_eq_finkPointAt ht,
        germ.rawPureDeviationContinuationGainCurve_eq_finkPointAt B ht]

/-- A moving correction for one player: prescribed drift is nonnegative and
every endpoint-neutral action satisfies the corrected Bellman inequality at
the current Fink point. -/
def IsPlayerNeutralBiasCorrectionAt
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (C : G.State → ℝ) : Prop :=
  (∀ source,
      0 ≤ G.finkContinuationResidual
        (fun state owner => if owner = who then C state else 0)
        (germ.finkPointAt ht) source who) ∧
    ∀ response : germ.ContinuationNeutralAction who,
      G.finkStageGain (germ.finkPointAt ht)
            response.source who response.1.2 +
          G.finkContinuationGain
            (B - fun state owner => if owner = who then C state else 0)
            (germ.finkPointAt ht)
            response.source who response.1.2 ≤
        G.finkContinuationResidual
          (fun state owner => if owner = who then C state else 0)
          (germ.finkPointAt ht) response.source who

omit [DecidableEq G.State] in
/-- A continuation gain plus the prescribed residual is the source-based
drift of the actual pure-deviation kernel. -/
theorem continuationGain_add_residual_eq_deviationDriftAt
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (C : G.State → ℝ) (who : ι)
    (response : germ.ContinuationNeutralAction who) :
    G.finkContinuationGain
          (fun state owner => if owner = who then C state else 0)
          (germ.finkPointAt ht)
          response.source who response.1.2 +
        G.finkContinuationResidual
          (fun state owner => if owner = who then C state else 0)
          (germ.finkPointAt ht) response.source who =
      expect
          (germ.finkPlayerNeutralOccupationKernelAt ht who (.inr response))
          C -
        C response.source := by
  rw [G.finkContinuationGain_eq_expect_stateKernels]
  unfold finkContinuationResidual finkContinuationEU
  rw [← G.expect_finkStateKernel_eq]
  simp only [if_pos]
  change
    (expect
          (G.finkPureDeviationStateKernel
            (germ.finkPointAt ht)
            response.source who response.1.2) C -
        expect
          (G.finkStateKernel
            (germ.finkPointAt ht) response.source) C) +
      (expect
          (G.finkStateKernel
            (germ.finkPointAt ht) response.source) C -
        C response.source) =
      expect
          (germ.finkPlayerNeutralOccupationKernelAt ht who (.inr response))
          C -
        C response.source
  change
    (expect
          (G.finkPureDeviationStateKernel
            (germ.finkPointAt ht)
            response.source who response.1.2) C -
        expect
          (G.finkStateKernel
            (germ.finkPointAt ht) response.source) C) +
      (expect
          (G.finkStateKernel
            (germ.finkPointAt ht) response.source) C -
        C response.source) =
      expect
          (G.finkPureDeviationStateKernel
            (germ.finkPointAt ht)
            response.source who response.1.2) C -
        C response.source
  ring

/-- For the player-neutral raw family, an ordinary charged-occupation
potential is exactly a moving bias correction in the fixed player's
coordinate. -/
theorem chargedOccupationPotential_iff_playerNeutralBiasCorrectionAt
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι) (C : G.State → ℝ) :
    IsChargedOccupationPotential
        (germ.rawPlayerNeutralOccupationColumn who t)
        (germ.rawPlayerNeutralOccupationCharge B who t) C ↔
      germ.IsPlayerNeutralBiasCorrectionAt B who ht C := by
  constructor
  · intro h
    constructor
    · intro source
      have hsource := h (.inl source)
      rw [germ.potential_pair_rawPlayerNeutralOccupationColumn_eq
        ht who C (.inl source)] at hsource
      change
        0 ≤
          expect (G.finkStateKernel
            (germ.finkPointAt ht) source) C - C source at hsource
      unfold finkContinuationResidual finkContinuationEU
      rw [← G.expect_finkStateKernel_eq]
      simp only [if_pos]
      exact hsource
    · intro response
      have hresponse := h (.inr response)
      rw [germ.potential_pair_rawPlayerNeutralOccupationColumn_eq
        ht who C (.inr response)] at hresponse
      rw [germ.rawPlayerNeutralOccupationCharge_eq_finkPointAt
        B ht who (.inr response)] at hresponse
      rw [G.finkContinuationGain_sub]
      have hid :=
        germ.continuationGain_add_residual_eq_deviationDriftAt
          ht C who response
      change
        G.finkStageGain (germ.finkPointAt ht)
              response.source who response.1.2 +
            G.finkContinuationGain B (germ.finkPointAt ht)
              response.source who response.1.2 ≤
          expect
              (germ.finkPlayerNeutralOccupationKernelAt
                ht who (.inr response)) C -
            C response.source at hresponse
      linarith
  · rintro ⟨hbaseline, hresponse⟩ index
    cases index with
    | inl source =>
        rw [germ.potential_pair_rawPlayerNeutralOccupationColumn_eq
          ht who C (.inl source)]
        rw [germ.rawPlayerNeutralOccupationCharge_eq_finkPointAt
          B ht who (.inl source)]
        have hsource := hbaseline source
        unfold finkContinuationResidual finkContinuationEU at hsource
        rw [← G.expect_finkStateKernel_eq] at hsource
        simp only [if_pos] at hsource
        exact hsource
    | inr response =>
        rw [germ.potential_pair_rawPlayerNeutralOccupationColumn_eq
          ht who C (.inr response)]
        rw [germ.rawPlayerNeutralOccupationCharge_eq_finkPointAt
          B ht who (.inr response)]
        have hcorrected := hresponse response
        rw [G.finkContinuationGain_sub] at hcorrected
        have hid :=
          germ.continuationGain_add_residual_eq_deviationDriftAt
            ht C who response
        change
          G.finkStageGain (germ.finkPointAt ht)
                response.source who response.1.2 +
              G.finkContinuationGain B (germ.finkPointAt ht)
                response.source who response.1.2 ≤
            expect
              (germ.finkPlayerNeutralOccupationKernelAt
                ht who (.inr response)) C -
              C response.source
        linarith

/-- The explicit punctured potential obtained by undoing the common clearing
power in a scaled player-neutral potential. -/
def
    puncturedPlayerNeutralPotentialAt
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who))
    (t : ℝ) : G.State → ℝ :=
  fun state => P.potential t state / t ^ P.poleOrder

/-- After dividing by its positive clearing power, the explicit punctured
player-neutral potential is eventually a genuine moving bias correction. -/
theorem
    AnalyticScaledChargedOccupationPotential.eventually_biasCorrectionAt
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
        germ.IsPlayerNeutralBiasCorrectionAt B who ht
          (germ.puncturedPlayerNeutralPotentialAt B who P t) := by
  filter_upwards [P.eventual, self_mem_nhdsWithin] with
    t hscaled htpos htvalid
  apply
    (germ.chargedOccupationPotential_iff_playerNeutralBiasCorrectionAt
      B htvalid who
        (germ.puncturedPlayerNeutralPotentialAt B who P t)).1
  intro index
  have hpow : 0 < t ^ P.poleOrder :=
    pow_pos (mem_Ioi.mp htpos) _
  have hsum :
      (∑ destination,
          germ.puncturedPlayerNeutralPotentialAt B who P t destination *
            germ.rawPlayerNeutralOccupationColumn
              who t index destination) =
        (∑ destination,
            P.potential t destination *
              germ.rawPlayerNeutralOccupationColumn
                who t index destination) /
          t ^ P.poleOrder := by
    simp only [puncturedPlayerNeutralPotentialAt, div_mul_eq_mul_div]
    rw [Finset.sum_div]
  rw [hsum]
  apply (le_div_iff₀ hpow).2
  simpa only [mul_comm] using hscaled index

/-- An endpoint positive charged circulation rules out clearing order zero
in the scaled-potential branch. This does not assert that the quotient
potential diverges: its analytic numerator may also vanish. -/
theorem
    AnalyticScaledChargedOccupationPotential.poleOrder_pos_of_endpoint
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who))
    (C₀ : HasNormalizedPositiveChargedCirculation
      (actualOccupationColumn
        (germ.playerNeutralOccupationKernel who)
        (germ.playerNeutralOccupationSource who))
      (germ.playerNeutralOccupationCharge B who)) :
    0 < P.poleOrder := by
  apply Nat.pos_of_ne_zero
  intro hpole
  have hpotential :
      IsChargedOccupationPotential
        (germ.rawPlayerNeutralOccupationColumn who 0)
        (germ.rawPlayerNeutralOccupationCharge B who 0)
        (P.potential 0) := by
    intro index
    let difference : ℝ → ℝ := fun t =>
      germ.rawPlayerNeutralOccupationCharge B who t index -
        ∑ destination,
          P.potential t destination *
            germ.rawPlayerNeutralOccupationColumn
              who t index destination
    have hdifferenceAnalytic : AnalyticAt ℝ difference 0 := by
      apply
        (germ.analytic_rawPlayerNeutralOccupationCharge
          B who index).sub
      apply Finset.univ.analyticAt_fun_sum
      intro destination _
      exact
        (analyticAt_pi_iff.mp P.analytic_potential destination).mul
          (germ.analytic_rawPlayerNeutralOccupationColumn
            who index destination)
    have hdifferenceNonpos :
        ∀ᶠ t in nhdsWithin 0 (Ioi 0), difference t ≤ 0 := by
      filter_upwards [P.eventual] with t ht
      dsimp only [difference]
      apply sub_nonpos.mpr
      simpa only [hpole, pow_zero, one_mul] using ht index
    have hdifferenceLimit :
        Tendsto difference (nhdsWithin 0 (Ioi 0))
          (nhds (difference 0)) :=
      hdifferenceAnalytic.continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    exact sub_nonpos.mp
      (le_of_tendsto hdifferenceLimit hdifferenceNonpos)
  have hendpointPotential :
      IsChargedOccupationPotential
        (actualOccupationColumn
          (germ.playerNeutralOccupationKernel who)
          (germ.playerNeutralOccupationSource who))
        (germ.playerNeutralOccupationCharge B who)
        (P.potential 0) := by
    rw [← germ.rawPlayerNeutralOccupationColumn_zero who,
      ← germ.rawPlayerNeutralOccupationCharge_zero B who]
    exact hpotential
  exact normalizedPositiveChargedCirculation_not_potential
    C₀ ⟨P.potential 0, hendpointPotential⟩

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
