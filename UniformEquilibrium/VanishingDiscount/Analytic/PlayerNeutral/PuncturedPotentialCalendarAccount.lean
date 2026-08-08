/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Analytic.PlayerNeutral.ScaledPotential
import Math.OnlineLearning.AnytimeMultiplicativeWeights
import Math.OnlineLearning.CompletedEpochCalendar
import Math.Probability.AdaptiveTransitionAccount
import Math.Probability.PotentialDominatedTransitionCost
import Math.OnlineLearning.ShiftedUniversalCalendar

/-!
# Calendar accounts for punctured player-neutral potentials

A pole-cleared analytic occupation potential may grow after division by its
clearing power.  This file keeps that full punctured potential.  It freezes
the parameter during each quadratic epoch, telescopes the resulting moving
charge against one fixed state potential, and pays the endpoint motion only
once per epoch.  The universal logarithmic scale makes the sum of those
endpoint bills sublinear in calendar time.

The stochastic conclusions apply only to predictable mixtures of the
specified active player-neutral occupation columns.  They do not classify
arbitrary deviations and make no credibility or punishment assumption.
The resulting account is one-sided: cumulative expected charge is bounded
above by a nonnegative sublinear budget.
-/

noncomputable section

open Filter Set Topology

namespace GameTheory
namespace StochasticGame

open Math Math.OnlineLearning Math.Probability
open Math.PMFProduct

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

namespace AnalyticBellmanGerm

open GameTheory.StochasticGame.AnalyticBellmanGerm.AnalyticScaledChargedOccupationPotential

/-- The shifted analytic parameter used at one calendar stage.  This is the
common game-side wrapper around `shiftedUniversalEpochScale` and
`anytimeEpochIndex` shared by the player-neutral and player-owned calendar
accounts. -/
def calendarScale (startEpoch stage : ℕ) : ℝ :=
  shiftedUniversalEpochScale startEpoch (anytimeEpochIndex stage)

/-- Restrict the punctured scaled-potential inequality to any fixed active
subfamily of raw player-neutral occupation columns.  The active subtype is
kept explicitly; no endpoint or leading-jet projection is used. -/
theorem
    AnalyticScaledChargedOccupationPotential.eventually_activeCharge_le_drift
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who))
    (active : Finset (germ.PlayerNeutralOccupationIndex who)) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
        ∀ index :
            {index : germ.PlayerNeutralOccupationIndex who //
              index ∈ active},
          germ.rawPlayerNeutralOccupationCharge B who t index.1 ≤
            transitionPotentialDrift
              (fun activeIndex =>
                germ.finkPlayerNeutralOccupationKernelAt
                  ht who activeIndex.1)
              (fun activeIndex =>
                germ.playerNeutralOccupationSource who activeIndex.1)
              (germ.puncturedPlayerNeutralPotentialAt B who P t)
              index := by
  have heventual :=
    eventually_biasCorrectionAt germ B who P
  filter_upwards [heventual] with t hcorrection
  intro ht index
  have hcharged :
      IsChargedOccupationPotential
        (germ.rawPlayerNeutralOccupationColumn who t)
        (germ.rawPlayerNeutralOccupationCharge B who t)
        (germ.puncturedPlayerNeutralPotentialAt B who P t) :=
    (germ.chargedOccupationPotential_iff_playerNeutralBiasCorrectionAt
      B ht who
        (germ.puncturedPlayerNeutralPotentialAt B who P t)).2
      (hcorrection ht)
  have hindex := hcharged index.1
  rw [germ.potential_pair_rawPlayerNeutralOccupationColumn_eq
    ht who
      (germ.puncturedPlayerNeutralPotentialAt B who P t)
      index.1] at hindex
  exact hindex

/-- The exact active-subtype charge-to-drift inequality is available at all
sufficiently late universal-calendar scales.  The statement quantifies over
the proof that the selected scale lies in the analytic interval, so it does
not hide a choice of a Fink point. -/
theorem
    AnalyticScaledChargedOccupationPotential.eventually_calendarActiveCharge_le_drift
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who))
    (active : Finset (germ.PlayerNeutralOccupationIndex who)) :
    ∀ᶠ k : ℕ in atTop,
      ∀ hk :
          universalEpochScale k ∈ Ioo (0 : ℝ) germ.radius,
        ∀ index :
            {index : germ.PlayerNeutralOccupationIndex who //
              index ∈ active},
          germ.rawPlayerNeutralOccupationCharge B who
              (universalEpochScale k) index.1 ≤
            transitionPotentialDrift
              (fun activeIndex =>
                germ.finkPlayerNeutralOccupationKernelAt
                  hk who activeIndex.1)
              (fun activeIndex =>
                germ.playerNeutralOccupationSource who activeIndex.1)
              (germ.puncturedPlayerNeutralPotentialAt B who P
                (universalEpochScale k))
              index := by
  have hscale :
      Tendsto universalEpochScale atTop
        (nhdsWithin 0 (Ioi (0 : ℝ))) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact
      ⟨tendsto_universalEpochScale,
        Filter.Eventually.of_forall universalEpochScale_pos⟩
  exact hscale.eventually
    (eventually_activeCharge_le_drift germ B who P active)

/-- Every analytic scaled potential admits a finite burn-in after which all
calendar scales are valid and the exact active charge-to-drift inequality
holds.  The burn-in is existential and is used only in the proof schedule;
no numerical stabilization radius is assumed. -/
theorem
    AnalyticScaledChargedOccupationPotential.exists_startEpoch_activeCharge_le_drift
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who))
    (active : Finset (germ.PlayerNeutralOccupationIndex who)) :
    ∃ (startEpoch : ℕ)
        (valid :
          ∀ k : ℕ,
            shiftedUniversalEpochScale startEpoch k ∈
              Ioo (0 : ℝ) germ.radius),
      ∀ k index,
        germ.rawPlayerNeutralOccupationCharge B who
            (shiftedUniversalEpochScale startEpoch k) index.1 ≤
          transitionPotentialDrift
            (fun activeIndex =>
              germ.finkPlayerNeutralOccupationKernelAt
                (valid k) who activeIndex.1)
            (fun activeIndex =>
              germ.playerNeutralOccupationSource who activeIndex.1)
            (germ.puncturedPlayerNeutralPotentialAt B who P
              (shiftedUniversalEpochScale startEpoch k))
            (index :
              {index : germ.PlayerNeutralOccupationIndex who //
                index ∈ active}) := by
  have hscale :
      Tendsto universalEpochScale atTop
        (nhdsWithin 0 (Ioi (0 : ℝ))) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact
      ⟨tendsto_universalEpochScale,
        Filter.Eventually.of_forall universalEpochScale_pos⟩
  have hvalid :
      ∀ᶠ k : ℕ in atTop,
        universalEpochScale k ∈ Ioo (0 : ℝ) germ.radius :=
    hscale.eventually (Ioo_mem_nhdsGT germ.radius_pos)
  have hcharge :=
    eventually_calendarActiveCharge_le_drift
      germ B who P active
  obtain ⟨startEpoch, hstart⟩ :=
    eventually_atTop.1 (hcharge.and hvalid)
  let valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius :=
    fun k =>
      (hstart (startEpoch + k) (by omega)).2
  refine ⟨startEpoch, valid, ?_⟩
  intro k index
  have h :=
    (hstart (startEpoch + k) (by omega)).1
      (valid k) index
  simpa only [shiftedUniversalEpochScale] using h

/-- At one fixed punctured parameter, every predictable
source-compatible mixture of active player-neutral columns has cumulative
expected moving charge bounded by twice the finite-state punctured
potential envelope. -/
theorem
    AnalyticScaledChargedOccupationPotential.expected_activeCharge_le
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who))
    (active : Finset (germ.PlayerNeutralOccupationIndex who))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (hcharge :
      ∀ index :
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active},
        germ.rawPlayerNeutralOccupationCharge B who t index.1 ≤
          transitionPotentialDrift
            (fun activeIndex =>
              germ.finkPlayerNeutralOccupationKernelAt
                ht who activeIndex.1)
            (fun activeIndex =>
              germ.playerNeutralOccupationSource who activeIndex.1)
            (germ.puncturedPlayerNeutralPotentialAt B who P t)
            index)
    (initial : G.State)
    (selection :
      ∀ n, (Fin (n + 1) → G.State) →
        PMF
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active})
    (source_compatible :
      ∀ n history index,
        selection n history index ≠ 0 →
          germ.playerNeutralOccupationSource who index.1 =
            history (Fin.last n))
    (T : ℕ) :
    expect
        (adaptiveHistoryLaw
          (adaptiveMarkovStep initial
            (mixedTransitionComparison
              (fun index =>
                germ.finkPlayerNeutralOccupationKernelAt
                  ht who index.1)
              selection))
          (T + 1))
        (mixedTransitionCostSum selection
          (fun index =>
            germ.rawPlayerNeutralOccupationCharge
              B who t index.1) T) ≤
      2 * finiteStatePotentialBound
        (germ.puncturedPlayerNeutralPotentialAt B who P t) := by
  apply expected_mixedTransitionCostSum_le_two_potentialBound
    (S := G.State)
    (I :=
      {index : germ.PlayerNeutralOccupationIndex who //
        index ∈ active})
    initial
    (fun index =>
      germ.finkPlayerNeutralOccupationKernelAt ht who index.1)
    (fun index =>
      germ.playerNeutralOccupationSource who index.1)
    (germ.puncturedPlayerNeutralPotentialAt B who P t)
    selection source_compatible
    (fun index =>
      germ.rawPlayerNeutralOccupationCharge B who t index.1)
    hcharge T

/-- Expected active moving raw charge in one independently presented
calendar epoch.  The initial state and predictable selector may vary with
the epoch.  The endpoint bound is uniform in both inputs, which is the
estimate needed after conditioning on a realized global prefix.  Identifying
these independently presented epoch laws with conditional suffix laws of one
behavior profile is a separate realization and disintegration theorem. -/
def
    AnalyticScaledChargedOccupationPotential.expectedActiveEpochCharge
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (active : Finset (germ.PlayerNeutralOccupationIndex who))
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (initial : ℕ → G.State)
    (selection :
      ℕ → ∀ n : ℕ, (Fin (n + 1) → G.State) →
        PMF
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active})
    (k T : ℕ) : ℝ :=
  expect
    (adaptiveHistoryLaw
      (adaptiveMarkovStep (initial k)
        (mixedTransitionComparison
          (fun index =>
            germ.finkPlayerNeutralOccupationKernelAt
              (valid k) who index.1)
          (selection k)))
      (T + 1))
    (mixedTransitionCostSum (selection k)
      (fun index =>
        germ.rawPlayerNeutralOccupationCharge B who
          (shiftedUniversalEpochScale startEpoch k) index.1) T)

/-- Expected active charge through all completed epochs and the current
epoch prefix. -/
def
    AnalyticScaledChargedOccupationPotential.expectedActiveCalendarCharge
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (active : Finset (germ.PlayerNeutralOccupationIndex who))
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (initial : ℕ → G.State)
    (selection :
      ℕ → ∀ n : ℕ, (Fin (n + 1) → G.State) →
        PMF
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active})
    (T : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (anytimeEpochIndex T),
    expectedActiveEpochCharge germ B who active startEpoch valid
      initial selection k (anytimeEpochLength k)) +
    expectedActiveEpochCharge germ B who active startEpoch valid
      initial selection (anytimeEpochIndex T)
        (anytimeEpochOffset T)

/-- The full endpoint bill for one universal-calendar epoch.  The quotient
is evaluated only at the positive universal scale. -/
def
    AnalyticScaledChargedOccupationPotential.puncturedPotentialEpochBudget
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who))
    (k : ℕ) : ℝ :=
  2 * finiteStatePotentialBound
    (germ.puncturedPlayerNeutralPotentialAt B who P
      (universalEpochScale k))

/-- Completed epochs plus the whole current epoch form the explicit
nonnegative calendar account. -/
def
    AnalyticScaledChargedOccupationPotential.puncturedPotentialCalendarBudget
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who))
    (T : ℕ) : ℝ :=
  completedAndCurrentEpochBudget
    (puncturedPotentialEpochBudget germ B who P) T

/-- Punctured endpoint bill after a fixed analytic burn-in. -/
def
    AnalyticScaledChargedOccupationPotential.shiftedPuncturedPotentialEpochBudget
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who))
    (startEpoch k : ℕ) : ℝ :=
  puncturedPotentialEpochBudget germ B who P (startEpoch + k)

/-- Completed-plus-current account after a fixed analytic burn-in. -/
def
    AnalyticScaledChargedOccupationPotential.shiftedPuncturedPotentialCalendarBudget
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who))
    (startEpoch T : ℕ) : ℝ :=
  completedAndCurrentEpochBudget
    (shiftedPuncturedPotentialEpochBudget
      germ B who P startEpoch) T

/-- Dividing the analytic numerator by a positive natural power multiplies
its finite-state envelope by the corresponding negative real power. -/
theorem
    AnalyticScaledChargedOccupationPotential.finiteStatePotentialBound_punctured
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who))
    {t : ℝ} (ht : 0 < t) :
    finiteStatePotentialBound
        (germ.puncturedPlayerNeutralPotentialAt B who P t) =
      finiteStatePotentialBound (P.potential t) *
        t ^ (-(P.poleOrder : ℝ)) := by
  have hpow : 0 < t ^ P.poleOrder := pow_pos ht _
  unfold finiteStatePotentialBound puncturedPlayerNeutralPotentialAt
  simp_rw [abs_div, abs_of_pos hpow, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  congr 1
  rw [Real.rpow_neg ht.le, Real.rpow_natCast]

/-- The finite-state envelope of the analytic numerator converges along the
universal calendar. -/
theorem
    AnalyticScaledChargedOccupationPotential.tendsto_numeratorBound
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)) :
    Tendsto
      (fun k : ℕ =>
        finiteStatePotentialBound
          (P.potential (universalEpochScale k)))
      atTop
      (𝓝 (finiteStatePotentialBound (P.potential 0))) := by
  unfold finiteStatePotentialBound
  apply tendsto_finsetSum Finset.univ
  intro state _
  exact
    (((analyticAt_pi_iff.mp P.analytic_potential state).continuousAt.tendsto
      ).comp tendsto_universalEpochScale).abs

/-- The singular endpoint bill is negligible compared with its quadratic
epoch length, for every finite clearing order. -/
theorem
    AnalyticScaledChargedOccupationPotential.tendsto_epochBudget_div_length
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)) :
    Tendsto
      (fun k : ℕ =>
        puncturedPotentialEpochBudget germ B who P k /
          (anytimeEpochLength k : ℝ))
      atTop (𝓝 0) := by
  have hscale :
      Tendsto
        (fun k : ℕ =>
          universalEpochScale k ^ (-(P.poleOrder : ℝ)) /
            ((k : ℝ) + 1) ^ (2 : ℝ))
        atTop (𝓝 0) :=
    tendsto_scale_neg_rpow_div_succ_rpow
      (P.poleOrder : ℝ) 2 (by norm_num)
  have hproduct :=
    (tendsto_numeratorBound germ B who P).const_mul 2 |>.mul hscale
  simpa only [puncturedPotentialEpochBudget,
    finiteStatePotentialBound_punctured germ B who P
      (universalEpochScale_pos _),
    anytimeEpochLength, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
    Real.rpow_two, mul_zero, mul_div_assoc, ← mul_assoc] using hproduct

/-- A fixed analytic burn-in does not change the vanishing
epoch-bill-to-length ratio. -/
theorem
    AnalyticScaledChargedOccupationPotential.tendsto_shiftedEpochBudget_div_length
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who))
    (startEpoch : ℕ) :
    Tendsto
      (fun k : ℕ =>
        shiftedPuncturedPotentialEpochBudget
            germ B who P startEpoch k /
          (anytimeEpochLength k : ℝ))
      atTop (𝓝 0) := by
  let lengthR : ℕ → ℝ := fun k => (anytimeEpochLength k : ℝ)
  let epochBudget : ℕ → ℝ :=
    puncturedPotentialEpochBudget germ B who P
  have hlength_ne (k : ℕ) :
      lengthR k = 0 → epochBudget k = 0 := by
    intro hzero
    have hpos : (0 : ℝ) < lengthR k := by
      dsimp only [lengthR]
      simp only [anytimeEpochLength]
      positivity
    exact (ne_of_gt hpos hzero).elim
  have hbudget_length :
      epochBudget =o[atTop] lengthR := by
    apply
      (Asymptotics.isLittleO_iff_tendsto
        hlength_ne).2
    exact tendsto_epochBudget_div_length germ B who P
  have hshift :
      Tendsto (fun k : ℕ => startEpoch + k) atTop atTop := by
    refine tendsto_atTop.2 fun K => ?_
    filter_upwards [eventually_ge_atTop K] with k hk
    omega
  have hshifted :
      (fun k : ℕ => epochBudget (startEpoch + k)) =o[atTop]
        (fun k : ℕ => lengthR (startEpoch + k)) :=
    hbudget_length.comp_tendsto hshift
  have hlength_shift :
      (fun k : ℕ => lengthR (startEpoch + k)) =O[atTop]
        lengthR := by
    rw [Asymptotics.isBigO_iff]
    refine
      ⟨(((startEpoch : ℝ) + 1) ^ 2),
        Filter.Eventually.of_forall fun k => ?_⟩
    have hleft_nonneg :
        0 ≤ lengthR (startEpoch + k) := by
      dsimp only [lengthR]
      positivity
    have hright_nonneg :
        0 ≤ lengthR k := by
      dsimp only [lengthR]
      positivity
    rw [Real.norm_of_nonneg hleft_nonneg,
      Real.norm_of_nonneg hright_nonneg]
    dsimp only [lengthR]
    simp only [anytimeEpochLength]
    push_cast
    have hbase :
        (startEpoch : ℝ) + (k : ℝ) + 1 ≤
          ((startEpoch : ℝ) + 1) * ((k : ℝ) + 1) := by
      have hstartR : 0 ≤ (startEpoch : ℝ) :=
        Nat.cast_nonneg startEpoch
      have hkR : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      nlinarith [mul_nonneg hstartR hkR]
    calc
      ((startEpoch : ℝ) + (k : ℝ) + 1) ^ 2 ≤
          (((startEpoch : ℝ) + 1) *
            ((k : ℝ) + 1)) ^ 2 := by
        exact pow_le_pow_left₀ (by positivity) hbase 2
      _ =
          ((startEpoch : ℝ) + 1) ^ 2 *
            ((k : ℝ) + 1) ^ 2 := by ring
  have hfinal :
      (fun k : ℕ => epochBudget (startEpoch + k)) =o[atTop]
        lengthR :=
    hshifted.trans_isBigO hlength_shift
  simpa only [shiftedPuncturedPotentialEpochBudget,
    epochBudget, lengthR] using
      hfinal.tendsto_div_nhds_zero

/-- The completed-plus-current punctured-potential calendar account is
nonnegative and asymptotically sublinear at every calendar horizon. -/
theorem
    AnalyticScaledChargedOccupationPotential.puncturedPotentialCalendarBudget_sublinear
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)) :
    IsAsymptoticallySublinear
      (puncturedPotentialCalendarBudget germ B who P) := by
  apply completedAndCurrentEpochBudget_sublinear
  · intro k
    unfold puncturedPotentialEpochBudget
    exact mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun state _ =>
        abs_nonneg
          (germ.puncturedPlayerNeutralPotentialAt
            B who P (universalEpochScale k) state))
  · exact tendsto_epochBudget_div_length germ B who P

/-- The completed-plus-current punctured account remains sublinear after
the burn-in needed to enter the analytic regime. -/
theorem
    AnalyticScaledChargedOccupationPotential.shiftedPuncturedPotentialCalendarBudget_sublinear
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who))
    (startEpoch : ℕ) :
    IsAsymptoticallySublinear
      (shiftedPuncturedPotentialCalendarBudget
        germ B who P startEpoch) := by
  apply completedAndCurrentEpochBudget_sublinear
  · intro k
    unfold shiftedPuncturedPotentialEpochBudget
      puncturedPotentialEpochBudget
    exact mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun state _ =>
        abs_nonneg
          (germ.puncturedPlayerNeutralPotentialAt B who P
            (universalEpochScale (startEpoch + k)) state))
  · exact
      tendsto_shiftedEpochBudget_div_length
        germ B who P startEpoch

/-- The exact moving raw charge accumulated through completed epochs and
the current epoch prefix is bounded above by the punctured-potential
calendar account.  This is a one-sided expectation estimate for the active
neutral family only. -/
theorem
    AnalyticScaledChargedOccupationPotential.expectedActiveCalendarCharge_le_budget
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who))
    (active : Finset (germ.PlayerNeutralOccupationIndex who))
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (initial : ℕ → G.State)
    (selection :
      ℕ → ∀ n : ℕ, (Fin (n + 1) → G.State) →
        PMF
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active})
    (source_compatible :
      ∀ k n history index,
        selection k n history index ≠ 0 →
          germ.playerNeutralOccupationSource who index.1 =
            history (Fin.last n))
    (hcharge :
      ∀ k index,
        germ.rawPlayerNeutralOccupationCharge B who
            (shiftedUniversalEpochScale startEpoch k) index.1 ≤
          transitionPotentialDrift
            (fun activeIndex =>
              germ.finkPlayerNeutralOccupationKernelAt
                (valid k) who activeIndex.1)
            (fun activeIndex =>
              germ.playerNeutralOccupationSource who activeIndex.1)
            (germ.puncturedPlayerNeutralPotentialAt B who P
              (shiftedUniversalEpochScale startEpoch k))
            (index :
              {index : germ.PlayerNeutralOccupationIndex who //
                index ∈ active}))
    (T : ℕ) :
    expectedActiveCalendarCharge germ B who active startEpoch valid
        initial selection T ≤
      shiftedPuncturedPotentialCalendarBudget
        germ B who P startEpoch T := by
  have hepoch (k horizon : ℕ) :
      expectedActiveEpochCharge germ B who active startEpoch valid
          initial selection k horizon ≤
        shiftedPuncturedPotentialEpochBudget
          germ B who P startEpoch k := by
    simpa only [expectedActiveEpochCharge,
      shiftedPuncturedPotentialEpochBudget,
      puncturedPotentialEpochBudget,
      shiftedUniversalEpochScale] using
      expected_activeCharge_le germ B who P active
        (valid k) (hcharge k) (initial k) (selection k)
        (source_compatible k) horizon
  unfold expectedActiveCalendarCharge
    shiftedPuncturedPotentialCalendarBudget
    completedAndCurrentEpochBudget
  apply add_le_add
  · exact Finset.sum_le_sum fun k _ =>
      hepoch k (anytimeEpochLength k)
  · exact hepoch (anytimeEpochIndex T) (anytimeEpochOffset T)

/-- Every scaled player-neutral potential therefore supplies, after a
finite analytic burn-in, a sublinear one-sided account for every predictable
source-compatible mixture of the chosen active neutral columns.  The
existence statement deliberately leaves arbitrary-deviation classification
and punishment credibility outside this theorem. -/
theorem
    AnalyticScaledChargedOccupationPotential.exists_sublinearActiveCalendarAccount
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who))
    (active : Finset (germ.PlayerNeutralOccupationIndex who)) :
    ∃ (startEpoch : ℕ)
        (valid :
          ∀ k : ℕ,
            shiftedUniversalEpochScale startEpoch k ∈
              Ioo (0 : ℝ) germ.radius),
      ∀ (initial : ℕ → G.State)
        (selection :
          ℕ → ∀ n : ℕ, (Fin (n + 1) → G.State) →
            PMF
              {index : germ.PlayerNeutralOccupationIndex who //
                index ∈ active}),
        (∀ k n history index,
          selection k n history index ≠ 0 →
            germ.playerNeutralOccupationSource who index.1 =
              history (Fin.last n)) →
        (∀ T,
          expectedActiveCalendarCharge germ B who active
              startEpoch valid initial selection T ≤
            shiftedPuncturedPotentialCalendarBudget
              germ B who P startEpoch T) ∧
          IsAsymptoticallySublinear
            (shiftedPuncturedPotentialCalendarBudget
              germ B who P startEpoch) := by
  obtain ⟨startEpoch, valid, hcharge⟩ :=
    exists_startEpoch_activeCharge_le_drift
      germ B who P active
  refine ⟨startEpoch, valid, ?_⟩
  intro initial selection source_compatible
  constructor
  · intro T
    exact expectedActiveCalendarCharge_le_budget
      germ B who P active startEpoch valid initial selection
      source_compatible hcharge T
  · exact shiftedPuncturedPotentialCalendarBudget_sublinear
      germ B who P startEpoch

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
