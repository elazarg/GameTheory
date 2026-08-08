/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Analytic.PlayerOwned.ScaledPotential
import UniformEquilibrium.VanishingDiscount.Analytic.PlayerNeutral.PuncturedPotentialCalendarAccount

/-!
# Calendar envelopes for full player-owned potentials

A scaled charged-occupation potential on the full operational family of one
player controls every pure action of that player.  Dividing by the clearing
power can make the resulting state potential singular at the endpoint.  The
universal quadratic calendar absorbs every finite pole order: the parameter
is frozen during an epoch, and twice the finite-state potential envelope is
charged once for that epoch.

This file contains only the analytic burn-in and the explicit sublinear
calendar envelope.  The actual full-history behavior law is constructed in
`PlayerOwnedBehaviorCalendarAccount`.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm

open Filter Math Math.OnlineLearning Math.Probability Set Topology
open Math.Probability.AnalyticScaledChargedOccupationPotential

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

/-- The full player-owned charge is eventually dominated by the semantic
drift of the punctured potential on every operational row. -/
theorem
    AnalyticScaledChargedOccupationPotential.eventually_playerOwnedCharge_le_drift
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who)) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
        ∀ index : OwnerOccupationIndex G who,
          germ.rawPlayerOwnedOccupationCharge B who t index ≤
            transitionPotentialDrift
              (germ.finkOwnerActualOccupationKernelAt ht who)
              (ownerActualOccupationSource who)
              (germ.puncturedPlayerOwnedPotentialAt B who P t)
              index := by
  have heventual :=
    AnalyticScaledChargedOccupationPotential.eventually_playerOwnedBiasCorrectionAt
      germ B who P
  filter_upwards [heventual] with t hcorrection
  intro ht index
  have hcharged :
      IsChargedOccupationPotential
        (germ.rawOwnerAnalyticOccupationColumn who t)
        (germ.rawPlayerOwnedOccupationCharge B who t)
        (germ.puncturedPlayerOwnedPotentialAt B who P t) :=
    (germ.chargedOccupationPotential_iff_playerOwnedBiasCorrectionAt
      B ht who
        (germ.puncturedPlayerOwnedPotentialAt B who P t)).2
      (hcorrection ht)
  have hindex := hcharged index
  rw [germ.potential_pair_rawOwnerAnalyticOccupationColumn_eq
    ht who (germ.puncturedPlayerOwnedPotentialAt B who P t)
      index] at hindex
  exact hindex

/-- A finite burn-in after which every shifted calendar scale is valid and
the full owner charge-to-drift inequality holds. -/
theorem
    AnalyticScaledChargedOccupationPotential.exists_startEpoch_playerOwnedCharge_le_drift
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who)) :
    ∃ (startEpoch : ℕ)
        (valid :
          ∀ k : ℕ,
            shiftedUniversalEpochScale startEpoch k ∈
              Ioo (0 : ℝ) germ.radius),
      ∀ k index,
        germ.rawPlayerOwnedOccupationCharge B who
            (shiftedUniversalEpochScale startEpoch k) index ≤
          transitionPotentialDrift
            (germ.finkOwnerActualOccupationKernelAt (valid k) who)
            (ownerActualOccupationSource who)
            (germ.puncturedPlayerOwnedPotentialAt B who P
              (shiftedUniversalEpochScale startEpoch k))
            index := by
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
  have hcharge :
      ∀ᶠ k : ℕ in atTop,
        ∀ hk :
            universalEpochScale k ∈ Ioo (0 : ℝ) germ.radius,
          ∀ index : OwnerOccupationIndex G who,
            germ.rawPlayerOwnedOccupationCharge B who
                (universalEpochScale k) index ≤
              transitionPotentialDrift
                (germ.finkOwnerActualOccupationKernelAt hk who)
                (ownerActualOccupationSource who)
                (germ.puncturedPlayerOwnedPotentialAt B who P
                  (universalEpochScale k))
                index := by
    exact hscale.eventually
      (eventually_playerOwnedCharge_le_drift germ B who P)
  obtain ⟨startEpoch, hstart⟩ :=
    eventually_atTop.1 (hcharge.and hvalid)
  let valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius :=
    fun k => (hstart (startEpoch + k) (by omega)).2
  refine ⟨startEpoch, valid, ?_⟩
  intro k index
  have h :=
    (hstart (startEpoch + k) (by omega)).1 (valid k) index
  simpa only [shiftedUniversalEpochScale] using h

/-- Twice the full player-owned punctured-potential envelope for one
calendar epoch. -/
def
    AnalyticScaledChargedOccupationPotential.playerOwnedPotentialEpochBudget
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who))
    (startEpoch k : ℕ) : ℝ :=
  2 * finiteStatePotentialBound
    (germ.puncturedPlayerOwnedPotentialAt B who P
      (shiftedUniversalEpochScale startEpoch k))

/-- Completed epochs plus the whole current epoch form an all-horizon
player-owned potential budget. -/
def
    AnalyticScaledChargedOccupationPotential.playerOwnedPotentialCalendarBudget
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who))
    (startEpoch T : ℕ) : ℝ :=
  completedAndCurrentEpochBudget
    (playerOwnedPotentialEpochBudget germ B who P startEpoch) T

/-- Dividing the analytic numerator by a positive natural power multiplies
its finite-state envelope by the corresponding negative real power. -/
theorem
    AnalyticScaledChargedOccupationPotential.finiteStatePotentialBound_playerOwned
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who))
    {t : ℝ} (ht : 0 < t) :
    finiteStatePotentialBound
        (germ.puncturedPlayerOwnedPotentialAt B who P t) =
      finiteStatePotentialBound (P.potential t) *
        t ^ (-(P.poleOrder : ℝ)) := by
  have hpow : 0 < t ^ P.poleOrder := pow_pos ht _
  unfold finiteStatePotentialBound puncturedPlayerOwnedPotentialAt
  simp_rw [abs_div, abs_of_pos hpow, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  congr 1
  rw [Real.rpow_neg ht.le, Real.rpow_natCast]

/-- The finite-state envelope of the analytic numerator converges along the
universal scale. -/
theorem
    AnalyticScaledChargedOccupationPotential.tendsto_playerOwnedNumeratorBound
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who)) :
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

/-- The unshifted full-owner epoch bill is negligible compared with the
quadratic epoch length. -/
theorem
    AnalyticScaledChargedOccupationPotential.tendsto_playerOwnedBaseEpochBudget_div_length
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who)) :
    Tendsto
      (fun k : ℕ =>
        (2 * finiteStatePotentialBound
          (germ.puncturedPlayerOwnedPotentialAt B who P
            (universalEpochScale k))) /
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
    (tendsto_playerOwnedNumeratorBound germ B who P).const_mul 2
      |>.mul hscale
  simpa only [
    finiteStatePotentialBound_playerOwned germ B who P
      (universalEpochScale_pos _),
    anytimeEpochLength, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
    Real.rpow_two, mul_zero, mul_div_assoc, ← mul_assoc] using hproduct

/-- A fixed analytic burn-in does not change the vanishing
epoch-bill-to-length ratio. -/
theorem
    AnalyticScaledChargedOccupationPotential.tendsto_playerOwnedEpochBudget_div_length
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who))
    (startEpoch : ℕ) :
    Tendsto
      (fun k : ℕ =>
        playerOwnedPotentialEpochBudget
            germ B who P startEpoch k /
          (anytimeEpochLength k : ℝ))
      atTop (𝓝 0) := by
  let lengthR : ℕ → ℝ := fun k => (anytimeEpochLength k : ℝ)
  let epochBudget : ℕ → ℝ := fun k =>
    2 * finiteStatePotentialBound
      (germ.puncturedPlayerOwnedPotentialAt B who P
        (universalEpochScale k))
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
    exact tendsto_playerOwnedBaseEpochBudget_div_length
      germ B who P
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
  simpa only [playerOwnedPotentialEpochBudget,
    shiftedUniversalEpochScale, epochBudget, lengthR] using
      hfinal.tendsto_div_nhds_zero

/-- The completed-plus-current player-owned potential account is
asymptotically sublinear at every horizon. -/
theorem
    AnalyticScaledChargedOccupationPotential.playerOwnedPotentialCalendarBudget_sublinear
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who))
    (startEpoch : ℕ) :
    IsAsymptoticallySublinear
      (playerOwnedPotentialCalendarBudget
        germ B who P startEpoch) := by
  apply completedAndCurrentEpochBudget_sublinear
  · intro k
    unfold playerOwnedPotentialEpochBudget
    exact mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun state _ =>
        abs_nonneg
          (germ.puncturedPlayerOwnedPotentialAt B who P
            (shiftedUniversalEpochScale startEpoch k) state))
  · exact
      tendsto_playerOwnedEpochBudget_div_length
        germ B who P startEpoch

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
