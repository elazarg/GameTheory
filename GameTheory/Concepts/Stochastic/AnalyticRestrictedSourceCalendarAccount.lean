/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.AnalyticRestrictedSourceChargeAlternative
import Math.Probability.SupportedMovingKernelEpochAccount

/-!
# Fixed-start calendar accounts for restricted analytic sources

An analytic raw occupation column may be indexed by a finite source family
`R` which is distinct from its finite ambient state space `S`.  The analytic
curve is real-valued; only the parameters selected by the fixed shifted
calendar are required to have a stochastic interpretation.

This file connects a pole-cleared
`AnalyticScaledChargedOccupationPotential` to that semantic interpretation.
The supplied calendar base is never rebased.  Instead, the analytic
inequality is allowed to begin at a finite relative epoch
`firstGoodEpoch`.  The resulting ambient-state punctured-potential bill is
negligible compared with the exact quadratic epoch length.
-/

set_option autoImplicit false

noncomputable section

namespace Math
namespace Probability

open Filter Math.OnlineLearning Set Topology

variable {R S : Type*}

/-- An epoch-indexed semantic kernel realizes the restricted raw occupation
column at the corresponding point of one fixed shifted calendar. -/
def RealizesShiftedRestrictedRawOccupationColumn
    [DecidableEq S]
    (column : ℝ → R → S → ℝ) (source : R → S)
    (base : ℕ) (kernel : ℕ → R → PMF S) : Prop :=
  ∀ epoch index destination,
    column (shiftedUniversalEpochScale base epoch) index destination =
      (kernel epoch index destination).toReal -
        if destination = source index then 1 else 0

namespace AnalyticScaledChargedOccupationPotential

/-- Undo the positive clearing power at a punctured parameter.  This
definition is independent of the type indexing the analytic columns. -/
def restrictedPuncturedPotentialAt
    [Fintype R] [Fintype S]
    {column : ℝ → R → S → ℝ} {charge : ℝ → R → ℝ}
    (P : AnalyticScaledChargedOccupationPotential column charge)
    (t : ℝ) (destination : S) : ℝ :=
  P.potential t destination / t ^ P.poleOrder

/-- The ambient-state punctured potential frozen during an epoch of the
fixed shifted calendar. -/
def shiftedRestrictedPuncturedPotential
    [Fintype R] [Fintype S]
    {column : ℝ → R → S → ℝ} {charge : ℝ → R → ℝ}
    (P : AnalyticScaledChargedOccupationPotential column charge)
    (base epoch : ℕ) : S → ℝ :=
  P.restrictedPuncturedPotentialAt
    (shiftedUniversalEpochScale base epoch)

/-- At one positive parameter, exact semantic realization of a restricted
raw column turns its scaled analytic inequality into ordinary potential
drift. -/
theorem charge_le_semanticKernel_restrictedPuncturedDrift
    [Fintype R] [Fintype S] [DecidableEq S]
    {column : ℝ → R → S → ℝ} {charge : ℝ → R → ℝ}
    (P : AnalyticScaledChargedOccupationPotential column charge)
    {t : ℝ} (ht : 0 < t)
    (source : R → S) (kernel : R → PMF S)
    (realizes :
      ∀ index destination,
        column t index destination =
          (kernel index destination).toReal -
            if destination = source index then 1 else 0)
    (scaled :
      ∀ index,
        t ^ P.poleOrder * charge t index ≤
          ∑ destination,
            P.potential t destination *
              column t index destination)
    (index : R) :
    charge t index ≤
      expect (kernel index) (P.restrictedPuncturedPotentialAt t) -
        P.restrictedPuncturedPotentialAt t (source index) := by
  have hcolumn :
      column t index =
        actualOccupationColumn kernel source index := by
    funext destination
    rw [realizes index destination]
    rfl
  have hpair :
      (∑ destination,
          P.potential t destination * column t index destination) =
        expect (kernel index) (P.potential t) -
          P.potential t (source index) := by
    rw [hcolumn]
    exact potential_pair_actualOccupationColumn
      kernel source (P.potential t) index
  have hpow : 0 < t ^ P.poleOrder := pow_pos ht _
  have hexpect :
      expect (kernel index) (P.restrictedPuncturedPotentialAt t) =
        expect (kernel index) (P.potential t) /
          t ^ P.poleOrder := by
    calc
      expect (kernel index) (P.restrictedPuncturedPotentialAt t) =
          expect (kernel index)
            (fun destination =>
              (t ^ P.poleOrder)⁻¹ *
                P.potential t destination) := by
            congr 1
            funext destination
            rw [restrictedPuncturedPotentialAt, div_eq_inv_mul]
      _ =
          (t ^ P.poleOrder)⁻¹ *
            expect (kernel index) (P.potential t) := by
            rw [expect_const_mul]
      _ =
          expect (kernel index) (P.potential t) /
            t ^ P.poleOrder := by
            rw [div_eq_mul_inv, mul_comm]
  rw [hexpect, restrictedPuncturedPotentialAt, ← sub_div]
  apply (le_div_iff₀ hpow).2
  rw [mul_comm]
  exact (scaled index).trans_eq hpair

/-- On the original fixed shifted calendar, the semantic charge-to-drift
inequality holds from some finite relative epoch onward.  In particular,
`base` is not increased or absorbed into `firstGoodEpoch`. -/
theorem exists_firstGoodEpoch_charge_le_semanticKernel_drift
    [Fintype R] [Fintype S] [DecidableEq S]
    {column : ℝ → R → S → ℝ} {charge : ℝ → R → ℝ}
    (P : AnalyticScaledChargedOccupationPotential column charge)
    (source : R → S) (base : ℕ)
    (kernel : ℕ → R → PMF S)
    (realizes :
      RealizesShiftedRestrictedRawOccupationColumn
        column source base kernel) :
    ∃ firstGoodEpoch : ℕ,
      ∀ epoch, firstGoodEpoch ≤ epoch → ∀ index,
        charge (shiftedUniversalEpochScale base epoch) index ≤
          expect (kernel epoch index)
              (P.shiftedRestrictedPuncturedPotential base epoch) -
            P.shiftedRestrictedPuncturedPotential
              base epoch (source index) := by
  have hscale :
      Tendsto (shiftedUniversalEpochScale base)
        atTop (nhdsWithin 0 (Ioi (0 : ℝ))) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact
      ⟨tendsto_shiftedUniversalEpochScale base,
        Filter.Eventually.of_forall fun epoch =>
          shiftedUniversalEpochScale_pos base epoch⟩
  have heventual :
      ∀ᶠ epoch : ℕ in atTop,
        ∀ index,
          shiftedUniversalEpochScale base epoch ^ P.poleOrder *
                charge
                  (shiftedUniversalEpochScale base epoch) index ≤
            ∑ destination,
              P.potential
                    (shiftedUniversalEpochScale base epoch)
                    destination *
                column
                  (shiftedUniversalEpochScale base epoch)
                  index destination :=
    hscale.eventually P.eventual
  obtain ⟨firstGoodEpoch, hgood⟩ :=
    eventually_atTop.1 heventual
  refine ⟨firstGoodEpoch, ?_⟩
  intro epoch epoch_ge index
  apply P.charge_le_semanticKernel_restrictedPuncturedDrift
    (shiftedUniversalEpochScale_pos base epoch)
    source (kernel epoch)
    (fun row destination =>
      realizes epoch row destination)
  exact hgood epoch epoch_ge

/-- Dividing the analytic numerator by a positive natural power multiplies
its ambient finite-state envelope by the corresponding negative real
power. -/
theorem finiteStatePotentialBound_restrictedPuncturedPotentialAt
    [Fintype R] [Fintype S]
    {column : ℝ → R → S → ℝ} {charge : ℝ → R → ℝ}
    (P : AnalyticScaledChargedOccupationPotential column charge)
    {t : ℝ} (ht : 0 < t) :
    finiteStatePotentialBound (P.restrictedPuncturedPotentialAt t) =
      finiteStatePotentialBound (P.potential t) *
        t ^ (-(P.poleOrder : ℝ)) := by
  have hpow : 0 < t ^ P.poleOrder := pow_pos ht _
  unfold finiteStatePotentialBound restrictedPuncturedPotentialAt
  simp_rw [abs_div, abs_of_pos hpow, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  congr 1
  rw [Real.rpow_neg ht.le, Real.rpow_natCast]

/-- The finite-state envelope of the analytic numerator converges along the
unshifted universal scale. -/
theorem tendsto_restrictedPotentialBound_universalEpochScale
    [Fintype R] [Fintype S]
    {column : ℝ → R → S → ℝ} {charge : ℝ → R → ℝ}
    (P : AnalyticScaledChargedOccupationPotential column charge) :
    Tendsto
      (fun epoch : ℕ =>
        finiteStatePotentialBound
          (P.potential (universalEpochScale epoch)))
      atTop
      (𝓝 (finiteStatePotentialBound (P.potential 0))) := by
  unfold finiteStatePotentialBound
  apply tendsto_finsetSum Finset.univ
  intro state _
  exact
    (((analyticAt_pi_iff.mp P.analytic_potential state).continuousAt.tendsto
      ).comp tendsto_universalEpochScale).abs

/-- The ambient finite-state potential bill on the original shifted
calendar is negligible compared with the exact quadratic epoch length. -/
theorem tendsto_shiftedRestrictedPotential_bill_div_length
    [Fintype R] [Fintype S]
    {column : ℝ → R → S → ℝ} {charge : ℝ → R → ℝ}
    (P : AnalyticScaledChargedOccupationPotential column charge)
    (base : ℕ) :
    Tendsto
      (fun epoch : ℕ =>
        epochPotentialBill
              (P.shiftedRestrictedPuncturedPotential base) epoch /
          (anytimeEpochLength epoch : ℝ))
      atTop (𝓝 0) := by
  let lengthR : ℕ → ℝ :=
    fun epoch => (anytimeEpochLength epoch : ℝ)
  let epochBill : ℕ → ℝ :=
    fun epoch =>
      2 * finiteStatePotentialBound
        (P.restrictedPuncturedPotentialAt
          (universalEpochScale epoch))
  have hscale :
      Tendsto
        (fun epoch : ℕ =>
          universalEpochScale epoch ^ (-(P.poleOrder : ℝ)) /
            ((epoch : ℝ) + 1) ^ (2 : ℝ))
        atTop (𝓝 0) :=
    tendsto_scale_neg_rpow_div_succ_rpow
      (P.poleOrder : ℝ) 2 (by norm_num)
  have hratio :
      Tendsto
        (fun epoch : ℕ => epochBill epoch / lengthR epoch)
        atTop (𝓝 0) := by
    have hproduct :=
      (P.tendsto_restrictedPotentialBound_universalEpochScale).const_mul 2
        |>.mul hscale
    simpa only [epochBill, lengthR,
      P.finiteStatePotentialBound_restrictedPuncturedPotentialAt
        (universalEpochScale_pos _),
      anytimeEpochLength, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
      Real.rpow_two, mul_zero, mul_div_assoc, ← mul_assoc] using
        hproduct
  have hlength_ne (epoch : ℕ) :
      lengthR epoch = 0 → epochBill epoch = 0 := by
    intro hzero
    have hpos : (0 : ℝ) < lengthR epoch := by
      dsimp only [lengthR]
      simp only [anytimeEpochLength]
      positivity
    exact (ne_of_gt hpos hzero).elim
  have hbill_length :
      epochBill =o[atTop] lengthR := by
    apply
      (Asymptotics.isLittleO_iff_tendsto hlength_ne).2
    exact hratio
  have hshift :
      Tendsto (fun epoch : ℕ => base + epoch) atTop atTop := by
    refine tendsto_atTop.2 fun lower => ?_
    filter_upwards [eventually_ge_atTop lower] with epoch epoch_ge
    omega
  have hshifted :
      (fun epoch : ℕ => epochBill (base + epoch)) =o[atTop]
        (fun epoch : ℕ => lengthR (base + epoch)) :=
    hbill_length.comp_tendsto hshift
  have hlength_shift :
      (fun epoch : ℕ => lengthR (base + epoch)) =O[atTop]
        lengthR := by
    rw [Asymptotics.isBigO_iff]
    refine
      ⟨(((base : ℝ) + 1) ^ 2),
        Filter.Eventually.of_forall fun epoch => ?_⟩
    have hleft_nonneg :
        0 ≤ lengthR (base + epoch) := by
      dsimp only [lengthR]
      positivity
    have hright_nonneg :
        0 ≤ lengthR epoch := by
      dsimp only [lengthR]
      positivity
    rw [Real.norm_of_nonneg hleft_nonneg,
      Real.norm_of_nonneg hright_nonneg]
    dsimp only [lengthR]
    simp only [anytimeEpochLength]
    push_cast
    have hbase :
        (base : ℝ) + (epoch : ℝ) + 1 ≤
          ((base : ℝ) + 1) * ((epoch : ℝ) + 1) := by
      have hbaseR : 0 ≤ (base : ℝ) := Nat.cast_nonneg base
      have hepochR : 0 ≤ (epoch : ℝ) := Nat.cast_nonneg epoch
      nlinarith [mul_nonneg hbaseR hepochR]
    calc
      ((base : ℝ) + (epoch : ℝ) + 1) ^ 2 ≤
          (((base : ℝ) + 1) * ((epoch : ℝ) + 1)) ^ 2 := by
        exact pow_le_pow_left₀ (by positivity) hbase 2
      _ =
          ((base : ℝ) + 1) ^ 2 *
            ((epoch : ℝ) + 1) ^ 2 := by ring
  have hfinal :
      (fun epoch : ℕ => epochBill (base + epoch)) =o[atTop]
        lengthR :=
    hshifted.trans_isBigO hlength_shift
  simpa only [epochPotentialBill,
    shiftedRestrictedPuncturedPotential,
    shiftedUniversalEpochScale, epochBill, lengthR] using
      hfinal.tendsto_div_nhds_zero

end AnalyticScaledChargedOccupationPotential

end Probability
end Math
