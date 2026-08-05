/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.OnlineLearning.CompletedEpochCalendar
import Math.Probability.AnalyticChargedOccupationFlow
import Math.Probability.HarmonicStateAccount

/-!
# Analytic Markov charge alternatives

For an analytic finite Markov kernel and an analytic signed state charge,
the analytic charged occupation alternative has an exact recurrence
interpretation:

* either a pole-cleared analytic stationary flow has positive total charge;
* or a pole-cleared analytic potential dominates the charge by its one-step
  drift.

The second branch is the local input to a moving-kernel epoch account.  This
file deliberately stops at that local analytic alternative; the stochastic
calendar telescope is independent of analytic selection.  A witness-state
indicator is retained as an important specialization.
-/

noncomputable section

namespace Math
namespace Probability

open Filter Set Topology
open Math.OnlineLearning

variable {S : Type*}

/-- The occupation column of the baseline row indexed by `source`. -/
def analyticMarkovOccupationColumn
    [Fintype S] [DecidableEq S]
    (kernel : ℝ → S → PMF S) :
    ℝ → S → S → ℝ :=
  fun t source =>
    actualOccupationColumn (kernel t) id source

/-- Unit occupation charge at one fixed witness state. -/
def witnessOccupationCharge
    [DecidableEq S] (witness : S) :
    ℝ → S → ℝ :=
  fun _ source => if source = witness then 1 else 0

theorem analytic_analyticMarkovOccupationColumn
    [Fintype S] [DecidableEq S]
    (kernel : ℝ → S → PMF S)
    (hkernel :
      ∀ source destination,
        AnalyticAt ℝ
          (fun t => (kernel t source destination).toReal) 0)
    (source destination : S) :
    AnalyticAt ℝ
      (fun t =>
        analyticMarkovOccupationColumn kernel t source destination)
      0 := by
  unfold analyticMarkovOccupationColumn
  simp only [actualOccupationColumn, id_eq]
  exact (hkernel source destination).sub analyticAt_const

theorem analytic_witnessOccupationCharge
    [DecidableEq S] (witness source : S) :
    AnalyticAt ℝ (fun t => witnessOccupationCharge witness t source) 0 := by
  exact analyticAt_const

/-- The analytic charged-flow alternative specialized to occupation of one
fixed state under an analytic Markov kernel. -/
theorem analyticPositiveWitnessCirculation_xor_scaledOccupationPotential
    [Fintype S] [DecidableEq S]
    (kernel : ℝ → S → PMF S) (witness : S)
    (hkernel :
      ∀ source destination,
        AnalyticAt ℝ
          (fun t => (kernel t source destination).toReal) 0) :
    Xor
      (Nonempty
        (AnalyticPositiveChargedCirculation
          (analyticMarkovOccupationColumn kernel)
          (witnessOccupationCharge witness)))
      (Nonempty
        (AnalyticScaledChargedOccupationPotential
          (analyticMarkovOccupationColumn kernel)
          (witnessOccupationCharge witness))) := by
  exact analyticPositiveChargedCirculation_xor_scaledPotential
    (analyticMarkovOccupationColumn kernel)
    (witnessOccupationCharge witness)
    (analytic_analyticMarkovOccupationColumn kernel hkernel)
    (analytic_witnessOccupationCharge witness)

namespace AnalyticPositiveChargedCirculation

/-- In the circulation branch, the exact total charge identity is exactly
positive mass at the witness state. -/
theorem eventually_mass_witness_eq
    [Fintype S] [DecidableEq S]
    {kernel : ℝ → S → PMF S} {witness : S}
    (C : AnalyticPositiveChargedCirculation
      (analyticMarkovOccupationColumn kernel)
      (witnessOccupationCharge witness)) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      C.mass t witness = t ^ C.poleOrder := by
  filter_upwards [C.eventual] with t ht
  simpa [witnessOccupationCharge] using ht.2.2

/-- The circulation branch is a pole-cleared analytic stationary flow whose
witness coordinate is a strictly positive power on the punctured germ. -/
theorem eventually_witness_positive_and_balance
    [Fintype S] [DecidableEq S]
    {kernel : ℝ → S → PMF S} {witness : S}
    (C : AnalyticPositiveChargedCirculation
      (analyticMarkovOccupationColumn kernel)
      (witnessOccupationCharge witness)) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      (∀ source, 0 ≤ C.mass t source) ∧
        0 < C.mass t witness ∧
        ∀ destination,
          ∑ source,
            C.mass t source *
              analyticMarkovOccupationColumn kernel
                t source destination = 0 := by
  filter_upwards
    [C.eventual, C.eventually_mass_witness_eq, self_mem_nhdsWithin]
      with t ht hmass htpos
  exact
    ⟨ht.1,
      hmass.symm ▸ pow_pos (mem_Ioi.mp htpos) _,
      ht.2.1⟩

end AnalyticPositiveChargedCirculation

namespace AnalyticScaledChargedOccupationPotential

/-- The ordinary punctured potential obtained by undoing the common
power-law clearing factor. -/
def puncturedPotentialAt
    [Fintype S]
    {column : ℝ → S → S → ℝ} {charge : ℝ → S → ℝ}
    (P : AnalyticScaledChargedOccupationPotential column charge)
    (t : ℝ) (destination : S) : ℝ :=
  P.potential t destination / t ^ P.poleOrder

/-- Semantic drift form of a scaled state-row charge under a Markov
kernel. -/
theorem eventually_scaled_markovCharge_le_drift
    [Fintype S] [DecidableEq S]
    {kernel : ℝ → S → PMF S} {charge : ℝ → S → ℝ}
    (P : AnalyticScaledChargedOccupationPotential
      (analyticMarkovOccupationColumn kernel) charge) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ∀ source,
        t ^ P.poleOrder * charge t source ≤
          expect (kernel t source) (P.potential t) -
            P.potential t source := by
  filter_upwards [P.eventual] with t ht source
  simpa [analyticMarkovOccupationColumn,
    potential_pair_actualOccupationColumn] using ht source

/-- After division by the positive clearing power, the original analytic
state charge is dominated by the punctured potential drift. -/
theorem eventually_markovCharge_le_punctured_drift
    [Fintype S] [DecidableEq S]
    {kernel : ℝ → S → PMF S} {charge : ℝ → S → ℝ}
    (P : AnalyticScaledChargedOccupationPotential
      (analyticMarkovOccupationColumn kernel) charge) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ∀ source,
        charge t source ≤
          expect (kernel t source)
              (fun destination =>
                P.puncturedPotentialAt t destination) -
            P.puncturedPotentialAt t source := by
  filter_upwards
    [P.eventually_scaled_markovCharge_le_drift,
      self_mem_nhdsWithin] with t ht htpos source
  have hpow : 0 < t ^ P.poleOrder :=
    pow_pos (mem_Ioi.mp htpos) _
  have hsum :
      expect (kernel t source)
          (fun destination =>
            P.puncturedPotentialAt t destination) =
        expect (kernel t source) (P.potential t) /
          t ^ P.poleOrder := by
    calc
      expect (kernel t source)
          (fun destination =>
            P.puncturedPotentialAt t destination) =
          expect (kernel t source)
            (fun destination =>
              (t ^ P.poleOrder)⁻¹ *
                P.potential t destination) := by
            congr 1
            funext destination
            rw [puncturedPotentialAt, div_eq_inv_mul]
      _ =
          (t ^ P.poleOrder)⁻¹ *
            expect (kernel t source) (P.potential t) := by
            rw [expect_const_mul]
      _ =
          expect (kernel t source) (P.potential t) /
            t ^ P.poleOrder := by
            rw [div_eq_mul_inv, mul_comm]
  rw [hsum, puncturedPotentialAt, ← sub_div]
  exact (le_div_iff₀ hpow).2 (by
    simpa [mul_comm] using ht source)

/-- After one finite burn-in, every shifted universal-calendar parameter
satisfies the analytic charge-to-drift inequality. -/
theorem exists_startEpoch_markovCharge_le_punctured_drift
    [Fintype S] [DecidableEq S]
    {kernel : ℝ → S → PMF S} {charge : ℝ → S → ℝ}
    (P : AnalyticScaledChargedOccupationPotential
      (analyticMarkovOccupationColumn kernel) charge) :
    ∃ startEpoch : ℕ,
      ∀ k source,
        charge (universalEpochScale (startEpoch + k)) source ≤
          expect (kernel (universalEpochScale (startEpoch + k)) source)
              (fun destination =>
                P.puncturedPotentialAt
                  (universalEpochScale (startEpoch + k))
                  destination) -
            P.puncturedPotentialAt
              (universalEpochScale (startEpoch + k)) source := by
  have hscale :
      Tendsto universalEpochScale atTop
        (nhdsWithin 0 (Ioi (0 : ℝ))) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact
      ⟨tendsto_universalEpochScale,
        Filter.Eventually.of_forall universalEpochScale_pos⟩
  have heventual :
      ∀ᶠ k : ℕ in atTop,
        ∀ source,
          charge (universalEpochScale k) source ≤
            expect (kernel (universalEpochScale k) source)
                (fun destination =>
                  P.puncturedPotentialAt
                    (universalEpochScale k) destination) -
              P.puncturedPotentialAt
                (universalEpochScale k) source :=
    hscale.eventually P.eventually_markovCharge_le_punctured_drift
  obtain ⟨startEpoch, hstart⟩ := eventually_atTop.1 heventual
  exact ⟨startEpoch, fun k => hstart (startEpoch + k) (by omega)⟩

/-- Semantic drift form of the scaled witness-potential branch. -/
theorem eventually_scaled_witnessIndicator_le_drift
    [Fintype S] [DecidableEq S]
    {kernel : ℝ → S → PMF S} {witness : S}
    (P : AnalyticScaledChargedOccupationPotential
      (analyticMarkovOccupationColumn kernel)
      (witnessOccupationCharge witness)) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ∀ source,
        t ^ P.poleOrder * (if source = witness then 1 else 0) ≤
          expect (kernel t source) (P.potential t) -
            P.potential t source := by
  simpa only [witnessOccupationCharge] using
    P.eventually_scaled_markovCharge_le_drift

/-- After division by the positive clearing power, the witness indicator is
dominated by one-step drift at every source. -/
theorem eventually_witnessIndicator_le_punctured_drift
    [Fintype S] [DecidableEq S]
    {kernel : ℝ → S → PMF S} {witness : S}
    (P : AnalyticScaledChargedOccupationPotential
      (analyticMarkovOccupationColumn kernel)
      (witnessOccupationCharge witness)) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ∀ source,
        (if source = witness then 1 else 0) ≤
          expect (kernel t source)
              (fun destination =>
                P.puncturedPotentialAt t destination) -
            P.puncturedPotentialAt t source := by
  simpa only [witnessOccupationCharge] using
    P.eventually_markovCharge_le_punctured_drift

/-- After one finite burn-in, every shifted universal-calendar parameter
lies in the punctured branch and satisfies the witness drift inequality. -/
theorem exists_startEpoch_witnessIndicator_le_punctured_drift
    [Fintype S] [DecidableEq S]
    {kernel : ℝ → S → PMF S} {witness : S}
    (P : AnalyticScaledChargedOccupationPotential
      (analyticMarkovOccupationColumn kernel)
      (witnessOccupationCharge witness)) :
    ∃ startEpoch : ℕ,
      ∀ k source,
        (if source = witness then 1 else 0) ≤
          expect (kernel (universalEpochScale (startEpoch + k)) source)
              (fun destination =>
                P.puncturedPotentialAt
                  (universalEpochScale (startEpoch + k))
                  destination) -
            P.puncturedPotentialAt
              (universalEpochScale (startEpoch + k)) source := by
  simpa only [witnessOccupationCharge] using
    P.exists_startEpoch_markovCharge_le_punctured_drift

/-- Endpoint bill for one shifted universal-calendar epoch. -/
def shiftedPuncturedPotentialEpochBudget
    [Fintype S]
    {column : ℝ → S → S → ℝ} {charge : ℝ → S → ℝ}
    (P : AnalyticScaledChargedOccupationPotential column charge)
    (startEpoch k : ℕ) : ℝ :=
  2 * finiteStatePotentialBound
    (P.puncturedPotentialAt
      (universalEpochScale (startEpoch + k)))

theorem shiftedPuncturedPotentialEpochBudget_nonneg
    [Fintype S]
    {column : ℝ → S → S → ℝ} {charge : ℝ → S → ℝ}
    (P : AnalyticScaledChargedOccupationPotential column charge)
    (startEpoch k : ℕ) :
    0 ≤ P.shiftedPuncturedPotentialEpochBudget startEpoch k := by
  unfold shiftedPuncturedPotentialEpochBudget finiteStatePotentialBound
  positivity

/-- Dividing by the clearing power multiplies the finite-state envelope by
the corresponding negative real power. -/
theorem finiteStatePotentialBound_puncturedPotentialAt
    [Fintype S]
    {column : ℝ → S → S → ℝ} {charge : ℝ → S → ℝ}
    (P : AnalyticScaledChargedOccupationPotential column charge)
    {t : ℝ} (ht : 0 < t) :
    finiteStatePotentialBound (P.puncturedPotentialAt t) =
      finiteStatePotentialBound (P.potential t) *
        t ^ (-(P.poleOrder : ℝ)) := by
  have hpow : 0 < t ^ P.poleOrder := pow_pos ht _
  unfold finiteStatePotentialBound puncturedPotentialAt
  simp_rw [abs_div, abs_of_pos hpow, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  congr 1
  rw [Real.rpow_neg ht.le, Real.rpow_natCast]

/-- The finite-state envelope of the analytic numerator converges along the
universal calendar. -/
theorem tendsto_potentialBound_universalEpochScale
    [Fintype S]
    {column : ℝ → S → S → ℝ} {charge : ℝ → S → ℝ}
    (P : AnalyticScaledChargedOccupationPotential column charge) :
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

/-- A fixed burn-in does not prevent the punctured endpoint bill from being
little-o of the quadratic epoch length. -/
theorem tendsto_shiftedPuncturedPotentialEpochBudget_div_length
    [Fintype S]
    {column : ℝ → S → S → ℝ} {charge : ℝ → S → ℝ}
    (P : AnalyticScaledChargedOccupationPotential column charge)
    (startEpoch : ℕ) :
    Tendsto
      (fun k : ℕ =>
        P.shiftedPuncturedPotentialEpochBudget startEpoch k /
          (anytimeEpochLength k : ℝ))
      atTop (𝓝 0) := by
  let lengthR : ℕ → ℝ := fun k => (anytimeEpochLength k : ℝ)
  let epochBudget : ℕ → ℝ :=
    fun k =>
      2 * finiteStatePotentialBound
        (P.puncturedPotentialAt (universalEpochScale k))
  have hscale :
      Tendsto
        (fun k : ℕ =>
          universalEpochScale k ^ (-(P.poleOrder : ℝ)) /
            ((k : ℝ) + 1) ^ (2 : ℝ))
        atTop (𝓝 0) :=
    tendsto_scale_neg_rpow_div_succ_rpow
      (P.poleOrder : ℝ) 2 (by norm_num)
  have hratio :
      Tendsto
        (fun k : ℕ =>
          epochBudget k / lengthR k)
        atTop (𝓝 0) := by
    have hproduct :=
      (P.tendsto_potentialBound_universalEpochScale).const_mul 2
        |>.mul hscale
    simpa only [epochBudget, lengthR,
      P.finiteStatePotentialBound_puncturedPotentialAt
        (universalEpochScale_pos _),
      anytimeEpochLength, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
      Real.rpow_two, mul_zero, mul_div_assoc, ← mul_assoc] using
        hproduct
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
      (Asymptotics.isLittleO_iff_tendsto hlength_ne).2
    exact hratio
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
  simpa only [shiftedPuncturedPotentialEpochBudget, epochBudget,
    lengthR] using hfinal.tendsto_div_nhds_zero

end AnalyticScaledChargedOccupationPotential

end Probability
end Math
