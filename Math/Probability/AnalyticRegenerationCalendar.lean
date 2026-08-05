/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.OnlineLearning.UniversalCalendar
import Math.Probability.AnalyticKernelRegeneration

/-!
# Calendar amplification of analytic regeneration

A target stopped kernel is absorbing at the target.  If every source has
probability at least `δ` of reaching the target in one block of `H` steps,
then failure after `n` consecutive blocks is at most `(1 - δ) ^ n`.

The kernel is fixed throughout each collection of blocks.  Applying this to
the universal logarithmic scale and the quadratic epoch length shows that a
one-block lower bound `c * t ^ K`, for any fixed finite `K`, is amplified to
success probability tending to one.  This file makes no claim about
strategies, monitoring, punishments, or closure of an equilibrium recursion.
-/

noncomputable section

namespace Math
namespace Probability

open Filter Finset BigOperators Set Topology

variable {S : Type*}

/-- A real-valued PMF on a finite type has total mass one. -/
theorem sum_pmf_toReal_eq_one
    [Fintype S] (distribution : PMF S) :
    ∑ state, (distribution state).toReal = 1 := by
  simpa [tsum_fintype] using
    (Math.Probability.pmf_toReal_tsum_one distribution)

/-- Every real PMF coordinate lies below one. -/
theorem pmf_apply_toReal_le_one
    (distribution : PMF S) (state : S) :
    (distribution state).toReal ≤ 1 := by
  have hle := PMF.coe_le_one distribution state
  exact
    (ENNReal.toReal_le_toReal
      (PMF.apply_ne_top distribution state)
      (by norm_num)).mpr hle |>.trans_eq (by simp)

/-- One minus the endpoint mass of a finite PMF bind is the average of the
corresponding one-step failure probabilities. -/
theorem one_sub_bind_apply_toReal
    [Fintype S]
    (distribution : PMF S)
    (transition : S → PMF S)
    (target : S) :
    1 - ((distribution.bind transition) target).toReal =
      ∑ state,
        (distribution state).toReal *
          (1 - (transition state target).toReal) := by
  calc
    1 - ((distribution.bind transition) target).toReal =
        (∑ state, (distribution state).toReal) -
          ∑ state,
            (distribution state).toReal *
              (transition state target).toReal := by
      rw [sum_pmf_toReal_eq_one,
        Math.ProbabilityMassFunction.bind_apply_toReal_eq_sum]
    _ =
        ∑ state,
          ((distribution state).toReal -
            (distribution state).toReal *
              (transition state target).toReal) := by
      rw [Finset.sum_sub_distrib]
    _ =
        ∑ state,
          (distribution state).toReal *
            (1 - (transition state target).toReal) := by
      apply Finset.sum_congr rfl
      intro state _
      ring

/-- For a target-stopped kernel, a uniform one-block target minorization
amplifies geometrically across repeated blocks. -/
theorem stopped_iter_block_failure_le_pow
    [Finite S]
    (kernel : S → PMF S)
    (target source : S)
    (horizon blocks : ℕ)
    (minorization : ℝ)
    (hminorization_le_one : minorization ≤ 1)
    (honeBlock :
      ∀ state,
        minorization ≤
          (Math.PMFIter.iter
            (stoppedAt kernel target)
            horizon state target).toReal) :
    1 -
        (Math.PMFIter.iter
          (stoppedAt kernel target)
          (blocks * horizon) source target).toReal ≤
      (1 - minorization) ^ blocks := by
  classical
  letI : Fintype S := Fintype.ofFinite S
  induction blocks with
  | zero =>
      simp [Math.PMFIter.iter_zero]
  | succ blocks ih =>
      let stopped : S → PMF S := stoppedAt kernel target
      let before : PMF S :=
        Math.PMFIter.iter
          stopped (blocks * horizon) source
      let block : S → PMF S :=
        Math.PMFIter.iter stopped horizon
      have htargetBlock :
          block target = PMF.pure target := by
        exact Math.PMFIter.iter_of_terminal
          (stoppedAt_target kernel target) horizon
      have htargetFailure :
          1 - (block target target).toReal = 0 := by
        rw [htargetBlock]
        simp
      have hfailureErase :
          1 - ((before.bind block) target).toReal =
            ∑ state ∈ (Finset.univ.erase target),
              (before state).toReal *
                (1 - (block state target).toReal) := by
        rw [one_sub_bind_apply_toReal before block target]
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ target)]
        simp [htargetFailure]
      have hpointwise :
          ∀ state ∈ (Finset.univ.erase target),
            (before state).toReal *
                (1 - (block state target).toReal) ≤
              (1 - minorization) *
                (before state).toReal := by
        intro state _
        have hblock :
            minorization ≤
              (block state target).toReal :=
          honeBlock state
        have hfailure :
            1 - (block state target).toReal ≤
              1 - minorization := by
          linarith
        have hmass :
            0 ≤ (before state).toReal :=
          ENNReal.toReal_nonneg
        nlinarith
      have hbeforeErase :
          (∑ state ∈ (Finset.univ.erase target),
              (before state).toReal) =
            1 - (before target).toReal := by
        have hsum := sum_pmf_toReal_eq_one before
        rw [← Finset.sum_erase_add _ _
          (Finset.mem_univ target)] at hsum
        linarith
      have honeStep :
          1 - ((before.bind block) target).toReal ≤
            (1 - minorization) *
              (1 - (before target).toReal) := by
        rw [hfailureErase]
        calc
          (∑ state ∈ (Finset.univ.erase target),
              (before state).toReal *
                (1 - (block state target).toReal)) ≤
              ∑ state ∈ (Finset.univ.erase target),
                (1 - minorization) *
                  (before state).toReal :=
            Finset.sum_le_sum hpointwise
          _ =
              (1 - minorization) *
                (∑ state ∈ (Finset.univ.erase target),
                  (before state).toReal) := by
            rw [Finset.mul_sum]
          _ =
              (1 - minorization) *
                (1 - (before target).toReal) := by
            rw [hbeforeErase]
      have hnonneg : 0 ≤ 1 - minorization := by
        linarith
      have hrecurrence :
          1 -
              (Math.PMFIter.iter
                (stoppedAt kernel target)
                ((blocks + 1) * horizon)
                source target).toReal ≤
            (1 - minorization) *
              (1 -
                (Math.PMFIter.iter
                  (stoppedAt kernel target)
                  (blocks * horizon)
                  source target).toReal) := by
        rw [Nat.add_mul, one_mul, Math.PMFIter.iter_add]
        exact honeStep
      calc
        1 -
            (Math.PMFIter.iter
              (stoppedAt kernel target)
              ((blocks + 1) * horizon)
              source target).toReal ≤
            (1 - minorization) *
              (1 -
                (Math.PMFIter.iter
                  (stoppedAt kernel target)
                  (blocks * horizon)
                  source target).toReal) :=
          hrecurrence
        _ ≤ (1 - minorization) *
              (1 - minorization) ^ blocks :=
          mul_le_mul_of_nonneg_left ih hnonneg
        _ = (1 - minorization) ^ (blocks + 1) := by
          rw [pow_succ]
          ring

/-- Elementary exponential envelope for a geometric failure term. -/
theorem one_sub_pow_le_exp_neg_nat_mul
    (minorization : ℝ) (blocks : ℕ)
    (hminorization_le_one : minorization ≤ 1) :
    (1 - minorization) ^ blocks ≤
      Real.exp (-((blocks : ℝ) * minorization)) := by
  have hbase_nonneg : 0 ≤ 1 - minorization := by
    linarith
  have hpow :=
    pow_le_pow_left₀ hbase_nonneg
      (Real.one_sub_le_exp_neg minorization) blocks
  calc
    (1 - minorization) ^ blocks ≤
        Real.exp (-minorization) ^ blocks := hpow
    _ = Real.exp ((blocks : ℝ) * (-minorization)) := by
      rw [Real.exp_nat_mul]
    _ = Real.exp (-((blocks : ℝ) * minorization)) := by
      congr 1
      ring

open Math.OnlineLearning

/-- The universal logarithmic scale beats the reciprocal square-root
calendar cost at every fixed natural power. -/
theorem tendsto_sqrt_mul_universalEpochScale_pow_atTop
    (exponent : ℕ) :
    Tendsto
      (fun k : ℕ =>
        Real.sqrt (k + 1) *
          universalEpochScale k ^ exponent)
      atTop atTop := by
  let ratio : ℕ → ℝ :=
    fun k =>
      universalEpochScale k ^ (-(exponent : ℝ)) /
        Real.sqrt (k + 1)
  have hratioZero :
      Tendsto ratio atTop (𝓝 0) := by
    simpa [ratio] using
      tendsto_scale_neg_rpow_div_sqrt_succ
        (exponent : ℝ)
  have hratioPos :
      ∀ k, 0 < ratio k := by
    intro k
    exact div_pos
      (Real.rpow_pos_of_pos
        (universalEpochScale_pos k) _)
      (Real.sqrt_pos.2 (by positivity))
  have hratioWithin :
      Tendsto ratio atTop
        (nhdsWithin 0 (Set.Ioi 0)) := by
    exact tendsto_inf.2
      ⟨hratioZero,
        tendsto_principal.2
          (Filter.Eventually.of_forall hratioPos)⟩
  have hinverse :
      Tendsto (fun k => (ratio k)⁻¹)
        atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp hratioWithin
  convert hinverse using 1
  funext k
  rw [show ratio k =
      universalEpochScale k ^ (-(exponent : ℝ)) /
        Real.sqrt (k + 1) by rfl]
  rw [inv_div]
  rw [Real.rpow_neg
    (universalEpochScale_pos k).le]
  rw [Real.rpow_natCast]
  simp [div_eq_mul_inv]

/-- The quadratic epoch length supplies enough blocks to amplify any fixed
finite power of the universal logarithmic scale. -/
theorem tendsto_anytimeEpochLength_mul_scale_pow_atTop
    (constant : ℝ) (hconstant : 0 < constant)
    (exponent : ℕ) :
    Tendsto
      (fun k : ℕ =>
        (anytimeEpochLength k : ℝ) *
          (constant *
            universalEpochScale k ^ exponent))
      atTop atTop := by
  have hroot :
      Tendsto
        (fun k : ℕ =>
          constant *
            (Real.sqrt (k + 1) *
              universalEpochScale k ^ exponent))
        atTop atTop :=
    (tendsto_sqrt_mul_universalEpochScale_pow_atTop
      exponent).const_mul_atTop hconstant
  apply tendsto_atTop_mono' atTop
  · filter_upwards [] with k
    have hsqrt :
        Real.sqrt (k + 1) ≤ ((k : ℝ) + 1) ^ 2 := by
      apply (Real.sqrt_le_iff).2
      constructor
      · positivity
      · have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by
          exact_mod_cast
            Nat.succ_le_succ (Nat.zero_le k)
        nlinarith [sq_nonneg (((k : ℝ) + 1) ^ 2 - 1)]
    have hscale :
        0 ≤ universalEpochScale k ^ exponent := by
      exact pow_nonneg
        (universalEpochScale_pos k).le exponent
    have hmul :
        constant *
            (Real.sqrt (k + 1) *
              universalEpochScale k ^ exponent) ≤
          (((k : ℝ) + 1) ^ 2) *
            (constant *
              universalEpochScale k ^ exponent) := by
      calc
        constant *
            (Real.sqrt (k + 1) *
              universalEpochScale k ^ exponent) =
            Real.sqrt (k + 1) *
              (constant *
                universalEpochScale k ^ exponent) := by
          ring
        _ ≤ (((k : ℝ) + 1) ^ 2) *
              (constant *
                universalEpochScale k ^ exponent) :=
          mul_le_mul_of_nonneg_right hsqrt
            (mul_nonneg hconstant.le hscale)
    simpa [anytimeEpochLength] using hmul
  · exact hroot

/-- The exponential envelope generated by the quadratic universal calendar
tends to zero at every fixed finite analytic order. -/
theorem tendsto_exp_neg_anytimeEpochLength_mul_scale_pow
    (constant : ℝ) (hconstant : 0 < constant)
    (exponent : ℕ) :
    Tendsto
      (fun k : ℕ =>
        Real.exp
          (-((anytimeEpochLength k : ℝ) *
            (constant *
              universalEpochScale k ^ exponent))))
      atTop (𝓝 0) := by
  exact Real.tendsto_exp_atBot.comp
    (tendsto_neg_atTop_atBot.comp
      (tendsto_anytimeEpochLength_mul_scale_pow_atTop
        constant hconstant exponent))

/-- The geometric failure envelope on the universal quadratic calendar tends
to zero.  The upper-bound assumption is needed only eventually and is
automatic when the signal is bounded by an actual probability. -/
theorem tendsto_one_sub_scale_pow_anytimeEpochLength
    (constant : ℝ) (hconstant : 0 < constant)
    (exponent : ℕ)
    (hle :
      ∀ᶠ k : ℕ in atTop,
        constant * universalEpochScale k ^ exponent ≤ 1) :
    Tendsto
      (fun k : ℕ =>
        (1 -
          constant *
            universalEpochScale k ^ exponent) ^
          anytimeEpochLength k)
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards [hle] with k hk
    exact pow_nonneg (sub_nonneg.mpr hk) _
  · filter_upwards [hle] with k hk
    exact one_sub_pow_le_exp_neg_nat_mul
      (constant *
        universalEpochScale k ^ exponent)
      (anytimeEpochLength k) hk
  · exact
      tendsto_exp_neg_anytimeEpochLength_mul_scale_pow
        constant hconstant exponent

/-- Even only `k + 1` regeneration blocks amplify every fixed analytic
power along the universal logarithmic scale.  This smaller block count fits
inside the actual quadratic epoch once `k + 1` exceeds the fixed block
horizon. -/
theorem tendsto_one_sub_scale_pow_succ
    (constant : ℝ) (hconstant : 0 < constant)
    (exponent : ℕ)
    (hle :
      ∀ᶠ k : ℕ in atTop,
        constant * universalEpochScale k ^ exponent ≤ 1) :
    Tendsto
      (fun k : ℕ =>
        (1 -
          constant *
            universalEpochScale k ^ exponent) ^ (k + 1))
      atTop (𝓝 0) := by
  have hsqrt :
      Tendsto
        (fun k : ℕ =>
          constant *
            (Real.sqrt (k + 1) *
              universalEpochScale k ^ exponent))
        atTop atTop :=
    (tendsto_sqrt_mul_universalEpochScale_pow_atTop
      exponent).const_mul_atTop hconstant
  have hsucc :
      Tendsto
        (fun k : ℕ =>
          ((k + 1 : ℕ) : ℝ) *
            (constant *
              universalEpochScale k ^ exponent))
        atTop atTop := by
    apply tendsto_atTop_mono' atTop
    · filter_upwards [] with k
      have hk :
          (1 : ℝ) ≤ (k : ℝ) + 1 := by
        exact_mod_cast
          Nat.succ_le_succ (Nat.zero_le k)
      have hsqrt_le :
          Real.sqrt ((k : ℝ) + 1) ≤ (k : ℝ) + 1 := by
        apply (Real.sqrt_le_iff).2
        constructor
        · positivity
        · nlinarith
      have hscale :
          0 ≤ universalEpochScale k ^ exponent :=
        pow_nonneg (universalEpochScale_pos k).le exponent
      calc
        constant *
              (Real.sqrt (k + 1) *
                universalEpochScale k ^ exponent) =
            Real.sqrt (k + 1) *
              (constant *
                universalEpochScale k ^ exponent) := by
          ring
        _ ≤ ((k : ℝ) + 1) *
              (constant *
                universalEpochScale k ^ exponent) :=
          mul_le_mul_of_nonneg_right hsqrt_le
            (mul_nonneg hconstant.le hscale)
        _ =
            ((k + 1 : ℕ) : ℝ) *
              (constant *
                universalEpochScale k ^ exponent) := by
          norm_num
    · exact hsqrt
  have hexp :
      Tendsto
        (fun k : ℕ =>
          Real.exp
            (-(((k + 1 : ℕ) : ℝ) *
              (constant *
                universalEpochScale k ^ exponent))))
        atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp hsucc)
  apply squeeze_zero'
  · filter_upwards [hle] with k hk
    exact pow_nonneg (sub_nonneg.mpr hk) _
  · filter_upwards [hle] with k hk
    exact one_sub_pow_le_exp_neg_nat_mul
      (constant *
        universalEpochScale k ^ exponent)
      (k + 1) hk
  · exact hexp

/-- Calendar amplification of analytic finite-state regeneration.

The kernel used in epoch `k` is frozen at `universalEpochScale k` for all
`anytimeEpochLength k` blocks, each of length `horizon`.  The theorem only
asserts that the resulting target-hitting failure tends to zero. -/
theorem exists_calendar_amplified_analytic_regeneration
    [Finite S]
    (kernel : ℝ → S → PMF S)
    (target : S)
    (edge : S → S → Prop)
    (hanalytic :
      ∀ source destination,
        AnalyticAt ℝ
          (fun t =>
            (stoppedAt
              (kernel t) target source destination).toReal) 0)
    (hedge :
      ∀ {source destination},
        edge source destination →
          ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
            0 <
              (stoppedAt
                (kernel t) target source destination).toReal)
    (hreach :
      ∀ source,
        Relation.ReflTransGen edge source target) :
    ∃ (horizon exponent : ℕ) (constant : ℝ),
      0 < constant ∧
        (∀ᶠ k : ℕ in atTop, ∀ source,
          1 -
              (Math.PMFIter.iter
                (stoppedAt
                  (kernel
                    (universalEpochScale k))
                  target)
                (anytimeEpochLength k * horizon)
                source target).toReal ≤
            (1 -
              constant *
                universalEpochScale k ^ exponent) ^
              anytimeEpochLength k) ∧
        ∀ source,
          Tendsto
            (fun k : ℕ =>
              1 -
                (Math.PMFIter.iter
                  (stoppedAt
                    (kernel
                      (universalEpochScale k))
                    target)
                  (anytimeEpochLength k * horizon)
                  source target).toReal)
            atTop (𝓝 0) := by
  letI : Fintype S := Fintype.ofFinite S
  obtain
    ⟨horizon, exponent, constant,
      hconstant, honeBlock⟩ :=
    exists_analytic_finiteHittingMinorization
      kernel target edge hanalytic hedge hreach
  have hscaleWithin :
      Tendsto universalEpochScale atTop
        (nhdsWithin 0 (Set.Ioi 0)) := by
    exact tendsto_inf.2
      ⟨tendsto_universalEpochScale,
        tendsto_principal.2
          (Filter.Eventually.of_forall
            universalEpochScale_pos)⟩
  have honeBlockCalendar :
      ∀ᶠ k : ℕ in atTop, ∀ source,
        constant *
            universalEpochScale k ^ exponent ≤
          (Math.PMFIter.iter
            (stoppedAt
              (kernel
                (universalEpochScale k))
              target)
            horizon source target).toReal :=
    hscaleWithin.eventually honeBlock
  have hsignalLeOne :
      ∀ᶠ k : ℕ in atTop,
        constant *
          universalEpochScale k ^ exponent ≤ 1 := by
    filter_upwards [honeBlockCalendar] with k hk
    exact (hk target).trans
      (pmf_apply_toReal_le_one _ target)
  have hgeometric :
      Tendsto
        (fun k : ℕ =>
          (1 -
            constant *
              universalEpochScale k ^ exponent) ^
            anytimeEpochLength k)
        atTop (𝓝 0) :=
    tendsto_one_sub_scale_pow_anytimeEpochLength
      constant hconstant exponent hsignalLeOne
  have hfailureBound :
      ∀ᶠ k : ℕ in atTop, ∀ source,
        1 -
            (Math.PMFIter.iter
              (stoppedAt
                (kernel
                  (universalEpochScale k))
                target)
              (anytimeEpochLength k * horizon)
              source target).toReal ≤
          (1 -
            constant *
              universalEpochScale k ^ exponent) ^
            anytimeEpochLength k := by
    filter_upwards
      [honeBlockCalendar, hsignalLeOne] with k hk hkOne
    intro source
    exact stopped_iter_block_failure_le_pow
      (kernel (universalEpochScale k))
      target source horizon
      (anytimeEpochLength k)
      (constant *
        universalEpochScale k ^ exponent)
      hkOne hk
  refine
    ⟨horizon, exponent, constant,
      hconstant, hfailureBound, ?_⟩
  intro source
  apply squeeze_zero'
  · filter_upwards [] with k
    exact sub_nonneg.mpr
      (pmf_apply_toReal_le_one _ target)
  · filter_upwards [hfailureBound] with k hk
    exact hk source
  · exact hgeometric

/-- Calendar amplification within one actual quadratic epoch.

The earlier block theorem allocates `anytimeEpochLength k` blocks, each of
the fixed regeneration horizon.  Here only `k + 1` blocks are used.  They fit
inside the actual epoch of `anytimeEpochLength k = (k + 1)^2` stages for all
large `k`, and still drive the target-hitting failure to zero. -/
theorem exists_actualEpoch_amplified_analytic_regeneration
    [Finite S]
    (kernel : ℝ → S → PMF S)
    (target : S)
    (edge : S → S → Prop)
    (hanalytic :
      ∀ source destination,
        AnalyticAt ℝ
          (fun t =>
            (stoppedAt
              (kernel t) target source destination).toReal) 0)
    (hedge :
      ∀ {source destination},
        edge source destination →
          ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
            0 <
              (stoppedAt
                (kernel t) target source destination).toReal)
    (hreach :
      ∀ source,
        Relation.ReflTransGen edge source target) :
    ∃ (exponent : ℕ) (constant : ℝ),
      0 < constant ∧
        (∀ᶠ k : ℕ in atTop, ∀ source,
          1 -
              (Math.PMFIter.iter
                (stoppedAt
                  (kernel
                    (universalEpochScale k))
                  target)
                (anytimeEpochLength k)
                source target).toReal ≤
            (1 -
              constant *
                universalEpochScale k ^ exponent) ^ (k + 1)) ∧
        ∀ source,
          Tendsto
            (fun k : ℕ =>
              1 -
                (Math.PMFIter.iter
                  (stoppedAt
                    (kernel
                      (universalEpochScale k))
                    target)
                  (anytimeEpochLength k)
                  source target).toReal)
            atTop (𝓝 0) := by
  letI : Fintype S := Fintype.ofFinite S
  obtain
    ⟨horizon, exponent, constant,
      hconstant, honeBlock⟩ :=
    exists_analytic_finiteHittingMinorization
      kernel target edge hanalytic hedge hreach
  have hscaleWithin :
      Tendsto universalEpochScale atTop
        (nhdsWithin 0 (Set.Ioi 0)) := by
    exact tendsto_inf.2
      ⟨tendsto_universalEpochScale,
        tendsto_principal.2
          (Filter.Eventually.of_forall
            universalEpochScale_pos)⟩
  have honeBlockCalendar :
      ∀ᶠ k : ℕ in atTop, ∀ source,
        constant *
            universalEpochScale k ^ exponent ≤
          (Math.PMFIter.iter
            (stoppedAt
              (kernel
                (universalEpochScale k))
              target)
            horizon source target).toReal :=
    hscaleWithin.eventually honeBlock
  have hsignalLeOne :
      ∀ᶠ k : ℕ in atTop,
        constant *
          universalEpochScale k ^ exponent ≤ 1 := by
    filter_upwards [honeBlockCalendar] with k hk
    exact (hk target).trans
      (pmf_apply_toReal_le_one _ target)
  have hgeometric :
      Tendsto
        (fun k : ℕ =>
          (1 -
            constant *
              universalEpochScale k ^ exponent) ^ (k + 1))
        atTop (𝓝 0) :=
    tendsto_one_sub_scale_pow_succ
      constant hconstant exponent hsignalLeOne
  have hfailureBound :
      ∀ᶠ k : ℕ in atTop, ∀ source,
        1 -
            (Math.PMFIter.iter
              (stoppedAt
                (kernel
                  (universalEpochScale k))
                target)
              (anytimeEpochLength k)
              source target).toReal ≤
          (1 -
            constant *
              universalEpochScale k ^ exponent) ^ (k + 1) := by
    filter_upwards
      [honeBlockCalendar, hsignalLeOne,
        eventually_ge_atTop horizon] with k hk hkOne hkH
    intro source
    have hshort :=
      stopped_iter_block_failure_le_pow
        (kernel (universalEpochScale k))
        target source horizon (k + 1)
        (constant *
          universalEpochScale k ^ exponent)
        hkOne hk
    have hsteps :
        (k + 1) * horizon ≤ anytimeEpochLength k := by
      rw [anytimeEpochLength, pow_two]
      exact Nat.mul_le_mul_left (k + 1)
        (hkH.trans (Nat.le_succ k))
    have hmass :=
      iter_stoppedAt_target_toReal_le_add
        (kernel (universalEpochScale k))
        target source ((k + 1) * horizon)
        (anytimeEpochLength k - (k + 1) * horizon)
    rw [Nat.add_sub_of_le hsteps] at hmass
    exact (sub_le_sub_left hmass 1).trans hshort
  refine
    ⟨exponent, constant,
      hconstant, hfailureBound, ?_⟩
  intro source
  apply squeeze_zero'
  · filter_upwards [] with k
    exact sub_nonneg.mpr
      (pmf_apply_toReal_le_one _ target)
  · filter_upwards [hfailureBound] with k hk
    exact hk source
  · exact hgeometric

end Probability
end Math
