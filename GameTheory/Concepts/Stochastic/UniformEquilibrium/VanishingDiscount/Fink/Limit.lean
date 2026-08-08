/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Fink.Schedule
import Math.MeanErgodic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Vanishing-Discount Compactness for Fink Fixed Points

Fink's fixed points all live in one compact strategy/value domain when stage
payoffs share a common bound.  This file extracts convergent subsequences from
arbitrary families of discounted fixed points, in particular along the
canonical discount sequence `n / (n + 1) → 1`.

This is the compactness input to a vanishing-discount selection argument.  It
does not assert the unresolved stabilization or excessive-function property
needed to turn a cluster point into a general multiplayer uniform equilibrium.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Filter
open Math.Probability Math.PMFProduct
open Math.ProbabilityMassFunction

variable {ι : Type}

/-- A nonnegative error cannot be summable if it remains at least a positive
multiple of the reciprocal calendar time.  The formulation below derives
that comparison from a positive product lower bound and a scale negligible
relative to calendar time. -/
theorem not_summable_of_eventually_pos_le_mul_of_inv_mul_tendsto_zero
    (a e : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (he0 : ∀ n, 0 ≤ e n)
    (hlower : ∀ᶠ n in atTop, c ≤ a n * e n)
    (hscale : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * a n)
      atTop (nhds 0)) :
    ¬ Summable e := by
  intro he
  have hscaleOne : ∀ᶠ n : ℕ in atTop, (n : ℝ)⁻¹ * a n < 1 := by
    have hclose := hscale.eventually (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)
    filter_upwards [hclose] with n hn
    rw [Real.dist_eq, sub_zero, abs_lt] at hn
    exact hn.2
  have hcompare : ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ)⁻¹ ≤ e n := by
    filter_upwards [hlower, hscaleOne, eventually_gt_atTop 0] with n hn hsmall hnpos
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hane : a n ≤ n := by
      have hlt : a n < (n : ℝ) := by
        simpa only [mul_one] using (inv_mul_lt_iff₀ hnreal).mp hsmall
      exact hlt.le
    have hmul : a n * e n ≤ (n : ℝ) * e n :=
      mul_le_mul_of_nonneg_right hane (he0 n)
    have hdiv : c / (n : ℝ) ≤ e n :=
      (div_le_iff₀ hnreal).2 (by
        simpa only [mul_comm] using hn.trans hmul)
    simpa only [div_eq_mul_inv] using hdiv
  have hharmonic : Summable (fun n : ℕ => c * (n : ℝ)⁻¹) := by
    apply Summable.of_norm_bounded_eventually_nat he
    filter_upwards [hcompare] with n hn
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg hc.le (inv_nonneg.mpr (Nat.cast_nonneg n)))]
    exact hn
  have honeDiv : Summable (fun n : ℕ => (n : ℝ)⁻¹) := by
    have hscaled := hharmonic.mul_left c⁻¹
    simpa only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] using hscaled
  exact Real.not_summable_natCast_inv honeDiv

/-- For nonnegative errors, a bounded normalized sum of cumulative prefix
errors already forces summability of the original errors.  Thus the nested
drift bill used by calendar verification is not weaker than summable drift. -/
theorem summable_of_eventually_normalized_cumulative_sum_le
    (e : ℕ → ℝ) (he0 : ∀ n, 0 ≤ e n) (C : ℝ)
    (hbound : ∀ᶠ T : ℕ in atTop,
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
        ∑ k ∈ Finset.range t, e k ≤ C) :
    Summable e := by
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.1 hbound
  apply summable_of_sum_range_le (c := 2 * C) he0
  intro N
  let T := max T₀ (2 * N + 2)
  have hT₀T : T₀ ≤ T := le_max_left _ _
  have htwo : 2 * N + 2 ≤ T := le_max_right _ _
  have hNT : N ≤ T := by omega
  have hTpos : 0 < T := by omega
  let P : ℝ := ∑ k ∈ Finset.range N, e k
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun k hk => he0 k
  have hinner : ∀ t ∈ Finset.Ico N T, P ≤
      ∑ k ∈ Finset.range t, e k := by
    intro t ht
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (Finset.mem_Ico.mp ht).1)
    intro k hk hnot
    exact he0 k
  have hIcoSubset : Finset.Ico N T ⊆ Finset.range T := by
    intro t ht
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp ht).2
  have houter : ((T - N : ℕ) : ℝ) * P ≤
      ∑ t ∈ Finset.range T, ∑ k ∈ Finset.range t, e k := by
    calc
      ((T - N : ℕ) : ℝ) * P = ∑ _t ∈ Finset.Ico N T, P := by
        simp [Nat.card_Ico, hNT]
      _ ≤ ∑ t ∈ Finset.Ico N T, ∑ k ∈ Finset.range t, e k :=
        Finset.sum_le_sum hinner
      _ ≤ ∑ t ∈ Finset.range T, ∑ k ∈ Finset.range t, e k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hIcoSubset
        intro t ht hnot
        exact Finset.sum_nonneg fun k hk => he0 k
  have hbill := hT₀ T hT₀T
  have hweighted : (T : ℝ)⁻¹ * (((T - N : ℕ) : ℝ) * P) ≤ C :=
    (mul_le_mul_of_nonneg_left houter
      (inv_nonneg.mpr (Nat.cast_nonneg T))).trans hbill
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hTpos
  have hratio : (1 / 2 : ℝ) ≤ ((T - N : ℕ) : ℝ) / T := by
    apply (le_div_iff₀ hTreal).2
    rw [Nat.cast_sub hNT]
    have hcast : (2 : ℝ) * N ≤ T := by exact_mod_cast (by omega : 2 * N ≤ T)
    linarith
  have hhalf : (1 / 2 : ℝ) * P ≤ C := by
    calc
      (1 / 2 : ℝ) * P ≤
          (((T - N : ℕ) : ℝ) / T) * P :=
        mul_le_mul_of_nonneg_right hratio hP0
      _ = (T : ℝ)⁻¹ * (((T - N : ℕ) : ℝ) * P) := by
        rw [div_eq_mul_inv]
        ring
      _ ≤ C := hweighted
  dsimp only [P] at hhalf ⊢
  linarith

/-- The canonical increasing sequence of discount factors approaching one. -/
def approachOneDiscount (n : ℕ) : ℝ := (n : ℝ) / (n + 1)

theorem approachOneDiscount_nonneg (n : ℕ) : 0 ≤ approachOneDiscount n := by
  exact div_nonneg (Nat.cast_nonneg n) (by positivity)

theorem approachOneDiscount_lt_one (n : ℕ) : approachOneDiscount n < 1 := by
  rw [approachOneDiscount, div_lt_one (by positivity)]
  exact_mod_cast Nat.lt_succ_self n

theorem approachOneDiscount_le_one (n : ℕ) : approachOneDiscount n ≤ 1 :=
  (approachOneDiscount_lt_one n).le

theorem tendsto_approachOneDiscount :
    Tendsto approachOneDiscount atTop (nhds 1) := by
  have hzero := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hrepr : approachOneDiscount =
      fun n : ℕ => 1 - 1 / ((n : ℝ) + 1) := by
    funext n
    rw [approachOneDiscount]
    field_simp
    ring
  rw [hrepr]
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  simpa using hone.sub hzero

/-- Any bounded family of Fink fixed points indexed by discount factors has
a convergent subsequence in the common compact strategy/value domain. -/
theorem exists_convergent_finkFixedPoint_subsequence
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] [∀ i, Nonempty (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ) (hU : 0 ≤ U)
    (hβ0 : ∀ n, 0 ≤ β n) (hβ1 : ∀ n, β n ≤ 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U) :
    ∃ (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U) (φ : ℕ → ℕ),
      (∀ n, G.finkMap (β n) U (hβ0 n) (hβ1 n) hpay (z n) = z n) ∧
        StrictMono φ ∧ Tendsto (z ∘ φ) atTop (nhds zlim) := by
  have hex : ∀ n, ∃ z : G.finkDomain U,
      G.finkMap (β n) U (hβ0 n) (hβ1 n) hpay z = z :=
    fun n => G.exists_finkMap_fixedPoint (β n) U hU (hβ0 n) (hβ1 n) hpay
  choose z hz using hex
  letI : CompactSpace (G.finkDomain U) :=
    isCompact_iff_compactSpace.mp (G.isCompact_finkDomain U)
  obtain ⟨zlim, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq z
  exact ⟨z, zlim, φ, hz, hφ, hlim⟩

/-- Canonical vanishing-discount specialization of compact Fink fixed-point
selection. -/
theorem exists_convergent_approachOne_finkFixedPoint_subsequence
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] [∀ i, Nonempty (G.Act i)]
    (U : ℝ) (hU : 0 ≤ U)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U) :
    ∃ (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U) (φ : ℕ → ℕ),
      (∀ n, G.finkMap (approachOneDiscount n) U
          (approachOneDiscount_nonneg n) (approachOneDiscount_le_one n)
          hpay (z n) = z n) ∧
        StrictMono φ ∧ Tendsto (z ∘ φ) atTop (nhds zlim) ∧
          Tendsto (approachOneDiscount ∘ φ) atTop (nhds 1) := by
  obtain ⟨z, zlim, φ, hz, hφ, hlim⟩ :=
    G.exists_convergent_finkFixedPoint_subsequence
      approachOneDiscount U hU approachOneDiscount_nonneg
        approachOneDiscount_le_one hpay
  refine ⟨z, zlim, φ, hz, hφ, hlim, ?_⟩
  exact tendsto_approachOneDiscount.comp hφ.tendsto_atTop

/-- Convergence in Fink's compact domain gives coordinatewise convergence of
the continuation values. -/
theorem tendsto_finkValue_apply
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim)) (s : G.State) (who : ι) :
    Tendsto (fun n => G.finkValue (z n) s who) atTop
      (nhds (G.finkValue zlim s who)) := by
  have hc : Continuous (fun q : G.finkDomain U => q.1.2 s who) := by
    fun_prop
  simpa only [finkValue, Function.comp_def] using (hc.tendsto zlim).comp hz

/-- Convergence in Fink's compact domain gives convergence of the entire
finite-dimensional continuation-value vector. -/
theorem tendsto_finkValue
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim)) :
    Tendsto (fun n => G.finkValue (z n)) atTop
      (nhds (G.finkValue zlim)) := by
  apply tendsto_pi_nhds.2
  intro s
  apply tendsto_pi_nhds.2
  intro who
  exact G.tendsto_finkValue_apply hz s who

/-- The real mixed-action weights converge coordinatewise as well. -/
theorem tendsto_finkStrategyWeight_apply
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim)) (s : G.State) (who : ι)
    (d : G.Act who) :
    Tendsto (fun n => z n |>.1.1 (s, who) d) atTop
      (nhds (zlim.1.1 (s, who) d)) := by
  have hc : Continuous (fun q : G.finkDomain U => q.1.1 (s, who) d) := by
    fun_prop
  exact (hc.tendsto zlim).comp hz

/-- Hence the decoded stationary mixed actions converge pointwise as PMFs. -/
theorem finkProfile_convergesPointwise
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim)) (s : G.State) (who : ι) :
    PMFConvergesPointwise (fun n => G.finkProfile (z n) s who)
      (G.finkProfile zlim s who) := by
  intro d
  have hw := G.tendsto_finkStrategyWeight_apply hz s who d
  have hof := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hw
  change Tendsto (fun n => ENNReal.ofReal (z n |>.1.1 (s, who) d)) atTop
    (nhds (ENNReal.ofReal (zlim.1.1 (s, who) d)))
  simpa only [Function.comp_def] using hof

/-- Against a fixed continuation function, the expected successor value of
the decoded stationary profiles converges along the Fink-domain sequence. -/
theorem tendsto_finkProfile_continuation
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim)) (W : G.State → ℝ)
    (s : G.State) :
    Tendsto (fun n => expect (pmfPi (G.finkProfile (z n) s)) (fun a =>
        expect (G.transition s a) W)) atTop
      (nhds (expect (pmfPi (G.finkProfile zlim s)) (fun a =>
        expect (G.transition s a) W))) := by
  classical
  have hsum : Tendsto (fun n => ∑ a : G.JointAct,
      ((pmfPi (G.finkProfile (z n) s)) a).toReal *
        expect (G.transition s a) W) atTop
      (nhds (∑ a : G.JointAct,
        ((pmfPi (G.finkProfile zlim s)) a).toReal *
          expect (G.transition s a) W)) := by
    apply tendsto_finsetSum Finset.univ
    intro a ha
    have hw := pmfPi_apply_toReal_tendsto
      (σs := fun n => G.finkProfile (z n) s)
      (σ := G.finkProfile zlim s) a
      (fun i => G.finkProfile_convergesPointwise hz s i (a i))
    exact hw.mul tendsto_const_nhds
  simpa only [expect_eq_sum] using hsum

/-- The same continuation expectation converges after fixing one player's
action to a pure deviation. -/
theorem tendsto_finkProfile_pureDeviationContinuation
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim)) (W : G.State → ℝ)
    (s : G.State) (who : ι) (d : G.Act who) :
    Tendsto (fun n =>
        expect (pmfPi (Function.update (G.finkProfile (z n) s)
          who (PMF.pure d))) (fun a => expect (G.transition s a) W)) atTop
      (nhds (expect (pmfPi (Function.update (G.finkProfile zlim s)
        who (PMF.pure d))) (fun a => expect (G.transition s a) W))) := by
  have hsum : Tendsto (fun n => ∑ a : G.JointAct,
      ((pmfPi (Function.update (G.finkProfile (z n) s)
        who (PMF.pure d))) a).toReal * expect (G.transition s a) W) atTop
      (nhds (∑ a : G.JointAct,
        ((pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) a).toReal * expect (G.transition s a) W)) := by
    apply tendsto_finsetSum Finset.univ
    intro a ha
    have hmarg : ∀ i, Tendsto (fun n =>
        (Function.update (G.finkProfile (z n) s) who (PMF.pure d)) i (a i))
        atTop (nhds
          ((Function.update (G.finkProfile zlim s) who (PMF.pure d)) i
            (a i))) := by
      intro i
      by_cases hi : i = who
      · subst i
        simp
      · simp only [Function.update_of_ne hi]
        exact G.finkProfile_convergesPointwise hz s i (a i)
    have hw := pmfPi_apply_toReal_tendsto
      (σs := fun n => Function.update (G.finkProfile (z n) s)
        who (PMF.pure d))
      (σ := Function.update (G.finkProfile zlim s) who (PMF.pure d))
      a hmarg
    exact hw.mul tendsto_const_nhds
  simpa only [expect_eq_sum] using hsum

/-- Jointly convergent continuation vectors and Fink-domain points have
convergent continuation gains.  The proof runs through the finite polynomial
coordinate presentation, avoiding any topological claims about `ENNReal`. -/
theorem tendsto_finkContinuationGain_of_tendsto
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {H : ℕ → G.State → Payoff ι} {Hlim : G.State → Payoff ι}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hH : Tendsto H atTop (nhds Hlim)) (hz : Tendsto z atTop (nhds zlim))
    (s : G.State) (who : ι) (d : G.Act who) :
    Tendsto (fun n => G.finkContinuationGain (H n) (z n) s who d) atTop
      (nhds (G.finkContinuationGain Hlim zlim s who d)) := by
  have hpair : Tendsto (fun n => (H n, z n)) atTop (nhds (Hlim, zlim)) := by
    simpa only [nhds_prod_eq] using hH.prodMk hz
  have ht :=
    ((G.continuous_finkContinuationCoordGain_param (U := U) s who d).tendsto
      (Hlim, zlim)).comp hpair
  simpa only [Function.comp_def, G.finkContinuationCoordGain_eq] using ht

/-- One-stage gains converge along a convergent Fink-domain sequence. -/
theorem tendsto_finkStageGain
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    (s : G.State) (who : ι) (d : G.Act who) :
    Tendsto (fun n => G.finkStageGain (z n) s who d) atTop
      (nhds (G.finkStageGain zlim s who d)) := by
  have ht := ((G.continuous_finkGain (U := U) 0 s who d).tendsto zlim).comp hz
  simpa only [G.finkGain_zero_eq_finkStageGain, Function.comp_def] using ht

/-- Every state/player coordinate is bounded by the finite-product sup norm. -/
theorem abs_finkBiasCoordinate_le_norm
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    (H : G.State → Payoff ι) (s : G.State) (who : ι) :
    |H s who| ≤ ‖H‖ := by
  have hplayer : ‖H s who‖ ≤ ‖H s‖ := norm_le_pi_norm (H s) who
  have hstate : ‖H s‖ ≤ ‖H‖ := norm_le_pi_norm H s
  simpa only [Real.norm_eq_abs] using hplayer.trans hstate

/-- All on-profile continuation residuals of a target vector. -/
def finkContinuationResidualVector (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (W : G.State → Payoff ι) {U : ℝ}
    (z : G.finkDomain U) : G.State → Payoff ι :=
  fun s who => G.finkContinuationResidual W z s who

/-- A state-constant payoff vector has exactly its current coordinate as
continuation value under every decoded Fink profile. -/
theorem finkContinuationEU_eq_of_stateConstant
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (W : G.State → Payoff ι)
    (hconstant : ∀ who s t, W s who = W t who)
    {U : ℝ} (z : G.finkDomain U) (s : G.State) (who : ι) :
    G.finkContinuationEU W z s who = W s who := by
  have hfun : (fun t => W t who) = fun _ => W s who := by
    funext t
    exact (hconstant who s t).symm
  unfold finkContinuationEU
  rw [hfun]
  simp

/-- State-constant payoff vectors have zero on-profile continuation
residual, uniformly over the Fink domain. -/
theorem finkContinuationResidualVector_eq_zero_of_stateConstant
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (W : G.State → Payoff ι)
    (hconstant : ∀ who s t, W s who = W t who)
    {U : ℝ} (z : G.finkDomain U) :
    G.finkContinuationResidualVector W z = 0 := by
  ext s who
  unfold finkContinuationResidualVector finkContinuationResidual
  rw [G.finkContinuationEU_eq_of_stateConstant W hconstant]
  simp

/-- State-constant payoff vectors also have zero continuation gain for every
pure deviation, uniformly over the Fink domain. -/
theorem finkContinuationGain_eq_zero_of_stateConstant
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (W : G.State → Payoff ι)
    (hconstant : ∀ who s t, W s who = W t who)
    {U : ℝ} (z : G.finkDomain U) (s : G.State) (who : ι)
    (d : G.Act who) :
    G.finkContinuationGain W z s who d = 0 := by
  have hfun : (fun t => W t who) = fun _ => W s who := by
    funext t
    exact (hconstant who s t).symm
  unfold finkContinuationGain
  rw [hfun]
  simp

/-- State transition kernel induced by one decoded stationary Fink profile. -/
def finkStateKernel (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : G.finkDomain U) (s : G.State) : PMF G.State :=
  (pmfPi (G.finkProfile z s)).bind (G.transition s)

/-- State transition kernel induced by replacing one player's component of a
decoded stationary Fink profile by a pure action. -/
def finkPureDeviationStateKernel (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : G.finkDomain U) (s : G.State)
    (who : ι) (d : G.Act who) : PMF G.State :=
  (pmfPi (Function.update (G.finkProfile z s)
    who (PMF.pure d))).bind (G.transition s)

/-- Expectations under the induced state kernel are exactly the nested
action/transition expectations used by `finkContinuationEU`. -/
theorem expect_finkStateKernel_eq
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : G.finkDomain U) (s : G.State) (w : G.State → ℝ) :
    expect (G.finkStateKernel z s) w =
      expect (pmfPi (G.finkProfile z s)) (fun a =>
        expect (G.transition s a) w) := by
  unfold finkStateKernel
  rw [expect_bind]

/-- Expectations under a pure unilateral-deviation state kernel are exactly
the corresponding nested action/transition expectations. -/
theorem expect_finkPureDeviationStateKernel_eq
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : G.finkDomain U) (s : G.State)
    (who : ι) (d : G.Act who) (w : G.State → ℝ) :
    expect (G.finkPureDeviationStateKernel z s who d) w =
      expect (pmfPi (Function.update (G.finkProfile z s)
        who (PMF.pure d))) (fun a =>
          expect (G.transition s a) w) := by
  unfold finkPureDeviationStateKernel
  rw [expect_bind]

/-- A Fink continuation gain is the difference between expectations under the
pure-deviation and baseline state kernels. -/
theorem finkContinuationGain_eq_expect_stateKernels
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (W : G.State → Payoff ι) {U : ℝ} (z : G.finkDomain U)
    (s : G.State) (who : ι) (d : G.Act who) :
    G.finkContinuationGain W z s who d =
      expect (G.finkPureDeviationStateKernel z s who d) (fun t => W t who) -
        expect (G.finkStateKernel z s) (fun t => W t who) := by
  rw [G.expect_finkPureDeviationStateKernel_eq,
    G.expect_finkStateKernel_eq]
  rfl

/-- If a pure unilateral deviation leaves the state kernel unchanged, then it
has zero continuation gain against every state-payoff vector. -/
theorem finkContinuationGain_eq_zero_of_pureDeviationStateKernel_eq
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (W : G.State → Payoff ι) {U : ℝ} (z : G.finkDomain U)
    (s : G.State) (who : ι) (d : G.Act who)
    (hkernel :
      G.finkPureDeviationStateKernel z s who d =
        G.finkStateKernel z s) :
    G.finkContinuationGain W z s who d = 0 := by
  rw [G.finkContinuationGain_eq_expect_stateKernels, hkernel, sub_self]

/-- Every Fink forcing splits into a harmonic recurrent obstruction and a
Poisson-solvable transient part.  The obstruction is exactly the vector of
Cesàro limits under the induced stationary state kernel. -/
theorem exists_finkHarmonicObstruction_add_continuationResidual
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : G.finkDomain U) (F : G.State → Payoff ι) :
    ∃ O K : G.State → Payoff ι,
      G.finkContinuationResidualVector O z = 0 ∧
      F = O + G.finkContinuationResidualVector K z ∧
      ∀ who, Tendsto (fun T : ℕ =>
        (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T,
          ((Math.MeanErgodic.markovOperator (G.finkStateKernel z)) ^ t)
            (fun s => F s who)) atTop (nhds (fun s => O s who)) := by
  have hplayer : ∀ who, ∃ o k : G.State → ℝ,
      (∀ s, expect (G.finkStateKernel z s) o = o s) ∧
      (∀ s, F s who = o s +
        (expect (G.finkStateKernel z s) k - k s)) ∧
      Tendsto (fun T : ℕ =>
        (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T,
          ((Math.MeanErgodic.markovOperator (G.finkStateKernel z)) ^ t)
            (fun s => F s who)) atTop (nhds o) := by
    intro who
    exact Math.MeanErgodic.exists_harmonic_add_poisson
      (G.finkStateKernel z) (fun s => F s who)
  choose o k ho hdecomp hlim using hplayer
  let O : G.State → Payoff ι := fun s who => o who s
  let K : G.State → Payoff ι := fun s who => k who s
  refine ⟨O, K, ?_, ?_, ?_⟩
  · ext s who
    unfold finkContinuationResidualVector finkContinuationResidual
      finkContinuationEU
    rw [← G.expect_finkStateKernel_eq z s (o who)]
    exact sub_eq_zero.mpr (ho who s)
  · ext s who
    unfold finkContinuationResidualVector finkContinuationResidual
      finkContinuationEU
    change F s who = o who s +
      ((expect (pmfPi (G.finkProfile z s)) fun a =>
        expect (G.transition s a) (k who)) - k who s)
    rw [← G.expect_finkStateKernel_eq z s (k who)]
    exact hdecomp who s
  · intro who
    simpa only [O] using hlim who

/-- Vector forcing represented by an on-profile average-reward Bellman
equation with value `V` and bias `J`. -/
def finkBellmanForcingVector (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (V J : G.State → Payoff ι) {U : ℝ}
    (z : G.finkDomain U) : G.State → Payoff ι :=
  fun s who => V s who + J s who - G.finkStageEU z s who -
    G.finkContinuationEU J z s who

/-- The limiting Bellman forcing has a canonical mean-ergodic split into a
harmonic obstruction and a Poisson-solvable continuation residual. -/
theorem exists_finkBellmanForcing_harmonicObstruction_decomposition
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : G.finkDomain U) (W H : G.State → Payoff ι) :
    ∃ O K : G.State → Payoff ι,
      G.finkContinuationResidualVector O z = 0 ∧
      G.finkBellmanForcingVector W H z =
        O + G.finkContinuationResidualVector K z ∧
      ∀ who, Tendsto (fun T : ℕ =>
        (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T,
          ((Math.MeanErgodic.markovOperator (G.finkStateKernel z)) ^ t)
            (fun s => G.finkBellmanForcingVector W H z s who))
          atTop (nhds (fun s => O s who)) :=
  G.exists_finkHarmonicObstruction_add_continuationResidual z
    (G.finkBellmanForcingVector W H z)

/-- At an interior bias scale, the rescaled Bellman remainder has a finite
limit determined by the limiting value, bias, and stationary profile. -/
theorem tendsto_smul_finkBellmanForcingVector
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    {V J E : ℕ → G.State → Payoff ι}
    {Vlim Jlim : G.State → Payoff ι}
    (hV : Tendsto V atTop (nhds Vlim))
    (hJ : Tendsto J atTop (nhds Jlim)) (a : ℕ → ℝ)
    (hbellman : ∀ n s who, V n s who + J n s who =
      G.finkStageEU (z n) s who +
        G.finkContinuationEU (J n) (z n) s who +
        a n * E n s who) :
    Tendsto (fun n => a n • E n) atTop
      (nhds (G.finkBellmanForcingVector Vlim Jlim zlim)) := by
  apply tendsto_pi_nhds.2
  intro s
  apply tendsto_pi_nhds.2
  intro who
  have hVcoord : Tendsto (fun n => V n s who) atTop
      (nhds (Vlim s who)) := by
    have hc : Continuous (fun H : G.State → Payoff ι => H s who) := by
      fun_prop
    exact (hc.tendsto Vlim).comp hV
  have hJcoord : Tendsto (fun n => J n s who) atTop
      (nhds (Jlim s who)) := by
    have hc : Continuous (fun H : G.State → Payoff ι => H s who) := by
      fun_prop
    exact (hc.tendsto Jlim).comp hJ
  have hstage :=
    ((G.continuous_finkStageEU (U := U) s who).tendsto zlim).comp hz
  have hpair : Tendsto (fun n => (J n, z n)) atTop
      (nhds (Jlim, zlim)) := by
    simpa only [nhds_prod_eq] using hJ.prodMk hz
  have hcontinuation :=
    ((G.continuous_finkContinuationEU_param (U := U) s who).tendsto
      (Jlim, zlim)).comp hpair
  have hforcing := ((hVcoord.add hJcoord).sub hstage).sub hcontinuation
  have hforcing' : Tendsto (fun n => a n * E n s who) atTop
      (nhds (G.finkBellmanForcingVector Vlim Jlim zlim s who)) := by
    apply hforcing.congr'
    exact Filter.Eventually.of_forall fun n => by
      simp only [Function.comp_apply]
      linarith [hbellman n s who]
  simpa only [Pi.smul_apply, smul_eq_mul] using hforcing'

/-- Continuation residuals respect addition. -/
theorem finkContinuationResidualVector_add
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (R K : G.State → Payoff ι) {U : ℝ} (z : G.finkDomain U) :
    G.finkContinuationResidualVector (R + K) z =
      G.finkContinuationResidualVector R z +
        G.finkContinuationResidualVector K z := by
  ext s who
  simp only [finkContinuationResidualVector, finkContinuationResidual,
    Pi.add_apply]
  rw [G.finkContinuationEU_add]
  ring

/-- Continuation residuals respect scalar multiplication. -/
theorem finkContinuationResidualVector_smul
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (c : ℝ) (R : G.State → Payoff ι) {U : ℝ} (z : G.finkDomain U) :
    G.finkContinuationResidualVector (c • R) z =
      c • G.finkContinuationResidualVector R z := by
  ext s who
  simp only [finkContinuationResidualVector, finkContinuationResidual,
    Pi.smul_apply, smul_eq_mul]
  rw [G.finkContinuationEU_smul]
  ring

/-- Continuation residuals respect negation. -/
theorem finkContinuationResidualVector_neg
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (R : G.State → Payoff ι) {U : ℝ} (z : G.finkDomain U) :
    G.finkContinuationResidualVector (-R) z =
      -G.finkContinuationResidualVector R z := by
  have hneg : -R = (-1 : ℝ) • R := by
    ext s who
    simp
  rw [hneg, G.finkContinuationResidualVector_smul]
  simp

/-- A unilateral mixed continuation value is the deviating player's
expectation of the corresponding pure-action continuation values. -/
theorem mixedDeviationContinuation_eq_expect_pure
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (x : G.StationaryMixedProfile) (W : G.State → Payoff ι)
    (s : G.State) (who : ι) (dev : PMF (G.Act who)) :
    expect (pmfPi (Function.update (x s) who dev))
        (fun a => expect (G.transition s a) (fun s' => W s' who)) =
      expect dev (fun d =>
        expect (pmfPi (Function.update (x s) who (PMF.pure d)))
          (fun a => expect (G.transition s a) (fun s' => W s' who))) := by
  rw [pmfPi_update_bind, expect_bind]

/-- If a finite-distribution expectation reaches a common pointwise upper
bound, every positive-probability point reaches that bound. -/
theorem eq_of_expect_eq_of_forall_le_of_ne_zero
    {α : Type} [Finite α] (μ : PMF α) (f : α → ℝ) (c : ℝ)
    (hexpect : expect μ f = c) (hle : ∀ a, f a ≤ c)
    {a : α} (ha : μ a ≠ 0) : f a = c := by
  apply le_antisymm (hle a)
  by_contra hnot
  have hlt : f a < c := lt_of_not_ge hnot
  have hstrict := expect_lt_const_of_le_of_exists_lt μ f hle ⟨a, ha, hlt⟩
  linarith

/-- Finite maximum principle for a strictly positive induced Fink state
kernel: every harmonic payoff coordinate is constant across states.  This is
the one-step-positive (hence irreducible) structural closure of the
state-constant interior branch. -/
theorem stateConstant_of_finkStateKernel_positive_of_harmonic
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (W : G.State → Payoff ι)
    (hpositive : ∀ s t, G.finkStateKernel z s t ≠ 0)
    (hharmonic : ∀ s who,
      W s who = expect (pmfPi (G.finkProfile z s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who))) :
    ∀ who s t, W s who = W t who := by
  intro who s t
  obtain ⟨m, _, hm⟩ := Finset.exists_max_image Finset.univ
    (fun r => W r who) ⟨s, Finset.mem_univ s⟩
  have hmean : expect (G.finkStateKernel z m) (fun r => W r who) =
      W m who := by
    rw [G.expect_finkStateKernel_eq]
    exact (hharmonic m who).symm
  have hall (r : G.State) : W r who = W m who :=
    eq_of_expect_eq_of_forall_le_of_ne_zero
      (G.finkStateKernel z m) (fun q => W q who) (W m who)
        hmean (fun q => hm q (Finset.mem_univ q)) (hpositive m r)
  exact (hall s).trans (hall t).symm

/-- Quantitative support pruning for a finite distribution.  If one point is
`δ` below a reference level, every point is at most `r` above it, and the
mean is at most `r` below it, then that point's mass times `δ` is at most
`2r`. -/
theorem pmf_apply_toReal_mul_gap_le_two_error
    {α : Type} [Finite α]
    (μ : PMF α) (f : α → ℝ) (c δ r : ℝ) (hr : 0 ≤ r)
    (hmean : c - r ≤ expect μ f)
    (hupper : ∀ b, f b ≤ c + r) {a : α} (ha : f a ≤ c - δ) :
    (μ a).toReal * δ ≤ 2 * r := by
  classical
  let g : α → ℝ := fun b =>
    c + r - if b = a then δ + r else 0
  have hfg : ∀ b, f b ≤ g b := by
    intro b
    by_cases hba : b = a
    · subst b
      dsimp [g]
      simp only [if_true]
      linarith
    · dsimp [g]
      simp only [if_false, hba, sub_zero]
      exact hupper b
  have hE : expect μ f ≤ expect μ g := expect_mono μ f g hfg
  have hindicator :
      expect μ (fun b => if b = a then δ + r else 0) =
        (μ a).toReal * (δ + r) := by
    letI : Fintype α := Fintype.ofFinite α
    rw [expect_eq_sum]
    simp
  have hg : expect μ g = c + r - (μ a).toReal * (δ + r) := by
    unfold g
    rw [expect_sub, expect_const, hindicator]
  rw [hg] at hE
  have hp0 : 0 ≤ (μ a).toReal := ENNReal.toReal_nonneg
  nlinarith [mul_nonneg hp0 hr, hmean.trans hE]

/-- A positive real family indexed by a finite predicate has a uniform
positive lower bound.  The predicate may be empty. -/
theorem exists_pos_le_of_finite
    {α : Type} [Finite α] (P : α → Prop) (f : α → ℝ)
    (hpos : ∀ a, P a → 0 < f a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a, P a → δ ≤ f a := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  let S : Finset ℝ := (Finset.univ.filter P).image f
  by_cases hS : S.Nonempty
  · let δ := S.min' hS
    have hδmem : δ ∈ S := Finset.min'_mem S hS
    obtain ⟨a, ha, hfa⟩ := Finset.mem_image.mp hδmem
    have haP : P a := (Finset.mem_filter.mp ha).2
    refine ⟨δ, ?_, ?_⟩
    · simpa [hfa] using hpos a haP
    · intro b hb
      exact Finset.min'_le S (f b)
        (Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb⟩, rfl⟩)
  · refine ⟨1, by norm_num, ?_⟩
    intro a ha
    exfalso
    exact hS ⟨f a,
      Finset.mem_image.mpr
        ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩, rfl⟩⟩

/-- A common upper bound for all pure unilateral continuation deviations is
also an upper bound for every mixed unilateral deviation. -/
theorem mixedDeviationContinuation_le_of_pure_bound
    (G : StochasticGame ι) [Finite G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Finite (G.Act i)] (x : G.StationaryMixedProfile)
    (W : G.State → Payoff ι) (s : G.State) (who : ι) (c : ℝ)
    (hpure : ∀ d : G.Act who,
      expect (pmfPi (Function.update (x s) who (PMF.pure d)))
          (fun a => expect (G.transition s a) (fun s' => W s' who)) ≤ c)
    (dev : PMF (G.Act who)) :
    expect (pmfPi (Function.update (x s) who dev))
        (fun a => expect (G.transition s a) (fun s' => W s' who)) ≤ c := by
  rw [G.mixedDeviationContinuation_eq_expect_pure x W s who dev]
  calc
    expect dev (fun d =>
        expect (pmfPi (Function.update (x s) who (PMF.pure d)))
          (fun a => expect (G.transition s a) (fun s' => W s' who))) ≤
        expect dev (fun _ => c) := expect_mono dev _ _ hpure
    _ = c := expect_const dev c

/-- A strictly continuation-losing action can receive substantial probability
only when the profile's harmonic/excessive errors are substantial. -/
theorem strictContinuation_probability_mul_gap_le
    (G : StochasticGame ι) [Finite G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Finite (G.Act i)]
    (x : G.StationaryMixedProfile) (W : G.State → Payoff ι)
    (s : G.State) (who : ι) (d : G.Act who) (δ r : ℝ) (hr : 0 ≤ r)
    (hharmonic :
      W s who - r ≤ expect (pmfPi (x s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)))
    (hexcessive : ∀ d' : G.Act who,
      expect (pmfPi (Function.update (x s) who (PMF.pure d'))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who + r)
    (hstrict :
      expect (pmfPi (Function.update (x s) who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who - δ) :
    ((x s who) d).toReal * δ ≤ 2 * r := by
  classical
  let f : G.Act who → ℝ := fun d' =>
    expect (pmfPi (Function.update (x s) who (PMF.pure d'))) (fun a =>
      expect (G.transition s a) (fun s' => W s' who))
  have hdecomp := G.mixedDeviationContinuation_eq_expect_pure
    x W s who (x s who)
  simp only [Function.update_eq_self] at hdecomp
  apply pmf_apply_toReal_mul_gap_le_two_error
    (x s who) f (W s who) δ r hr
  · rw [← hdecomp]
    exact hharmonic
  · exact hexcessive
  · exact hstrict

/-- Finiteness upgrades all strict continuation losses of a stationary
profile to one common positive gap, simultaneously over states, players, and
actions. -/
theorem exists_uniform_strictContinuationGap
    (G : StochasticGame ι) [Finite G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Finite (G.Act i)]
    (x : G.StationaryMixedProfile) (W : G.State → Payoff ι) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (x s) who (PMF.pure d))) (fun a =>
          expect (G.transition s a) (fun s' => W s' who)) < W s who →
        expect (pmfPi (Function.update (x s) who (PMF.pure d))) (fun a =>
          expect (G.transition s a) (fun s' => W s' who)) ≤ W s who - δ := by
  let D := Σ p : G.FinkAgent, G.FinkAction p
  let P : D → Prop := fun q =>
    expect (pmfPi (Function.update (x q.1.1) q.1.2 (PMF.pure q.2))) (fun a =>
      expect (G.transition q.1.1 a) (fun s' => W s' q.1.2)) <
        W q.1.1 q.1.2
  let f : D → ℝ := fun q =>
    W q.1.1 q.1.2 -
      expect (pmfPi (Function.update (x q.1.1) q.1.2 (PMF.pure q.2))) (fun a =>
        expect (G.transition q.1.1 a) (fun s' => W s' q.1.2))
  have hpos : ∀ q, P q → 0 < f q := by
    intro q hq
    dsimp [P, f] at hq ⊢
    linarith
  obtain ⟨δ, hδ, hlower⟩ := exists_pos_le_of_finite P f hpos
  refine ⟨δ, hδ, ?_⟩
  intro s who d hstrict
  have hgap := hlower ⟨(s, who), d⟩ hstrict
  dsimp [f] at hgap
  linarith

/-- Pure actions that strictly lower a player's target continuation value
against a reference stationary profile. -/
def strictContinuationActions
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (xref : G.StationaryMixedProfile) (W : G.State → Payoff ι)
    (s : G.State) (who : ι) : Finset (G.Act who) :=
  Finset.univ.filter fun d =>
    expect (pmfPi (Function.update (xref s) who (PMF.pure d))) (fun a =>
      expect (G.transition s a) (fun s' => W s' who)) < W s who

/-- Outside the strict-loss set, excessiveness makes a reference action
exactly continuation-neutral.  Therefore coordinatewise approximation of its
continuation value is approximation to the target itself. -/
theorem abs_pureDeviationContinuation_sub_target_le_of_not_mem_strict
    (G : StochasticGame ι) [Finite G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (xref x : G.StationaryMixedProfile) (W : G.State → Payoff ι)
    (s : G.State) (who : ι) (d : G.Act who) (r : ℝ)
    (hexcessive :
      expect (pmfPi (Function.update (xref s) who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who)
    (hclose :
      |expect (pmfPi (Function.update (x s) who (PMF.pure d))) (fun a =>
          expect (G.transition s a) (fun s' => W s' who)) -
        expect (pmfPi (Function.update (xref s) who (PMF.pure d))) (fun a =>
          expect (G.transition s a) (fun s' => W s' who))| ≤ r)
    (hneutral : d ∉ G.strictContinuationActions xref W s who) :
    |expect (pmfPi (Function.update (x s) who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) - W s who| ≤ r := by
  have hnlt : ¬ expect (pmfPi (Function.update (xref s) who (PMF.pure d)))
      (fun a => expect (G.transition s a) (fun s' => W s' who)) < W s who := by
    simpa [strictContinuationActions] using hneutral
  have heq : expect (pmfPi (Function.update (xref s) who (PMF.pure d)))
      (fun a => expect (G.transition s a) (fun s' => W s' who)) = W s who :=
    le_antisymm hexcessive (le_of_not_gt hnlt)
  simpa only [heq] using hclose

/-- Every action used with positive probability by a harmonic/excessive
limit profile is continuation-neutral: it preserves the limiting value
against the other players' limiting mixed actions. -/
theorem finkLimit_support_continuation_eq
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (W : G.State → Payoff ι) (s : G.State) (who : ι) (d : G.Act who)
    (hharmonic : W s who =
      expect (pmfPi (G.finkProfile z s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)))
    (hexcessive : ∀ d' : G.Act who,
      expect (pmfPi (Function.update (G.finkProfile z s)
          who (PMF.pure d'))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who)
    (hpos : G.finkProfile z s who d ≠ 0) :
    expect (pmfPi (Function.update (G.finkProfile z s)
        who (PMF.pure d))) (fun a =>
      expect (G.transition s a) (fun s' => W s' who)) = W s who := by
  have hdecomp := G.mixedDeviationContinuation_eq_expect_pure
    (G.finkProfile z) W s who (G.finkProfile z s who)
  simp only [Function.update_eq_self] at hdecomp
  have hexpect : expect (G.finkProfile z s who) (fun d' =>
      expect (pmfPi (Function.update (G.finkProfile z s)
        who (PMF.pure d'))) (fun a =>
          expect (G.transition s a) (fun s' => W s' who))) = W s who :=
    hdecomp.symm.trans hharmonic.symm
  exact eq_of_expect_eq_of_forall_le_of_ne_zero
    (G.finkProfile z s who) _ (W s who) hexpect hexcessive hpos

/-- A stationary profile is continuation-neutral on its support for `W` if
every positively played pure action preserves that player's expected next
state value against the other players' mixed actions. -/
def IsContinuationNeutralOnSupport (G : StochasticGame ι) [Fintype ι]
    [DecidableEq ι]
    (x : G.StationaryMixedProfile) (W : G.State → Payoff ι) : Prop :=
  ∀ s who (d : G.Act who), x s who d ≠ 0 →
    expect (pmfPi (Function.update (x s) who (PMF.pure d))) (fun a =>
      expect (G.transition s a) (fun s' => W s' who)) = W s who

/-- Harmonicity on path and excessiveness against pure deviations imply
continuation-neutrality on the profile's support. -/
theorem isContinuationNeutralOnSupport_of_harmonic_excessive
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (W : G.State → Payoff ι)
    (hharmonic : ∀ s who, W s who =
      expect (pmfPi (G.finkProfile z s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)))
    (hexcessive : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile z s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who) :
    G.IsContinuationNeutralOnSupport (G.finkProfile z) W := by
  intro s who d hpos
  exact G.finkLimit_support_continuation_eq z W s who d
    (hharmonic s who) (hexcessive s who) hpos

/-- An action in the support of a limiting profile is eventually in the
support of every convergent discounted fixed-point profile.  Consequently
its centered higher-order gain equation holds exactly along the tail. -/
theorem eventually_finkCenteredGain_eq_zero_of_limit_support
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {β : ℕ → ℝ} {U : ℝ}
    (hβ0 : ∀ n, 0 ≤ β n) (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (W : G.State → Payoff ι) (s : G.State) (who : ι)
    (d : G.Act who) (hpos : G.finkProfile zlim s who d ≠ 0) :
    ∀ᶠ n in atTop,
      G.finkStageGain (z n) s who d +
          (β n / (1 - β n)) * G.finkContinuationGain W (z n) s who d +
            G.finkContinuationGain
              (G.finkRelativeBias (β n) W (z n)) (z n) s who d = 0 := by
  have hlimitPos : 0 < zlim.1.1 (s, who) d := by
    rw [← G.finkProfile_apply_toReal zlim s who d]
    exact ENNReal.toReal_pos hpos (PMF.apply_ne_top _ _)
  have ht := G.tendsto_finkStrategyWeight_apply hz s who d
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht
    (zlim.1.1 (s, who) d) hlimitPos
  filter_upwards [Filter.eventually_atTop.2 ⟨N, hN⟩] with n hn
  have hnpos : G.finkProfile (z n) s who d ≠ 0 := by
    intro hnzero
    have hweightZero : z n |>.1.1 (s, who) d = 0 := by
      rw [← G.finkProfile_apply_toReal (z n) s who d, hnzero]
      simp
    rw [Real.dist_eq, hweightZero, zero_sub, abs_neg,
      abs_of_pos hlimitPos] at hn
    exact (lt_irrefl _ hn)
  exact G.finkCenteredGain_eq_zero_of_finkMap_fixedPoint_of_ne_zero
    (β n) U (hβ0 n) (hβ1 n) hpay (z n) (hfix n) W s who d hnpos

/-- In the finite relative-bias branch, the apparently singular target
continuation residual has a finite limit on every limiting supported action.
Its limit is forced by the next-order centered gain equation. -/
theorem tendsto_scaled_finkContinuationGain_of_limit_support
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {β : ℕ → ℝ} {U : ℝ}
    (hβ0 : ∀ n, 0 ≤ β n) (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (W H : G.State → Payoff ι)
    (hH : Tendsto (fun n => G.finkRelativeBias (β n) W (z n))
      atTop (nhds H))
    (s : G.State) (who : ι) (d : G.Act who)
    (hpos : G.finkProfile zlim s who d ≠ 0) :
    Tendsto (fun n => (β n / (1 - β n)) *
        G.finkContinuationGain W (z n) s who d) atTop
      (nhds (-(G.finkStageGain zlim s who d +
        G.finkContinuationGain H zlim s who d))) := by
  have hstage := G.tendsto_finkStageGain hz s who d
  have hbias := G.tendsto_finkContinuationGain_of_tendsto hH hz s who d
  have hneg := (hstage.add hbias).neg
  apply hneg.congr'
  filter_upwards [G.eventually_finkCenteredGain_eq_zero_of_limit_support
    hβ0 hβ1 hpay hz hfix W s who d hpos] with n hn
  linarith

/-- The finite vector space of pure-action coordinates, indexed by state,
player, and that player's action. -/
abbrev FinkPureActionVector (G : StochasticGame ι) :=
  G.State → ∀ who : ι, G.Act who → ℝ

/-- A single coordinate of the finite pure-action vector. -/
abbrev FinkPureActionIndex (G : StochasticGame ι) :=
  G.State × (Σ who : ι, G.Act who)

/-- Codomain of the finite supported tangent system: its first component is
the on-profile harmonicity equation and its second component records the
supported pure-action continuation equations. -/
abbrev FinkSupportTangentEquationVector (G : StochasticGame ι) :=
  (G.State → Payoff ι) × G.FinkPureActionVector

/-- Linear operator of the finite supported tangent system.  Off-support
action coordinates are masked to zero; the first component forces the
adjustment to be harmonic for the limiting on-profile state kernel. -/
noncomputable def finkSupportTangentOperator
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U) :
    (G.State → Payoff ι) →ₗ[ℝ] G.FinkSupportTangentEquationVector :=
  { toFun := fun A =>
      (G.finkContinuationResidualVector A z, fun s who d =>
        if G.finkProfile z s who d ≠ 0 then
          G.finkContinuationGain A z s who d else 0)
    map_add' := by
      intro A B
      apply Prod.ext
      · exact G.finkContinuationResidualVector_add A B z
      · funext s who d
        change (if G.finkProfile z s who d ≠ 0 then
            G.finkContinuationGain (A + B) z s who d else 0) =
          (if G.finkProfile z s who d ≠ 0 then
            G.finkContinuationGain A z s who d else 0) +
          (if G.finkProfile z s who d ≠ 0 then
            G.finkContinuationGain B z s who d else 0)
        by_cases hd : G.finkProfile z s who d ≠ 0
        · rw [if_pos hd, if_pos hd, if_pos hd]
          exact G.finkContinuationGain_add A B z s who d
        · rw [if_neg hd, if_neg hd, if_neg hd, add_zero]
    map_smul' := by
      intro c A
      apply Prod.ext
      · exact G.finkContinuationResidualVector_smul c A z
      · funext s who d
        change (if G.finkProfile z s who d ≠ 0 then
            G.finkContinuationGain (c • A) z s who d else 0) =
          c * (if G.finkProfile z s who d ≠ 0 then
            G.finkContinuationGain A z s who d else 0)
        by_cases hd : G.finkProfile z s who d ≠ 0
        · rw [if_pos hd, if_pos hd]
          exact G.finkContinuationGain_smul c A z s who d
        · rw [if_neg hd, if_neg hd, mul_zero] }

/-- Right-hand side of the finite supported tangent system. -/
noncomputable def finkSupportTangentTarget
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι) :
    G.FinkSupportTangentEquationVector :=
  (0, fun s who d =>
    if G.finkProfile z s who d ≠ 0 then
      G.finkStageGain z s who d +
        G.finkContinuationGain (H - K) z s who d else 0)

/-- Solving the operator equation is exactly choosing a harmonic adjustment
that matches every supported tangent gain. -/
theorem finkSupportTangentOperator_eq_target_iff
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (H K A : G.State → Payoff ι) :
    G.finkSupportTangentOperator z A =
        G.finkSupportTangentTarget z H K ↔
      G.finkContinuationResidualVector A z = 0 ∧
        ∀ s who (d : G.Act who), G.finkProfile z s who d ≠ 0 →
          G.finkContinuationGain A z s who d =
            G.finkStageGain z s who d +
              G.finkContinuationGain (H - K) z s who d := by
  constructor
  · intro heq
    have hfirst := congrArg Prod.fst heq
    change G.finkContinuationResidualVector A z = 0 at hfirst
    refine ⟨hfirst, ?_⟩
    intro s who d hd
    have hcoord := congrFun (congrFun (congrFun
      (congrArg Prod.snd heq) s) who) d
    change (if G.finkProfile z s who d ≠ 0 then
          G.finkContinuationGain A z s who d else 0) =
        (if G.finkProfile z s who d ≠ 0 then
          G.finkStageGain z s who d +
            G.finkContinuationGain (H - K) z s who d else 0) at hcoord
    rwa [if_pos hd, if_pos hd] at hcoord
  · rintro ⟨hharmonic, htangent⟩
    apply Prod.ext
    · change G.finkContinuationResidualVector A z = 0
      exact hharmonic
    · funext s who d
      by_cases hd : G.finkProfile z s who d ≠ 0
      · change (if G.finkProfile z s who d ≠ 0 then
              G.finkContinuationGain A z s who d else 0) =
            (if G.finkProfile z s who d ≠ 0 then
              G.finkStageGain z s who d +
                G.finkContinuationGain (H - K) z s who d else 0)
        rw [if_pos hd, if_pos hd]
        exact htangent s who d hd
      · change (if G.finkProfile z s who d ≠ 0 then
            G.finkContinuationGain A z s who d else 0) =
          (if G.finkProfile z s who d ≠ 0 then
            G.finkStageGain z s who d +
              G.finkContinuationGain (H - K) z s who d else 0)
        rw [if_neg hd, if_neg hd]

/-- Fredholm/Farkas form of supported tangent feasibility.  A harmonic
adjustment exists exactly when every linear functional annihilating the
tangent operator's range also annihilates the required supported target. -/
theorem exists_finkSupportHarmonicAdjustment_iff_forall_dual
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι) :
    (∃ A : G.State → Payoff ι,
      G.finkContinuationResidualVector A z = 0 ∧
        ∀ s who (d : G.Act who), G.finkProfile z s who d ≠ 0 →
          G.finkContinuationGain A z s who d =
            G.finkStageGain z s who d +
              G.finkContinuationGain (H - K) z s who d) ↔
    ∀ ℓ : Module.Dual ℝ G.FinkSupportTangentEquationVector,
      (∀ A : G.State → Payoff ι,
        ℓ (G.finkSupportTangentOperator z A) = 0) →
      ℓ (G.finkSupportTangentTarget z H K) = 0 := by
  constructor
  · rintro ⟨A, hA⟩ ℓ hℓ
    rw [← (G.finkSupportTangentOperator_eq_target_iff z H K A).2 hA]
    exact hℓ A
  · intro hdual
    have hmem : G.finkSupportTangentTarget z H K ∈
        LinearMap.range (G.finkSupportTangentOperator z) := by
      apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff
        (LinearMap.range (G.finkSupportTangentOperator z))
          (G.finkSupportTangentTarget z H K)).mp
      intro ℓ hℓ
      apply hdual ℓ
      intro A
      exact (Submodule.mem_dualAnnihilator ℓ).mp hℓ
        (G.finkSupportTangentOperator z A) ⟨A, rfl⟩
    obtain ⟨A, hA⟩ := hmem
    exact ⟨A, (G.finkSupportTangentOperator_eq_target_iff z H K A).1 hA⟩

/-- Uniform finite-action pruning: one positive gap controls every strict
limiting continuation deviation, simultaneously over all states and players. -/
theorem eventually_all_strictDeviation_probability_mul_le
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim)) (W : G.State → Payoff ι)
    (r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n)
    (hharmonic : ∀ n s who,
      W s who - r n ≤ expect (pmfPi (G.finkProfile (z n) s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)))
    (hexcessive : ∀ n s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile (z n) s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who + r n) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop, ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) < W s who →
      ((G.finkProfile (z n) s who) d).toReal * δ ≤ 2 * r n := by
  obtain ⟨Δ, hΔ, hgap⟩ :=
    G.exists_uniform_strictContinuationGap (G.finkProfile zlim) W
  let δ := Δ / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hmargin : ∀ᶠ n in atTop, ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) < W s who →
      expect (pmfPi (Function.update (G.finkProfile (z n) s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who - δ := by
    rw [Filter.eventually_all]
    intro s
    rw [Filter.eventually_all]
    intro who
    rw [Filter.eventually_all]
    intro d
    by_cases hstrict : expect (pmfPi (Function.update (G.finkProfile zlim s)
        who (PMF.pure d))) (fun a =>
          expect (G.transition s a) (fun s' => W s' who)) < W s who
    · have ht := G.tendsto_finkProfile_pureDeviationContinuation hz
        (fun s' => W s' who) s who d
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht δ hδ
      filter_upwards [Filter.eventually_atTop.2 ⟨N, hN⟩] with n hn
      intro _
      have hlimit := hgap s who d hstrict
      rw [Real.dist_eq, abs_lt] at hn
      dsimp [δ] at hn ⊢
      linarith
    · exact Filter.Eventually.of_forall fun _ h => (hstrict h).elim
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hmargin] with n hn
  intro s who d hstrict
  exact G.strictContinuation_probability_mul_gap_le
    (G.finkProfile (z n)) W s who d δ (r n) (hr n)
      (hharmonic n s who) (hexcessive n s who) (hn s who d hstrict)

/-- Harmonicity and pure-action excessiveness of a limiting profile become
uniform approximate drift bounds along every convergent finite-state/action
Fink-domain sequence. -/
theorem eventually_finkProfile_harmonic_excessive_close
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim)) (W : G.State → Payoff ι)
    (hharmonic : ∀ s who,
      W s who = expect (pmfPi (G.finkProfile zlim s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)))
    (hexcessive : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in atTop,
      (∀ s who,
        |expect (pmfPi (G.finkProfile (z n) s)) (fun a =>
            expect (G.transition s a) (fun s' => W s' who)) - W s who| ≤ η) ∧
      ∀ s who (dev : PMF (G.Act who)),
        expect (pmfPi (Function.update (G.finkProfile (z n) s) who dev)) (fun a =>
          expect (G.transition s a) (fun s' => W s' who)) ≤ W s who + η := by
  have hon : ∀ᶠ n in atTop, ∀ s who,
      |expect (pmfPi (G.finkProfile (z n) s)) (fun a =>
          expect (G.transition s a) (fun s' => W s' who)) - W s who| ≤ η := by
    rw [Filter.eventually_all]
    intro s
    rw [Filter.eventually_all]
    intro who
    have ht := G.tendsto_finkProfile_continuation hz
      (fun s' => W s' who) s
    rw [← hharmonic s who] at ht
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht η hη
    filter_upwards [Filter.eventually_atTop.2 ⟨N, hN⟩] with n hn
    simpa only [Real.dist_eq] using (le_of_lt hn)
  have hdev : ∀ᶠ n in atTop, ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile (z n) s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who + η := by
    rw [Filter.eventually_all]
    intro s
    rw [Filter.eventually_all]
    intro who
    rw [Filter.eventually_all]
    intro d
    have ht := G.tendsto_finkProfile_pureDeviationContinuation hz
      (fun s' => W s' who) s who d
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht η hη
    filter_upwards [Filter.eventually_atTop.2 ⟨N, hN⟩] with n hn
    rw [Real.dist_eq, abs_lt] at hn
    linarith [hexcessive s who d]
  filter_upwards [hon, hdev] with n hn hd
  refine ⟨hn, fun s who dev => ?_⟩
  exact G.mixedDeviationContinuation_le_of_pure_bound
    (G.finkProfile (z n)) W s who (W s who + η) (hd s who) dev

/-- Coordinatewise convergence in the finite Fink value cube is eventually
uniform over states and players. -/
theorem eventually_finkValue_close
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim)) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in atTop, ∀ s who,
      |G.finkValue (z n) s who - G.finkValue zlim s who| ≤ η := by
  rw [Filter.eventually_all]
  intro s
  rw [Filter.eventually_all]
  intro who
  have ht := G.tendsto_finkValue_apply hz s who
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht η hη
  filter_upwards [Filter.eventually_atTop.2 ⟨N, hN⟩] with n hn
  simpa only [Real.dist_eq] using (le_of_lt hn)

/-- Pure-deviation continuation values converge uniformly over the finite
state-player-action coordinates. -/
theorem eventually_finkPureDeviationContinuation_close
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim)) (W : G.State → Payoff ι)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in atTop, ∀ s who (d : G.Act who),
      |expect (pmfPi (Function.update (G.finkProfile (z n) s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) -
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who))| ≤ η := by
  rw [Filter.eventually_all]
  intro s
  rw [Filter.eventually_all]
  intro who
  rw [Filter.eventually_all]
  intro d
  have ht := G.tendsto_finkProfile_pureDeviationContinuation hz
    (fun s' => W s' who) s who d
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht η hη
  filter_upwards [Filter.eventually_atTop.2 ⟨N, hN⟩] with n hn
  simpa only [Real.dist_eq] using (le_of_lt hn)

/-- A further subsequence can be chosen so value convergence and all
harmonic/excessive transition residuals are bounded explicitly by
`1 / (n + 1)`.  This leaves scaled-bias growth as the only uncontrolled rate. -/
theorem exists_strictMono_finkApproximation_subsequence
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    (hharmonic : ∀ s who,
      G.finkValue zlim s who =
        expect (pmfPi (G.finkProfile zlim s)) (fun a =>
          expect (G.transition s a) (fun s' => G.finkValue zlim s' who)))
    (hexcessive : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => G.finkValue zlim s' who)) ≤
          G.finkValue zlim s who) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ n,
      (∀ s who,
        |G.finkValue (z (ψ n)) s who - G.finkValue zlim s who| ≤
          (((n + 1 : ℕ) : ℝ))⁻¹) ∧
      (∀ s who,
        |expect (pmfPi (G.finkProfile (z (ψ n)) s)) (fun a =>
            expect (G.transition s a) (fun s' => G.finkValue zlim s' who)) -
          G.finkValue zlim s who| ≤ (((n + 1 : ℕ) : ℝ))⁻¹) ∧
      (∀ s who (d : G.Act who),
        |expect (pmfPi (Function.update (G.finkProfile (z (ψ n)) s)
            who (PMF.pure d))) (fun a =>
          expect (G.transition s a) (fun s' => G.finkValue zlim s' who)) -
        expect (pmfPi (Function.update (G.finkProfile zlim s)
            who (PMF.pure d))) (fun a =>
          expect (G.transition s a) (fun s' => G.finkValue zlim s' who))| ≤
            (((n + 1 : ℕ) : ℝ))⁻¹) ∧
      ∀ s who (dev : PMF (G.Act who)),
        expect (pmfPi (Function.update (G.finkProfile (z (ψ n)) s) who dev))
            (fun a => expect (G.transition s a)
              (fun s' => G.finkValue zlim s' who)) ≤
          G.finkValue zlim s who + (((n + 1 : ℕ) : ℝ))⁻¹ := by
  let P : ℕ → ℕ → Prop := fun n k =>
    (∀ s who,
      |G.finkValue (z k) s who - G.finkValue zlim s who| ≤
        (((n + 1 : ℕ) : ℝ))⁻¹) ∧
    (∀ s who,
      |expect (pmfPi (G.finkProfile (z k) s)) (fun a =>
          expect (G.transition s a) (fun s' => G.finkValue zlim s' who)) -
        G.finkValue zlim s who| ≤ (((n + 1 : ℕ) : ℝ))⁻¹) ∧
    (∀ s who (d : G.Act who),
      |expect (pmfPi (Function.update (G.finkProfile (z k) s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => G.finkValue zlim s' who)) -
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => G.finkValue zlim s' who))| ≤
          (((n + 1 : ℕ) : ℝ))⁻¹) ∧
    ∀ s who (dev : PMF (G.Act who)),
      expect (pmfPi (Function.update (G.finkProfile (z k) s) who dev))
          (fun a => expect (G.transition s a)
            (fun s' => G.finkValue zlim s' who)) ≤
        G.finkValue zlim s who + (((n + 1 : ℕ) : ℝ))⁻¹
  have hev : ∀ n, ∀ᶠ k in atTop, P n k := by
    intro n
    have hη : 0 < (((n + 1 : ℕ) : ℝ))⁻¹ := by positivity
    have hv := G.eventually_finkValue_close hz hη
    have hd := G.eventually_finkProfile_harmonic_excessive_close hz
      (G.finkValue zlim) hharmonic hexcessive hη
    have hpure := G.eventually_finkPureDeviationContinuation_close hz
      (G.finkValue zlim) hη
    filter_upwards [hv, hd, hpure] with k hk hdk hpk
    exact ⟨hk, hdk.1, hpk, hdk.2⟩
  have hexN : ∀ n, ∃ N, ∀ k, N ≤ k → P n k := by
    intro n
    exact Filter.eventually_atTop.mp (hev n)
  choose N hN using hexN
  let ψ : ℕ → ℕ := fun n => Nat.rec (N 0)
    (fun k previous => max (N (k + 1)) (previous + 1)) n
  have hNle : ∀ n, N n ≤ ψ n := by
    intro n
    induction n with
    | zero => simp [ψ]
    | succ n ih =>
        rw [show ψ (n + 1) = max (N (n + 1)) (ψ n + 1) by simp [ψ]]
        exact le_max_left _ _
  have hstep : ∀ n, ψ n < ψ (n + 1) := by
    intro n
    rw [show ψ (n + 1) = max (N (n + 1)) (ψ n + 1) by simp [ψ]]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  refine ⟨ψ, strictMono_nat_of_lt_succ hstep, ?_⟩
  intro n
  exact hN n (ψ n) (hNle n)

/-- Auxiliary pure payoffs are jointly continuous in the discount factor and
the Fink-domain point. -/
theorem continuous_finkDiscountedAuxPayoff_param
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    (s : G.State) (a : G.JointAct) (who : ι) :
    Continuous (fun q : ℝ × G.finkDomain U =>
      G.discountedAuxPayoff q.1 (G.finkValue q.2) s a who) := by
  unfold discountedAuxPayoff finkValue
  simp_rw [expect_eq_sum]
  fun_prop

/-- Baseline auxiliary expected payoff is jointly continuous in the discount
factor and Fink coordinates. -/
theorem continuous_finkAuxEU_param
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (s : G.State) (who : ι) :
    Continuous (fun q : ℝ × G.finkDomain U =>
      G.finkAuxEU q.1 q.2 s who) := by
  unfold finkAuxEU
  refine continuous_finsetSum (s := (Finset.univ : Finset G.JointAct)) ?_
  intro a ha
  have hw : Continuous (fun q : ℝ × G.finkDomain U =>
      ∏ i, q.2.1.1 (s, i) (a i)) := by
    fun_prop
  exact hw.mul (G.continuous_finkDiscountedAuxPayoff_param s a who)

/-- Pure-deviation auxiliary expected payoff is jointly continuous in the
discount factor and Fink coordinates. -/
theorem continuous_finkDeviationAuxEU_param
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    (s : G.State) (who : ι) (d : G.Act who) :
    Continuous (fun q : ℝ × G.finkDomain U =>
      G.finkDeviationAuxEU q.1 q.2 s who d) := by
  unfold finkDeviationAuxEU
  refine continuous_finsetSum (s := (Finset.univ : Finset G.JointAct)) ?_
  intro a ha
  have hw : Continuous (fun q : ℝ × G.finkDomain U =>
      (((PMF.pure d) (a who)).toReal) *
        (∏ i ∈ (Finset.univ.erase who), q.2.1.1 (s, i) (a i))) := by
    fun_prop
  exact hw.mul (G.continuous_finkDiscountedAuxPayoff_param s a who)

/-- The auxiliary expected payoff tends to its value at every parameter
point.  This pointwise form keeps later filter compositions lightweight. -/
theorem tendsto_finkAuxEU_param
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    (q : ℝ × G.finkDomain U) (s : G.State) (who : ι) :
    Tendsto (fun p : ℝ × G.finkDomain U =>
      G.finkAuxEU p.1 p.2 s who) (nhds q)
      (nhds (G.finkAuxEU q.1 q.2 s who)) :=
  (G.continuous_finkAuxEU_param (U := U) s who).tendsto q

/-- The pure-deviation auxiliary payoff tends to its value at every
parameter point. -/
theorem tendsto_finkDeviationAuxEU_param
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    (q : ℝ × G.finkDomain U) (s : G.State) (who : ι) (d : G.Act who) :
    Tendsto (fun p : ℝ × G.finkDomain U =>
      G.finkDeviationAuxEU p.1 p.2 s who d) (nhds q)
      (nhds (G.finkDeviationAuxEU q.1 q.2 s who d)) :=
  (G.continuous_finkDeviationAuxEU_param (U := U) s who d).tendsto q

/-- Joint convergence of the discount and domain point transports through
the auxiliary expected payoff. -/
theorem tendsto_finkAuxEU_of_tendsto
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {β : ℕ → ℝ} {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    {φ : ℕ → ℕ} (s : G.State) (who : ι)
    (hβlim : Tendsto (β ∘ φ) atTop (nhds 1))
    (hzlim : Tendsto (z ∘ φ) atTop (nhds zlim)) :
    Tendsto ((fun p : ℝ × G.finkDomain U =>
      G.finkAuxEU p.1 p.2 s who) ∘
        fun k => (β (φ k), z (φ k))) atTop
      (nhds (G.finkAuxEU 1 zlim s who)) := by
  have hpair : Tendsto (fun k => (β (φ k), z (φ k))) atTop
      (nhds (1, zlim)) := by
    simpa only [Function.comp_def, nhds_prod_eq] using hβlim.prodMk hzlim
  exact (G.tendsto_finkAuxEU_param (1, zlim) s who).comp hpair

/-- Joint convergence of the discount and domain point transports through a
pure-deviation auxiliary payoff. -/
theorem tendsto_finkDeviationAuxEU_of_tendsto
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {β : ℕ → ℝ} {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    {φ : ℕ → ℕ} (s : G.State) (who : ι) (d : G.Act who)
    (hβlim : Tendsto (β ∘ φ) atTop (nhds 1))
    (hzlim : Tendsto (z ∘ φ) atTop (nhds zlim)) :
    Tendsto ((fun p : ℝ × G.finkDomain U =>
      G.finkDeviationAuxEU p.1 p.2 s who d) ∘
        fun k => (β (φ k), z (φ k))) atTop
      (nhds (G.finkDeviationAuxEU 1 zlim s who d)) := by
  have hpair : Tendsto (fun k => (β (φ k), z (φ k))) atTop
      (nhds (1, zlim)) := by
    simpa only [Function.comp_def, nhds_prod_eq] using hβlim.prodMk hzlim
  exact (G.tendsto_finkDeviationAuxEU_param (1, zlim) s who d).comp hpair

/-- Convergence of Fink-domain points gives coordinatewise convergence of
their decoded value functions, also after passing to a subsequence. -/
theorem tendsto_finkValue_of_comp_tendsto
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U} {φ : ℕ → ℕ}
    (hzlim : Tendsto (z ∘ φ) atTop (nhds zlim))
    (s : G.State) (who : ι) :
    Tendsto (fun k => G.finkValue (z (φ k)) s who) atTop
      (nhds (G.finkValue zlim s who)) := by
  have hz' : Tendsto (fun k => z (φ k)) atTop (nhds zlim) := by
    simpa only [Function.comp_def] using hzlim
  exact G.tendsto_finkValue_apply hz' s who

/-- Two real sequences that agree pointwise have the same limit. -/
theorem tendsto_eq_of_forall_eq {f g : ℕ → ℝ} {a b : ℝ}
    (hf : Tendsto f atTop (nhds a)) (hg : Tendsto g atTop (nhds b))
    (hfg : ∀ n, f n = g n) : a = b := by
  have hf' : Tendsto f atTop (nhds b) :=
    hg.congr' (Filter.Eventually.of_forall fun n => (hfg n).symm)
  exact tendsto_nhds_unique hf hf'

/-- If the Fink value equation holds along a convergent sequence whose
discounts tend to one, it also holds at the limit with discount one. -/
theorem finkAuxEU_one_eq_finkValue_of_tendsto
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ)
    (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U) (φ : ℕ → ℕ)
    (s : G.State) (who : ι)
    (hvalue : ∀ n,
      G.finkAuxEU (β n) (z n) s who = G.finkValue (z n) s who)
    (hβlim : Tendsto (β ∘ φ) atTop (nhds 1))
    (hzlim : Tendsto (z ∘ φ) atTop (nhds zlim)) :
    G.finkAuxEU 1 zlim s who = G.finkValue zlim s who := by
  have haux : Tendsto
      ((fun p : ℝ × G.finkDomain U =>
        G.finkAuxEU p.1 p.2 s who) ∘
          fun k => (β (φ k), z (φ k))) atTop
      (nhds (G.finkAuxEU 1 zlim s who)) :=
    G.tendsto_finkAuxEU_of_tendsto s who hβlim hzlim
  have hval : Tendsto (fun k => G.finkValue (z (φ k)) s who) atTop
      (nhds (G.finkValue zlim s who)) :=
    G.tendsto_finkValue_of_comp_tendsto hzlim s who
  exact tendsto_eq_of_forall_eq haux hval fun k => by
    simpa only [Function.comp_apply] using hvalue (φ k)

/-- Pure-deviation optimality is closed under a convergent vanishing-discount
subsequence. -/
theorem finkDeviationAuxEU_one_le_finkAuxEU_of_tendsto
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ)
    (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U) (φ : ℕ → ℕ)
    (s : G.State) (who : ι) (d : G.Act who)
    (hdev : ∀ n,
      G.finkDeviationAuxEU (β n) (z n) s who d ≤
        G.finkAuxEU (β n) (z n) s who)
    (hβlim : Tendsto (β ∘ φ) atTop (nhds 1))
    (hzlim : Tendsto (z ∘ φ) atTop (nhds zlim)) :
    G.finkDeviationAuxEU 1 zlim s who d ≤ G.finkAuxEU 1 zlim s who := by
  have hleft := G.tendsto_finkDeviationAuxEU_of_tendsto
    s who d hβlim hzlim
  have hright := G.tendsto_finkAuxEU_of_tendsto s who hβlim hzlim
  apply le_of_tendsto_of_tendsto hleft hright
  exact Filter.Eventually.of_forall fun k => by
    simpa only [Function.comp_apply] using hdev (φ k)

/-- At discount one, the Fink value equation says precisely that the value is
harmonic for the transition kernel induced by the stationary profile. -/
theorem finkValue_harmonic_of_finkAuxEU_one_eq
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (s : G.State) (who : ι)
    (hlimit : G.finkAuxEU 1 z s who = G.finkValue z s who) :
    G.finkValue z s who =
      expect (pmfPi (G.finkProfile z s)) (fun a =>
        expect (G.transition s a) (fun s' => G.finkValue z s' who)) := by
  rw [G.finkAuxEU_eq_discountedAuxEU, G.discountedAuxEU_eq] at hlimit
  simpa using hlimit.symm

/-- At discount one, a Fink pure-deviation inequality compares only expected
successor values: the current-stage payoff has vanished. -/
theorem pureDeviationContinuation_le_onProfile_of_finkAuxEU_one_le
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (s : G.State) (who : ι) (d : G.Act who)
    (hdev : G.finkDeviationAuxEU 1 z s who d ≤ G.finkAuxEU 1 z s who) :
    expect (pmfPi (Function.update (G.finkProfile z s) who (PMF.pure d)))
        (fun a => expect (G.transition s a)
          (fun s' => G.finkValue z s' who)) ≤
      expect (pmfPi (G.finkProfile z s)) (fun a =>
        expect (G.transition s a) (fun s' => G.finkValue z s' who)) := by
  rw [G.finkDeviationAuxEU_eq_discountedAuxEU,
    G.finkAuxEU_eq_discountedAuxEU,
    G.discountedAuxEU_eq, G.discountedAuxEU_eq] at hdev
  simpa using hdev

/-- Excessiveness against every pure action extends by linearity to every
mixed action of the deviating player. -/
theorem mixedDeviationContinuation_le_of_pure
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (s : G.State) (who : ι)
    (hpure : ∀ d : G.Act who,
      expect (pmfPi (Function.update (G.finkProfile z s) who (PMF.pure d)))
          (fun a => expect (G.transition s a)
            (fun s' => G.finkValue z s' who)) ≤
        G.finkValue z s who)
    (dev : PMF (G.Act who)) :
    expect (pmfPi (Function.update (G.finkProfile z s) who dev))
        (fun a => expect (G.transition s a)
          (fun s' => G.finkValue z s' who)) ≤
      G.finkValue z s who := by
  let f : G.JointAct → ℝ := fun a =>
    expect (G.transition s a) (fun s' => G.finkValue z s' who)
  calc
    expect (pmfPi (Function.update (G.finkProfile z s) who dev)) f =
        expect dev (fun d =>
          expect (pmfPi (Function.update (G.finkProfile z s) who (PMF.pure d)))
            f) := by
          rw [pmfPi_update_bind, expect_bind]
    _ ≤ expect dev (fun _ => G.finkValue z s who) := by
      exact expect_mono dev _ _ hpure
    _ = G.finkValue z s who := expect_const dev _

/-- A convergent family of Fink fixed points with discounts tending to one
has a harmonic limiting continuation value under its limiting stationary
profile.  This is the first limiting equation behind the excessive-function
selection step. -/
theorem finkValue_harmonic_of_fixedPoint_tendsto
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n ≤ 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U) (φ : ℕ → ℕ)
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n) hpay (z n) = z n)
    (hβlim : Tendsto (β ∘ φ) atTop (nhds 1))
    (hzlim : Tendsto (z ∘ φ) atTop (nhds zlim))
    (s : G.State) (who : ι) :
    G.finkValue zlim s who =
      expect (pmfPi (G.finkProfile zlim s)) (fun a =>
        expect (G.transition s a) (fun s' => G.finkValue zlim s' who)) := by
  have hvalue : ∀ n,
      G.finkAuxEU (β n) (z n) s who = G.finkValue (z n) s who := by
    intro n
    exact G.finkAuxEU_eq_finkValue_of_finkMap_fixedPoint
      (β n) U (hβ0 n) (hβ1 n) hpay (z n) (hfix n) s who
  have hlimit := G.finkAuxEU_one_eq_finkValue_of_tendsto
    β U z zlim φ s who hvalue hβlim hzlim
  exact G.finkValue_harmonic_of_finkAuxEU_one_eq zlim s who hlimit

/-- The limiting Fink value is excessive against every unilateral pure
action, while it is harmonic on the limiting stationary profile. -/
theorem finkValue_excessive_pureDeviation_of_fixedPoint_tendsto
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n ≤ 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U) (φ : ℕ → ℕ)
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n) hpay (z n) = z n)
    (hβlim : Tendsto (β ∘ φ) atTop (nhds 1))
    (hzlim : Tendsto (z ∘ φ) atTop (nhds zlim))
    (s : G.State) (who : ι) (d : G.Act who) :
    expect (pmfPi (Function.update (G.finkProfile zlim s) who (PMF.pure d)))
        (fun a => expect (G.transition s a)
          (fun s' => G.finkValue zlim s' who)) ≤
      G.finkValue zlim s who := by
  have hdev : ∀ n,
      G.finkDeviationAuxEU (β n) (z n) s who d ≤
        G.finkAuxEU (β n) (z n) s who := by
    intro n
    exact G.finkDeviationAuxEU_le_finkAuxEU_of_finkMap_fixedPoint
      (β n) U (hβ0 n) (hβ1 n) hpay (z n) (hfix n) s who d
  have hdevLimit := G.finkDeviationAuxEU_one_le_finkAuxEU_of_tendsto
    β U z zlim φ s who d hdev hβlim hzlim
  have hcont :=
    G.pureDeviationContinuation_le_onProfile_of_finkAuxEU_one_le
      zlim s who d hdevLimit
  exact hcont.trans_eq
    (G.finkValue_harmonic_of_fixedPoint_tendsto β U hβ0 hβ1 hpay
      z zlim φ hfix hβlim hzlim s who).symm

/-- A stationary average-reward Bellman certificate closes the verification
problem without any annealing calendar.  Harmonicity/excessiveness transports
the state-dependent target `W` through arbitrary horizons, while the bounded
bias `H` contributes only an endpoint term. -/
theorem isUniformEquilibriumPayoff_of_stationaryAverageRewardBias
    (G : StochasticGame ι) [Finite G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Finite (G.Act i)] (s₀ : G.State)
    (x : G.StationaryMixedProfile) (W H : G.State → Payoff ι)
    (hharmonic : ∀ s who,
      W s who = expect (pmfPi (x s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)))
    (hexcessive : ∀ s who (dev : PMF (G.Act who)),
      expect (pmfPi (Function.update (x s) who dev)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who)
    (honProfile : ∀ s who,
      W s who + H s who = G.mixedStageEU s (x s) who +
        expect (pmfPi (x s)) (fun a =>
          expect (G.transition s a) (fun s' => H s' who)))
    (hdeviation : ∀ s who (dev : PMF (G.Act who)),
      G.mixedStageEU s (Function.update (x s) who dev) who +
          expect (pmfPi (Function.update (x s) who dev)) (fun a =>
            expect (G.transition s a) (fun s' => H s' who)) ≤
        W s who + H s who) :
    G.IsUniformEquilibriumPayoff s₀ (W s₀) := by
  letI : Fintype G.State := Fintype.ofFinite G.State
  letI : ∀ i, Fintype (G.Act i) := fun i => Fintype.ofFinite (G.Act i)
  apply G.isUniformEquilibriumPayoff_of_deviation_caps s₀ (W s₀)
  intro δ hδ
  let xConst : ℕ → G.StationaryMixedProfile := fun _ => x
  let σ := G.scheduledMarkovBehaviorProfile xConst
  let C : ℝ := ‖H‖
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * C / δ)
  refine ⟨σ, N + 1, ?_⟩
  intro T hT
  have hTpos : 0 < T := lt_of_lt_of_le (Nat.zero_lt_succ N) hT
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hTpos
  have hNT : (N : ℝ) ≤ T := by
    exact_mod_cast (Nat.le_trans (Nat.le_succ N) hT)
  have hratio : 2 * C / δ ≤ (T : ℝ) := hN.trans hNT
  have hboundary : 2 * C / (T : ℝ) ≤ δ := by
    rw [div_le_iff₀ hTreal]
    have hδT : 2 * C ≤ δ * (T : ℝ) := by
      simpa only [mul_comm] using (div_le_iff₀ hδ).mp hratio
    nlinarith
  have hHbound : ∀ t s who, |(fun _ : ℕ => H) t s who| ≤ C :=
    fun _ s who => G.abs_finkBiasCoordinate_le_norm H s who
  have htarget : ∀ who,
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
          G.expectedStateValue σ s₀ t (fun s => W s who) =
        W s₀ who := by
    intro who
    have hclose := G.scheduled_targetAverage_close_initial
      xConst (fun _ => W) W (fun _ => 0) (fun _ => 0) who s₀
      (fun _ _ => by simp)
      (fun _ s => by rw [← hharmonic s]; simp) hTpos
    have hzero : (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
        ((fun _ : ℕ => 0) t +
          ∑ k ∈ Finset.range t, (fun _ : ℕ => 0) k) = 0 := by
      simp
    rw [hzero] at hclose
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hclose (abs_nonneg _)))
  constructor
  · intro who
    have hlo := G.finiteAveragePayoff_ge_targetAverage_of_averageReward_bellman_le
      σ s₀ who (fun _ s => W s who) (fun _ s => H s who)
        (fun _ => 0) (C0 := C) (CT := C)
        (hHbound 0 · who) (hHbound T · who) (fun t h => by
          change W h.2 who + H h.2 who ≤
            G.mixedStageEU h.2 (x h.2) who +
              expect (pmfPi (x h.2)) (fun a =>
                expect (G.transition h.2 a) (fun s' => H s' who)) + 0
          linarith [honProfile h.2 who]) hTpos
    have hup := G.finiteAveragePayoff_le_targetAverage_of_averageReward_bellman_ge
      σ s₀ who (fun _ s => W s who) (fun _ s => H s who)
        (fun _ => 0) (C0 := C) (CT := C)
        (hHbound 0 · who) (hHbound T · who) (fun t h => by
          change G.mixedStageEU h.2 (x h.2) who +
                expect (pmfPi (x h.2)) (fun a =>
                  expect (G.transition h.2 a) (fun s' => H s' who)) ≤
              W h.2 who + H h.2 who + 0
          linarith [honProfile h.2 who]) hTpos
    rw [htarget who] at hlo hup
    simp only [add_zero, Finset.sum_const_zero, mul_zero] at hlo hup
    have hboundary' : (C + C) / (T : ℝ) ≤ δ := by
      simpa only [two_mul] using hboundary
    rw [abs_le]
    constructor <;> linarith
  · intro who dev
    have hexcessiveConst : ∀ t s (d : PMF (G.Act who)),
        expect (pmfPi (Function.update (xConst t s) who d)) (fun a =>
          expect (G.transition s a) (fun s' => W s' who)) ≤
            W s who + (fun _ : ℕ => 0) t := by
      intro t s d
      simpa only [xConst, add_zero] using hexcessive s who d
    have htargetDev := G.scheduled_deviation_targetAverage_le_initial
      xConst (fun _ => W) W (fun _ => 0) (fun _ => 0) who dev s₀
      (fun _ _ => by simp)
      hexcessiveConst hTpos
    have hup := G.finiteAveragePayoff_le_targetAverage_of_averageReward_bellman_ge
      (Function.update σ who dev) s₀ who
        (fun _ s => W s who) (fun _ s => H s who) (fun _ => 0)
        (C0 := C) (CT := C) (hHbound 0 · who) (hHbound T · who)
        (fun t h => by
          unfold stageEUAt
          rw [G.stageActionDist_update_scheduledMarkovBehaviorProfile]
          dsimp only [xConst]
          change G.mixedStageEU h.2
                (Function.update (x h.2) who (dev t h)) who +
              expect (pmfPi (Function.update (x h.2) who (dev t h)))
                (fun a => expect (G.transition h.2 a)
                  (fun s' => H s' who)) ≤ W h.2 who + H h.2 who + 0
          linarith [hdeviation h.2 who (dev t h)]) hTpos
    simp only [Finset.sum_const_zero, add_zero, mul_zero] at htargetDev hup
    have hboundary' : (C + C) / (T : ℝ) ≤ δ := by
      simpa only [two_mul] using hboundary
    linarith

/-- It is enough to verify the average-reward bias inequality on pure actions
that preserve the harmonic target `W`.  By finiteness, all remaining actions
decrease `W` by one common positive gap.  Adding a sufficiently large multiple
of `W` to the bias leaves the on-profile Bellman equation unchanged and makes
the deviation inequality automatic on those strict-loss actions. -/
theorem isUniformEquilibriumPayoff_of_stationaryAverageRewardBias_on_neutral
    (G : StochasticGame ι) [Finite G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Finite (G.Act i)] (s₀ : G.State)
    (x : G.StationaryMixedProfile) (W H : G.State → Payoff ι)
    (hharmonic : ∀ s who,
      W s who = expect (pmfPi (x s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)))
    (hexcessive : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (x s) who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who)
    (honProfile : ∀ s who,
      W s who + H s who = G.mixedStageEU s (x s) who +
        expect (pmfPi (x s)) (fun a =>
          expect (G.transition s a) (fun s' => H s' who)))
    (hneutral : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (x s) who (PMF.pure d))) (fun a =>
          expect (G.transition s a) (fun s' => W s' who)) = W s who →
        G.mixedStageEU s
              (Function.update (x s) who (PMF.pure d)) who +
            expect (pmfPi (Function.update (x s) who (PMF.pure d)))
              (fun a => expect (G.transition s a) (fun s' => H s' who)) ≤
          W s who + H s who) :
    G.IsUniformEquilibriumPayoff s₀ (W s₀) := by
  let D := Σ p : G.State × ι, G.Act p.2
  let base : D → ℝ := fun q =>
    G.mixedStageEU q.1.1
          (Function.update (x q.1.1) q.1.2 (PMF.pure q.2)) q.1.2 +
      expect (pmfPi (Function.update (x q.1.1) q.1.2 (PMF.pure q.2)))
        (fun a => expect (G.transition q.1.1 a) (fun s' => H s' q.1.2)) -
      (W q.1.1 q.1.2 + H q.1.1 q.1.2)
  obtain ⟨B, hB⟩ := Math.Probability.exists_abs_bound_of_finite base
  obtain ⟨δ, hδ, hgap⟩ := G.exists_uniform_strictContinuationGap x W
  let c : ℝ := (|B| + 1) / δ
  let H' : G.State → Payoff ι := fun s who => H s who + c * W s who
  have hc0 : 0 ≤ c := div_nonneg (by positivity) hδ.le
  have hcδ : c * δ = |B| + 1 := by
    dsimp only [c]
    field_simp
  have hcontAdd : ∀ s (mu : PMF G.JointAct) who,
      expect mu (fun a => expect (G.transition s a) (fun s' => H' s' who)) =
        expect mu (fun a => expect (G.transition s a) (fun s' => H s' who)) +
          c * expect mu (fun a =>
            expect (G.transition s a) (fun s' => W s' who)) := by
    intro s mu who
    dsimp only [H']
    simp_rw [expect_add, expect_const_mul]
  have hpure : ∀ s who (d : G.Act who),
      G.mixedStageEU s
            (Function.update (x s) who (PMF.pure d)) who +
          expect (pmfPi (Function.update (x s) who (PMF.pure d)))
            (fun a => expect (G.transition s a) (fun s' => H' s' who)) ≤
        W s who + H' s who := by
    intro s who d
    let contW := expect
      (pmfPi (Function.update (x s) who (PMF.pure d)))
      (fun a => expect (G.transition s a) (fun s' => W s' who))
    rw [hcontAdd]
    change G.mixedStageEU s
          (Function.update (x s) who (PMF.pure d)) who +
        (expect (pmfPi (Function.update (x s) who (PMF.pure d)))
            (fun a => expect (G.transition s a) (fun s' => H s' who)) +
          c * contW) ≤ W s who + (H s who + c * W s who)
    by_cases hstrict : contW < W s who
    · have hgap' := hgap s who d hstrict
      have hbaseUpper : base ⟨(s, who), d⟩ ≤ |B| :=
        (le_abs_self _).trans ((hB ⟨(s, who), d⟩).trans (le_abs_self B))
      have hcLoss : c * (contW - W s who) ≤ c * (-δ) := by
        apply mul_le_mul_of_nonneg_left _ hc0
        dsimp only [contW] at hgap' ⊢
        linarith
      dsimp only [base] at hbaseUpper
      linarith
    · have heq : contW = W s who := by
        apply le_antisymm
        · exact hexcessive s who d
        · exact le_of_not_gt hstrict
      have hn := hneutral s who d (by simpa only [contW] using heq)
      rw [heq]
      linarith
  have hmixedExcessive : ∀ s who (dev : PMF (G.Act who)),
      expect (pmfPi (Function.update (x s) who dev)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who := by
    intro s who dev
    exact G.mixedDeviationContinuation_le_of_pure_bound
      x W s who (W s who) (hexcessive s who) dev
  have honProfile' : ∀ s who,
      W s who + H' s who = G.mixedStageEU s (x s) who +
        expect (pmfPi (x s)) (fun a =>
          expect (G.transition s a) (fun s' => H' s' who)) := by
    intro s who
    rw [hcontAdd]
    rw [← hharmonic s who]
    dsimp only [H']
    linarith [honProfile s who]
  have hmixed : ∀ s who (dev : PMF (G.Act who)),
      G.mixedStageEU s (Function.update (x s) who dev) who +
          expect (pmfPi (Function.update (x s) who dev)) (fun a =>
            expect (G.transition s a) (fun s' => H' s' who)) ≤
        W s who + H' s who := by
    intro s who dev
    calc
      G.mixedStageEU s (Function.update (x s) who dev) who +
            expect (pmfPi (Function.update (x s) who dev)) (fun a =>
              expect (G.transition s a) (fun s' => H' s' who)) =
          expect dev (fun d =>
            G.mixedStageEU s
                  (Function.update (x s) who (PMF.pure d)) who +
              expect (pmfPi (Function.update (x s) who (PMF.pure d)))
                (fun a => expect (G.transition s a)
                  (fun s' => H' s' who))) := by
            unfold mixedStageEU
            rw [pmfPi_update_bind]
            rw [expect_bind, expect_bind, expect_add]
      _ ≤ expect dev (fun _ => W s who + H' s who) :=
        expect_mono dev _ _ (hpure s who)
      _ = W s who + H' s who := expect_const dev _
  exact G.isUniformEquilibriumPayoff_of_stationaryAverageRewardBias
    s₀ x W H' hharmonic hmixedExcessive honProfile' hmixed

/-- A finite relative-bias branch closes to a stationary uniform equilibrium
when its singular target-continuation terms are controlled by one further
potential `K`.  The on-profile forcing must converge to the residual of `K`,
while continuation-neutral pure deviations only need the corresponding
asymptotic lower bound.  Strict continuation losses are handled by the finite
gap argument in
`isUniformEquilibriumPayoff_of_stationaryAverageRewardBias_on_neutral`.
Subtracting `K` from the limiting relative bias then gives an average-reward
verification certificate.  This is the finite-bias analogue of one Poisson
correction, and needs no calendar. -/
theorem isUniformEquilibriumPayoff_of_finkInteriorLowerCorrectionCertificate
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (s₀ : G.State)
    (β : ℕ → ℝ) (U : ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U)
    (W H K : G.State → Payoff ι)
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (hz : Tendsto z atTop (nhds zlim))
    (hV : Tendsto (fun n => G.finkValue (z n)) atTop (nhds W))
    (hH : Tendsto (fun n => G.finkRelativeBias (β n) W (z n))
      atTop (nhds H))
    (hharmonic : ∀ s who,
      W s who = expect (pmfPi (G.finkProfile zlim s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)))
    (hexcessive : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who)
    (hscaledResidual : Tendsto (fun n =>
      (β n / (1 - β n)) • G.finkContinuationResidualVector W (z n))
        atTop (nhds (-G.finkContinuationResidualVector K zlim)))
    (hscaledGainLower : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) = W s who →
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, -G.finkContinuationGain K zlim s who d - ε ≤
          (β n / (1 - β n)) *
            G.finkContinuationGain W (z n) s who d) :
    G.IsUniformEquilibriumPayoff s₀ (W s₀) := by
  let a : ℕ → ℝ := fun n => β n / (1 - β n)
  let J : ℕ → G.State → Payoff ι := fun n =>
    G.finkRelativeBias (β n) W (z n)
  let E : ℕ → G.State → Payoff ι := fun n =>
    G.finkContinuationResidualVector W (z n)
  have hbellman : ∀ n s who,
      G.finkValue (z n) s who + J n s who =
        G.finkStageEU (z n) s who +
          G.finkContinuationEU (J n) (z n) s who +
            a n * E n s who := by
    intro n s who
    simpa only [J, E, a, finkContinuationResidualVector] using
      G.finkValue_add_relativeBias_eq_finkEU_add
        (β n) U (hβ0 n) (hβ1 n) hpay (z n) (hfix n) W s who
  have hforcing := G.tendsto_smul_finkBellmanForcingVector hz hV
    (by simpa only [J] using hH) a hbellman
  have hforcingCorrection : G.finkBellmanForcingVector W H zlim =
      -G.finkContinuationResidualVector K zlim := by
    apply tendsto_nhds_unique hforcing
    simpa only [a, E] using hscaledResidual
  have honProfile : ∀ s who,
      W s who + (H - K) s who =
        G.mixedStageEU s (G.finkProfile zlim s) who +
          expect (pmfPi (G.finkProfile zlim s)) (fun a =>
            expect (G.transition s a) (fun s' => (H - K) s' who)) := by
    intro s who
    have hcoord := congrFun (congrFun hforcingCorrection s) who
    unfold finkBellmanForcingVector finkContinuationResidualVector
      finkContinuationResidual at hcoord
    change W s who + H s who - G.finkStageEU zlim s who -
        G.finkContinuationEU H zlim s who =
      -(G.finkContinuationEU K zlim s who - K s who) at hcoord
    change W s who + (H - K) s who =
      G.finkStageEU zlim s who +
        G.finkContinuationEU (H - K) zlim s who
    rw [G.finkContinuationEU_sub]
    simp only [Pi.sub_apply] at hcoord ⊢
    linarith
  have hpure : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) = W s who →
      G.mixedStageEU s
            (Function.update (G.finkProfile zlim s) who (PMF.pure d)) who +
          expect (pmfPi (Function.update (G.finkProfile zlim s)
            who (PMF.pure d))) (fun a =>
              expect (G.transition s a) (fun s' => (H - K) s' who)) ≤
        W s who + (H - K) s who := by
    intro s who d hneutral
    have hstage := G.tendsto_finkStageGain hz s who d
    have hbias := G.tendsto_finkContinuationGain_of_tendsto hH hz s who d
    have hbase : Tendsto (fun n =>
        G.finkStageGain (z n) s who d +
          G.finkContinuationGain
            (G.finkRelativeBias (β n) W (z n)) (z n) s who d)
        atTop (nhds (G.finkStageGain zlim s who d +
          G.finkContinuationGain H zlim s who d)) := by
      exact hstage.add hbias
    have hnonpos : G.finkStageGain zlim s who d +
        G.finkContinuationGain (H - K) zlim s who d ≤ 0 := by
      have hlimit : G.finkStageGain zlim s who d +
          (-G.finkContinuationGain K zlim s who d) +
            G.finkContinuationGain H zlim s who d ≤ 0 := by
        by_contra hnot
        have hpos : 0 < G.finkStageGain zlim s who d +
            (-G.finkContinuationGain K zlim s who d) +
              G.finkContinuationGain H zlim s who d :=
          lt_of_not_ge hnot
        let ε := (G.finkStageGain zlim s who d +
          (-G.finkContinuationGain K zlim s who d) +
            G.finkContinuationGain H zlim s who d) / 4
        have hε : 0 < ε := by
          dsimp only [ε]
          linarith
        obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hbase ε hε
        have hbaseClose : ∀ᶠ n in atTop,
            |(G.finkStageGain (z n) s who d +
                G.finkContinuationGain
                  (G.finkRelativeBias (β n) W (z n)) (z n) s who d) -
              (G.finkStageGain zlim s who d +
                G.finkContinuationGain H zlim s who d)| < ε := by
          filter_upwards [Filter.eventually_atTop.2 ⟨N, hN⟩] with n hn
          simpa only [Real.dist_eq] using hn
        have hlower := hscaledGainLower s who d hneutral ε hε
        obtain ⟨n, hnclose, hnlower⟩ := (hbaseClose.and hlower).exists
        have hcenter :=
          G.finkCenteredGain_nonpos_of_finkMap_fixedPoint
            (β n) U (hβ0 n) (hβ1 n) hpay (z n) (hfix n) W s who d
        rw [abs_lt] at hnclose
        dsimp only [ε] at hnclose hnlower
        linarith
      rw [G.finkContinuationGain_sub]
      linarith
    unfold finkStageGain finkContinuationGain at hnonpos
    have hon := honProfile s who
    linarith
  exact G.isUniformEquilibriumPayoff_of_stationaryAverageRewardBias_on_neutral
    s₀ (G.finkProfile zlim) W (H - K) hharmonic hexcessive
      honProfile hpure

/-- Two-sided convergence is a convenient sufficient condition for the
one-sided pure-deviation control in
`isUniformEquilibriumPayoff_of_finkInteriorLowerCorrectionCertificate`. -/
theorem isUniformEquilibriumPayoff_of_finkInteriorCorrectionCertificate
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (s₀ : G.State)
    (β : ℕ → ℝ) (U : ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U)
    (W H K : G.State → Payoff ι)
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (hz : Tendsto z atTop (nhds zlim))
    (hV : Tendsto (fun n => G.finkValue (z n)) atTop (nhds W))
    (hH : Tendsto (fun n => G.finkRelativeBias (β n) W (z n))
      atTop (nhds H))
    (hharmonic : ∀ s who,
      W s who = expect (pmfPi (G.finkProfile zlim s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)))
    (hexcessive : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who)
    (hscaledResidual : Tendsto (fun n =>
      (β n / (1 - β n)) • G.finkContinuationResidualVector W (z n))
        atTop (nhds (-G.finkContinuationResidualVector K zlim)))
    (hscaledGain : ∀ s who (d : G.Act who),
      Tendsto (fun n => (β n / (1 - β n)) *
        G.finkContinuationGain W (z n) s who d) atTop
          (nhds (-G.finkContinuationGain K zlim s who d))) :
    G.IsUniformEquilibriumPayoff s₀ (W s₀) := by
  apply G.isUniformEquilibriumPayoff_of_finkInteriorLowerCorrectionCertificate
    s₀ β U hβ0 hβ1 hpay z zlim W H K hfix hz hV hH
      hharmonic hexcessive hscaledResidual
  intro s who d _ ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hscaledGain s who d) ε hε
  filter_upwards [Filter.eventually_atTop.2 ⟨N, hN⟩] with n hn
  rw [Real.dist_eq, abs_lt] at hn
  linarith

/-- Algebraic Poisson form of the one-sided interior correction criterion.
The on-profile scaled residual convergence is automatic from the centered
Fink Bellman equation; it is enough to identify its forced limit as the
negative continuation residual of `K`. -/
theorem isUniformEquilibriumPayoff_of_finkInteriorPoissonLowerCorrection
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (s₀ : G.State)
    (β : ℕ → ℝ) (U : ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U)
    (W H K : G.State → Payoff ι)
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (hz : Tendsto z atTop (nhds zlim))
    (hV : Tendsto (fun n => G.finkValue (z n)) atTop (nhds W))
    (hH : Tendsto (fun n => G.finkRelativeBias (β n) W (z n))
      atTop (nhds H))
    (hharmonic : ∀ s who,
      W s who = expect (pmfPi (G.finkProfile zlim s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)))
    (hexcessive : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who)
    (hPoisson : G.finkBellmanForcingVector W H zlim =
      -G.finkContinuationResidualVector K zlim)
    (hscaledGainLower : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) = W s who →
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, -G.finkContinuationGain K zlim s who d - ε ≤
          (β n / (1 - β n)) *
            G.finkContinuationGain W (z n) s who d) :
    G.IsUniformEquilibriumPayoff s₀ (W s₀) := by
  let a : ℕ → ℝ := fun n => β n / (1 - β n)
  let E : ℕ → G.State → Payoff ι := fun n =>
    G.finkContinuationResidualVector W (z n)
  let J : ℕ → G.State → Payoff ι := fun n =>
    G.finkRelativeBias (β n) W (z n)
  have hbellman : ∀ n s who,
      G.finkValue (z n) s who + J n s who =
        G.finkStageEU (z n) s who +
          G.finkContinuationEU (J n) (z n) s who +
            a n * E n s who := by
    intro n s who
    simpa only [J, E, a, finkContinuationResidualVector] using
      G.finkValue_add_relativeBias_eq_finkEU_add
        (β n) U (hβ0 n) (hβ1 n) hpay (z n) (hfix n) W s who
  have hscaledResidual := G.tendsto_smul_finkBellmanForcingVector hz hV
    (by simpa only [J] using hH) a hbellman
  apply G.isUniformEquilibriumPayoff_of_finkInteriorLowerCorrectionCertificate
    s₀ β U hβ0 hβ1 hpay z zlim W H K hfix hz hV hH
      hharmonic hexcessive
  · simpa only [a, E, hPoisson] using hscaledResidual
  · exact hscaledGainLower

/-- Harmonic-adjustment form of the interior criterion.  A Poisson solution
may be shifted by any potential harmonic for the limiting on-profile kernel;
the remaining task is precisely to choose that shift so the
continuation-neutral deviation lower bounds hold. -/
theorem isUniformEquilibriumPayoff_of_finkInteriorPoissonHarmonicAdjustment
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (s₀ : G.State)
    (β : ℕ → ℝ) (U : ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U)
    (W H K A : G.State → Payoff ι)
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (hz : Tendsto z atTop (nhds zlim))
    (hV : Tendsto (fun n => G.finkValue (z n)) atTop (nhds W))
    (hH : Tendsto (fun n => G.finkRelativeBias (β n) W (z n))
      atTop (nhds H))
    (hharmonic : ∀ s who,
      W s who = expect (pmfPi (G.finkProfile zlim s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)))
    (hexcessive : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who)
    (hPoisson : G.finkBellmanForcingVector W H zlim =
      -G.finkContinuationResidualVector K zlim)
    (hAharmonic : G.finkContinuationResidualVector A zlim = 0)
    (hscaledGainLower : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) = W s who →
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop,
          -G.finkContinuationGain (K + A) zlim s who d - ε ≤
            (β n / (1 - β n)) *
              G.finkContinuationGain W (z n) s who d) :
    G.IsUniformEquilibriumPayoff s₀ (W s₀) := by
  have hresidual : G.finkContinuationResidualVector (K + A) zlim =
      G.finkContinuationResidualVector K zlim := by
    rw [G.finkContinuationResidualVector_add, hAharmonic, add_zero]
  apply G.isUniformEquilibriumPayoff_of_finkInteriorPoissonLowerCorrection
    s₀ β U hβ0 hβ1 hpay z zlim W H (K + A) hfix hz hV hH
      hharmonic hexcessive
  · rw [hresidual]
    exact hPoisson
  · exact hscaledGainLower

/-- Support/off-support form of the harmonic-adjustment criterion.  On an
action retained by the limiting profile, the centered Fink equality gives a
finite singular-gain limit, so a static average-reward inequality suffices.
Only continuation-neutral actions that vanish from the limiting support need
an asymptotic lower bound. -/
theorem isUniformEquilibriumPayoff_of_finkInteriorPoissonHarmonicAdjustment_onSupport
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (s₀ : G.State)
    (β : ℕ → ℝ) (U : ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U)
    (W H K A : G.State → Payoff ι)
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (hz : Tendsto z atTop (nhds zlim))
    (hV : Tendsto (fun n => G.finkValue (z n)) atTop (nhds W))
    (hH : Tendsto (fun n => G.finkRelativeBias (β n) W (z n))
      atTop (nhds H))
    (hharmonic : ∀ s who,
      W s who = expect (pmfPi (G.finkProfile zlim s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)))
    (hexcessive : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who)
    (hPoisson : G.finkBellmanForcingVector W H zlim =
      -G.finkContinuationResidualVector K zlim)
    (hAharmonic : G.finkContinuationResidualVector A zlim = 0)
    (hsupport : ∀ s who (d : G.Act who),
      G.finkProfile zlim s who d ≠ 0 →
      G.finkStageGain zlim s who d +
        G.finkContinuationGain (H - (K + A)) zlim s who d ≤ 0)
    (hoffSupport : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) = W s who →
      G.finkProfile zlim s who d = 0 →
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop,
          -G.finkContinuationGain (K + A) zlim s who d - ε ≤
            (β n / (1 - β n)) *
              G.finkContinuationGain W (z n) s who d) :
    G.IsUniformEquilibriumPayoff s₀ (W s₀) := by
  apply G.isUniformEquilibriumPayoff_of_finkInteriorPoissonHarmonicAdjustment
    s₀ β U hβ0 hβ1 hpay z zlim W H K A hfix hz hV hH
      hharmonic hexcessive hPoisson hAharmonic
  intro s who d hneutral ε hε
  by_cases hzero : G.finkProfile zlim s who d = 0
  · exact hoffSupport s who d hneutral hzero ε hε
  · have hlimit := G.tendsto_scaled_finkContinuationGain_of_limit_support
      hβ0 hβ1 hpay hz hfix W H hH s who d hzero
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlimit ε hε
    filter_upwards [Filter.eventually_atTop.2 ⟨N, hN⟩] with n hn
    rw [Real.dist_eq, abs_lt] at hn
    have hstatic := hsupport s who d hzero
    rw [G.finkContinuationGain_sub] at hstatic
    linarith

/-- Two-sided pure-deviation convergence specializes the one-sided algebraic
Poisson correction criterion. -/
theorem isUniformEquilibriumPayoff_of_finkInteriorPoissonCorrection
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (s₀ : G.State)
    (β : ℕ → ℝ) (U : ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U)
    (W H K : G.State → Payoff ι)
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (hz : Tendsto z atTop (nhds zlim))
    (hV : Tendsto (fun n => G.finkValue (z n)) atTop (nhds W))
    (hH : Tendsto (fun n => G.finkRelativeBias (β n) W (z n))
      atTop (nhds H))
    (hharmonic : ∀ s who,
      W s who = expect (pmfPi (G.finkProfile zlim s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)))
    (hexcessive : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who)
    (hPoisson : G.finkBellmanForcingVector W H zlim =
      -G.finkContinuationResidualVector K zlim)
    (hscaledGain : ∀ s who (d : G.Act who),
      Tendsto (fun n => (β n / (1 - β n)) *
        G.finkContinuationGain W (z n) s who d) atTop
          (nhds (-G.finkContinuationGain K zlim s who d))) :
    G.IsUniformEquilibriumPayoff s₀ (W s₀) := by
  apply G.isUniformEquilibriumPayoff_of_finkInteriorPoissonLowerCorrection
    s₀ β U hβ0 hβ1 hpay z zlim W H K hfix hz hV hH
      hharmonic hexcessive hPoisson
  intro s who d _ ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hscaledGain s who d) ε hε
  filter_upwards [Filter.eventually_atTop.2 ⟨N, hN⟩] with n hn
  rw [Real.dist_eq, abs_lt] at hn
  linarith

/-- Zero-correction specialization of
`isUniformEquilibriumPayoff_of_finkInteriorCorrectionCertificate`. -/
theorem isUniformEquilibriumPayoff_of_finkInteriorCertificate
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (s₀ : G.State)
    (β : ℕ → ℝ) (U : ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U)
    (W H : G.State → Payoff ι)
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (hz : Tendsto z atTop (nhds zlim))
    (hV : Tendsto (fun n => G.finkValue (z n)) atTop (nhds W))
    (hH : Tendsto (fun n => G.finkRelativeBias (β n) W (z n))
      atTop (nhds H))
    (hharmonic : ∀ s who,
      W s who = expect (pmfPi (G.finkProfile zlim s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)))
    (hexcessive : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who)
    (hscaledResidual : Tendsto (fun n =>
      (β n / (1 - β n)) • G.finkContinuationResidualVector W (z n))
        atTop (nhds 0))
    (hscaledGain : ∀ s who (d : G.Act who),
      Tendsto (fun n => (β n / (1 - β n)) *
        G.finkContinuationGain W (z n) s who d) atTop (nhds 0)) :
    G.IsUniformEquilibriumPayoff s₀ (W s₀) := by
  apply G.isUniformEquilibriumPayoff_of_finkInteriorCorrectionCertificate
    s₀ β U hβ0 hβ1 hpay z zlim W H 0 hfix hz hV hH
      hharmonic hexcessive
  · have hzero : -G.finkContinuationResidualVector
        (0 : G.State → Payoff ι) zlim = 0 := by
      ext s who
      simp [finkContinuationResidualVector, finkContinuationResidual,
        finkContinuationEU]
    rw [hzero]
    exact hscaledResidual
  · intro s who d
    simpa only [finkContinuationGain, Pi.zero_apply, expect_const,
      sub_self, neg_zero] using hscaledGain s who d

/-- The finite-relative-bias branch closes outright when the limiting value
is state-constant for each player.  In that case every singular target
residual and every pure target-continuation gain is identically zero, so no
Poisson or tangent correction is needed. -/
theorem isUniformEquilibriumPayoff_of_finkInterior_stateConstantValue
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (s₀ : G.State)
    (β : ℕ → ℝ) (U : ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U)
    (W H : G.State → Payoff ι)
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (hz : Tendsto z atTop (nhds zlim))
    (hV : Tendsto (fun n => G.finkValue (z n)) atTop (nhds W))
    (hH : Tendsto (fun n => G.finkRelativeBias (β n) W (z n))
      atTop (nhds H))
    (hconstant : ∀ who s t, W s who = W t who) :
    G.IsUniformEquilibriumPayoff s₀ (W s₀) := by
  apply G.isUniformEquilibriumPayoff_of_finkInteriorCertificate
    s₀ β U hβ0 hβ1 hpay z zlim W H hfix hz hV hH
  · intro s who
    change W s who = G.finkContinuationEU W zlim s who
    exact (G.finkContinuationEU_eq_of_stateConstant
      W hconstant zlim s who).symm
  · intro s who d
    have hfun : (fun t => W t who) = fun _ => W s who := by
      funext t
      exact (hconstant who s t).symm
    rw [hfun]
    simp
  · simpa only [G.finkContinuationResidualVector_eq_zero_of_stateConstant
      W hconstant, smul_zero] using
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => (0 : G.State → Payoff ι)) atTop (nhds 0))
  · intro s who d
    simpa only [G.finkContinuationGain_eq_zero_of_stateConstant
      W hconstant, mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))

/-- A strictly positive limiting induced state kernel closes the finite-bias
interior branch.  The finite maximum principle first makes the harmonic value
state-constant, after which the zero-correction theorem applies. -/
theorem isUniformEquilibriumPayoff_of_finkInterior_positiveStateKernel
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (s₀ : G.State)
    (β : ℕ → ℝ) (U : ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U)
    (W H : G.State → Payoff ι)
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (hz : Tendsto z atTop (nhds zlim))
    (hV : Tendsto (fun n => G.finkValue (z n)) atTop (nhds W))
    (hH : Tendsto (fun n => G.finkRelativeBias (β n) W (z n))
      atTop (nhds H))
    (hharmonic : ∀ s who,
      W s who = expect (pmfPi (G.finkProfile zlim s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)))
    (hpositive : ∀ s t, G.finkStateKernel zlim s t ≠ 0) :
    G.IsUniformEquilibriumPayoff s₀ (W s₀) := by
  apply G.isUniformEquilibriumPayoff_of_finkInterior_stateConstantValue
    s₀ β U hβ0 hβ1 hpay z zlim W H hfix hz hV hH
  exact G.stateConstant_of_finkStateKernel_positive_of_harmonic
    zlim W hpositive hharmonic

/-- Canonical vanishing-discount selection yields a stationary profile and
bounded value function that are harmonic on path and excessive against every
unilateral mixed action. -/
theorem exists_finkLimit_harmonic_excessive
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] [∀ i, Nonempty (G.Act i)]
    (U : ℝ) (hU : 0 ≤ U)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U) :
    ∃ zlim : G.finkDomain U,
      (∀ s who,
        G.finkValue zlim s who =
          expect (pmfPi (G.finkProfile zlim s)) (fun a =>
            expect (G.transition s a)
              (fun s' => G.finkValue zlim s' who))) ∧
      ∀ s who (dev : PMF (G.Act who)),
        expect (pmfPi (Function.update (G.finkProfile zlim s) who dev))
            (fun a => expect (G.transition s a)
              (fun s' => G.finkValue zlim s' who)) ≤
          G.finkValue zlim s who := by
  obtain ⟨z, zlim, φ, hfix, hφ, hzlim, hβlim⟩ :=
    G.exists_convergent_approachOne_finkFixedPoint_subsequence U hU hpay
  refine ⟨zlim, ?_, ?_⟩
  · intro s who
    exact G.finkValue_harmonic_of_fixedPoint_tendsto
      approachOneDiscount U approachOneDiscount_nonneg
        approachOneDiscount_le_one hpay z zlim φ hfix hβlim hzlim s who
  · intro s who dev
    apply G.mixedDeviationContinuation_le_of_pure zlim s who
    intro d
    exact G.finkValue_excessive_pureDeviation_of_fixedPoint_tendsto
      approachOneDiscount U approachOneDiscount_nonneg
        approachOneDiscount_le_one hpay z zlim φ hfix hβlim hzlim s who d

/-- The canonical limit certificate additionally plays only continuation-
neutral actions.  Strictly value-decreasing actions are absent from its
support and therefore belong to lower-order transient behavior. -/
theorem exists_finkLimit_harmonic_excessive_neutral
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] [∀ i, Nonempty (G.Act i)]
    (U : ℝ) (hU : 0 ≤ U)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U) :
    ∃ zlim : G.finkDomain U,
      (∀ s who,
        G.finkValue zlim s who =
          expect (pmfPi (G.finkProfile zlim s)) (fun a =>
            expect (G.transition s a)
              (fun s' => G.finkValue zlim s' who))) ∧
      (∀ s who (dev : PMF (G.Act who)),
        expect (pmfPi (Function.update (G.finkProfile zlim s) who dev))
            (fun a => expect (G.transition s a)
              (fun s' => G.finkValue zlim s' who)) ≤
          G.finkValue zlim s who) ∧
      G.IsContinuationNeutralOnSupport (G.finkProfile zlim)
        (G.finkValue zlim) := by
  obtain ⟨zlim, hharmonic, hexcessive⟩ :=
    G.exists_finkLimit_harmonic_excessive U hU hpay
  refine ⟨zlim, hharmonic, hexcessive, ?_⟩
  apply G.isContinuationNeutralOnSupport_of_harmonic_excessive zlim
    (G.finkValue zlim) hharmonic
  intro s who d
  exact hexcessive s who (PMF.pure d)

/-- Canonical Fink fixed points admit a further vanishing-discount family
whose value and transition residuals have the explicit rate `1 / (n + 1)`.
The theorem deliberately makes no claim about the growth of the corresponding
scaled biases. -/
theorem exists_fast_approachOne_finkFixedPoint_family
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] [∀ i, Nonempty (G.Act i)]
    (U : ℝ) (hU : 0 ≤ U)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U) :
    ∃ (β : ℕ → ℝ) (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U)
      (hβ0 : ∀ n, 0 ≤ β n) (hβ1 : ∀ n, β n < 1),
      (∀ n, G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n) ∧
      Tendsto β atTop (nhds 1) ∧
      Tendsto z atTop (nhds zlim) ∧
      (∀ s who,
        G.finkValue zlim s who =
          expect (pmfPi (G.finkProfile zlim s)) (fun a =>
            expect (G.transition s a)
              (fun s' => G.finkValue zlim s' who))) ∧
      (∀ s who (d : G.Act who),
        expect (pmfPi (Function.update (G.finkProfile zlim s)
            who (PMF.pure d))) (fun a =>
          expect (G.transition s a)
            (fun s' => G.finkValue zlim s' who)) ≤ G.finkValue zlim s who) ∧
      G.IsContinuationNeutralOnSupport (G.finkProfile zlim)
        (G.finkValue zlim) ∧
      (∀ n,
        (∀ s who,
          |G.finkValue (z n) s who - G.finkValue zlim s who| ≤
            (((n + 1 : ℕ) : ℝ))⁻¹) ∧
        (∀ s who,
          |expect (pmfPi (G.finkProfile (z n) s)) (fun a =>
              expect (G.transition s a)
                (fun s' => G.finkValue zlim s' who)) -
            G.finkValue zlim s who| ≤ (((n + 1 : ℕ) : ℝ))⁻¹) ∧
        (∀ s who (d : G.Act who),
          |expect (pmfPi (Function.update (G.finkProfile (z n) s)
              who (PMF.pure d))) (fun a =>
            expect (G.transition s a) (fun s' => G.finkValue zlim s' who)) -
          expect (pmfPi (Function.update (G.finkProfile zlim s)
              who (PMF.pure d))) (fun a =>
            expect (G.transition s a) (fun s' => G.finkValue zlim s' who))| ≤
              (((n + 1 : ℕ) : ℝ))⁻¹) ∧
        ∀ s who (dev : PMF (G.Act who)),
          expect (pmfPi (Function.update (G.finkProfile (z n) s) who dev))
              (fun a => expect (G.transition s a)
                (fun s' => G.finkValue zlim s' who)) ≤
            G.finkValue zlim s who + (((n + 1 : ℕ) : ℝ))⁻¹) ∧
      (∀ n s who (d : G.Act who),
        d ∉ G.strictContinuationActions (G.finkProfile zlim)
            (G.finkValue zlim) s who →
        |expect (pmfPi (Function.update (G.finkProfile (z n) s)
            who (PMF.pure d))) (fun a =>
          expect (G.transition s a)
            (fun s' => G.finkValue zlim s' who)) - G.finkValue zlim s who| ≤
              (((n + 1 : ℕ) : ℝ))⁻¹) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop, ∀ s who (d : G.Act who),
        expect (pmfPi (Function.update (G.finkProfile zlim s)
            who (PMF.pure d))) (fun a =>
          expect (G.transition s a)
            (fun s' => G.finkValue zlim s' who)) < G.finkValue zlim s who →
        ((G.finkProfile (z n) s who) d).toReal * δ ≤
          2 * (((n + 1 : ℕ) : ℝ))⁻¹ := by
  obtain ⟨z₀, zlim, φ, hfix, hφ, hzlim, hβlim⟩ :=
    G.exists_convergent_approachOne_finkFixedPoint_subsequence U hU hpay
  have hharmonic : ∀ s who,
      G.finkValue zlim s who =
        expect (pmfPi (G.finkProfile zlim s)) (fun a =>
          expect (G.transition s a) (fun s' => G.finkValue zlim s' who)) := by
    intro s who
    exact G.finkValue_harmonic_of_fixedPoint_tendsto
      approachOneDiscount U approachOneDiscount_nonneg
        approachOneDiscount_le_one hpay z₀ zlim φ hfix hβlim hzlim s who
  have hexcessive : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => G.finkValue zlim s' who)) ≤
          G.finkValue zlim s who := by
    intro s who d
    exact G.finkValue_excessive_pureDeviation_of_fixedPoint_tendsto
      approachOneDiscount U approachOneDiscount_nonneg
        approachOneDiscount_le_one hpay z₀ zlim φ hfix hβlim hzlim s who d
  obtain ⟨ψ, hψ, happrox⟩ :=
    G.exists_strictMono_finkApproximation_subsequence
      (z := z₀ ∘ φ) hzlim hharmonic hexcessive
  let β : ℕ → ℝ := fun n => approachOneDiscount (φ (ψ n))
  let z : ℕ → G.finkDomain U := fun n => z₀ (φ (ψ n))
  have hβ0 : ∀ n, 0 ≤ β n := fun n => approachOneDiscount_nonneg _
  have hβ1 : ∀ n, β n < 1 := fun n => approachOneDiscount_lt_one _
  have hfixFast : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n := by
    intro n
    simpa [β, z] using hfix (φ (ψ n))
  have hβFast : Tendsto β atTop (nhds 1) := by
    have ht := hβlim.comp hψ.tendsto_atTop
    simpa only [β, Function.comp_def] using ht
  have hzFast : Tendsto z atTop (nhds zlim) := by
    have ht := hzlim.comp hψ.tendsto_atTop
    simpa only [z, Function.comp_def] using ht
  have hneutral : G.IsContinuationNeutralOnSupport (G.finkProfile zlim)
      (G.finkValue zlim) := by
    exact G.isContinuationNeutralOnSupport_of_harmonic_excessive
      zlim (G.finkValue zlim) hharmonic hexcessive
  have happroxFast : ∀ n,
      (∀ s who,
        |G.finkValue (z n) s who - G.finkValue zlim s who| ≤
          (((n + 1 : ℕ) : ℝ))⁻¹) ∧
      (∀ s who,
        |expect (pmfPi (G.finkProfile (z n) s)) (fun a =>
            expect (G.transition s a)
              (fun s' => G.finkValue zlim s' who)) -
          G.finkValue zlim s who| ≤ (((n + 1 : ℕ) : ℝ))⁻¹) ∧
      (∀ s who (d : G.Act who),
        |expect (pmfPi (Function.update (G.finkProfile (z n) s)
            who (PMF.pure d))) (fun a =>
          expect (G.transition s a) (fun s' => G.finkValue zlim s' who)) -
        expect (pmfPi (Function.update (G.finkProfile zlim s)
            who (PMF.pure d))) (fun a =>
          expect (G.transition s a) (fun s' => G.finkValue zlim s' who))| ≤
            (((n + 1 : ℕ) : ℝ))⁻¹) ∧
      ∀ s who (dev : PMF (G.Act who)),
        expect (pmfPi (Function.update (G.finkProfile (z n) s) who dev))
            (fun a => expect (G.transition s a)
              (fun s' => G.finkValue zlim s' who)) ≤
          G.finkValue zlim s who + (((n + 1 : ℕ) : ℝ))⁻¹ := by
    intro n
    simpa only [z, Function.comp_apply] using happrox n
  have hprune := G.eventually_all_strictDeviation_probability_mul_le
    hzFast (G.finkValue zlim) (fun n => (((n + 1 : ℕ) : ℝ))⁻¹)
      (fun n => by positivity)
      (fun n s who => by
        have h := (abs_le.mp ((happroxFast n).2.1 s who)).1
        linarith)
      (fun n s who d => (happroxFast n).2.2.2 s who (PMF.pure d))
  have hneutralRate : ∀ n s who (d : G.Act who),
      d ∉ G.strictContinuationActions (G.finkProfile zlim)
          (G.finkValue zlim) s who →
      |expect (pmfPi (Function.update (G.finkProfile (z n) s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a)
          (fun s' => G.finkValue zlim s' who)) - G.finkValue zlim s who| ≤
            (((n + 1 : ℕ) : ℝ))⁻¹ := by
    intro n s who d hd
    exact G.abs_pureDeviationContinuation_sub_target_le_of_not_mem_strict
      (G.finkProfile zlim) (G.finkProfile (z n)) (G.finkValue zlim)
        s who d (((n + 1 : ℕ) : ℝ))⁻¹ (hexcessive s who d)
          ((happroxFast n).2.2.1 s who d) hd
  exact ⟨β, z, zlim, hβ0, hβ1, hfixFast, hβFast, hzFast,
    hharmonic, hexcessive, hneutral, happroxFast, hneutralRate, hprune⟩

-- ============================================================================
-- Time-dependent potential verification
-- ============================================================================

/-- Exact on-profile one-step decomposition for adjacent corrections.  The
defect is the same-index continuation residual plus the continuation value of
the correction increment. -/
theorem fink_correctedTarget_onProfile_step_eq
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)]
    (W R₀ R₁ : G.State → Payoff ι) {U : ℝ}
    (z : G.finkDomain U) (s : G.State) (who : ι) :
    expect (pmfPi (G.finkProfile z s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who + R₁ s' who)) -
      (W s who + R₀ s who) =
    G.finkContinuationResidual (W + R₀) z s who +
      G.finkContinuationEU (R₁ - R₀) z s who := by
  change G.finkContinuationEU (W + R₁) z s who -
      (W + R₀) s who = _
  rw [show W + R₁ = (W + R₀) + (R₁ - R₀) by abel]
  rw [G.finkContinuationEU_add]
  simp only [finkContinuationResidual, Pi.add_apply]
  ring

/-- Exact pure-deviation analogue of
`fink_correctedTarget_onProfile_step_eq`. -/
theorem fink_correctedTarget_pureDeviation_step_eq
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (W R₀ R₁ : G.State → Payoff ι) {U : ℝ}
    (z : G.finkDomain U) (s : G.State) (who : ι)
    (d : G.Act who) :
    expect (pmfPi (Function.update (G.finkProfile z s)
        who (PMF.pure d))) (fun a =>
      expect (G.transition s a) (fun s' => W s' who + R₁ s' who)) -
        (W s who + R₀ s who) =
      G.finkContinuationResidual (W + R₀) z s who +
        G.finkContinuationGain (W + R₀) z s who d +
        expect (pmfPi (Function.update (G.finkProfile z s)
            who (PMF.pure d))) (fun a =>
          expect (G.transition s a) (fun s' => (R₁ - R₀) s' who)) := by
  change (expect (pmfPi (Function.update (G.finkProfile z s)
      who (PMF.pure d))) (fun a =>
    expect (G.transition s a) (fun s' => (W + R₁) s' who))) -
      (W + R₀) s who = _
  rw [show W + R₁ = (W + R₀) + (R₁ - R₀) by abel]
  unfold finkContinuationResidual finkContinuationGain finkContinuationEU
  simp_rw [Pi.add_apply, expect_add]
  ring

/-- Same-index harmonic error and adjacent correction motion jointly bound
the on-profile time-dependent potential step. -/
theorem abs_fink_correctedTarget_onProfile_step_le
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)]
    (W R₀ R₁ : G.State → Payoff ι) {U : ℝ}
    (z : G.finkDomain U) (s : G.State) (who : ι) (r m : ℝ)
    (hresidual : |G.finkContinuationResidual (W + R₀) z s who| ≤ r)
    (hmove : ∀ s', |(R₁ - R₀) s' who| ≤ m) :
    |expect (pmfPi (G.finkProfile z s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who + R₁ s' who)) -
      (W s who + R₀ s who)| ≤ r + m := by
  rw [G.fink_correctedTarget_onProfile_step_eq W R₀ R₁ z s who]
  have hcontinuation :
      |G.finkContinuationEU (R₁ - R₀) z s who| ≤ m := by
    unfold finkContinuationEU
    exact abs_expect_le_of_abs_le _ _ fun a =>
      abs_expect_le_of_abs_le _ _ hmove
  exact (abs_add_le _ _).trans (add_le_add hresidual hcontinuation)

/-- Pure gain bounds lift to arbitrary mixed deviations after adding the
same-index residual and adjacent correction-motion charges. -/
theorem fink_correctedTarget_mixedDeviation_step_le
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (W R₀ R₁ : G.State → Payoff ι) {U : ℝ}
    (z : G.finkDomain U) (s : G.State) (who : ι)
    (r g m : ℝ)
    (hresidual : G.finkContinuationResidual (W + R₀) z s who ≤ r)
    (hgain : ∀ d : G.Act who,
      G.finkContinuationGain (W + R₀) z s who d ≤ g)
    (hmove : ∀ s', |(R₁ - R₀) s' who| ≤ m)
    (dev : PMF (G.Act who)) :
    expect (pmfPi (Function.update (G.finkProfile z s) who dev)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who + R₁ s' who)) ≤
      W s who + R₀ s who + (r + g + m) := by
  apply G.mixedDeviationContinuation_le_of_pure_bound
    (G.finkProfile z) (W + R₁) s who
      (W s who + R₀ s who + (r + g + m))
  intro d
  have hmovePure :
      expect (pmfPi (Function.update (G.finkProfile z s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => (R₁ - R₀) s' who)) ≤ m := by
    exact (le_abs_self _).trans (abs_expect_le_of_abs_le _ _ fun a =>
      abs_expect_le_of_abs_le _ _ hmove)
  have hdecomp :=
    G.fink_correctedTarget_pureDeviation_step_eq W R₀ R₁ z s who d
  simp only [Pi.add_apply] at ⊢
  linarith [hgain d]

/-- Finite sum of the positive pure-deviation continuation gains of a
potential.  Using a sum rather than a maximum also covers degenerate empty
coordinate types without extra inhabitedness assumptions. -/
noncomputable def finkPositiveContinuationGainSum
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (C : G.State → Payoff ι) {U : ℝ} (z : G.finkDomain U) : ℝ :=
  ∑ p : G.FinkPureActionIndex,
    max (G.finkContinuationGain C z p.1 p.2.1 p.2.2) 0

theorem finkContinuationGain_le_positiveSum
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (C : G.State → Payoff ι) {U : ℝ} (z : G.finkDomain U)
    (s : G.State) (who : ι) (d : G.Act who) :
    G.finkContinuationGain C z s who d ≤
      G.finkPositiveContinuationGainSum C z := by
  classical
  let q : G.FinkPureActionIndex := ⟨s, ⟨who, d⟩⟩
  calc
    G.finkContinuationGain C z s who d ≤
        max (G.finkContinuationGain C z s who d) 0 := le_max_left _ _
    _ ≤ ∑ p : G.FinkPureActionIndex,
        max (G.finkContinuationGain C z p.1 p.2.1 p.2.2) 0 := by
      let f : G.FinkPureActionIndex → ℝ := fun p =>
        max (G.finkContinuationGain C z p.1 p.2.1 p.2.2) 0
      change f q ≤ ∑ p, f p
      exact Finset.single_le_sum
        (fun p _ => le_max_right
          (G.finkContinuationGain C z p.1 p.2.1 p.2.2) 0)
        (Finset.mem_univ q)
    _ = G.finkPositiveContinuationGainSum C z := rfl

/-- One scalar charges all defects in an adjacent corrected-target step:
same-index harmonic residual, positive pure-deviation gain, and correction
motion. -/
noncomputable def finkCorrectedTargetStepError
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (W : G.State → Payoff ι) (R : ℕ → G.State → Payoff ι)
    {U : ℝ} (z : ℕ → G.finkDomain U) (t : ℕ) : ℝ :=
  ‖G.finkContinuationResidualVector (W + R t) (z t)‖ +
    G.finkPositiveContinuationGainSum (W + R t) (z t) +
    ‖R (t + 1) - R t‖

theorem finkCorrectedTargetStepError_nonneg
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (W : G.State → Payoff ι) (R : ℕ → G.State → Payoff ι)
    {U : ℝ} (z : ℕ → G.finkDomain U) (t : ℕ) :
    0 ≤ G.finkCorrectedTargetStepError W R z t := by
  unfold finkCorrectedTargetStepError finkPositiveContinuationGainSum
  positivity

/-- A nonzero first-order continuation residual cannot be hidden by a
zero-correction annealing calendar whose bias scale is negligible relative to
calendar time.  The residual forces at least harmonic-series hold cost, so
the summable-drift verification route is genuinely unavailable on this
branch. -/
theorem not_summable_zeroCorrectionStepError_of_scaledResidual_tendsto_ne_zero
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    (a : ℕ → ℝ) (ha0 : ∀ n, 0 ≤ a n)
    (z : ℕ → G.finkDomain U) (W F : G.State → Payoff ι)
    (hscaled : Tendsto (fun n =>
      a n • G.finkContinuationResidualVector W (z n))
        atTop (nhds F))
    (hF : F ≠ 0) (κ : ℕ → ℕ) (hκ : Tendsto κ atTop atTop)
    (hterminal : Tendsto (fun T : ℕ =>
      (T : ℝ)⁻¹ * a (κ T)) atTop (nhds 0)) :
    ¬ Summable (fun t => G.finkCorrectedTargetStepError W
      ((fun _ => 0) ∘ κ) (z ∘ κ) t) := by
  let e : ℕ → ℝ := fun t => G.finkCorrectedTargetStepError W
    ((fun _ => 0) ∘ κ) (z ∘ κ) t
  let c : ℝ := ‖F‖ / 2
  have hc : 0 < c := by
    dsimp only [c]
    exact half_pos (norm_pos_iff.mpr hF)
  have hnorm : Tendsto (fun t =>
      ‖a (κ t) • G.finkContinuationResidualVector W (z (κ t))‖)
      atTop (nhds ‖F‖) := by
    simpa only [Function.comp_apply] using (hscaled.comp hκ).norm
  have hlowerNorm : ∀ᶠ t : ℕ in atTop,
      c ≤ ‖a (κ t) •
        G.finkContinuationResidualVector W (z (κ t))‖ := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hnorm c hc
    filter_upwards [Filter.eventually_atTop.2 ⟨N, hN⟩] with t ht
    rw [Real.dist_eq, abs_lt] at ht
    dsimp only [c] at ht ⊢
    linarith
  have he0 : ∀ t, 0 ≤ e t := fun t =>
    G.finkCorrectedTargetStepError_nonneg W
      ((fun _ => 0) ∘ κ) (z ∘ κ) t
  have hlower : ∀ᶠ t : ℕ in atTop, c ≤ a (κ t) * e t := by
    filter_upwards [hlowerNorm] with t ht
    have hstep : ‖G.finkContinuationResidualVector W (z (κ t))‖ ≤ e t := by
      dsimp only [e]
      unfold finkCorrectedTargetStepError
      simp only [Function.comp_apply, add_zero, sub_self,
        norm_zero, add_zero]
      apply le_add_of_nonneg_right
      unfold finkPositiveContinuationGainSum
      exact Finset.sum_nonneg fun p hp => le_max_right _ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ha0 (κ t))] at ht
    exact ht.trans (mul_le_mul_of_nonneg_left hstep (ha0 (κ t)))
  exact not_summable_of_eventually_pos_le_mul_of_inv_mul_tendsto_zero
    (a ∘ κ) e c hc he0 hlower (by
      simpa only [Function.comp_apply] using hterminal)

/-- Concrete finite-bias no-go theorem.  If the limiting Bellman forcing is
nonzero, every zero-correction calendar that amortizes the scaled discounted
bias necessarily has nonsummable corrected-target drift. -/
theorem not_summable_zeroCorrectionStepError_of_finkBellmanForcing_ne_zero
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (β : ℕ → ℝ) (U : ℝ)
    (hβ0 : ∀ n, 0 ≤ β n) (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U)
    (W H : G.State → Payoff ι)
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (hz : Tendsto z atTop (nhds zlim))
    (hV : Tendsto (fun n => G.finkValue (z n)) atTop (nhds W))
    (hH : Tendsto (fun n => G.finkRelativeBias (β n) W (z n))
      atTop (nhds H))
    (hforcing : G.finkBellmanForcingVector W H zlim ≠ 0)
    (κ : ℕ → ℕ) (hκ : Tendsto κ atTop atTop)
    (hterminal : Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
      (β (κ T) / (1 - β (κ T)))) atTop (nhds 0)) :
    ¬ Summable (fun t => G.finkCorrectedTargetStepError W
      ((fun _ => 0) ∘ κ) (z ∘ κ) t) := by
  let a : ℕ → ℝ := fun n => β n / (1 - β n)
  let J : ℕ → G.State → Payoff ι := fun n =>
    G.finkRelativeBias (β n) W (z n)
  let E : ℕ → G.State → Payoff ι := fun n =>
    G.finkContinuationResidualVector W (z n)
  have ha0 : ∀ n, 0 ≤ a n := fun n =>
    div_nonneg (hβ0 n) (sub_nonneg.mpr (hβ1 n).le)
  have hbellman : ∀ n s who,
      G.finkValue (z n) s who + J n s who =
        G.finkStageEU (z n) s who +
          G.finkContinuationEU (J n) (z n) s who +
            a n * E n s who := by
    intro n s who
    simpa only [J, E, a, finkContinuationResidualVector] using
      G.finkValue_add_relativeBias_eq_finkEU_add
        (β n) U (hβ0 n) (hβ1 n) hpay (z n) (hfix n) W s who
  have hscaled := G.tendsto_smul_finkBellmanForcingVector hz hV
    (by simpa only [J] using hH) a hbellman
  apply G.not_summable_zeroCorrectionStepError_of_scaledResidual_tendsto_ne_zero
    a ha0 z W (G.finkBellmanForcingVector W H zlim) hscaled hforcing
      κ hκ
  simpa only [a] using hterminal

/-- Strong zero-correction calendar no-go theorem.  Under nonzero limiting
Bellman forcing, the exact normalized cumulative-drift bill appearing in
`IsIndexedFinkCorrectedCalendarSelectable` is unbounded along every
cofinal bias-amortizing calendar. -/
theorem not_eventually_bounded_zeroCorrectionCumulativeDrift_of_finkBellmanForcing_ne_zero
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (β : ℕ → ℝ) (U : ℝ)
    (hβ0 : ∀ n, 0 ≤ β n) (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U)
    (W H : G.State → Payoff ι)
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (hz : Tendsto z atTop (nhds zlim))
    (hV : Tendsto (fun n => G.finkValue (z n)) atTop (nhds W))
    (hH : Tendsto (fun n => G.finkRelativeBias (β n) W (z n))
      atTop (nhds H))
    (hforcing : G.finkBellmanForcingVector W H zlim ≠ 0)
    (κ : ℕ → ℕ) (hκ : Tendsto κ atTop atTop)
    (hterminal : Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
      (β (κ T) / (1 - β (κ T)))) atTop (nhds 0)) :
    ¬ ∃ C : ℝ, ∀ᶠ T : ℕ in atTop,
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
        ∑ k ∈ Finset.range t,
          G.finkCorrectedTargetStepError W
            ((fun _ => 0) ∘ κ) (z ∘ κ) k ≤ C := by
  rintro ⟨C, hC⟩
  let e : ℕ → ℝ := fun t => G.finkCorrectedTargetStepError W
    ((fun _ => 0) ∘ κ) (z ∘ κ) t
  have he0 : ∀ t, 0 ≤ e t := fun t =>
    G.finkCorrectedTargetStepError_nonneg W
      ((fun _ => 0) ∘ κ) (z ∘ κ) t
  have heSummable : Summable e :=
    summable_of_eventually_normalized_cumulative_sum_le e he0 C
      (by simpa only [e] using hC)
  have heNotSummable :=
    G.not_summable_zeroCorrectionStepError_of_finkBellmanForcing_ne_zero
      β U hβ0 hβ1 hpay z zlim W H hfix hz hV hH hforcing
        κ hκ hterminal
  exact heNotSummable (by simpa only [e] using heSummable)

/-- The canonical corrected-target error controls the on-profile step in the
exact form consumed by the time-dependent potential telescope. -/
theorem abs_fink_correctedTarget_onProfile_step_le_stepError
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (W : G.State → Payoff ι) (R : ℕ → G.State → Payoff ι)
    {U : ℝ} (z : ℕ → G.finkDomain U) (t : ℕ)
    (s : G.State) (who : ι) :
    |expect (pmfPi (G.finkProfile (z t) s)) (fun a =>
        expect (G.transition s a)
          (fun s' => W s' who + R (t + 1) s' who)) -
      (W s who + R t s who)| ≤
        G.finkCorrectedTargetStepError W R z t := by
  have hresidual :
      |G.finkContinuationResidual (W + R t) (z t) s who| ≤
        ‖G.finkContinuationResidualVector (W + R t) (z t)‖ := by
    exact G.abs_finkBiasCoordinate_le_norm
      (G.finkContinuationResidualVector (W + R t) (z t)) s who
  have hmove : ∀ s', |(R (t + 1) - R t) s' who| ≤
      ‖R (t + 1) - R t‖ := fun s' =>
    G.abs_finkBiasCoordinate_le_norm (R (t + 1) - R t) s' who
  have hstep := G.abs_fink_correctedTarget_onProfile_step_le
    W (R t) (R (t + 1)) (z t) s who
      ‖G.finkContinuationResidualVector (W + R t) (z t)‖
      ‖R (t + 1) - R t‖ hresidual hmove
  have hgainNonneg : 0 ≤
      G.finkPositiveContinuationGainSum (W + R t) (z t) := by
    unfold finkPositiveContinuationGainSum
    exact Finset.sum_nonneg fun p _ => le_max_right _ _
  exact hstep.trans (by
    unfold finkCorrectedTargetStepError
    linarith)

/-- The same canonical error controls every mixed unilateral deviation, and
hence every history-dependent deviation after the telescope. -/
theorem fink_correctedTarget_mixedDeviation_step_le_stepError
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (W : G.State → Payoff ι) (R : ℕ → G.State → Payoff ι)
    {U : ℝ} (z : ℕ → G.finkDomain U) (t : ℕ)
    (s : G.State) (who : ι) (dev : PMF (G.Act who)) :
    expect (pmfPi (Function.update (G.finkProfile (z t) s) who dev))
        (fun a => expect (G.transition s a)
          (fun s' => W s' who + R (t + 1) s' who)) ≤
      W s who + R t s who + G.finkCorrectedTargetStepError W R z t := by
  apply G.fink_correctedTarget_mixedDeviation_step_le
    W (R t) (R (t + 1)) (z t) s who
      ‖G.finkContinuationResidualVector (W + R t) (z t)‖
      (G.finkPositiveContinuationGainSum (W + R t) (z t))
      ‖R (t + 1) - R t‖
  · exact (le_abs_self _).trans
      (G.abs_finkBiasCoordinate_le_norm
        (G.finkContinuationResidualVector (W + R t) (z t)) s who)
  · intro d
    exact G.finkContinuationGain_le_positiveSum (W + R t) (z t) s who d
  · intro s'
    exact G.abs_finkBiasCoordinate_le_norm (R (t + 1) - R t) s' who

/-- A time-dependent state potential telescopes along a scheduled Markov
profile.  Unlike a pointwise bound on the drift of one fixed target, this
form retains cancellations supplied by Poisson corrections. -/
theorem scheduled_expectedTimeDependentStateValue_close_initial
    (G : StochasticGame ι) [Fintype ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (x : ℕ → G.StationaryMixedProfile)
    (C : ℕ → G.State → Payoff ι) (r : ℕ → ℝ)
    (who : ι) (s₀ : G.State)
    (hstep : ∀ t s,
      |expect (pmfPi (x t s)) (fun a =>
          expect (G.transition s a) (fun s' => C (t + 1) s' who)) -
        C t s who| ≤ r t)
    (T : ℕ) :
    |G.expectedStateValue (G.scheduledMarkovBehaviorProfile x) s₀ T
        (fun s => C T s who) - C 0 s₀ who| ≤
      ∑ t ∈ Finset.range T, r t := by
  let σ := G.scheduledMarkovBehaviorProfile x
  let A : ℕ → ℝ := fun t =>
    G.expectedStateValue σ s₀ t (fun s => C t s who)
  have hA : ∀ T, |A T - A 0| ≤ ∑ t ∈ Finset.range T, r t := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
        have hup : A (N + 1) ≤ A N + r N := by
          rw [show A (N + 1) = G.expectedStateValue σ s₀ (N + 1)
              (fun s => C (N + 1) s who) from rfl,
            G.expectedStateValue_succ]
          calc
            expect (G.histDist σ s₀ N) (fun h =>
                expect (G.stageActionDist σ h) (fun a =>
                  expect (G.transition h.2 a)
                    (fun s' => C (N + 1) s' who))) ≤
              expect (G.histDist σ s₀ N)
                (fun h => C N h.2 who + r N) := by
              apply expect_mono
              intro h
              rw [show G.stageActionDist σ h = pmfPi (x N h.2) from rfl]
              have hh := (abs_le.mp (hstep N h.2)).2
              linarith
            _ = A N + r N := by
              rw [expect_add, expect_const]
              rfl
        have hlo : A N ≤ A (N + 1) + r N := by
          calc
            A N = expect (G.histDist σ s₀ N)
                (fun h => C N h.2 who) := rfl
            _ ≤ expect (G.histDist σ s₀ N) (fun h =>
                expect (G.stageActionDist σ h) (fun a =>
                  expect (G.transition h.2 a)
                    (fun s' => C (N + 1) s' who)) + r N) := by
              apply expect_mono
              intro h
              rw [show G.stageActionDist σ h = pmfPi (x N h.2) from rfl]
              have hh := (abs_le.mp (hstep N h.2)).1
              linarith
            _ = A (N + 1) + r N := by
              rw [expect_add, expect_const]
              change _ = G.expectedStateValue σ s₀ (N + 1)
                (fun s => C (N + 1) s who) + r N
              rw [G.expectedStateValue_succ]
        have hone : |A (N + 1) - A N| ≤ r N :=
          abs_le.mpr ⟨by linarith, by linarith⟩
        have htriangle : |A (N + 1) - A 0| ≤
            |A (N + 1) - A N| + |A N - A 0| := by
          calc
            |A (N + 1) - A 0| =
                |(A (N + 1) - A N) + (A N - A 0)| := by ring_nf
            _ ≤ _ := abs_add_le _ _
        rw [Finset.sum_range_succ]
        linarith
  simpa only [A, σ, G.expectedStateValue_zero] using hA T

/-- Deviation-side time-dependent potential telescope.  A one-step
superharmonic correction remains valid against an arbitrary history-dependent
unilateral deviation. -/
theorem scheduled_deviation_expectedTimeDependentStateValue_le_initial
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (x : ℕ → G.StationaryMixedProfile)
    (C : ℕ → G.State → Payoff ι) (r : ℕ → ℝ)
    (who : ι) (dev : G.BehaviorStrategy who) (s₀ : G.State)
    (hstep : ∀ t s (d : PMF (G.Act who)),
      expect (pmfPi (Function.update (x t s) who d)) (fun a =>
          expect (G.transition s a) (fun s' => C (t + 1) s' who)) ≤
        C t s who + r t)
    (T : ℕ) :
    G.expectedStateValue
        (Function.update (G.scheduledMarkovBehaviorProfile x) who dev)
        s₀ T (fun s => C T s who) ≤
      C 0 s₀ who + ∑ t ∈ Finset.range T, r t := by
  induction T with
  | zero => simp
  | succ T ih =>
      let σ := Function.update (G.scheduledMarkovBehaviorProfile x) who dev
      have hone : G.expectedStateValue σ s₀ (T + 1)
          (fun s => C (T + 1) s who) ≤
          G.expectedStateValue σ s₀ T (fun s => C T s who) + r T := by
        rw [G.expectedStateValue_succ]
        calc
          expect (G.histDist σ s₀ T) (fun h =>
              expect (G.stageActionDist σ h) (fun a =>
                expect (G.transition h.2 a)
                  (fun s' => C (T + 1) s' who))) ≤
            expect (G.histDist σ s₀ T)
              (fun h => C T h.2 who + r T) := by
              apply expect_mono
              intro h
              rw [G.stageActionDist_update_scheduledMarkovBehaviorProfile]
              exact hstep T h.2 (dev T h)
          _ = G.expectedStateValue σ s₀ T
              (fun s => C T s who) + r T := by
            rw [expect_add, expect_const]
            rfl
      rw [Finset.sum_range_succ]
      linarith

/-- A bounded time-dependent correction converts the potential telescope
into control of the original target.  The correction is paid only at the two
endpoints, not once per calendar stage. -/
theorem scheduled_expectedStateValue_close_initial_of_correction
    (G : StochasticGame ι) [Fintype ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (x : ℕ → G.StationaryMixedProfile) (W : G.State → Payoff ι)
    (R : ℕ → G.State → Payoff ι) (c r : ℕ → ℝ)
    (who : ι) (s₀ : G.State)
    (hR : ∀ t s, |R t s who| ≤ c t)
    (hstep : ∀ t s,
      |expect (pmfPi (x t s)) (fun a =>
          expect (G.transition s a)
            (fun s' => W s' who + R (t + 1) s' who)) -
        (W s who + R t s who)| ≤ r t)
    (T : ℕ) :
    |G.expectedStateValue (G.scheduledMarkovBehaviorProfile x) s₀ T
        (fun s => W s who) - W s₀ who| ≤
      c 0 + c T + ∑ t ∈ Finset.range T, r t := by
  let σ := G.scheduledMarkovBehaviorProfile x
  let C : ℕ → G.State → Payoff ι :=
    fun t s i => W s i + R t s i
  have hC := G.scheduled_expectedTimeDependentStateValue_close_initial
    x C r who s₀ (by
      intro t s
      simpa only [C] using hstep t s) T
  have hdecomp : G.expectedStateValue σ s₀ T
      (fun s => C T s who) =
      G.expectedStateValue σ s₀ T (fun s => W s who) +
        G.expectedStateValue σ s₀ T (fun s => R T s who) := by
    unfold expectedStateValue
    rw [expect_add]
  have hRT : |G.expectedStateValue σ s₀ T
      (fun s => R T s who)| ≤ c T := by
    unfold expectedStateValue
    exact abs_expect_le_of_abs_le _ _ fun h => hR T h.2
  have hR0 := hR 0 s₀
  have htriangle :
      |G.expectedStateValue σ s₀ T (fun s => W s who) - W s₀ who| ≤
        |G.expectedStateValue σ s₀ T (fun s => C T s who) -
          C 0 s₀ who| + |R 0 s₀ who| +
            |G.expectedStateValue σ s₀ T (fun s => R T s who)| := by
    rw [hdecomp]
    dsimp only [C]
    let a := (G.expectedStateValue σ s₀ T (fun s => W s who) +
      G.expectedStateValue σ s₀ T (fun s => R T s who)) -
        (W s₀ who + R 0 s₀ who)
    let b := R 0 s₀ who
    let d := G.expectedStateValue σ s₀ T (fun s => R T s who)
    change |(G.expectedStateValue σ s₀ T (fun s => W s who) -
      W s₀ who)| ≤ |a| + |b| + |d|
    have heq : G.expectedStateValue σ s₀ T (fun s => W s who) -
        W s₀ who = a + b - d := by
      dsimp only [a, b, d]
      ring
    rw [heq]
    calc
      |a + b - d| = |(a + b) + (-d)| := by ring_nf
      _ ≤ |a + b| + |-d| := abs_add_le _ _
      _ ≤ (|a| + |b|) + |d| := by
        rw [abs_neg]
        exact add_le_add (abs_add_le _ _) le_rfl
  exact htriangle.trans (by linarith)

/-- Deviation-side corrected-potential estimate.  A bounded correction is
again charged only at the endpoints. -/
theorem scheduled_deviation_expectedStateValue_le_initial_of_correction
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (x : ℕ → G.StationaryMixedProfile) (W : G.State → Payoff ι)
    (R : ℕ → G.State → Payoff ι) (c r : ℕ → ℝ)
    (who : ι) (dev : G.BehaviorStrategy who) (s₀ : G.State)
    (hR : ∀ t s, |R t s who| ≤ c t)
    (hstep : ∀ t s (d : PMF (G.Act who)),
      expect (pmfPi (Function.update (x t s) who d)) (fun a =>
          expect (G.transition s a)
            (fun s' => W s' who + R (t + 1) s' who)) ≤
        W s who + R t s who + r t)
    (T : ℕ) :
    G.expectedStateValue
        (Function.update (G.scheduledMarkovBehaviorProfile x) who dev)
        s₀ T (fun s => W s who) ≤
      W s₀ who + c 0 + c T + ∑ t ∈ Finset.range T, r t := by
  let σ := Function.update (G.scheduledMarkovBehaviorProfile x) who dev
  let C : ℕ → G.State → Payoff ι :=
    fun t s i => W s i + R t s i
  have hC :=
    G.scheduled_deviation_expectedTimeDependentStateValue_le_initial
      x C r who dev s₀ (by
        intro t s d
        simpa only [C, add_assoc] using hstep t s d) T
  have hdecomp : G.expectedStateValue σ s₀ T
      (fun s => C T s who) =
      G.expectedStateValue σ s₀ T (fun s => W s who) +
        G.expectedStateValue σ s₀ T (fun s => R T s who) := by
    unfold expectedStateValue
    rw [expect_add]
  have hRT : |G.expectedStateValue σ s₀ T
      (fun s => R T s who)| ≤ c T := by
    unfold expectedStateValue
    exact abs_expect_le_of_abs_le _ _ fun h => hR T h.2
  have hR0 := hR 0 s₀
  rw [hdecomp] at hC
  dsimp only [C] at hC
  linarith [neg_abs_le (G.expectedStateValue σ s₀ T
    (fun s => R T s who)), le_abs_self (R 0 s₀ who)]

/-- Scheduled certificate values close to a target inherit the corrected
potential estimate. -/
theorem scheduled_expectedTarget_close_initial_of_correction
    (G : StochasticGame ι) [Fintype ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (x : ℕ → G.StationaryMixedProfile)
    (V : ℕ → G.State → Payoff ι) (W : G.State → Payoff ι)
    (R : ℕ → G.State → Payoff ι) (q c r : ℕ → ℝ)
    (who : ι) (s₀ : G.State)
    (hclose : ∀ t s, |V t s who - W s who| ≤ q t)
    (hR : ∀ t s, |R t s who| ≤ c t)
    (hstep : ∀ t s,
      |expect (pmfPi (x t s)) (fun a =>
          expect (G.transition s a)
            (fun s' => W s' who + R (t + 1) s' who)) -
        (W s who + R t s who)| ≤ r t)
    (T : ℕ) :
    |G.expectedStateValue (G.scheduledMarkovBehaviorProfile x) s₀ T
        (fun s => V T s who) - W s₀ who| ≤
      q T + c 0 + c T + ∑ t ∈ Finset.range T, r t := by
  let σ := G.scheduledMarkovBehaviorProfile x
  have hVW :
      |G.expectedStateValue σ s₀ T (fun s => V T s who) -
        G.expectedStateValue σ s₀ T (fun s => W s who)| ≤ q T := by
    unfold expectedStateValue
    rw [← expect_sub]
    exact abs_expect_le_of_abs_le _ _ fun h => hclose T h.2
  have hW := G.scheduled_expectedStateValue_close_initial_of_correction
    x W R c r who s₀ hR hstep T
  have htriangle :
      |G.expectedStateValue σ s₀ T (fun s => V T s who) - W s₀ who| ≤
        |G.expectedStateValue σ s₀ T (fun s => V T s who) -
          G.expectedStateValue σ s₀ T (fun s => W s who)| +
        |G.expectedStateValue σ s₀ T (fun s => W s who) - W s₀ who| := by
    calc
      |_ - _| = |(_ - G.expectedStateValue σ s₀ T
          (fun s => W s who)) +
          (G.expectedStateValue σ s₀ T (fun s => W s who) -
            W s₀ who)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  linarith

/-- Deviation-side certificate estimate with a bounded Poisson correction. -/
theorem scheduled_deviation_expectedTarget_le_initial_of_correction
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (x : ℕ → G.StationaryMixedProfile)
    (V : ℕ → G.State → Payoff ι) (W : G.State → Payoff ι)
    (R : ℕ → G.State → Payoff ι) (q c r : ℕ → ℝ)
    (who : ι) (dev : G.BehaviorStrategy who) (s₀ : G.State)
    (hclose : ∀ t s, |V t s who - W s who| ≤ q t)
    (hR : ∀ t s, |R t s who| ≤ c t)
    (hstep : ∀ t s (d : PMF (G.Act who)),
      expect (pmfPi (Function.update (x t s) who d)) (fun a =>
          expect (G.transition s a)
            (fun s' => W s' who + R (t + 1) s' who)) ≤
        W s who + R t s who + r t)
    (T : ℕ) :
    G.expectedStateValue
        (Function.update (G.scheduledMarkovBehaviorProfile x) who dev)
        s₀ T (fun s => V T s who) ≤
      W s₀ who + q T + c 0 + c T +
        ∑ t ∈ Finset.range T, r t := by
  let σ := Function.update (G.scheduledMarkovBehaviorProfile x) who dev
  have hVW : G.expectedStateValue σ s₀ T (fun s => V T s who) ≤
      G.expectedStateValue σ s₀ T (fun s => W s who) + q T := by
    calc
      G.expectedStateValue σ s₀ T (fun s => V T s who) ≤
          expect (G.histDist σ s₀ T) (fun h => W h.2 who + q T) := by
        apply expect_mono
        intro h
        have hh := (abs_le.mp (hclose T h.2)).2
        linarith
      _ = G.expectedStateValue σ s₀ T (fun s => W s who) + q T := by
        rw [expect_add, expect_const]
        rfl
  have hW :=
    G.scheduled_deviation_expectedStateValue_le_initial_of_correction
      x W R c r who dev s₀ hR hstep T
  linarith

/-- Average on-path target estimate retaining time-dependent Poisson
corrections. -/
theorem scheduled_targetAverage_close_initial_of_correction
    (G : StochasticGame ι) [Fintype ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (x : ℕ → G.StationaryMixedProfile)
    (V : ℕ → G.State → Payoff ι) (W : G.State → Payoff ι)
    (R : ℕ → G.State → Payoff ι) (q c r : ℕ → ℝ)
    (who : ι) (s₀ : G.State)
    (hclose : ∀ t s, |V t s who - W s who| ≤ q t)
    (hR : ∀ t s, |R t s who| ≤ c t)
    (hstep : ∀ t s,
      |expect (pmfPi (x t s)) (fun a =>
          expect (G.transition s a)
            (fun s' => W s' who + R (t + 1) s' who)) -
        (W s who + R t s who)| ≤ r t)
    {T : ℕ} (hT : 0 < T) :
    |(T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
          G.expectedStateValue (G.scheduledMarkovBehaviorProfile x) s₀ t
            (fun s => V t s who) - W s₀ who| ≤
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
        (q t + c 0 + c t + ∑ k ∈ Finset.range t, r k) := by
  let A : ℕ → ℝ := fun t =>
    G.expectedStateValue (G.scheduledMarkovBehaviorProfile x) s₀ t
      (fun s => V t s who)
  let E : ℕ → ℝ := fun t =>
    q t + c 0 + c t + ∑ k ∈ Finset.range t, r k
  have hpoint : ∀ t, |A t - W s₀ who| ≤ E t := fun t =>
    G.scheduled_expectedTarget_close_initial_of_correction
      x V W R q c r who s₀ hclose hR hstep t
  have hsum : |∑ t ∈ Finset.range T, (A t - W s₀ who)| ≤
      ∑ t ∈ Finset.range T, E t := by
    calc
      |∑ t ∈ Finset.range T, (A t - W s₀ who)| ≤
          ∑ t ∈ Finset.range T, |A t - W s₀ who| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ Finset.range T, E t :=
        Finset.sum_le_sum fun t _ => hpoint t
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  have hinv : 0 ≤ (T : ℝ)⁻¹ := inv_nonneg.mpr hTreal.le
  have hid : (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, A t - W s₀ who =
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, (A t - W s₀ who) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp [ne_of_gt hTreal]
  change |(T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, A t - W s₀ who| ≤
    (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, E t
  rw [hid, abs_mul, abs_of_nonneg hinv]
  exact mul_le_mul_of_nonneg_left hsum hinv

/-- Average deviation estimate retaining time-dependent Poisson
corrections. -/
theorem scheduled_deviation_targetAverage_le_initial_of_correction
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (x : ℕ → G.StationaryMixedProfile)
    (V : ℕ → G.State → Payoff ι) (W : G.State → Payoff ι)
    (R : ℕ → G.State → Payoff ι) (q c r : ℕ → ℝ)
    (who : ι) (dev : G.BehaviorStrategy who) (s₀ : G.State)
    (hclose : ∀ t s, |V t s who - W s who| ≤ q t)
    (hR : ∀ t s, |R t s who| ≤ c t)
    (hstep : ∀ t s (d : PMF (G.Act who)),
      expect (pmfPi (Function.update (x t s) who d)) (fun a =>
          expect (G.transition s a)
            (fun s' => W s' who + R (t + 1) s' who)) ≤
        W s who + R t s who + r t)
    {T : ℕ} (hT : 0 < T) :
    (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
        G.expectedStateValue
          (Function.update (G.scheduledMarkovBehaviorProfile x) who dev)
          s₀ t (fun s => V t s who) ≤
      W s₀ who + (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
        (q t + c 0 + c t + ∑ k ∈ Finset.range t, r k) := by
  let A : ℕ → ℝ := fun t => G.expectedStateValue
    (Function.update (G.scheduledMarkovBehaviorProfile x) who dev)
    s₀ t (fun s => V t s who)
  let E : ℕ → ℝ := fun t =>
    q t + c 0 + c t + ∑ k ∈ Finset.range t, r k
  have hpoint : ∀ t, A t ≤ W s₀ who + E t := by
    intro t
    dsimp only [A, E]
    simpa only [add_assoc] using
      G.scheduled_deviation_expectedTarget_le_initial_of_correction
        x V W R q c r who dev s₀ hclose hR hstep t
  have hsum : (∑ t ∈ Finset.range T, A t) ≤
      ∑ t ∈ Finset.range T, (W s₀ who + E t) :=
    Finset.sum_le_sum fun t _ => hpoint t
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  have hinv : 0 ≤ (T : ℝ)⁻¹ := inv_nonneg.mpr hTreal.le
  have hmul := mul_le_mul_of_nonneg_left hsum hinv
  change (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, A t ≤
    W s₀ who + (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, E t
  calc
    (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, A t ≤
        (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, (W s₀ who + E t) := hmul
    _ = W s₀ who + (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, E t := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp [ne_of_gt hTreal]

/-- Corrected-potential schedule criterion for a uniform equilibrium payoff.
This is the cancellation-aware replacement for the scalar harmonic-drift
criterion: Poisson corrections are paid through their endpoint bounds. -/
theorem isUniformEquilibriumPayoff_of_scheduledFink_correctedTarget
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State) (W : G.State → Payoff ι)
    (hcert : ∀ η : ℝ, 0 < η →
      ∃ (β : ℕ → ℝ) (x : ℕ → G.StationaryMixedProfile)
        (V R : ℕ → G.State → Payoff ι)
        (e B q c r : ℕ → ℝ) (T₀ : ℕ),
        G.IsDiscountedStationaryBellmanSchedule β x V ∧
          (∀ t, β t < 1) ∧ G.IsScheduledFinkSwitchBound β V e ∧
          (∀ t s who, |G.scheduledFinkBias β V t s who| ≤ B t) ∧
          (∀ t s who, |V t s who - W s who| ≤ q t) ∧
          (∀ t s who, |R t s who| ≤ c t) ∧
          (∀ t s who,
            |expect (pmfPi (x t s)) (fun a =>
                expect (G.transition s a)
                  (fun s' => W s' who + R (t + 1) s' who)) -
              (W s who + R t s who)| ≤ r t) ∧
          (∀ t s who (d : PMF (G.Act who)),
            expect (pmfPi (Function.update (x t s) who d)) (fun a =>
                expect (G.transition s a)
                  (fun s' => W s' who + R (t + 1) s' who)) ≤
              W s who + R t s who + r t) ∧
          ∀ T, T₀ ≤ T → 0 < T ∧
            ((B 0 + B T) / (T : ℝ) +
              (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, e t ≤ η) ∧
            (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
              (q t + c 0 + c t +
                ∑ k ∈ Finset.range t, r k) ≤ η) :
    G.IsUniformEquilibriumPayoff s₀ (W s₀) := by
  apply G.isUniformEquilibriumPayoff_of_scheduledFink_targetAverages s₀ (W s₀)
  intro η hη
  obtain ⟨β, x, V, R, e, B, q, c, r, T₀,
      hF, hβ1, hswitch, hbias, hclose, hR,
      hharmonic, hexcessive, hasymp⟩ := hcert η hη
  refine ⟨β, x, V, e, B, T₀, hF, hβ1, hswitch, hbias, ?_⟩
  intro T hT
  obtain ⟨hTpos, hboundary, htarget⟩ := hasymp T hT
  refine ⟨hTpos, hboundary, ?_, ?_⟩
  · intro who
    exact (G.scheduled_targetAverage_close_initial_of_correction
      x V W R q c r who s₀ (fun t s => hclose t s who)
      (fun t s => hR t s who) (fun t s => hharmonic t s who) hTpos).trans
        htarget
  · intro who dev
    have hdev := G.scheduled_deviation_targetAverage_le_initial_of_correction
      x V W R q c r who dev s₀ (fun t s => hclose t s who)
        (fun t s => hR t s who)
        (fun t s d => hexcessive t s who d) hTpos
    linarith

-- ============================================================================
-- Calendar schedules indexed by discounted Fink fixed points
-- ============================================================================

/-- Read a discounted fixed-point family according to the calendar index
selector `κ`. -/
def indexedFinkDiscount (β : ℕ → ℝ) (κ : ℕ → ℕ) (t : ℕ) : ℝ := β (κ t)

/-- Stationary profile scheduled at time `t` by the index selector `κ`. -/
def indexedFinkProfile (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : ℕ → G.finkDomain U) (κ : ℕ → ℕ) :
    ℕ → G.StationaryMixedProfile :=
  fun t => G.finkProfile (z (κ t))

/-- Continuation values scheduled at time `t` by `κ`. -/
def indexedFinkValue (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : ℕ → G.finkDomain U) (κ : ℕ → ℕ) :
    ℕ → G.State → Payoff ι :=
  fun t => G.finkValue (z (κ t))

/-- Natural uniform bound on the scaled bias of discounted fixed point `n`. -/
def finkScaledBiasBound (β : ℕ → ℝ) (U : ℝ) (n : ℕ) : ℝ :=
  (β n / (1 - β n)) * U

/-- Activation times for a slow calendar.  Layer `n` is not activated before
calendar time `n * |B n|`, and consecutive activation times are distinct. -/
noncomputable def slowCalendarStart (B : ℕ → ℝ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => max (slowCalendarStart B n + 1)
      (Nat.ceil (((n + 1 : ℕ) : ℝ) * |B (n + 1)|))

theorem strictMono_slowCalendarStart (B : ℕ → ℝ) :
    StrictMono (slowCalendarStart B) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [slowCalendarStart]
  exact (Nat.lt_succ_self _).trans_le (le_max_left _ _)

theorem slowCalendarStart_cost_le (B : ℕ → ℝ) (n : ℕ) :
    (n : ℝ) * |B n| ≤ (slowCalendarStart B n : ℝ) := by
  cases n with
  | zero => simp [slowCalendarStart]
  | succ n =>
      rw [slowCalendarStart]
      exact (Nat.le_ceil _).trans (by
        exact_mod_cast (le_max_right
          (slowCalendarStart B n + 1)
          (Nat.ceil ((((n + 1 : ℕ) : ℝ) * |B (n + 1)|)))))

/-- The slow unit-step calendar is the greatest layer whose activation time
has arrived. -/
noncomputable def slowUnitStepCalendar (B : ℕ → ℝ) (t : ℕ) : ℕ :=
  Nat.findGreatest (fun n => slowCalendarStart B n ≤ t) t

@[simp] theorem slowUnitStepCalendar_zero (B : ℕ → ℝ) :
    slowUnitStepCalendar B 0 = 0 := by
  simp [slowUnitStepCalendar]

theorem slowCalendarStart_slowUnitStepCalendar_le
    (B : ℕ → ℝ) (t : ℕ) :
    slowCalendarStart B (slowUnitStepCalendar B t) ≤ t := by
  exact Nat.findGreatest_spec (P := fun n => slowCalendarStart B n ≤ t)
    (Nat.zero_le t) (by simp [slowCalendarStart])

theorem slowUnitStepCalendar_slowCalendarStart
    (B : ℕ → ℝ) (n : ℕ) :
    slowUnitStepCalendar B (slowCalendarStart B n) = n := by
  apply le_antisymm
  · let k := slowUnitStepCalendar B (slowCalendarStart B n)
    have hkStart : slowCalendarStart B k ≤ slowCalendarStart B n :=
      slowCalendarStart_slowUnitStepCalendar_le B (slowCalendarStart B n)
    by_contra hnot
    have hnk : n < k := Nat.lt_of_not_ge hnot
    have hlt := strictMono_slowCalendarStart B hnk
    omega
  · have hnStart : n ≤ slowCalendarStart B n :=
      (strictMono_slowCalendarStart B).id_le n
    exact Nat.le_findGreatest hnStart le_rfl

/-- Calendar layer `n` occupies exactly the half-open activation interval
from its own start time to the next layer's start time. -/
theorem slowUnitStepCalendar_eq_iff
    (B : ℕ → ℝ) (t n : ℕ) :
    slowUnitStepCalendar B t = n ↔
      slowCalendarStart B n ≤ t ∧ t < slowCalendarStart B (n + 1) := by
  constructor
  · intro hν
    constructor
    · simpa only [hν] using slowCalendarStart_slowUnitStepCalendar_le B t
    · by_contra hnot
      have hnext : slowCalendarStart B (n + 1) ≤ t :=
        Nat.le_of_not_gt hnot
      have hnextT : n + 1 ≤ t :=
        (strictMono_slowCalendarStart B).id_le (n + 1) |>.trans hnext
      have hle : n + 1 ≤ slowUnitStepCalendar B t :=
        Nat.le_findGreatest hnextT hnext
      rw [hν] at hle
      omega
  · rintro ⟨hstart, hnext⟩
    have hnt : n ≤ t :=
      (strictMono_slowCalendarStart B).id_le n |>.trans hstart
    have hnle : n ≤ slowUnitStepCalendar B t :=
      Nat.le_findGreatest hnt hstart
    apply le_antisymm
    · by_contra hnot
      have hnextle : n + 1 ≤ slowUnitStepCalendar B t := by omega
      have hmono := (strictMono_slowCalendarStart B).monotone hnextle
      have hgreatest := slowCalendarStart_slowUnitStepCalendar_le B t
      omega
    · exact hnle

/-- Number of calendar stages for which one slow-calendar layer is held. -/
noncomputable def slowCalendarBlockLength (B : ℕ → ℝ) (n : ℕ) : ℕ :=
  slowCalendarStart B (n + 1) - slowCalendarStart B n

theorem slowCalendarStart_add_blockLength (B : ℕ → ℝ) (n : ℕ) :
    slowCalendarStart B n + slowCalendarBlockLength B n =
      slowCalendarStart B (n + 1) := by
  unfold slowCalendarBlockLength
  exact Nat.add_sub_of_le
    (strictMono_slowCalendarStart B (Nat.lt_succ_self n)).le

/-- Sharp adjacent switching charge obtained by centering the scaled Fink
bias at a target vector `W`.  The first term is the actual relative-bias
change; the second is only the change of discount scale applied to `W`. -/
def indexedFinkRelativeSwitchError (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ) {U₀ : ℝ}
    (z : ℕ → G.finkDomain U₀) (W : G.State → Payoff ι)
    (κ : ℕ → ℕ) (t : ℕ) : ℝ :=
  ‖G.finkRelativeBias (β (κ (t + 1))) W (z (κ (t + 1))) -
      G.finkRelativeBias (β (κ t)) W (z (κ t))‖ +
    |β (κ (t + 1)) / (1 - β (κ (t + 1))) -
      β (κ t) / (1 - β (κ t))| * U

/-- Charge zero while an indexed schedule stays on one fixed point and the
sum of the adjacent bias bounds when it switches. -/
def indexedFinkSwitchError (β : ℕ → ℝ) (U : ℝ) (κ : ℕ → ℕ)
    (t : ℕ) : ℝ :=
  if κ (t + 1) = κ t then 0
  else finkScaledBiasBound β U (κ (t + 1)) +
    finkScaledBiasBound β U (κ t)

/-- The exact quantitative calendar-selection property required to amortize
scaled Fink biases while keeping accumulated harmonic/excessive drift
negligible. -/
def IsIndexedFinkCalendarSelectable (β : ℕ → ℝ) (U : ℝ)
    (q r : ℕ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ (κ : ℕ → ℕ) (T₀ : ℕ),
    ∀ T, T₀ ≤ T → 0 < T ∧
      ((finkScaledBiasBound β U (κ 0) +
            finkScaledBiasBound β U (κ T)) / (T : ℝ) +
          (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
            indexedFinkSwitchError β U κ t ≤ η) ∧
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
        (q (κ t) + ∑ k ∈ Finset.range t, r (κ k)) ≤ η

/-- Calendar selectability with the sharp centered adjacent-switch charge.
Unlike `IsIndexedFinkCalendarSelectable`, this interface can exploit
cancellation between neighboring scaled discounted values. -/
def IsIndexedFinkRelativeCalendarSelectable (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ) {U₀ : ℝ}
    (z : ℕ → G.finkDomain U₀) (W : G.State → Payoff ι)
    (q r : ℕ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ (κ : ℕ → ℕ) (T₀ : ℕ),
    ∀ T, T₀ ≤ T → 0 < T ∧
      ((finkScaledBiasBound β U (κ 0) +
            finkScaledBiasBound β U (κ T)) / (T : ℝ) +
          (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
            G.indexedFinkRelativeSwitchError β U z W κ t ≤ η) ∧
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
        (q (κ t) + ∑ k ∈ Finset.range t, r (κ k)) ≤ η

/-- Calendar selectability in the exact cancellation-aware form produced by
the verified reference hierarchy.  The correction is read on the same
calendar as the Fink fixed points; its endpoint norms are paid once, while
its canonical adjacent step error is accumulated by the potential telescope. -/
def IsIndexedFinkCorrectedCalendarSelectable (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ) {U₀ : ℝ}
    (z : ℕ → G.finkDomain U₀) (W : G.State → Payoff ι)
    (R : ℕ → G.State → Payoff ι) (q : ℕ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ (κ : ℕ → ℕ) (T₀ : ℕ),
    ∀ T, T₀ ≤ T → 0 < T ∧
      ((finkScaledBiasBound β U (κ 0) +
            finkScaledBiasBound β U (κ T)) / (T : ℝ) +
          (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
            G.indexedFinkRelativeSwitchError β U z W κ t ≤ η) ∧
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
        (q (κ t) + ‖R (κ 0)‖ + ‖R (κ t)‖ +
          ∑ k ∈ Finset.range t,
            G.finkCorrectedTargetStepError W (R ∘ κ) (z ∘ κ) k) ≤ η

/-- Indexed Fink fixed points form a calendar-time Bellman schedule. -/
theorem isDiscountedStationaryBellmanSchedule_indexedFink
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : ℕ → G.finkDomain U)
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (κ : ℕ → ℕ) :
    G.IsDiscountedStationaryBellmanSchedule
      (indexedFinkDiscount β κ) (G.indexedFinkProfile z κ)
        (G.indexedFinkValue z κ) := by
  intro t
  exact G.isDiscountedStationaryBellmanEq_of_finkMap_fixedPoint
    (β (κ t)) U (hβ0 (κ t)) (hβ1 (κ t)).le hpay
      (z (κ t)) (hfix (κ t))

/-- The scheduled bias of an indexed fixed point obeys its natural scaled
cube bound. -/
theorem abs_scheduledFinkBias_indexed_le
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n < 1) (z : ℕ → G.finkDomain U)
    (κ : ℕ → ℕ) (t : ℕ) (s : G.State) (who : ι) :
    |G.scheduledFinkBias (indexedFinkDiscount β κ)
        (G.indexedFinkValue z κ) t s who| ≤
      finkScaledBiasBound β U (κ t) := by
  have hratio : 0 ≤ β (κ t) / (1 - β (κ t)) :=
    div_nonneg (hβ0 (κ t)) (by linarith [hβ1 (κ t)])
  rw [scheduledFinkBias]
  change |(β (κ t) / (1 - β (κ t))) * G.finkValue (z (κ t)) s who| ≤ _
  rw [abs_mul, abs_of_nonneg hratio]
  exact mul_le_mul_of_nonneg_left (G.abs_finkValue_le (z (κ t)) s who) hratio

/-- The centered adjacent charge is a valid switching-error bound.  This is
the exact dictionary between absolute scheduled biases and the relative
biases controlled by the finite Fink hierarchy. -/
theorem isScheduledFinkSwitchBound_indexed_relative
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ) (z : ℕ → G.finkDomain U)
    (W : G.State → Payoff ι)
    (hW : ∀ s who, |W s who| ≤ U) (κ : ℕ → ℕ) :
    G.IsScheduledFinkSwitchBound (indexedFinkDiscount β κ)
      (G.indexedFinkValue z κ)
      (G.indexedFinkRelativeSwitchError β U z W κ) := by
  intro t s who
  let a₁ := β (κ (t + 1)) / (1 - β (κ (t + 1)))
  let a₀ := β (κ t) / (1 - β (κ t))
  let J₁ := G.finkRelativeBias (β (κ (t + 1))) W (z (κ (t + 1)))
  let J₀ := G.finkRelativeBias (β (κ t)) W (z (κ t))
  have hdecomp :
      G.scheduledFinkBias (indexedFinkDiscount β κ)
          (G.indexedFinkValue z κ) (t + 1) s who -
        G.scheduledFinkBias (indexedFinkDiscount β κ)
          (G.indexedFinkValue z κ) t s who =
      (J₁ - J₀) s who + (a₁ - a₀) * W s who := by
    simp only [scheduledFinkBias, indexedFinkDiscount, indexedFinkValue,
      J₁, J₀, a₁, a₀, finkRelativeBias, Pi.sub_apply]
    ring
  have hstate : ‖(J₁ - J₀) s‖ ≤ ‖J₁ - J₀‖ := by
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg (J₁ - J₀))).mp le_rfl s
  have hcoord : |(J₁ - J₀) s who| ≤ ‖J₁ - J₀‖ := by
    have hplayer : ‖(J₁ - J₀) s who‖ ≤ ‖(J₁ - J₀) s‖ := by
      exact (pi_norm_le_iff_of_nonneg
        (norm_nonneg ((J₁ - J₀) s))).mp le_rfl who
    simpa only [Real.norm_eq_abs] using hplayer.trans hstate
  have hscale : |(a₁ - a₀) * W s who| ≤ |a₁ - a₀| * U := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hW s who) (abs_nonneg _)
  rw [hdecomp]
  calc
    |(J₁ - J₀) s who + (a₁ - a₀) * W s who| ≤
        |(J₁ - J₀) s who| + |(a₁ - a₀) * W s who| :=
      abs_add_le _ _
    _ ≤ ‖J₁ - J₀‖ + |a₁ - a₀| * U :=
      add_le_add hcoord hscale
    _ = G.indexedFinkRelativeSwitchError β U z W κ t := by
      rfl

/-- The adjacent-bias charge is a valid switching-error bound for every
indexed Fink schedule. -/
theorem isScheduledFinkSwitchBound_indexed
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n < 1) (z : ℕ → G.finkDomain U)
    (κ : ℕ → ℕ) :
    G.IsScheduledFinkSwitchBound (indexedFinkDiscount β κ)
      (G.indexedFinkValue z κ) (indexedFinkSwitchError β U κ) := by
  intro t s who
  by_cases hκ : κ (t + 1) = κ t
  · simp [indexedFinkSwitchError, hκ, scheduledFinkBias,
      indexedFinkDiscount, indexedFinkValue]
  · have hnext := G.abs_scheduledFinkBias_indexed_le
      β U hβ0 hβ1 z κ (t + 1) s who
    have hcurrent := G.abs_scheduledFinkBias_indexed_le
      β U hβ0 hβ1 z κ t s who
    calc
      |G.scheduledFinkBias (indexedFinkDiscount β κ)
          (G.indexedFinkValue z κ) (t + 1) s who -
        G.scheduledFinkBias (indexedFinkDiscount β κ)
          (G.indexedFinkValue z κ) t s who| ≤
          |G.scheduledFinkBias (indexedFinkDiscount β κ)
            (G.indexedFinkValue z κ) (t + 1) s who| +
          |G.scheduledFinkBias (indexedFinkDiscount β κ)
            (G.indexedFinkValue z κ) t s who| := abs_sub _ _
      _ ≤ finkScaledBiasBound β U (κ (t + 1)) +
          finkScaledBiasBound β U (κ t) := add_le_add hnext hcurrent
      _ = indexedFinkSwitchError β U κ t := by
        simp [indexedFinkSwitchError, hκ]

/-- Conditional indexed-family bridge to a uniform equilibrium payoff.  All
game-theoretic verification is discharged here; the remaining hypothesis is
the quantitative calendar selection condition balancing scaled biases against
the accumulated harmonic/excessive residuals. -/
theorem isUniformEquilibriumPayoff_of_indexedFinkFixedPoints
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (s₀ : G.State) (β : ℕ → ℝ) (U : ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : ℕ → G.finkDomain U) (W : G.State → Payoff ι)
    (q r : ℕ → ℝ)
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (hclose : ∀ n s who, |G.finkValue (z n) s who - W s who| ≤ q n)
    (hharmonic : ∀ n s who,
      |expect (pmfPi (G.finkProfile (z n) s)) (fun a =>
          expect (G.transition s a) (fun s' => W s' who)) - W s who| ≤ r n)
    (hexcessive : ∀ n s who (d : PMF (G.Act who)),
      expect (pmfPi (Function.update (G.finkProfile (z n) s) who d))
          (fun a => expect (G.transition s a) (fun s' => W s' who)) ≤
        W s who + r n)
    (hselect : IsIndexedFinkCalendarSelectable β U q r) :
    G.IsUniformEquilibriumPayoff s₀ (W s₀) := by
  apply G.isUniformEquilibriumPayoff_of_scheduledFink_harmonicTarget s₀ W
  intro η hη
  obtain ⟨κ, T₀, hκ⟩ := hselect η hη
  refine ⟨indexedFinkDiscount β κ, G.indexedFinkProfile z κ,
    G.indexedFinkValue z κ, indexedFinkSwitchError β U κ,
    (fun t => finkScaledBiasBound β U (κ t)),
    (fun t => q (κ t)), (fun t => r (κ t)), T₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact G.isDiscountedStationaryBellmanSchedule_indexedFink
      β U hβ0 hβ1 hpay z hfix κ
  · exact fun t => hβ1 (κ t)
  · exact G.isScheduledFinkSwitchBound_indexed β U hβ0 hβ1 z κ
  · exact G.abs_scheduledFinkBias_indexed_le β U hβ0 hβ1 z κ
  · intro t s who
    exact hclose (κ t) s who
  · intro t s who
    exact hharmonic (κ t) s who
  · intro t s who d
    exact hexcessive (κ t) s who d
  · exact hκ

/-- Sharp centered-switch version of the indexed-family bridge.  Its only
schedule cost is the actual adjacent relative-bias motion plus the adjacent
change of discount scale on the bounded target `W`. -/
theorem isUniformEquilibriumPayoff_of_indexedFinkFixedPoints_relativeSwitch
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (s₀ : G.State) (β : ℕ → ℝ) (U : ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : ℕ → G.finkDomain U) (W : G.State → Payoff ι)
    (hW : ∀ s who, |W s who| ≤ U) (q r : ℕ → ℝ)
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (hclose : ∀ n s who, |G.finkValue (z n) s who - W s who| ≤ q n)
    (hharmonic : ∀ n s who,
      |expect (pmfPi (G.finkProfile (z n) s)) (fun a =>
          expect (G.transition s a) (fun s' => W s' who)) - W s who| ≤ r n)
    (hexcessive : ∀ n s who (d : PMF (G.Act who)),
      expect (pmfPi (Function.update (G.finkProfile (z n) s) who d))
          (fun a => expect (G.transition s a) (fun s' => W s' who)) ≤
        W s who + r n)
    (hselect : G.IsIndexedFinkRelativeCalendarSelectable
      β U z W q r) :
    G.IsUniformEquilibriumPayoff s₀ (W s₀) := by
  apply G.isUniformEquilibriumPayoff_of_scheduledFink_harmonicTarget s₀ W
  intro η hη
  obtain ⟨κ, T₀, hκ⟩ := hselect η hη
  refine ⟨indexedFinkDiscount β κ, G.indexedFinkProfile z κ,
    G.indexedFinkValue z κ,
    G.indexedFinkRelativeSwitchError β U z W κ,
    (fun t => finkScaledBiasBound β U (κ t)),
    (fun t => q (κ t)), (fun t => r (κ t)), T₀,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact G.isDiscountedStationaryBellmanSchedule_indexedFink
      β U hβ0 hβ1 hpay z hfix κ
  · exact fun t => hβ1 (κ t)
  · exact G.isScheduledFinkSwitchBound_indexed_relative β U z W hW κ
  · exact G.abs_scheduledFinkBias_indexed_le β U hβ0 hβ1 z κ
  · intro t s who
    exact hclose (κ t) s who
  · intro t s who
    exact hharmonic (κ t) s who
  · intro t s who d
    exact hexcessive (κ t) s who d
  · exact hκ

/-- End-to-end bridge from the corrected calendar produced by the reference
hierarchy to a uniform equilibrium payoff.  All Bellman, switching,
on-profile, mixed-deviation, and history-dependent verification is discharged
here; only `IsIndexedFinkCorrectedCalendarSelectable` remains quantitative. -/
theorem isUniformEquilibriumPayoff_of_indexedFinkFixedPoints_correctedTarget
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (s₀ : G.State) (β : ℕ → ℝ) (U : ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : ℕ → G.finkDomain U) (W : G.State → Payoff ι)
    (hW : ∀ s who, |W s who| ≤ U)
    (R : ℕ → G.State → Payoff ι) (q : ℕ → ℝ)
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (hclose : ∀ n s who, |G.finkValue (z n) s who - W s who| ≤ q n)
    (hselect : G.IsIndexedFinkCorrectedCalendarSelectable
      β U z W R q) :
    G.IsUniformEquilibriumPayoff s₀ (W s₀) := by
  apply G.isUniformEquilibriumPayoff_of_scheduledFink_correctedTarget s₀ W
  intro η hη
  obtain ⟨κ, T₀, hκ⟩ := hselect η hη
  refine ⟨indexedFinkDiscount β κ, G.indexedFinkProfile z κ,
    G.indexedFinkValue z κ, R ∘ κ,
    G.indexedFinkRelativeSwitchError β U z W κ,
    (fun t => finkScaledBiasBound β U (κ t)),
    (q ∘ κ), (fun t => ‖R (κ t)‖),
    (fun t => G.finkCorrectedTargetStepError W (R ∘ κ) (z ∘ κ) t),
    T₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact G.isDiscountedStationaryBellmanSchedule_indexedFink
      β U hβ0 hβ1 hpay z hfix κ
  · exact fun t => hβ1 (κ t)
  · exact G.isScheduledFinkSwitchBound_indexed_relative β U z W hW κ
  · exact G.abs_scheduledFinkBias_indexed_le β U hβ0 hβ1 z κ
  · intro t s who
    exact hclose (κ t) s who
  · intro t s who
    exact G.abs_finkBiasCoordinate_le_norm (R (κ t)) s who
  · intro t s who
    exact G.abs_fink_correctedTarget_onProfile_step_le_stepError
      W (R ∘ κ) (z ∘ κ) t s who
  · intro t s who dev
    exact G.fink_correctedTarget_mixedDeviation_step_le_stepError
      W (R ∘ κ) (z ∘ κ) t s who dev
  · exact hκ

end StochasticGame
end GameTheory
