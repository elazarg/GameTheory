/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.FinkSchedule
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

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

/-- Continuation gains against a fixed target converge along a convergent
Fink-domain sequence. -/
theorem tendsto_finkContinuationGain
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim)) (W : G.State → Payoff ι)
    (s : G.State) (who : ι) (d : G.Act who) :
    Tendsto (fun n => G.finkContinuationGain W (z n) s who d) atTop
      (nhds (G.finkContinuationGain W zlim s who d)) := by
  have hdev := G.tendsto_finkProfile_pureDeviationContinuation hz
    (fun s' => W s' who) s who d
  have hbase := G.tendsto_finkProfile_continuation hz
    (fun s' => W s' who) s
  simpa only [finkContinuationGain] using hdev.sub hbase

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

/-- Radial compactification of a finite-dimensional bias vector.  Bounded
biases remain in the open unit ball, while an unbounded sequence can converge
to a direction on its boundary. -/
def compactifyFinkBias (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι]
    (H : G.State → Payoff ι) : G.State → Payoff ι :=
  (1 / (1 + ‖H‖)) • H

/-- The multiplier which turns the first-order value error `Vβ - W` into
the radially compactified relative bias.  A boundary bias direction forces
this multiplier to become the next diverging lexicographic scale. -/
def finkProjectiveBiasScale (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (β : ℝ) (W : G.State → Payoff ι) {U : ℝ}
    (z : G.finkDomain U) : ℝ :=
  (β / (1 - β)) / (1 + ‖G.finkRelativeBias β W z‖)

/-- Radial compactification of the relative bias is exactly the value error
rescaled by `finkProjectiveBiasScale`. -/
theorem compactify_finkRelativeBias_eq
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)] (β : ℝ)
    (W : G.State → Payoff ι) {U : ℝ} (z : G.finkDomain U) :
    G.compactifyFinkBias (G.finkRelativeBias β W z) =
      G.finkProjectiveBiasScale β W z • (G.finkValue z - W) := by
  ext s who
  simp only [compactifyFinkBias, finkProjectiveBiasScale,
    finkRelativeBias, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

theorem norm_compactify_finkRelativeBias_eq
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)] {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (W : G.State → Payoff ι) {U : ℝ} (z : G.finkDomain U) :
    ‖G.compactifyFinkBias (G.finkRelativeBias β W z)‖ =
      G.finkProjectiveBiasScale β W z * ‖G.finkValue z - W‖ := by
  rw [G.compactify_finkRelativeBias_eq]
  have hscale : 0 ≤ G.finkProjectiveBiasScale β W z := by
    exact div_nonneg (div_nonneg hβ0 (by linarith)) (by positivity)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale]

theorem finkContinuationGain_compactifyFinkBias
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (H : G.State → Payoff ι)
    {U : ℝ} (z : G.finkDomain U) (s : G.State)
    (who : ι) (d : G.Act who) :
    G.finkContinuationGain (G.compactifyFinkBias H) z s who d =
      (1 / (1 + ‖H‖)) * G.finkContinuationGain H z s who d := by
  unfold compactifyFinkBias
  exact G.finkContinuationGain_smul (1 / (1 + ‖H‖)) H z s who d

theorem norm_compactifyFinkBias_eq
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    (H : G.State → Payoff ι) :
    ‖G.compactifyFinkBias H‖ = ‖H‖ / (1 + ‖H‖) := by
  have hden : 0 < 1 + ‖H‖ := by positivity
  simp [compactifyFinkBias, norm_smul, Real.norm_eq_abs,
    abs_of_pos hden, div_eq_mul_inv]
  ring

theorem norm_compactifyFinkBias_lt_one
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    (H : G.State → Payoff ι) :
    ‖G.compactifyFinkBias H‖ < 1 := by
  rw [G.norm_compactifyFinkBias_eq H]
  exact (div_lt_one (by positivity)).2 (by linarith [norm_nonneg H])

/-- Inverse radial chart on the open unit bias ball. -/
def decompactifyFinkBias (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι]
    (K : G.State → Payoff ι) : G.State → Payoff ι :=
  (1 / (1 - ‖K‖)) • K

@[simp] theorem decompactify_compactifyFinkBias
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    (H : G.State → Payoff ι) :
    G.decompactifyFinkBias (G.compactifyFinkBias H) = H := by
  rw [decompactifyFinkBias, G.norm_compactifyFinkBias_eq H,
    compactifyFinkBias, smul_smul]
  have hden : 1 + ‖H‖ ≠ 0 := ne_of_gt (by positivity)
  convert one_smul ℝ H using 1
  field_simp [hden]
  ring_nf

theorem compactifyFinkBias_mem_closedBall
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    (H : G.State → Payoff ι) :
    G.compactifyFinkBias H ∈
      Metric.closedBall (0 : G.State → Payoff ι) 1 := by
  rw [Metric.mem_closedBall]
  simpa only [dist_zero_right] using (G.norm_compactifyFinkBias_lt_one H).le

/-- Reaching the boundary of the radial compactification is exactly the
unbounded-bias regime: the norms of the original biases tend to infinity. -/
theorem tendsto_norm_finkBias_atTop_of_compactify_tendsto_norm_eq_one
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    {H : ℕ → G.State → Payoff ι} {K : G.State → Payoff ι}
    (hlim : Tendsto (G.compactifyFinkBias ∘ H) atTop (nhds K))
    (hK : ‖K‖ = 1) :
    Tendsto (fun n => ‖H n‖) atTop atTop := by
  have hnorm : Tendsto (fun n => ‖G.compactifyFinkBias (H n)‖)
      atTop (nhds 1) := by
    have ht := continuous_norm.tendsto K |>.comp hlim
    simpa only [Function.comp_def, hK] using ht
  refine tendsto_atTop.2 fun b => ?_
  let B := max b 0
  have hB0 : 0 ≤ B := le_max_right b 0
  have hfrac : B / (1 + B) < 1 := by
    exact (div_lt_one (by linarith)).2 (by linarith)
  filter_upwards [hnorm.eventually (eventually_gt_nhds hfrac)] with n hn
  rw [G.norm_compactifyFinkBias_eq] at hn
  have hdenB : 0 < 1 + B := by linarith
  have hdenH : 0 < 1 + ‖H n‖ := by positivity
  rw [div_lt_div_iff₀ hdenB hdenH] at hn
  have hBH : B < ‖H n‖ := by linarith
  exact (le_max_left b 0).trans hBH.le

/-- A projective boundary direction over a convergent Fink value family
creates a genuinely faster scale: the multiplier which rescales
`Vβ - Vlim` to the compactified bias tends to infinity. -/
theorem tendsto_finkProjectiveBiasScale_atTop_of_boundary
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)] {β : ℕ → ℝ} {U : ℝ}
    (hβ0 : ∀ n, 0 ≤ β n) (hβ1 : ∀ n, β n < 1)
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    {K : G.State → Payoff ι}
    (hKlim : Tendsto (G.compactifyFinkBias ∘ fun n =>
      G.finkRelativeBias (β n) (G.finkValue zlim) (z n))
        atTop (nhds K))
    (hKnorm : ‖K‖ = 1) :
    Tendsto (fun n => G.finkProjectiveBiasScale
      (β n) (G.finkValue zlim) (z n)) atTop atTop := by
  have herror : Tendsto (fun n =>
      ‖G.finkValue (z n) - G.finkValue zlim‖) atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℕ => G.finkValue zlim) atTop
        (nhds (G.finkValue zlim)) := tendsto_const_nhds
    have ht := (G.tendsto_finkValue hz).sub hconst
    have hn := ht.norm
    simpa using hn
  have hcompactNorm : Tendsto (fun n =>
      ‖G.compactifyFinkBias
        (G.finkRelativeBias (β n) (G.finkValue zlim) (z n))‖)
      atTop (nhds 1) := by
    have ht := continuous_norm.tendsto K |>.comp hKlim
    simpa only [Function.comp_def, hKnorm] using ht
  refine tendsto_atTop.2 fun b => ?_
  let B := max b 1
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right b 1)
  let ε : ℝ := 1 / (2 * (B + 1))
  have hεpos : 0 < ε := by
    dsimp [ε]
    positivity
  have hBε : B * ε < (1 / 2 : ℝ) := by
    dsimp [ε]
    calc
      B * (1 / (2 * (B + 1))) = B / (2 * (B + 1)) := by ring
      _ < (1 : ℝ) / 2 := by
        rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
        linarith
  filter_upwards
    [hcompactNorm.eventually
        (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
      herror.eventually (eventually_lt_nhds hεpos)] with n hlarge hsmall
  have heq := G.norm_compactify_finkRelativeBias_eq
    (hβ0 n) (hβ1 n) (G.finkValue zlim) (z n)
  have hBscale : B < G.finkProjectiveBiasScale
      (β n) (G.finkValue zlim) (z n) := by
    by_contra hnot
    have hscaleB : G.finkProjectiveBiasScale
        (β n) (G.finkValue zlim) (z n) ≤ B := le_of_not_gt hnot
    have hsmallCompact :
        ‖G.compactifyFinkBias
          (G.finkRelativeBias (β n) (G.finkValue zlim) (z n))‖ <
            (1 / 2 : ℝ) := by
      calc
        ‖G.compactifyFinkBias
            (G.finkRelativeBias (β n) (G.finkValue zlim) (z n))‖ =
            G.finkProjectiveBiasScale
                (β n) (G.finkValue zlim) (z n) *
              ‖G.finkValue (z n) - G.finkValue zlim‖ := heq
        _ ≤ B * ‖G.finkValue (z n) - G.finkValue zlim‖ :=
          mul_le_mul_of_nonneg_right hscaleB (norm_nonneg _)
        _ < B * ε := mul_lt_mul_of_pos_left hsmall hBpos
        _ < (1 / 2 : ℝ) := hBε
    linarith
  exact (le_max_left b 1).trans hBscale.le

/-- Every relative-bias family has a projectively convergent subsequence in
the compactified finite-dimensional bias ball. -/
theorem exists_convergent_compactifiedFinkBias_subsequence
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    (H : ℕ → G.State → Payoff ι) :
    ∃ (Hlim : G.State → Payoff ι) (φ : ℕ → ℕ),
      Hlim ∈ Metric.closedBall (0 : G.State → Payoff ι) 1 ∧
      StrictMono φ ∧
      Tendsto (G.compactifyFinkBias ∘ H ∘ φ) atTop (nhds Hlim) := by
  let K := Metric.closedBall (0 : G.State → Payoff ι) 1
  let y : ℕ → K := fun n =>
    ⟨G.compactifyFinkBias (H n), G.compactifyFinkBias_mem_closedBall (H n)⟩
  letI : CompactSpace K :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
  obtain ⟨ylim, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq y
  refine ⟨ylim.1, φ, ylim.2, hφ, ?_⟩
  have ht := continuous_subtype_val.tendsto ylim |>.comp hlim
  simpa only [y, Function.comp_def] using ht

/-- An interior compactified limit is equivalent to an ordinary finite bias
limit. -/
theorem tendsto_finkBias_of_compactify_tendsto_of_norm_lt_one
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    {H : ℕ → G.State → Payoff ι} {K : G.State → Payoff ι}
    (hlim : Tendsto (G.compactifyFinkBias ∘ H) atTop (nhds K))
    (hK : ‖K‖ < 1) :
    Tendsto H atTop (nhds (G.decompactifyFinkBias K)) := by
  have hden : 1 - ‖K‖ ≠ 0 := by linarith
  have hc : ContinuousAt (G.decompactifyFinkBias) K := by
    unfold decompactifyFinkBias
    fun_prop
  have ht := hc.tendsto.comp hlim
  simpa only [Function.comp_def, G.decompactify_compactifyFinkBias] using ht

/-- Projective compactness dichotomy for finite-dimensional bias families.
After passing to a subsequence, either the compactified limit is interior and
the original biases converge, or the limit lies on the unit boundary and
records a higher-order bias direction. -/
theorem exists_finkBias_subsequence_interior_or_direction
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    (H : ℕ → G.State → Payoff ι) :
    ∃ (K : G.State → Payoff ι) (φ : ℕ → ℕ),
      StrictMono φ ∧
      Tendsto (G.compactifyFinkBias ∘ H ∘ φ) atTop (nhds K) ∧
      ((‖K‖ < 1 ∧
          Tendsto (H ∘ φ) atTop (nhds (G.decompactifyFinkBias K))) ∨
        (‖K‖ = 1 ∧ Tendsto (fun n => ‖H (φ n)‖) atTop atTop)) := by
  obtain ⟨K, φ, hKmem, hφ, hlim⟩ :=
    G.exists_convergent_compactifiedFinkBias_subsequence H
  have hKle : ‖K‖ ≤ 1 := by
    rw [Metric.mem_closedBall] at hKmem
    simpa only [dist_zero_right] using hKmem
  refine ⟨K, φ, hφ, hlim, ?_⟩
  by_cases hKlt : ‖K‖ < 1
  · left
    refine ⟨hKlt, ?_⟩
    exact G.tendsto_finkBias_of_compactify_tendsto_of_norm_lt_one
      (H := H ∘ φ) (K := K) (by simpa only [Function.comp_def] using hlim) hKlt
  · right
    have hKeq : ‖K‖ = 1 := le_antisymm hKle (le_of_not_gt hKlt)
    refine ⟨hKeq, ?_⟩
    apply G.tendsto_norm_finkBias_atTop_of_compactify_tendsto_norm_eq_one
      (H := H ∘ φ) (K := K) _ hKeq
    simpa only [Function.comp_def] using hlim

/-- Specialization of the projective compactness dichotomy to the relative
biases of a discounted Fink family around a target `W`. -/
theorem exists_finkRelativeBias_subsequence_interior_or_direction
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) {U : ℝ} (z : ℕ → G.finkDomain U)
    (W : G.State → Payoff ι) :
    ∃ (K : G.State → Payoff ι) (φ : ℕ → ℕ),
      StrictMono φ ∧
      Tendsto (G.compactifyFinkBias ∘
          (fun n => G.finkRelativeBias (β n) W (z n)) ∘ φ)
        atTop (nhds K) ∧
      ((‖K‖ < 1 ∧
          Tendsto ((fun n => G.finkRelativeBias (β n) W (z n)) ∘ φ)
            atTop (nhds (G.decompactifyFinkBias K))) ∨
        (‖K‖ = 1 ∧
          Tendsto (fun n =>
            ‖G.finkRelativeBias (β (φ n)) W (z (φ n))‖)
            atTop atTop)) := by
  exact G.exists_finkBias_subsequence_interior_or_direction
    (fun n => G.finkRelativeBias (β n) W (z n))

/-- A convergent Fink value family has a subsequence on which its relative
bias either converges at the original discounted scale or produces a unit
direction at a new, strictly diverging projective scale.  Convergence of the
underlying Fink-domain points is preserved by the extraction. -/
theorem exists_finkValueBias_subsequence_interior_or_boundaryScale
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)] (β : ℕ → ℝ)
    (hβ0 : ∀ n, 0 ≤ β n) (hβ1 : ∀ n, β n < 1)
    {U : ℝ} (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U)
    (hz : Tendsto z atTop (nhds zlim)) :
    ∃ (K : G.State → Payoff ι) (φ : ℕ → ℕ),
      StrictMono φ ∧
      Tendsto (z ∘ φ) atTop (nhds zlim) ∧
      Tendsto (G.compactifyFinkBias ∘
          (fun n => G.finkRelativeBias
            (β n) (G.finkValue zlim) (z n)) ∘ φ)
        atTop (nhds K) ∧
      ((‖K‖ < 1 ∧
          Tendsto ((fun n => G.finkRelativeBias
            (β n) (G.finkValue zlim) (z n)) ∘ φ)
              atTop (nhds (G.decompactifyFinkBias K))) ∨
        (‖K‖ = 1 ∧
          Tendsto (fun n =>
            ‖G.finkRelativeBias (β (φ n))
              (G.finkValue zlim) (z (φ n))‖) atTop atTop ∧
          Tendsto (fun n => G.finkProjectiveBiasScale
            (β (φ n)) (G.finkValue zlim) (z (φ n)))
              atTop atTop)) := by
  obtain ⟨K, φ, hφ, hKlim, halternative⟩ :=
    G.exists_finkRelativeBias_subsequence_interior_or_direction
      β z (G.finkValue zlim)
  have hzφ : Tendsto (z ∘ φ) atTop (nhds zlim) :=
    hz.comp hφ.tendsto_atTop
  refine ⟨K, φ, hφ, hzφ, hKlim, ?_⟩
  rcases halternative with hinterior | hboundary
  · exact Or.inl hinterior
  · exact Or.inr ⟨hboundary.1, hboundary.2, by
      apply G.tendsto_finkProjectiveBiasScale_atTop_of_boundary
        (fun n => hβ0 (φ n)) (fun n => hβ1 (φ n)) hzφ
        (K := K) _ hboundary.1
      simpa only [Function.comp_def] using hKlim⟩

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

/-- Probability assigned by `x` to actions that are strict continuation
losses relative to `xref` and `W`. -/
def strictContinuationMass
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (xref x : G.StationaryMixedProfile) (W : G.State → Payoff ι)
    (s : G.State) (who : ι) : ℝ :=
  ∑ d ∈ G.strictContinuationActions xref W s who,
    ((x s who) d).toReal

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

/-- Coordinatewise pruning estimates sum to an estimate on the entire strict
continuation-loss mass. -/
theorem strictContinuationMass_mul_le
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (xref x : G.StationaryMixedProfile) (W : G.State → Payoff ι)
    (s : G.State) (who : ι) (δ r : ℝ)
    (hpoint : ∀ d ∈ G.strictContinuationActions xref W s who,
      ((x s who) d).toReal * δ ≤ 2 * r) :
    G.strictContinuationMass xref x W s who * δ ≤
      2 * (G.strictContinuationActions xref W s who).card * r := by
  rw [strictContinuationMass, Finset.sum_mul]
  calc
    ∑ d ∈ G.strictContinuationActions xref W s who,
        ((x s who) d).toReal * δ ≤
        ∑ _d ∈ G.strictContinuationActions xref W s who, 2 * r :=
      Finset.sum_le_sum fun d hd => hpoint d hd
    _ = 2 * (G.strictContinuationActions xref W s who).card * r := by
      simp
      ring

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

/-- For a limiting supported action, the unscaled target-continuation gain
along the discounted fixed-point sequence converges to zero.  The unresolved
quantity is precisely this residual after multiplication by `β / (1 - β)`. -/
theorem tendsto_finkContinuationGain_zero_of_limit_support
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    (W : G.State → Payoff ι) (s : G.State) (who : ι)
    (d : G.Act who)
    (hharmonic : W s who =
      expect (pmfPi (G.finkProfile zlim s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)))
    (hexcessive : ∀ d' : G.Act who,
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d'))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who)
    (hpos : G.finkProfile zlim s who d ≠ 0) :
    Tendsto (fun n => G.finkContinuationGain W (z n) s who d)
      atTop (nhds 0) := by
  have hneutral := G.finkLimit_support_continuation_eq
    zlim W s who d hharmonic hexcessive hpos
  have hzero : G.finkContinuationGain W zlim s who d = 0 := by
    unfold finkContinuationGain
    rw [hneutral, ← hharmonic]
    ring
  have ht := G.tendsto_finkContinuationGain hz W s who d
  simpa only [hzero] using ht

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

/-- In the projective boundary branch, dividing the centered gain equation
by the diverging bias scale removes the stage term.  The remaining normalized
target residual converges to the negative continuation gain of the boundary
direction. -/
theorem tendsto_normalized_scaled_finkContinuationGain_of_limit_support
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {β : ℕ → ℝ} {U : ℝ}
    (hβ0 : ∀ n, 0 ≤ β n) (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (W K : G.State → Payoff ι)
    (hKlim : Tendsto (G.compactifyFinkBias ∘
      fun n => G.finkRelativeBias (β n) W (z n)) atTop (nhds K))
    (hKnorm : ‖K‖ = 1)
    (s : G.State) (who : ι) (d : G.Act who)
    (hpos : G.finkProfile zlim s who d ≠ 0) :
    Tendsto (fun n =>
        (1 / (1 + ‖G.finkRelativeBias (β n) W (z n)‖)) *
          ((β n / (1 - β n)) *
            G.finkContinuationGain W (z n) s who d)) atTop
      (nhds (-G.finkContinuationGain K zlim s who d)) := by
  let H : ℕ → G.State → Payoff ι :=
    fun n => G.finkRelativeBias (β n) W (z n)
  have hnorm : Tendsto (fun n => ‖H n‖) atTop atTop :=
    G.tendsto_norm_finkBias_atTop_of_compactify_tendsto_norm_eq_one
      (H := H) (K := K) (by simpa only [H] using hKlim) hKnorm
  have hscale : Tendsto (fun n => 1 + ‖H n‖) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [tendsto_atTop.1 hnorm (b - 1)] with n hn
    linarith
  have hinv : Tendsto (fun n => 1 / (1 + ‖H n‖)) atTop (nhds 0) := by
    simpa only [Function.comp_def, one_div] using
      tendsto_inv_atTop_zero.comp hscale
  have hstage := G.tendsto_finkStageGain hz s who d
  have hstageScaled : Tendsto
      (fun n => (1 / (1 + ‖H n‖)) * G.finkStageGain (z n) s who d)
      atTop (nhds 0) := by
    simpa using hinv.mul hstage
  have hcompact : Tendsto (fun n => G.compactifyFinkBias (H n))
      atTop (nhds K) := by
    simpa only [H, Function.comp_def] using hKlim
  have hcompactGain :=
    G.tendsto_finkContinuationGain_of_tendsto hcompact hz s who d
  have hrhs := (hstageScaled.add hcompactGain).neg
  have hrhs' : Tendsto (fun n =>
      -(1 / (1 + ‖H n‖) * G.finkStageGain (z n) s who d +
        G.finkContinuationGain (G.compactifyFinkBias (H n))
          (z n) s who d)) atTop
      (nhds (-G.finkContinuationGain K zlim s who d)) := by
    simpa only [zero_add] using hrhs
  apply hrhs'.congr'
  filter_upwards [G.eventually_finkCenteredGain_eq_zero_of_limit_support
    hβ0 hβ1 hpay hz hfix W s who d hpos] with n hn
  rw [G.finkContinuationGain_compactifyFinkBias]
  dsimp only [H]
  have htarget :
      (β n / (1 - β n)) * G.finkContinuationGain W (z n) s who d =
        -(G.finkStageGain (z n) s who d +
          G.finkContinuationGain
            (G.finkRelativeBias (β n) W (z n)) (z n) s who d) := by
    linarith
  rw [htarget]
  ring

/-- Named-scale form of the boundary equation.  On each limiting supported
action, the continuation loss of the leading value `W`, magnified by the new
projective scale, is canceled by the continuation gain of the first boundary
direction. -/
theorem tendsto_finkProjectiveBiasScale_mul_continuationGain_of_limit_support
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {β : ℕ → ℝ} {U : ℝ}
    (hβ0 : ∀ n, 0 ≤ β n) (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (W K : G.State → Payoff ι)
    (hKlim : Tendsto (G.compactifyFinkBias ∘
      fun n => G.finkRelativeBias (β n) W (z n)) atTop (nhds K))
    (hKnorm : ‖K‖ = 1)
    (s : G.State) (who : ι) (d : G.Act who)
    (hpos : G.finkProfile zlim s who d ≠ 0) :
    Tendsto (fun n =>
        G.finkProjectiveBiasScale (β n) W (z n) *
          G.finkContinuationGain W (z n) s who d) atTop
      (nhds (-G.finkContinuationGain K zlim s who d)) := by
  have ht := G.tendsto_normalized_scaled_finkContinuationGain_of_limit_support
    hβ0 hβ1 hpay hz hfix W K hKlim hKnorm s who d hpos
  convert ht using 1
  funext n
  unfold finkProjectiveBiasScale
  ring

/-- Boundary-scale optimality for every pure action.  The support equation
above is exact in the limit; off support, the corresponding lexicographic
gain is asymptotically nonpositive. -/
theorem eventually_finkProjectiveGain_le_of_boundary
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {β : ℕ → ℝ} {U : ℝ}
    (hβ0 : ∀ n, 0 ≤ β n) (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (W K : G.State → Payoff ι)
    (hKlim : Tendsto (G.compactifyFinkBias ∘
      fun n => G.finkRelativeBias (β n) W (z n)) atTop (nhds K))
    (hKnorm : ‖K‖ = 1)
    (s : G.State) (who : ι) (d : G.Act who)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      G.finkProjectiveBiasScale (β n) W (z n) *
          G.finkContinuationGain W (z n) s who d +
        G.finkContinuationGain K zlim s who d ≤ ε := by
  let H : ℕ → G.State → Payoff ι :=
    fun n => G.finkRelativeBias (β n) W (z n)
  have hnorm : Tendsto (fun n => ‖H n‖) atTop atTop :=
    G.tendsto_norm_finkBias_atTop_of_compactify_tendsto_norm_eq_one
      (H := H) (K := K) (by simpa only [H] using hKlim) hKnorm
  have hscale : Tendsto (fun n => 1 + ‖H n‖) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [tendsto_atTop.1 hnorm (b - 1)] with n hn
    linarith
  have hinv : Tendsto (fun n => 1 / (1 + ‖H n‖)) atTop (nhds 0) := by
    simpa only [Function.comp_def, one_div] using
      tendsto_inv_atTop_zero.comp hscale
  have hstage := G.tendsto_finkStageGain hz s who d
  have hstageScaled : Tendsto
      (fun n => (1 / (1 + ‖H n‖)) * G.finkStageGain (z n) s who d)
      atTop (nhds 0) := by
    simpa using hinv.mul hstage
  have hcompact : Tendsto (fun n => G.compactifyFinkBias (H n))
      atTop (nhds K) := by
    simpa only [H, Function.comp_def] using hKlim
  have hcompactGain :=
    G.tendsto_finkContinuationGain_of_tendsto hcompact hz s who d
  have hrhs : Tendsto (fun n =>
      (G.finkContinuationGain K zlim s who d -
          G.finkContinuationGain (G.compactifyFinkBias (H n))
            (z n) s who d) -
        (1 / (1 + ‖H n‖)) * G.finkStageGain (z n) s who d)
      atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℕ =>
        G.finkContinuationGain K zlim s who d) atTop
        (nhds (G.finkContinuationGain K zlim s who d)) :=
      tendsto_const_nhds
    have ht := (hconst.sub hcompactGain).sub hstageScaled
    simpa using ht
  filter_upwards [hrhs.eventually (eventually_lt_nhds hε)] with n hn
  have hcenter := G.finkCenteredGain_nonpos_of_finkMap_fixedPoint
    (β n) U (hβ0 n) (hβ1 n) hpay (z n) (hfix n) W s who d
  have hc0 : 0 ≤ 1 / (1 + ‖H n‖) := by positivity
  have hscaled := mul_nonpos_of_nonneg_of_nonpos hc0 hcenter
  have hdecomp :
      (1 / (1 + ‖H n‖)) *
          (G.finkStageGain (z n) s who d +
            (β n / (1 - β n)) *
              G.finkContinuationGain W (z n) s who d +
            G.finkContinuationGain (H n) (z n) s who d) =
        (1 / (1 + ‖H n‖)) * G.finkStageGain (z n) s who d +
          G.finkProjectiveBiasScale (β n) W (z n) *
            G.finkContinuationGain W (z n) s who d +
          G.finkContinuationGain (G.compactifyFinkBias (H n))
            (z n) s who d := by
    rw [G.finkContinuationGain_compactifyFinkBias]
    dsimp only [H]
    unfold finkProjectiveBiasScale
    ring
  rw [hdecomp] at hscaled
  dsimp only [H] at hn ⊢
  linarith

/-- Finite-coordinate uniform form of boundary-scale optimality. -/
theorem eventually_all_finkProjectiveGain_le_of_boundary
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {β : ℕ → ℝ} {U : ℝ}
    (hβ0 : ∀ n, 0 ≤ β n) (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (W K : G.State → Payoff ι)
    (hKlim : Tendsto (G.compactifyFinkBias ∘
      fun n => G.finkRelativeBias (β n) W (z n)) atTop (nhds K))
    (hKnorm : ‖K‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ s who (d : G.Act who),
      G.finkProjectiveBiasScale (β n) W (z n) *
          G.finkContinuationGain W (z n) s who d +
        G.finkContinuationGain K zlim s who d ≤ ε := by
  rw [Filter.eventually_all]
  intro s
  rw [Filter.eventually_all]
  intro who
  rw [Filter.eventually_all]
  intro d
  exact G.eventually_finkProjectiveGain_le_of_boundary
    hβ0 hβ1 hpay hz hfix W K hKlim hKnorm s who d hε

/-- Uniform complementary slackness on the limiting support at the boundary
scale. -/
theorem eventually_all_abs_finkProjectiveGain_le_of_limit_support
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {β : ℕ → ℝ} {U : ℝ}
    (hβ0 : ∀ n, 0 ≤ β n) (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (W K : G.State → Payoff ι)
    (hKlim : Tendsto (G.compactifyFinkBias ∘
      fun n => G.finkRelativeBias (β n) W (z n)) atTop (nhds K))
    (hKnorm : ‖K‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ s who (d : G.Act who),
      G.finkProfile zlim s who d ≠ 0 →
        |G.finkProjectiveBiasScale (β n) W (z n) *
            G.finkContinuationGain W (z n) s who d +
          G.finkContinuationGain K zlim s who d| ≤ ε := by
  rw [Filter.eventually_all]
  intro s
  rw [Filter.eventually_all]
  intro who
  rw [Filter.eventually_all]
  intro d
  by_cases hpos : G.finkProfile zlim s who d ≠ 0
  · have ht :=
      G.tendsto_finkProjectiveBiasScale_mul_continuationGain_of_limit_support
        hβ0 hβ1 hpay hz hfix W K hKlim hKnorm s who d hpos
    have hconst : Tendsto (fun _ : ℕ =>
        G.finkContinuationGain K zlim s who d) atTop
        (nhds (G.finkContinuationGain K zlim s who d)) :=
      tendsto_const_nhds
    have hsum := ht.add hconst
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (by simpa using hsum) ε hε
    filter_upwards [Filter.eventually_atTop.2 ⟨N, hN⟩] with n hn
    intro _
    simpa only [Real.dist_eq, sub_zero] using hn.le
  · exact Filter.Eventually.of_forall fun _ h => (hpos h).elim

/-- The finite vector space of pure-action coordinates, indexed by state,
player, and that player's action. -/
abbrev FinkPureActionVector (G : StochasticGame ι) :=
  G.State → ∀ who : ι, G.Act who → ℝ

/-- A single coordinate of the finite pure-action vector. -/
abbrev FinkPureActionIndex (G : StochasticGame ι) :=
  G.State × (Σ who : ι, G.Act who)

/-- Coordinates selected strictly positively by an action-loss direction. -/
def positiveFinkActionIndices (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (L : G.FinkPureActionVector) : Finset G.FinkPureActionIndex :=
  Finset.univ.filter fun p => 0 < L p.1 p.2.1 p.2.2

@[simp] theorem mem_positiveFinkActionIndices
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (L : G.FinkPureActionVector) (p : G.FinkPureActionIndex) :
    p ∈ G.positiveFinkActionIndices L ↔ 0 < L p.1 p.2.1 p.2.2 := by
  simp [positiveFinkActionIndices]

/-- Pure-action coordinates in the support of a decoded Fink profile. -/
def finkSupportIndices (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : G.finkDomain U) : Finset G.FinkPureActionIndex :=
  Finset.univ.filter fun p => G.finkProfile z p.1 p.2.1 p.2.2 ≠ 0

@[simp] theorem mem_finkSupportIndices
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : G.finkDomain U) (p : G.FinkPureActionIndex) :
    p ∈ G.finkSupportIndices z ↔
      G.finkProfile z p.1 p.2.1 p.2.2 ≠ 0 := by
  simp [finkSupportIndices]

theorem positiveFinkActionIndices_nonempty_of_norm_eq_one_of_nonneg
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (L : G.FinkPureActionVector) (hnorm : ‖L‖ = 1)
    (hnonneg : ∀ s who (d : G.Act who), 0 ≤ L s who d) :
    (G.positiveFinkActionIndices L).Nonempty := by
  have hpositive : ∃ (s : G.State) (who : ι) (d : G.Act who),
      0 < L s who d := by
    by_contra hnot
    have hnonpos : ∀ s who (d : G.Act who), L s who d ≤ 0 := by
      intro s who d
      exact le_of_not_gt fun h => hnot ⟨s, who, d, h⟩
    have hzero : L = 0 := by
      funext s who d
      exact le_antisymm (hnonpos s who d) (hnonneg s who d)
    rw [hzero] at hnorm
    simp at hnorm
  obtain ⟨s, who, d, hd⟩ := hpositive
  exact ⟨⟨s, ⟨who, d⟩⟩, by simp [hd]⟩

theorem positiveFinkActionIndices_disjoint_finkSupportIndices
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (L : G.FinkPureActionVector) {U : ℝ} (z : G.finkDomain U)
    (hsupport : ∀ s who (d : G.Act who),
      G.finkProfile z s who d ≠ 0 → L s who d = 0) :
    Disjoint (G.positiveFinkActionIndices L) (G.finkSupportIndices z) := by
  rw [Finset.disjoint_left]
  intro p hp hsupportp
  have hpos := (G.mem_positiveFinkActionIndices L p).mp hp
  have hplayed := (G.mem_finkSupportIndices z p).mp hsupportp
  exact (not_lt_of_ge (le_of_eq (hsupport p.1 p.2.1 p.2.2 hplayed))) hpos

/-- Zero the coordinates already assigned to earlier pruning layers. -/
noncomputable def maskFinkActionVector (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (P : Finset G.FinkPureActionIndex) (L : G.FinkPureActionVector) :
    G.FinkPureActionVector := by
  classical
  exact fun s who d => if ⟨s, ⟨who, d⟩⟩ ∈ P then 0 else L s who d

@[simp] theorem maskFinkActionVector_apply_of_mem
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (P : Finset G.FinkPureActionIndex) (L : G.FinkPureActionVector)
    (s : G.State) (who : ι) (d : G.Act who)
    (hmem : ⟨s, ⟨who, d⟩⟩ ∈ P) :
    G.maskFinkActionVector P L s who d = 0 := by
  classical
  simp [maskFinkActionVector, hmem]

@[simp] theorem maskFinkActionVector_apply_of_not_mem
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (P : Finset G.FinkPureActionIndex) (L : G.FinkPureActionVector)
    (s : G.State) (who : ι) (d : G.Act who)
    (hmem : ⟨s, ⟨who, d⟩⟩ ∉ P) :
    G.maskFinkActionVector P L s who d = L s who d := by
  classical
  simp [maskFinkActionVector, hmem]

theorem maskFinkActionVector_nonneg
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (P : Finset G.FinkPureActionIndex) (L : G.FinkPureActionVector)
    (hL : ∀ s who (d : G.Act who), 0 ≤ L s who d) :
    ∀ s who (d : G.Act who), 0 ≤ G.maskFinkActionVector P L s who d := by
  classical
  intro s who d
  by_cases hmem : ⟨s, ⟨who, d⟩⟩ ∈ P
  · simp [hmem]
  · simpa [G.maskFinkActionVector_apply_of_not_mem P L s who d hmem]
      using hL s who d

theorem positiveFinkActionIndices_disjoint_of_masked_zero
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (P : Finset G.FinkPureActionIndex) (K : G.FinkPureActionVector)
    (hzero : ∀ p ∈ P, K p.1 p.2.1 p.2.2 = 0) :
    Disjoint P (G.positiveFinkActionIndices K) := by
  rw [Finset.disjoint_left]
  intro p hp hpositive
  have hpos := (G.mem_positiveFinkActionIndices K p).mp hpositive
  exact (not_lt_of_ge (le_of_eq (hzero p hp))) hpos

/-- Enlarge a pruning mask by all coordinates selected by the next positive
direction. -/
noncomputable def extendFinkActionMask (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (P : Finset G.FinkPureActionIndex) (K : G.FinkPureActionVector) :
    Finset G.FinkPureActionIndex := by
  classical
  exact P ∪ G.positiveFinkActionIndices K

theorem strictSubset_union_positiveFinkActionIndices_of_nonempty_disjoint
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (P : Finset G.FinkPureActionIndex) (K : G.FinkPureActionVector)
    (hnonempty : (G.positiveFinkActionIndices K).Nonempty)
    (hdisjoint : Disjoint P (G.positiveFinkActionIndices K)) :
    P ⊂ G.extendFinkActionMask P K := by
  classical
  unfold extendFinkActionMask
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left, ?_⟩
  intro heq
  obtain ⟨p, hp⟩ := hnonempty
  have hpP : p ∈ P := by
    rw [heq]
    exact Finset.mem_union_right P hp
  exact Finset.disjoint_left.mp hdisjoint hpP hp

theorem extendFinkActionMask_disjoint
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (P S : Finset G.FinkPureActionIndex) (K : G.FinkPureActionVector)
    (hPS : Disjoint P S)
    (hKS : Disjoint (G.positiveFinkActionIndices K) S) :
    Disjoint (G.extendFinkActionMask P K) S := by
  classical
  unfold extendFinkActionMask
  rw [Finset.disjoint_union_left]
  exact ⟨hPS, hKS⟩

/-- The first boundary-layer gain in every pure-action coordinate. -/
def finkProjectiveGainVector (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (β : ℝ)
    (W K : G.State → Payoff ι) {U : ℝ}
    (z : G.finkDomain U) : G.FinkPureActionVector :=
  fun s who d =>
    G.finkProjectiveBiasScale β W z *
        G.finkContinuationGain W z s who d +
      G.finkContinuationGain K z s who d

/-- Nonnegative loss corresponding to a projective gain.  It agrees with
the negative gain once boundary optimality has become exact, while remaining
well behaved before that tail. -/
def finkProjectiveLossVector (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (β : ℝ)
    (W K : G.State → Payoff ι) {U : ℝ}
    (z : G.finkDomain U) : G.FinkPureActionVector :=
  fun s who d => max (-(G.finkProjectiveGainVector
    β W K z s who d)) 0

theorem finkProjectiveLossVector_nonneg
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)] (β : ℝ)
    (W K : G.State → Payoff ι) {U : ℝ}
    (z : G.finkDomain U)
    (s : G.State) (who : ι) (d : G.Act who) :
    0 ≤ G.finkProjectiveLossVector β W K z s who d := by
  unfold finkProjectiveLossVector
  exact le_max_right _ _

/-- A player's own mixed action averages its pure continuation gains to
zero. -/
theorem expect_finkContinuationGain_eq_zero
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (W : G.State → Payoff ι)
    {U : ℝ} (z : G.finkDomain U) (s : G.State) (who : ι) :
    expect (G.finkProfile z s who) (fun d =>
      G.finkContinuationGain W z s who d) = 0 := by
  have hdecomp := G.mixedDeviationContinuation_eq_expect_pure
    (G.finkProfile z) W s who (G.finkProfile z s who)
  simp only [Function.update_eq_self] at hdecomp
  unfold finkContinuationGain
  rw [expect_sub, expect_const, ← hdecomp]
  ring

/-- Consequently the complete current-profile projective gain vector has
zero own-action mean at every state and player. -/
theorem expect_finkProjectiveGainVector_eq_zero
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (β : ℝ)
    (W K : G.State → Payoff ι) {U : ℝ}
    (z : G.finkDomain U) (s : G.State) (who : ι) :
    expect (G.finkProfile z s who) (fun d =>
      G.finkProjectiveGainVector β W K z s who d) = 0 := by
  unfold finkProjectiveGainVector
  rw [expect_add, expect_const_mul,
    G.expect_finkContinuationGain_eq_zero,
    G.expect_finkContinuationGain_eq_zero]
  ring

/-- If every zero-mean gain coordinate is at most `ε`, the expected
negative-part loss is at most `ε`. -/
theorem expect_finkProjectiveLossVector_le
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (β : ℝ)
    (W K : G.State → Payoff ι) {U : ℝ}
    (z : G.finkDomain U) (s : G.State) (who : ι)
    {ε : ℝ} (hε0 : 0 ≤ ε)
    (hupper : ∀ d : G.Act who,
      G.finkProjectiveGainVector β W K z s who d ≤ ε) :
    expect (G.finkProfile z s who) (fun d =>
      G.finkProjectiveLossVector β W K z s who d) ≤ ε := by
  calc
    expect (G.finkProfile z s who) (fun d =>
        G.finkProjectiveLossVector β W K z s who d) ≤
      expect (G.finkProfile z s who) (fun d =>
        ε - G.finkProjectiveGainVector β W K z s who d) := by
      apply expect_mono
      intro d
      unfold finkProjectiveLossVector
      apply max_le
      · linarith
      · linarith [hupper d]
    _ = ε := by
      rw [expect_sub, expect_const,
        G.expect_finkProjectiveGainVector_eq_zero]
      ring

/-- Uniform boundary optimality with the correction gain evaluated at the
current profile.  This form has exact zero own-action mean. -/
theorem eventually_all_finkProjectiveGainVector_le_of_boundary
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {β : ℕ → ℝ} {U : ℝ}
    (hβ0 : ∀ n, 0 ≤ β n) (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (W K : G.State → Payoff ι)
    (hKlim : Tendsto (G.compactifyFinkBias ∘
      fun n => G.finkRelativeBias (β n) W (z n)) atTop (nhds K))
    (hKnorm : ‖K‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ s who (d : G.Act who),
      G.finkProjectiveGainVector (β n) W K (z n) s who d ≤ ε := by
  have hhalf : 0 < ε / 2 := by linarith
  have hlimitGain := G.eventually_all_finkProjectiveGain_le_of_boundary
    hβ0 hβ1 hpay hz hfix W K hKlim hKnorm hhalf
  have hKclose : ∀ᶠ n in atTop, ∀ s who (d : G.Act who),
      |G.finkContinuationGain K (z n) s who d -
        G.finkContinuationGain K zlim s who d| ≤ ε / 2 := by
    rw [Filter.eventually_all]
    intro s
    rw [Filter.eventually_all]
    intro who
    rw [Filter.eventually_all]
    intro d
    have ht := G.tendsto_finkContinuationGain hz K s who d
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht (ε / 2) hhalf
    filter_upwards [Filter.eventually_atTop.2 ⟨N, hN⟩] with n hn
    simpa only [Real.dist_eq] using hn.le
  filter_upwards [hlimitGain, hKclose] with n hn hKn
  intro s who d
  have hmain := hn s who d
  have hcorr := (abs_le.mp (hKn s who d)).2
  unfold finkProjectiveGainVector
  linarith

/-- The current-profile projective loss tends to zero on every action in the
limiting support. -/
theorem tendsto_finkProjectiveLossVector_zero_of_limit_support
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {β : ℕ → ℝ} {U : ℝ}
    (hβ0 : ∀ n, 0 ≤ β n) (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (W K : G.State → Payoff ι)
    (hKlim : Tendsto (G.compactifyFinkBias ∘
      fun n => G.finkRelativeBias (β n) W (z n)) atTop (nhds K))
    (hKnorm : ‖K‖ = 1)
    (s : G.State) (who : ι) (d : G.Act who)
    (hpos : G.finkProfile zlim s who d ≠ 0) :
    Tendsto (fun n =>
      G.finkProjectiveLossVector (β n) W K (z n) s who d)
      atTop (nhds 0) := by
  have hmain :=
    G.tendsto_finkProjectiveBiasScale_mul_continuationGain_of_limit_support
      hβ0 hβ1 hpay hz hfix W K hKlim hKnorm s who d hpos
  have hKcurrent := G.tendsto_finkContinuationGain hz K s who d
  have hgain : Tendsto (fun n =>
      G.finkProjectiveGainVector (β n) W K (z n) s who d)
      atTop (nhds 0) := by
    have ht := hmain.add hKcurrent
    simpa only [finkProjectiveGainVector, neg_add_cancel] using ht
  have hloss := hgain.neg.max
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ))
      atTop (nhds 0))
  simpa only [finkProjectiveLossVector, neg_zero, max_self] using hloss

/-- At a projective boundary, the expected current-profile loss vanishes for
every state and player. -/
theorem tendsto_expect_finkProjectiveLossVector_zero_of_boundary
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {β : ℕ → ℝ} {U : ℝ}
    (hβ0 : ∀ n, 0 ≤ β n) (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (W K : G.State → Payoff ι)
    (hKlim : Tendsto (G.compactifyFinkBias ∘
      fun n => G.finkRelativeBias (β n) W (z n)) atTop (nhds K))
    (hKnorm : ‖K‖ = 1) (s : G.State) (who : ι) :
    Tendsto (fun n => expect (G.finkProfile (z n) s who) (fun d =>
      G.finkProjectiveLossVector (β n) W K (z n) s who d))
      atTop (nhds 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  have hupper := G.eventually_all_finkProjectiveGainVector_le_of_boundary
    hβ0 hβ1 hpay hz hfix W K hKlim hKnorm hhalf
  apply Filter.eventually_atTop.mp
  filter_upwards [hupper] with n hn
  have hloss0 : 0 ≤ expect (G.finkProfile (z n) s who) (fun d =>
      G.finkProjectiveLossVector (β n) W K (z n) s who d) := by
    exact expect_nonneg _ _ fun d =>
      G.finkProjectiveLossVector_nonneg
        (β n) W K (z n) s who d
  have hloss := G.expect_finkProjectiveLossVector_le
    (β n) W K (z n) s who hhalf.le (hn s who)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hloss0]
  linarith

/-- A nonnegative summand is bounded by its finite PMF expectation. -/
theorem pmf_apply_toReal_mul_le_expect_of_nonneg
    {α : Type} [Finite α] (p : PMF α) (f : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) (a : α) :
    (p a).toReal * f a ≤ expect p f := by
  letI := Fintype.ofFinite α
  rw [expect_eq_sum]
  exact Finset.single_le_sum
    (fun b _ => mul_nonneg ENNReal.toReal_nonneg (hf b))
    (Finset.mem_univ a)

/-- Every individual probability-weighted boundary loss tends to zero.  Thus
an action whose loss diverges must be played at a correspondingly faster
vanishing rate. -/
theorem tendsto_finkProfile_mul_projectiveLoss_zero_of_boundary
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {β : ℕ → ℝ} {U : ℝ}
    (hβ0 : ∀ n, 0 ≤ β n) (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (W K : G.State → Payoff ι)
    (hKlim : Tendsto (G.compactifyFinkBias ∘
      fun n => G.finkRelativeBias (β n) W (z n)) atTop (nhds K))
    (hKnorm : ‖K‖ = 1)
    (s : G.State) (who : ι) (d : G.Act who) :
    Tendsto (fun n => ((G.finkProfile (z n) s who) d).toReal *
      G.finkProjectiveLossVector (β n) W K (z n) s who d)
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    exact mul_nonneg ENNReal.toReal_nonneg
      (G.finkProjectiveLossVector_nonneg
        (β n) W K (z n) s who d)
  · intro n
    exact pmf_apply_toReal_mul_le_expect_of_nonneg
      (G.finkProfile (z n) s who)
      (fun d' => G.finkProjectiveLossVector
        (β n) W K (z n) s who d')
      (fun d' => G.finkProjectiveLossVector_nonneg
        (β n) W K (z n) s who d') d
  · exact G.tendsto_expect_finkProjectiveLossVector_zero_of_boundary
      hβ0 hβ1 hpay hz hfix W K hKlim hKnorm s who

/-- Radial compactification for the finite pure-action loss space. -/
def compactifyFinkActionVector (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (L : G.FinkPureActionVector) : G.FinkPureActionVector :=
  (1 / (1 + ‖L‖)) • L

theorem norm_compactifyFinkActionVector_eq
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (L : G.FinkPureActionVector) :
    ‖G.compactifyFinkActionVector L‖ = ‖L‖ / (1 + ‖L‖) := by
  have hden : 0 < 1 + ‖L‖ := by positivity
  simp [compactifyFinkActionVector, norm_smul, Real.norm_eq_abs,
    abs_of_pos hden, div_eq_mul_inv]
  ring

theorem norm_compactifyFinkActionVector_lt_one
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (L : G.FinkPureActionVector) :
    ‖G.compactifyFinkActionVector L‖ < 1 := by
  rw [G.norm_compactifyFinkActionVector_eq L]
  exact (div_lt_one (by positivity)).2 (by linarith [norm_nonneg L])

theorem compactifyFinkActionVector_mem_closedBall
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (L : G.FinkPureActionVector) :
    G.compactifyFinkActionVector L ∈
      Metric.closedBall (0 : G.FinkPureActionVector) 1 := by
  rw [Metric.mem_closedBall]
  simpa only [dist_zero_right] using
    (G.norm_compactifyFinkActionVector_lt_one L).le

theorem compactifyFinkActionVector_apply_nonneg
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (L : G.FinkPureActionVector)
    (hL : ∀ s who (d : G.Act who), 0 ≤ L s who d)
    (s : G.State) (who : ι) (d : G.Act who) :
    0 ≤ G.compactifyFinkActionVector L s who d := by
  simp only [compactifyFinkActionVector, Pi.smul_apply, smul_eq_mul]
  exact mul_nonneg (by positivity) (hL s who d)

/-- A nonnegative action coordinate tending to zero still tends to zero
after radial compactification, regardless of the other coordinates' growth. -/
theorem tendsto_compactifyFinkActionVector_apply_zero
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    {L : ℕ → G.FinkPureActionVector}
    (hL : ∀ n s who (d : G.Act who), 0 ≤ L n s who d)
    (s : G.State) (who : ι) (d : G.Act who)
    (hzero : Tendsto (fun n => L n s who d) atTop (nhds 0)) :
    Tendsto (fun n => G.compactifyFinkActionVector (L n) s who d)
      atTop (nhds 0) := by
  apply squeeze_zero
  · exact fun n => G.compactifyFinkActionVector_apply_nonneg
      (L n) (hL n) s who d
  · intro n
    simp only [compactifyFinkActionVector, Pi.smul_apply, smul_eq_mul]
    have hfactor : 1 / (1 + ‖L n‖) ≤ 1 := by
      exact (div_le_one (by positivity)).2 (by linarith [norm_nonneg (L n)])
    exact mul_le_of_le_one_left (hL n s who d) hfactor
  · exact hzero

/-- If a probability-weighted coordinate tends to zero while its radial
compactification tends to a positive number, then the probability vanishes
faster than the reciprocal total-vector scale. -/
theorem tendsto_mul_one_add_norm_finkActionVector_zero_of_compactify_apply_pos
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    {L : ℕ → G.FinkPureActionVector} {p : ℕ → ℝ}
    (s : G.State) (who : ι) (d : G.Act who) {c : ℝ} (hc : 0 < c)
    (hcompact : Tendsto (fun n =>
      G.compactifyFinkActionVector (L n) s who d) atTop (nhds c))
    (hweighted : Tendsto (fun n => p n * L n s who d) atTop (nhds 0)) :
    Tendsto (fun n => p n * (1 + ‖L n‖)) atTop (nhds 0) := by
  have hinv := hcompact.inv₀ (ne_of_gt hc)
  have hmul := hweighted.mul hinv
  have hmul' : Tendsto (fun n =>
      (p n * L n s who d) *
        (G.compactifyFinkActionVector (L n) s who d)⁻¹)
      atTop (nhds 0) := by
    simpa using hmul
  apply hmul'.congr'
  filter_upwards [hcompact.eventually (eventually_ne_nhds (ne_of_gt hc))]
    with n hn
  have hden : 1 + ‖L n‖ ≠ 0 := ne_of_gt (by positivity)
  have hloss : L n s who d ≠ 0 := by
    intro hloss
    apply hn
    simp [compactifyFinkActionVector, hloss]
  simp only [compactifyFinkActionVector, Pi.smul_apply, smul_eq_mul]
  field_simp [hden, hloss]

/-- Inverse radial chart on the open pure-action vector ball. -/
def decompactifyFinkActionVector (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (K : G.FinkPureActionVector) : G.FinkPureActionVector :=
  (1 / (1 - ‖K‖)) • K

@[simp] theorem decompactify_compactifyFinkActionVector
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (L : G.FinkPureActionVector) :
    G.decompactifyFinkActionVector (G.compactifyFinkActionVector L) = L := by
  rw [decompactifyFinkActionVector,
    G.norm_compactifyFinkActionVector_eq L,
    compactifyFinkActionVector, smul_smul]
  have hden : 1 + ‖L‖ ≠ 0 := ne_of_gt (by positivity)
  convert one_smul ℝ L using 1
  field_simp [hden]
  ring_nf

/-- An interior compactified action-vector limit gives an ordinary finite
loss-vector limit. -/
theorem tendsto_finkActionVector_of_compactify_tendsto_of_norm_lt_one
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    {L : ℕ → G.FinkPureActionVector} {K : G.FinkPureActionVector}
    (hlim : Tendsto (G.compactifyFinkActionVector ∘ L) atTop (nhds K))
    (hK : ‖K‖ < 1) :
    Tendsto L atTop (nhds (G.decompactifyFinkActionVector K)) := by
  have hden : 1 - ‖K‖ ≠ 0 := by linarith
  have hc : ContinuousAt (G.decompactifyFinkActionVector) K := by
    unfold decompactifyFinkActionVector
    fun_prop
  have ht := hc.tendsto.comp hlim
  simpa only [Function.comp_def,
    G.decompactify_compactifyFinkActionVector] using ht

/-- A unit compactified action-vector limit forces the original loss norms
to diverge. -/
theorem tendsto_norm_finkActionVector_atTop_of_compactify_tendsto_norm_eq_one
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    {L : ℕ → G.FinkPureActionVector} {K : G.FinkPureActionVector}
    (hlim : Tendsto (G.compactifyFinkActionVector ∘ L) atTop (nhds K))
    (hK : ‖K‖ = 1) :
    Tendsto (fun n => ‖L n‖) atTop atTop := by
  have hnorm : Tendsto (fun n => ‖G.compactifyFinkActionVector (L n)‖)
      atTop (nhds 1) := by
    have ht := continuous_norm.tendsto K |>.comp hlim
    simpa only [Function.comp_def, hK] using ht
  refine tendsto_atTop.2 fun b => ?_
  let B := max b 0
  have hB0 : 0 ≤ B := le_max_right b 0
  have hfrac : B / (1 + B) < 1 := by
    exact (div_lt_one (by linarith)).2 (by linarith)
  filter_upwards [hnorm.eventually (eventually_gt_nhds hfrac)] with n hn
  rw [G.norm_compactifyFinkActionVector_eq] at hn
  have hdenB : 0 < 1 + B := by linarith
  have hdenL : 0 < 1 + ‖L n‖ := by positivity
  rw [div_lt_div_iff₀ hdenB hdenL] at hn
  have hBL : B < ‖L n‖ := by linarith
  exact (le_max_left b 0).trans hBL.le

/-- Every projective loss family has a convergent radial subsequence. -/
theorem exists_convergent_compactifiedFinkActionVector_subsequence
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (L : ℕ → G.FinkPureActionVector) :
    ∃ (Llim : G.FinkPureActionVector) (φ : ℕ → ℕ),
      Llim ∈ Metric.closedBall (0 : G.FinkPureActionVector) 1 ∧
      StrictMono φ ∧
      Tendsto (G.compactifyFinkActionVector ∘ L ∘ φ)
        atTop (nhds Llim) := by
  let C := Metric.closedBall (0 : G.FinkPureActionVector) 1
  let y : ℕ → C := fun n =>
    ⟨G.compactifyFinkActionVector (L n),
      G.compactifyFinkActionVector_mem_closedBall (L n)⟩
  letI : CompactSpace C :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
  obtain ⟨ylim, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq y
  refine ⟨ylim.1, φ, ylim.2, hφ, ?_⟩
  have ht := continuous_subtype_val.tendsto ylim |>.comp hlim
  simpa only [y, Function.comp_def] using ht

/-- Projective compactness dichotomy for finite pure-action loss vectors. -/
theorem exists_finkActionVector_subsequence_interior_or_direction
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (L : ℕ → G.FinkPureActionVector) :
    ∃ (K : G.FinkPureActionVector) (φ : ℕ → ℕ),
      StrictMono φ ∧
      Tendsto (G.compactifyFinkActionVector ∘ L ∘ φ)
        atTop (nhds K) ∧
      ((‖K‖ < 1 ∧ Tendsto (L ∘ φ) atTop
          (nhds (G.decompactifyFinkActionVector K))) ∨
        (‖K‖ = 1 ∧ Tendsto (fun n => ‖L (φ n)‖) atTop atTop)) := by
  obtain ⟨K, φ, hKmem, hφ, hlim⟩ :=
    G.exists_convergent_compactifiedFinkActionVector_subsequence L
  have hKle : ‖K‖ ≤ 1 := by
    rw [Metric.mem_closedBall] at hKmem
    simpa only [dist_zero_right] using hKmem
  refine ⟨K, φ, hφ, hlim, ?_⟩
  by_cases hKlt : ‖K‖ < 1
  · left
    refine ⟨hKlt, ?_⟩
    apply G.tendsto_finkActionVector_of_compactify_tendsto_of_norm_lt_one
      (L := L ∘ φ) (K := K) _ hKlt
    simpa only [Function.comp_def] using hlim
  · right
    have hKeq : ‖K‖ = 1 := le_antisymm hKle (le_of_not_gt hKlt)
    refine ⟨hKeq, ?_⟩
    apply G.tendsto_norm_finkActionVector_atTop_of_compactify_tendsto_norm_eq_one
      (L := L ∘ φ) (K := K) _ hKeq
    simpa only [Function.comp_def] using hlim

/-- A limit of radially compactified masked vectors is zero on every masked
coordinate. -/
theorem finkActionVector_limit_apply_eq_zero_of_mem_mask
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (P : Finset G.FinkPureActionIndex) (L : ℕ → G.FinkPureActionVector)
    (K : G.FinkPureActionVector)
    (hlim : Tendsto (fun n =>
      G.compactifyFinkActionVector (G.maskFinkActionVector P (L n)))
        atTop (nhds K))
    (p : G.FinkPureActionIndex) (hp : p ∈ P) :
    K p.1 p.2.1 p.2.2 = 0 := by
  have hc : Continuous (fun Q : G.FinkPureActionVector =>
      Q p.1 p.2.1 p.2.2) := by
    fun_prop
  have hcoord := (hc.tendsto K).comp hlim
  have hzero : Tendsto (fun n =>
      G.compactifyFinkActionVector
        (G.maskFinkActionVector P (L n)) p.1 p.2.1 p.2.2)
      atTop (nhds 0) := by
    have heq : (fun n => G.compactifyFinkActionVector
        (G.maskFinkActionVector P (L n)) p.1 p.2.1 p.2.2) =
        (fun _ : ℕ => (0 : ℝ)) := by
      funext n
      simp [compactifyFinkActionVector,
        G.maskFinkActionVector_apply_of_mem P (L n)
          p.1 p.2.1 p.2.2 hp]
    rw [heq]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hcoord hzero

/-- Nonnegativity is closed under masked radial limits. -/
theorem finkActionVector_limit_nonneg_of_masked_nonneg
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (P : Finset G.FinkPureActionIndex) (L : ℕ → G.FinkPureActionVector)
    (hL : ∀ n s who (d : G.Act who), 0 ≤ L n s who d)
    (K : G.FinkPureActionVector)
    (hlim : Tendsto (fun n =>
      G.compactifyFinkActionVector (G.maskFinkActionVector P (L n)))
        atTop (nhds K)) :
    ∀ s who (d : G.Act who), 0 ≤ K s who d := by
  intro s who d
  have hc : Continuous (fun Q : G.FinkPureActionVector => Q s who d) := by
    fun_prop
  have hcoord := (hc.tendsto K).comp hlim
  apply ge_of_tendsto' hcoord
  intro n
  apply G.compactifyFinkActionVector_apply_nonneg
  exact G.maskFinkActionVector_nonneg P (L n) (hL n)

/-- A protected coordinate which already tends to zero remains zero in every
masked radial limit. -/
theorem finkActionVector_limit_apply_eq_zero_of_tendsto_zero
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (P : Finset G.FinkPureActionIndex) (L : ℕ → G.FinkPureActionVector)
    (hL : ∀ n s who (d : G.Act who), 0 ≤ L n s who d)
    (K : G.FinkPureActionVector)
    (hlim : Tendsto (fun n =>
      G.compactifyFinkActionVector (G.maskFinkActionVector P (L n)))
        atTop (nhds K))
    (p : G.FinkPureActionIndex)
    (hzero : Tendsto (fun n => L n p.1 p.2.1 p.2.2) atTop (nhds 0)) :
    K p.1 p.2.1 p.2.2 = 0 := by
  by_cases hp : p ∈ P
  · exact G.finkActionVector_limit_apply_eq_zero_of_mem_mask
      P L K hlim p hp
  · have hmaskedZero : Tendsto (fun n =>
        G.maskFinkActionVector P (L n) p.1 p.2.1 p.2.2)
        atTop (nhds 0) := by
      have heq : (fun n =>
          G.maskFinkActionVector P (L n) p.1 p.2.1 p.2.2) =
          (fun n => L n p.1 p.2.1 p.2.2) := by
        funext n
        exact G.maskFinkActionVector_apply_of_not_mem
          P (L n) p.1 p.2.1 p.2.2 hp
      rw [heq]
      exact hzero
    have hcompactZero :=
      G.tendsto_compactifyFinkActionVector_apply_zero
        (L := fun n => G.maskFinkActionVector P (L n))
        (fun n => G.maskFinkActionVector_nonneg P (L n) (hL n))
        p.1 p.2.1 p.2.2 hmaskedZero
    have hc : Continuous (fun Q : G.FinkPureActionVector =>
        Q p.1 p.2.1 p.2.2) := by
      fun_prop
    have hcoord := (hc.tendsto K).comp hlim
    exact tendsto_nhds_unique hcoord hcompactZero

/-- One masked action-face step.  The bounded branch converges in the
remaining coordinates.  In the boundary branch a nonempty positive face,
disjoint from the old mask, strictly enlarges that mask. -/
theorem exists_maskedFinkActionVector_subsequence_interior_or_strictExtension
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (P : Finset G.FinkPureActionIndex) (L : ℕ → G.FinkPureActionVector)
    (hL : ∀ n s who (d : G.Act who), 0 ≤ L n s who d) :
    ∃ (K : G.FinkPureActionVector) (φ : ℕ → ℕ),
      StrictMono φ ∧
      Tendsto (G.compactifyFinkActionVector ∘
        (fun n => G.maskFinkActionVector P (L n)) ∘ φ)
          atTop (nhds K) ∧
      ((‖K‖ < 1 ∧ Tendsto
          ((fun n => G.maskFinkActionVector P (L n)) ∘ φ) atTop
            (nhds (G.decompactifyFinkActionVector K))) ∨
        (‖K‖ = 1 ∧ Tendsto (fun n =>
            ‖G.maskFinkActionVector P (L (φ n))‖) atTop atTop ∧
          (∀ s who (d : G.Act who), 0 ≤ K s who d) ∧
          (∀ p ∈ P, K p.1 p.2.1 p.2.2 = 0) ∧
          (G.positiveFinkActionIndices K).Nonempty ∧
          Disjoint P (G.positiveFinkActionIndices K) ∧
          P ⊂ G.extendFinkActionMask P K)) := by
  let M : ℕ → G.FinkPureActionVector := fun n =>
    G.maskFinkActionVector P (L n)
  obtain ⟨K, φ, hφ, hlim, halternative⟩ :=
    G.exists_finkActionVector_subsequence_interior_or_direction M
  refine ⟨K, φ, hφ, ?_, ?_⟩
  · simpa only [M, Function.comp_def] using hlim
  rcases halternative with hinterior | hboundary
  · exact Or.inl (by simpa only [M, Function.comp_def] using hinterior)
  · right
    have hlim' : Tendsto (fun n =>
        G.compactifyFinkActionVector
          (G.maskFinkActionVector P (L (φ n)))) atTop (nhds K) := by
      simpa only [M, Function.comp_def] using hlim
    have hnonneg := G.finkActionVector_limit_nonneg_of_masked_nonneg
      P (L ∘ φ) (fun n => hL (φ n)) K
        (by simpa only [Function.comp_def] using hlim')
    have hzero : ∀ p ∈ P, K p.1 p.2.1 p.2.2 = 0 := by
      intro p hp
      exact G.finkActionVector_limit_apply_eq_zero_of_mem_mask
        P (L ∘ φ) K (by simpa only [Function.comp_def] using hlim') p hp
    have hpositive :=
      G.positiveFinkActionIndices_nonempty_of_norm_eq_one_of_nonneg
        K hboundary.1 hnonneg
    have hdisjoint :=
      G.positiveFinkActionIndices_disjoint_of_masked_zero P K hzero
    have hstrict :=
      G.strictSubset_union_positiveFinkActionIndices_of_nonempty_disjoint
        P K hpositive hdisjoint
    refine ⟨hboundary.1, ?_, hnonneg, hzero,
      hpositive, hdisjoint, hstrict⟩
    simpa only [M, Function.comp_def] using hboundary.2

/-- Protected-coordinate refinement of one masked step.  If every coordinate
in `S` tends to zero and the old mask is disjoint from `S`, the enlarged mask
in the boundary branch remains disjoint from `S`. -/
theorem exists_maskedFinkActionVector_subsequence_interior_or_protectedExtension
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (P S : Finset G.FinkPureActionIndex)
    (L : ℕ → G.FinkPureActionVector)
    (hL : ∀ n s who (d : G.Act who), 0 ≤ L n s who d)
    (hPS : Disjoint P S)
    (hprotected : ∀ p ∈ S,
      Tendsto (fun n => L n p.1 p.2.1 p.2.2) atTop (nhds 0)) :
    ∃ (K : G.FinkPureActionVector) (φ : ℕ → ℕ),
      StrictMono φ ∧
      Tendsto (G.compactifyFinkActionVector ∘
        (fun n => G.maskFinkActionVector P (L n)) ∘ φ)
          atTop (nhds K) ∧
      ((‖K‖ < 1 ∧ Tendsto
          ((fun n => G.maskFinkActionVector P (L n)) ∘ φ) atTop
            (nhds (G.decompactifyFinkActionVector K))) ∨
        (‖K‖ = 1 ∧ Tendsto (fun n =>
            ‖G.maskFinkActionVector P (L (φ n))‖) atTop atTop ∧
          (∀ s who (d : G.Act who), 0 ≤ K s who d) ∧
          (∀ p ∈ P, K p.1 p.2.1 p.2.2 = 0) ∧
          (G.positiveFinkActionIndices K).Nonempty ∧
          Disjoint P (G.positiveFinkActionIndices K) ∧
          P ⊂ G.extendFinkActionMask P K ∧
          Disjoint (G.extendFinkActionMask P K) S)) := by
  obtain ⟨K, φ, hφ, hlim, halternative⟩ :=
    G.exists_maskedFinkActionVector_subsequence_interior_or_strictExtension
      P L hL
  refine ⟨K, φ, hφ, hlim, ?_⟩
  rcases halternative with hinterior | hboundary
  · exact Or.inl hinterior
  · right
    have hlim' : Tendsto (fun n =>
        G.compactifyFinkActionVector
          (G.maskFinkActionVector P (L (φ n)))) atTop (nhds K) := by
      simpa only [Function.comp_def] using hlim
    have hSzero : ∀ p ∈ S, K p.1 p.2.1 p.2.2 = 0 := by
      intro p hp
      apply G.finkActionVector_limit_apply_eq_zero_of_tendsto_zero
        P (L ∘ φ) (fun n => hL (φ n)) K
          (by simpa only [Function.comp_def] using hlim') p
      exact (hprotected p hp).comp hφ.tendsto_atTop
    have hpositiveS : Disjoint (G.positiveFinkActionIndices K) S :=
      (G.positiveFinkActionIndices_disjoint_of_masked_zero S K hSzero).symm
    have hextendS := G.extendFinkActionMask_disjoint
      P S K hPS hpositiveS
    exact ⟨hboundary.1, hboundary.2.1, hboundary.2.2.1,
      hboundary.2.2.2.1, hboundary.2.2.2.2.1,
      hboundary.2.2.2.2.2.1, hboundary.2.2.2.2.2.2,
      hextendS⟩

/-- Finite termination of masked radial extraction.  Starting from any mask
and any nonnegative finite action-vector sequence, repeated boundary steps
can occur only finitely often because each one strictly enlarges the mask.
Along a final subsequence, every unmasked coordinate therefore has an
ordinary finite limit. -/
theorem exists_subsequence_maskedFinkActionVector_tendsto
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (P₀ : Finset G.FinkPureActionIndex)
    (L₀ : ℕ → G.FinkPureActionVector)
    (hL₀ : ∀ n s who (d : G.Act who), 0 ≤ L₀ n s who d) :
    ∃ (P : Finset G.FinkPureActionIndex) (φ : ℕ → ℕ)
      (Llim : G.FinkPureActionVector),
      P₀ ⊆ P ∧ StrictMono φ ∧
      Tendsto ((fun n => G.maskFinkActionVector P (L₀ n)) ∘ φ)
        atTop (nhds Llim) := by
  classical
  let total : ℕ := Finset.card (Finset.univ : Finset G.FinkPureActionIndex)
  have aux : ∀ N : ℕ, ∀ (P : Finset G.FinkPureActionIndex)
      (L : ℕ → G.FinkPureActionVector),
      total - P.card = N →
      (∀ n s who (d : G.Act who), 0 ≤ L n s who d) →
      ∃ (P' : Finset G.FinkPureActionIndex) (φ : ℕ → ℕ)
        (Llim : G.FinkPureActionVector),
        P ⊆ P' ∧ StrictMono φ ∧
        Tendsto ((fun n => G.maskFinkActionVector P' (L n)) ∘ φ)
          atTop (nhds Llim) := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
        intro P L hN hL
        obtain ⟨K, φ, hφ, hcompact, hinterior | hboundary⟩ :=
          G.exists_maskedFinkActionVector_subsequence_interior_or_strictExtension
            P L hL
        · exact ⟨P, φ, G.decompactifyFinkActionVector K,
            Finset.Subset.rfl, hφ, hinterior.2⟩
        · let P' := G.extendFinkActionMask P K
          have hstrict : P ⊂ P' := by
            exact hboundary.2.2.2.2.2.2
          have hcard : P.card < P'.card := Finset.card_lt_card hstrict
          have hP'le : P'.card ≤ total := by
            dsimp [total]
            exact Finset.card_le_card (Finset.subset_univ P')
          have hremain : total - P'.card < N := by omega
          let L' : ℕ → G.FinkPureActionVector := L ∘ φ
          have hL' : ∀ n s who (d : G.Act who), 0 ≤ L' n s who d := by
            intro n s who d
            exact hL (φ n) s who d
          obtain ⟨Pfinal, ψ, Llim, hP'final, hψ, hlim⟩ :=
            ih (total - P'.card) hremain P' L' rfl hL'
          refine ⟨Pfinal, φ ∘ ψ, Llim,
            Finset.Subset.trans (Finset.ssubset_iff_subset_ne.mp hstrict).1
              hP'final,
            hφ.comp hψ, ?_⟩
          simpa only [L', Function.comp_def] using hlim
  exact aux (total - P₀.card) P₀ L₀ rfl hL₀

/-- Finite termination while protecting a set of coordinates known to tend
to zero.  No protected coordinate is ever added to the pruning mask. -/
theorem exists_subsequence_maskedFinkActionVector_tendsto_protected
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (P₀ S : Finset G.FinkPureActionIndex)
    (L₀ : ℕ → G.FinkPureActionVector)
    (hL₀ : ∀ n s who (d : G.Act who), 0 ≤ L₀ n s who d)
    (hP₀S : Disjoint P₀ S)
    (hprotected₀ : ∀ p ∈ S,
      Tendsto (fun n => L₀ n p.1 p.2.1 p.2.2) atTop (nhds 0)) :
    ∃ (P : Finset G.FinkPureActionIndex) (φ : ℕ → ℕ)
      (Llim : G.FinkPureActionVector),
      P₀ ⊆ P ∧ Disjoint P S ∧ StrictMono φ ∧
      Tendsto ((fun n => G.maskFinkActionVector P (L₀ n)) ∘ φ)
        atTop (nhds Llim) := by
  classical
  let total : ℕ := Finset.card (Finset.univ : Finset G.FinkPureActionIndex)
  have aux : ∀ N : ℕ, ∀ (P : Finset G.FinkPureActionIndex)
      (L : ℕ → G.FinkPureActionVector),
      total - P.card = N →
      (∀ n s who (d : G.Act who), 0 ≤ L n s who d) →
      Disjoint P S →
      (∀ p ∈ S, Tendsto (fun n => L n p.1 p.2.1 p.2.2)
        atTop (nhds 0)) →
      ∃ (P' : Finset G.FinkPureActionIndex) (φ : ℕ → ℕ)
        (Llim : G.FinkPureActionVector),
        P ⊆ P' ∧ Disjoint P' S ∧ StrictMono φ ∧
        Tendsto ((fun n => G.maskFinkActionVector P' (L n)) ∘ φ)
          atTop (nhds Llim) := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
        intro P L hN hL hPS hprotected
        obtain ⟨K, φ, hφ, hcompact, hinterior | hboundary⟩ :=
          G.exists_maskedFinkActionVector_subsequence_interior_or_protectedExtension
            P S L hL hPS hprotected
        · exact ⟨P, φ, G.decompactifyFinkActionVector K,
            Finset.Subset.rfl, hPS, hφ, hinterior.2⟩
        · rcases hboundary with
            ⟨hnorm, hnormdiv, hnonneg, hzero, hpositive,
              hdisjoint, hstrict, hextendS⟩
          let P' := G.extendFinkActionMask P K
          have hcard : P.card < P'.card := Finset.card_lt_card hstrict
          have hP'le : P'.card ≤ total := by
            dsimp [total]
            exact Finset.card_le_card (Finset.subset_univ P')
          have hremain : total - P'.card < N := by omega
          let L' : ℕ → G.FinkPureActionVector := L ∘ φ
          have hL' : ∀ n s who (d : G.Act who), 0 ≤ L' n s who d := by
            intro n s who d
            exact hL (φ n) s who d
          have hprotected' : ∀ p ∈ S,
              Tendsto (fun n => L' n p.1 p.2.1 p.2.2)
                atTop (nhds 0) := by
            intro p hp
            exact (hprotected p hp).comp hφ.tendsto_atTop
          obtain ⟨Pfinal, ψ, Llim, hP'final, hfinalS, hψ, hlim⟩ :=
            ih (total - P'.card) hremain P' L' rfl hL'
              hextendS hprotected'
          refine ⟨Pfinal, φ ∘ ψ, Llim,
            Finset.Subset.trans (Finset.ssubset_iff_subset_ne.mp hstrict).1
              hP'final,
            hfinalS, hφ.comp hψ, ?_⟩
          simpa only [L', Function.comp_def] using hlim
  exact aux (total - P₀.card) P₀ L₀ rfl hL₀ hP₀S hprotected₀

/-- Finite-termination specialization to the projective loss family of a
convergent Fink sequence. -/
theorem exists_subsequence_maskedFinkProjectiveLoss_tendsto
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (β : ℕ → ℝ)
    (W K : G.State → Payoff ι) {U : ℝ}
    (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U)
    (hz : Tendsto z atTop (nhds zlim)) :
    ∃ (P : Finset G.FinkPureActionIndex) (φ : ℕ → ℕ)
      (Llim : G.FinkPureActionVector),
      StrictMono φ ∧ Tendsto (z ∘ φ) atTop (nhds zlim) ∧
      Tendsto ((fun n => G.maskFinkActionVector P
        (G.finkProjectiveLossVector (β n) W K (z n))) ∘ φ)
          atTop (nhds Llim) := by
  obtain ⟨P, φ, Llim, hempty, hφ, hlim⟩ :=
    G.exists_subsequence_maskedFinkActionVector_tendsto
      ∅ (fun n => G.finkProjectiveLossVector (β n) W K (z n))
        (fun n s who d => G.finkProjectiveLossVector_nonneg
          (β n) W K (z n) s who d)
  refine ⟨P, φ, Llim, hφ, hz.comp hφ.tendsto_atTop, ?_⟩
  simpa only [Function.comp_def] using hlim

/-- Boundary-certificate specialization with the limiting support protected.
After finitely many action-loss scales, all remaining losses have a finite
vector limit, while the accumulated pruning mask is disjoint from every
action played by the limiting profile. -/
theorem exists_terminal_maskedFinkProjectiveLoss_subsequence
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {β : ℕ → ℝ} {U : ℝ}
    (hβ0 : ∀ n, 0 ≤ β n) (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (W K : G.State → Payoff ι)
    (hKlim : Tendsto (G.compactifyFinkBias ∘
      fun n => G.finkRelativeBias (β n) W (z n)) atTop (nhds K))
    (hKnorm : ‖K‖ = 1) :
    ∃ (P : Finset G.FinkPureActionIndex) (φ : ℕ → ℕ)
      (Llim : G.FinkPureActionVector),
      Disjoint P (G.finkSupportIndices zlim) ∧ StrictMono φ ∧
      Tendsto (z ∘ φ) atTop (nhds zlim) ∧
      Tendsto ((G.compactifyFinkBias ∘
        fun n => G.finkRelativeBias (β n) W (z n)) ∘ φ)
          atTop (nhds K) ∧
      Tendsto ((fun n => G.maskFinkActionVector P
        (G.finkProjectiveLossVector (β n) W K (z n))) ∘ φ)
          atTop (nhds Llim) := by
  let L : ℕ → G.FinkPureActionVector := fun n =>
    G.finkProjectiveLossVector (β n) W K (z n)
  let S := G.finkSupportIndices zlim
  have hprotected : ∀ p ∈ S,
      Tendsto (fun n => L n p.1 p.2.1 p.2.2) atTop (nhds 0) := by
    intro p hp
    have hpos : G.finkProfile zlim p.1 p.2.1 p.2.2 ≠ 0 := by
      exact (G.mem_finkSupportIndices zlim p).mp hp
    exact G.tendsto_finkProjectiveLossVector_zero_of_limit_support
      hβ0 hβ1 hpay hz hfix W K hKlim hKnorm
        p.1 p.2.1 p.2.2 hpos
  obtain ⟨P, φ, Llim, hempty, hPS, hφ, hlim⟩ :=
    G.exists_subsequence_maskedFinkActionVector_tendsto_protected
      ∅ S L (fun n s who d => G.finkProjectiveLossVector_nonneg
        (β n) W K (z n) s who d)
      (Finset.disjoint_empty_left S) hprotected
  refine ⟨P, φ, Llim, hPS, hφ, hz.comp hφ.tendsto_atTop, ?_, ?_⟩
  · have ht := hKlim.comp hφ.tendsto_atTop
    simpa only [Function.comp_def] using ht
  · simpa only [L, Function.comp_def] using hlim

/-- The next finite action-face extraction.  Either all first-layer losses
are bounded along a subsequence, or their projective boundary direction is a
nonzero nonnegative vector which vanishes on the current limiting support.
Hence the boundary case identifies an action outside that support to prune
at the next lexicographic layer. -/
theorem exists_finkProjectiveLoss_subsequence_interior_or_pruningDirection
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {β : ℕ → ℝ} {U : ℝ}
    (hβ0 : ∀ n, 0 ≤ β n) (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (W K : G.State → Payoff ι)
    (hKlim : Tendsto (G.compactifyFinkBias ∘
      fun n => G.finkRelativeBias (β n) W (z n)) atTop (nhds K))
    (hKnorm : ‖K‖ = 1) :
    ∃ (Llim : G.FinkPureActionVector) (φ : ℕ → ℕ),
      StrictMono φ ∧
      Tendsto (G.compactifyFinkActionVector ∘
          (fun n => G.finkProjectiveLossVector
            (β n) W K (z n)) ∘ φ)
        atTop (nhds Llim) ∧
      ((‖Llim‖ < 1 ∧
          Tendsto ((fun n => G.finkProjectiveLossVector
            (β n) W K (z n)) ∘ φ) atTop
              (nhds (G.decompactifyFinkActionVector Llim))) ∨
        (‖Llim‖ = 1 ∧
          Tendsto (fun n =>
            ‖G.finkProjectiveLossVector
              (β (φ n)) W K (z (φ n))‖) atTop atTop ∧
          (∀ s who (d : G.Act who), 0 ≤ Llim s who d) ∧
          (∀ s who (d : G.Act who),
            G.finkProfile zlim s who d ≠ 0 → Llim s who d = 0) ∧
          (∀ s who (d : G.Act who), 0 < Llim s who d →
            G.finkProfile zlim s who d = 0 ∧
            Tendsto (fun n =>
              ((G.finkProfile (z (φ n)) s who) d).toReal *
                (1 + ‖G.finkProjectiveLossVector
                  (β (φ n)) W K (z (φ n))‖))
              atTop (nhds 0)) ∧
          (∃ (s : G.State) (who : ι) (d : G.Act who),
            0 < Llim s who d))) := by
  let L : ℕ → G.FinkPureActionVector := fun n =>
    G.finkProjectiveLossVector (β n) W K (z n)
  obtain ⟨Llim, φ, hφ, hLlim, halternative⟩ :=
    G.exists_finkActionVector_subsequence_interior_or_direction L
  refine ⟨Llim, φ, hφ, ?_, ?_⟩
  · simpa only [L, Function.comp_def] using hLlim
  rcases halternative with hinterior | hboundary
  · exact Or.inl (by simpa only [L, Function.comp_def] using hinterior)
  · right
    have hcoordTendsto (s : G.State) (who : ι) (d : G.Act who) :
        Tendsto (fun n =>
          G.compactifyFinkActionVector (L (φ n)) s who d)
          atTop (nhds (Llim s who d)) := by
      have hc : Continuous (fun Q : G.FinkPureActionVector => Q s who d) := by
        fun_prop
      have ht := (hc.tendsto Llim).comp hLlim
      simpa only [Function.comp_def] using ht
    have hnonneg : ∀ s who (d : G.Act who), 0 ≤ Llim s who d := by
      intro s who d
      apply ge_of_tendsto' (hcoordTendsto s who d)
      intro n
      apply G.compactifyFinkActionVector_apply_nonneg
      intro s' who' d'
      exact G.finkProjectiveLossVector_nonneg
        (β (φ n)) W K (z (φ n)) s' who' d'
    have hsupport : ∀ s who (d : G.Act who),
        G.finkProfile zlim s who d ≠ 0 → Llim s who d = 0 := by
      intro s who d hpos
      have hmain :=
        G.tendsto_finkProjectiveBiasScale_mul_continuationGain_of_limit_support
          hβ0 hβ1 hpay hz hfix W K hKlim hKnorm s who d hpos
      have hKcurrent := G.tendsto_finkContinuationGain hz K s who d
      have hgain : Tendsto (fun n =>
          G.finkProjectiveGainVector (β n) W K (z n) s who d)
          atTop (nhds 0) := by
        have ht := hmain.add hKcurrent
        simpa only [finkProjectiveGainVector, neg_add_cancel] using ht
      have hgainφ := hgain.comp hφ.tendsto_atTop
      have hlossφ : Tendsto (fun n => L (φ n) s who d)
          atTop (nhds 0) := by
        have ht := hgainφ.neg.max
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ))
            atTop (nhds 0))
        simpa only [L, finkProjectiveLossVector, Function.comp_def,
          neg_zero, max_self] using ht
      have hcompactZero :=
        G.tendsto_compactifyFinkActionVector_apply_zero
          (L := L ∘ φ)
          (fun n s' who' d' => G.finkProjectiveLossVector_nonneg
            (β (φ n)) W K (z (φ n)) s' who' d')
          s who d (by simpa only [Function.comp_def] using hlossφ)
      exact tendsto_nhds_unique (hcoordTendsto s who d) hcompactZero
    have hpositive : ∃ (s : G.State) (who : ι) (d : G.Act who),
        0 < Llim s who d := by
      by_contra hnot
      have hnonpos : ∀ s who (d : G.Act who), Llim s who d ≤ 0 := by
        intro s who d
        exact le_of_not_gt fun h => hnot ⟨s, who, d, h⟩
      have hzero : Llim = 0 := by
        funext s who d
        exact le_antisymm (hnonpos s who d) (hnonneg s who d)
      rw [hzero] at hboundary
      simp at hboundary
    have hprune : ∀ s who (d : G.Act who), 0 < Llim s who d →
        G.finkProfile zlim s who d = 0 ∧
        Tendsto (fun n =>
          ((G.finkProfile (z (φ n)) s who) d).toReal *
            (1 + ‖G.finkProjectiveLossVector
              (β (φ n)) W K (z (φ n))‖))
          atTop (nhds 0) := by
      intro s who d hdpos
      have hweighted :=
        (G.tendsto_finkProfile_mul_projectiveLoss_zero_of_boundary
          hβ0 hβ1 hpay hz hfix W K hKlim hKnorm s who d).comp
            hφ.tendsto_atTop
      have hrate :=
        G.tendsto_mul_one_add_norm_finkActionVector_zero_of_compactify_apply_pos
          (L := L ∘ φ)
          (p := fun n => ((G.finkProfile (z (φ n)) s who) d).toReal)
          s who d hdpos (hcoordTendsto s who d)
            (by simpa only [L, Function.comp_def] using hweighted)
      refine ⟨?_, by simpa only [L, Function.comp_def] using hrate⟩
      by_contra hpos
      exact (not_lt_of_ge (le_of_eq (hsupport s who d hpos)) hdpos)
    obtain ⟨s, who, d, hdpos⟩ := hpositive
    refine ⟨hboundary.1, ?_, hnonneg, hsupport,
      hprune, s, who, d, hdpos⟩
    · simpa only [L, Function.comp_def] using hboundary.2

/-- A strictly value-decreasing pure action has zero probability in the
limiting stationary profile. -/
theorem finkLimit_strictDeviation_probability_zero
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
    (hstrict : expect (pmfPi (Function.update (G.finkProfile z s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) < W s who) :
    G.finkProfile z s who d = 0 := by
  by_contra hne
  have heq := G.finkLimit_support_continuation_eq
    z W s who d hharmonic hexcessive hne
  linarith

/-- Along a convergent Fink family, the probability of every strictly
value-decreasing limiting action tends to zero. -/
theorem tendsto_finkProfile_strictDeviation_probability_zero
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim)) (W : G.State → Payoff ι)
    (s : G.State) (who : ι) (d : G.Act who)
    (hharmonic : W s who =
      expect (pmfPi (G.finkProfile zlim s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)))
    (hexcessive : ∀ d' : G.Act who,
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d'))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who)
    (hstrict : expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) < W s who) :
    Tendsto (fun n => G.finkProfile (z n) s who d) atTop (nhds 0) := by
  have hzero := G.finkLimit_strictDeviation_probability_zero
    zlim W s who d hharmonic hexcessive hstrict
  have ht := G.finkProfile_convergesPointwise hz s who d
  simpa only [hzero] using ht

/-- A strict limiting continuation loss persists with a fixed positive
margin along all sufficiently late discounted Fink profiles. -/
theorem eventually_finkProfile_strictDeviation_margin
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim)) (W : G.State → Payoff ι)
    (s : G.State) (who : ι) (d : G.Act who)
    (hstrict : expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) < W s who) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop,
      expect (pmfPi (Function.update (G.finkProfile (z n) s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who - δ := by
  let L := expect (pmfPi (Function.update (G.finkProfile zlim s)
      who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who))
  let δ := (W s who - L) / 2
  have hδ : 0 < δ := by dsimp [δ, L]; linarith
  have ht := G.tendsto_finkProfile_pureDeviationContinuation hz
    (fun s' => W s' who) s who d
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht δ hδ
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [Filter.eventually_atTop.2 ⟨N, hN⟩] with n hn
  rw [Real.dist_eq, abs_lt] at hn
  dsimp [δ, L]
  dsimp [L, δ] at hn
  linarith

/-- Quantitative tail pruning along a convergent Fink family.  Once a limiting
action has a strict continuation loss, its current probability is bounded by
the same harmonic/excessive error that controls the family. -/
theorem eventually_finkProfile_strictDeviation_probability_mul_le
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim)) (W : G.State → Payoff ι)
    (s : G.State) (who : ι) (d : G.Act who)
    (hstrict : expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) < W s who)
    (r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n)
    (hharmonic : ∀ n,
      W s who - r n ≤ expect (pmfPi (G.finkProfile (z n) s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)))
    (hexcessive : ∀ n (d' : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile (z n) s)
          who (PMF.pure d'))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who + r n) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop,
      ((G.finkProfile (z n) s who) d).toReal * δ ≤ 2 * r n := by
  obtain ⟨δ, hδ, hmargin⟩ :=
    G.eventually_finkProfile_strictDeviation_margin hz W s who d hstrict
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hmargin] with n hn
  exact G.strictContinuation_probability_mul_gap_le
    (G.finkProfile (z n)) W s who d δ (r n) (hr n)
      (hharmonic n) (hexcessive n) hn

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

/-- Equivalent aggregate form: the total probability outside the limiting
continuation-neutral face is `O(r n)`, uniformly over states and players. -/
theorem eventually_strictContinuationMass_mul_le
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
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop, ∀ s who,
      G.strictContinuationMass (G.finkProfile zlim) (G.finkProfile (z n))
          W s who * δ ≤
        2 * (G.strictContinuationActions (G.finkProfile zlim) W s who).card *
          r n := by
  obtain ⟨δ, hδ, hpoint⟩ :=
    G.eventually_all_strictDeviation_probability_mul_le
      hz W r hr hharmonic hexcessive
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hpoint] with n hn
  intro s who
  apply G.strictContinuationMass_mul_le
  intro d hd
  exact hn s who d (Finset.mem_filter.mp hd).2

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

/-- A statewise excessive continuation value becomes a supermartingale in
expectation against every history-dependent unilateral deviation. -/
theorem expectedStateValue_antitone_of_mixedDeviationContinuation_le
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (who : ι) (dev : G.BehaviorStrategy who) (s₀ : G.State)
    (hexcessive : ∀ s (d : PMF (G.Act who)),
      expect (pmfPi (Function.update (G.finkProfile z s) who d))
          (fun a => expect (G.transition s a)
            (fun s' => G.finkValue z s' who)) ≤
        G.finkValue z s who) :
    Antitone (fun t => G.expectedStateValue
      (Function.update (G.markovBehaviorProfile (G.finkProfile z)) who dev)
      s₀ t (fun s => G.finkValue z s who)) := by
  apply antitone_nat_of_succ_le
  intro t
  rw [G.expectedStateValue_succ]
  apply expect_mono
  intro h
  rw [G.stageActionDist_update_markovBehaviorProfile]
  exact hexcessive h.2 (dev t h)

/-- Consequently, the expected limiting Fink value at every future horizon
is capped by its initial-state value under any unilateral behavioral
deviation. -/
theorem expectedStateValue_deviation_le_initial_of_mixedContinuation_le
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (who : ι) (dev : G.BehaviorStrategy who) (s₀ : G.State)
    (hexcessive : ∀ s (d : PMF (G.Act who)),
      expect (pmfPi (Function.update (G.finkProfile z s) who d))
          (fun a => expect (G.transition s a)
            (fun s' => G.finkValue z s' who)) ≤
        G.finkValue z s who)
    (T : ℕ) :
    G.expectedStateValue
        (Function.update (G.markovBehaviorProfile (G.finkProfile z)) who dev)
        s₀ T (fun s => G.finkValue z s who) ≤
      G.finkValue z s₀ who := by
  have hanti := G.expectedStateValue_antitone_of_mixedDeviationContinuation_le
    z who dev s₀ hexcessive
  simpa using hanti (Nat.zero_le T)

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

/-- A useful sufficient form of calendar selectability.  It separates the
remaining construction into vanishing terminal bias, vanishing average switch
cost, ordinary convergence of value errors, and a summable total transition
drift. -/
theorem isIndexedFinkCalendarSelectable_of_summableDrift
    (β : ℕ → ℝ) (U : ℝ) (q r : ℕ → ℝ)
    (hcalendar : ∀ ε : ℝ, 0 < ε → ∃ κ : ℕ → ℕ,
      Tendsto (fun T : ℕ => (T : ℝ)⁻¹ * finkScaledBiasBound β U (κ T))
        atTop (nhds 0) ∧
      Tendsto (fun T : ℕ => (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
        indexedFinkSwitchError β U κ t) atTop (nhds 0) ∧
      Tendsto (q ∘ κ) atTop (nhds 0) ∧
      (∀ t, 0 ≤ r (κ t)) ∧ Summable (r ∘ κ) ∧
      ∑' t, r (κ t) ≤ ε) :
    IsIndexedFinkCalendarSelectable β U q r := by
  intro η hη
  have hhalf : 0 < η / 2 := by linarith
  obtain ⟨κ, hterminal, hswitch, hq, hr0, hrsum, hrTotal⟩ :=
    hcalendar (η / 2) hhalf
  have hqavg : Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
      ∑ t ∈ Finset.range T, q (κ t)) atTop (nhds 0) := by
    simpa only [Function.comp_apply] using hq.cesaro
  have hinitial : Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
      finkScaledBiasBound β U (κ 0)) atTop (nhds 0) := by
    have ht := tendsto_const_div_atTop_nhds_zero_nat
      (finkScaledBiasBound β U (κ 0))
    simpa only [div_eq_inv_mul] using ht
  have hbias : Tendsto (fun T : ℕ =>
      (finkScaledBiasBound β U (κ 0) +
          finkScaledBiasBound β U (κ T)) / (T : ℝ) +
        (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
          indexedFinkSwitchError β U κ t) atTop (nhds 0) := by
    have ht := (hinitial.add hterminal).add hswitch
    convert ht using 1
    · funext T
      rw [div_eq_inv_mul]
      ring
    · simp
  obtain ⟨Nb, hNb⟩ := Metric.tendsto_atTop.mp hbias η hη
  obtain ⟨Nq, hNq⟩ := Metric.tendsto_atTop.mp hqavg (η / 2) hhalf
  let T₀ := max 1 (max Nb Nq)
  refine ⟨κ, T₀, fun T hT => ?_⟩
  have hTone : 1 ≤ T := le_trans (le_max_left _ _) hT
  have hTpos : 0 < T := Nat.zero_lt_of_lt hTone
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hTpos
  have hNbT : Nb ≤ T := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hT)
  have hNqT : Nq ≤ T := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hT)
  have hbiasLe :
      (finkScaledBiasBound β U (κ 0) +
          finkScaledBiasBound β U (κ T)) / (T : ℝ) +
        (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
          indexedFinkSwitchError β U κ t ≤ η := by
    have hb := hNb T hNbT
    rw [Real.dist_eq, sub_zero] at hb
    exact (le_abs_self _).trans hb.le
  have hqLe : (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, q (κ t) ≤ η / 2 := by
    have hqT := hNq T hNqT
    rw [Real.dist_eq, sub_zero] at hqT
    exact (le_abs_self _).trans hqT.le
  have hprefix : ∀ t, (∑ k ∈ Finset.range t, r (κ k)) ≤
      ∑' k, r (κ k) := by
    intro t
    exact hrsum.sum_le_tsum (Finset.range t) (fun k _ => hr0 k)
  have htarget : (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
      (q (κ t) + ∑ k ∈ Finset.range t, r (κ k)) ≤ η := by
    have hsum : (∑ t ∈ Finset.range T,
        (q (κ t) + ∑ k ∈ Finset.range t, r (κ k))) ≤
        ∑ t ∈ Finset.range T, (q (κ t) + ∑' k, r (κ k)) :=
      Finset.sum_le_sum fun t _ => add_le_add le_rfl (hprefix t)
    have hmul := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hTreal.le)
    calc
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
          (q (κ t) + ∑ k ∈ Finset.range t, r (κ k)) ≤
          (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
            (q (κ t) + ∑' k, r (κ k)) := hmul
      _ = (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, q (κ t) +
          ∑' k, r (κ k) := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp [ne_of_gt hTreal]
      _ ≤ η / 2 + η / 2 := add_le_add hqLe hrTotal
      _ = η := by ring
  exact ⟨hTpos, hbiasLe, htarget⟩

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

end StochasticGame
end GameTheory
