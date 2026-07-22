/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.FinkSchedule
import Math.MeanErgodic
import Mathlib.Analysis.PSeries
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

/-- Remove the leading radial direction from a bias vector.  This is the
next, lower-order potential in a lexicographic bias expansion. -/
def finkCorrectedBias (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι]
    (H K : G.State → Payoff ι) : G.State → Payoff ι :=
  H - (1 + ‖H‖) • K

/-- A coordinate of a state/player bias vector. -/
abbrev FinkBiasIndex (G : StochasticGame ι) := G.State × ι

def finkBiasCoordinate (G : StochasticGame ι)
    (H : G.State → Payoff ι) (p : G.FinkBiasIndex) : ℝ :=
  H p.1 p.2

/-- Every state/player coordinate is bounded by the finite-product sup norm. -/
theorem abs_finkBiasCoordinate_le_norm
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    (H : G.State → Payoff ι) (s : G.State) (who : ι) :
    |H s who| ≤ ‖H‖ := by
  have hplayer : ‖H s who‖ ≤ ‖H s‖ := norm_le_pi_norm (H s) who
  have hstate : ‖H s‖ ≤ ‖H‖ := norm_le_pi_norm H s
  simpa only [Real.norm_eq_abs] using hplayer.trans hstate

/-- Add one protected state/player coordinate without exposing a decidable
equality assumption in theorem statements. -/
noncomputable def extendFinkBiasMask (G : StochasticGame ι)
    (P : Finset G.FinkBiasIndex) (p : G.FinkBiasIndex) :
    Finset G.FinkBiasIndex := by
  classical
  exact insert p P

theorem mem_extendFinkBiasMask_iff (G : StochasticGame ι)
    (P : Finset G.FinkBiasIndex) (p q : G.FinkBiasIndex) :
    q ∈ G.extendFinkBiasMask P p ↔ q = p ∨ q ∈ P := by
  classical
  simp [extendFinkBiasMask]

/-- In the finite state/player cube, every nonzero bias attains its sup norm
at some state/player coordinate. -/
theorem exists_finkBiasCoordinate_abs_eq_norm
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    (H : G.State → Payoff ι) (hH : ‖H‖ ≠ 0) :
    ∃ p : G.FinkBiasIndex, |G.finkBiasCoordinate H p| = ‖H‖ := by
  letI : Nonempty G.State := by
    obtain h | h := isEmpty_or_nonempty G.State
    · haveI : IsEmpty G.State := h
      exact False.elim (hH (by simp only [Subsingleton.elim H 0, norm_zero]))
    · exact h
  letI : Nonempty ι := by
    obtain h | h := isEmpty_or_nonempty ι
    · haveI : IsEmpty ι := h
      exact False.elim (hH (by simp only [Subsingleton.elim H 0, norm_zero]))
    · exact h
  obtain ⟨s, hs⟩ := (IsGreatest.pi_norm H).1
  obtain ⟨who, hwho⟩ := (IsGreatest.pi_norm (H s)).1
  refine ⟨⟨s, who⟩, ?_⟩
  simpa only [finkBiasCoordinate, Real.norm_eq_abs] using hwho.trans hs

/-- After passing to a subsequence, one fixed signed coordinate attains the
norm of every bias in the subsequence. -/
theorem exists_finkBiasCoordinate_eq_smul_norm_subsequence
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    (H : ℕ → G.State → Payoff ι) (hne : ∀ n, ‖H n‖ ≠ 0) :
    ∃ (p : G.FinkBiasIndex) (σ : ℝ) (φ : ℕ → ℕ),
      (σ = 1 ∨ σ = -1) ∧ StrictMono φ ∧
        ∀ n, G.finkBiasCoordinate (H (φ n)) p = σ * ‖H (φ n)‖ := by
  classical
  choose p hp using fun n => G.exists_finkBiasCoordinate_abs_eq_norm
    (H n) (hne n)
  let sign : ℕ → Bool := fun n => decide
    (0 ≤ G.finkBiasCoordinate (H n) (p n))
  let color : ℕ → G.FinkBiasIndex × Bool := fun n => (p n, sign n)
  obtain ⟨⟨p₀, b⟩, hinfinite⟩ := Finite.exists_infinite_fiber color
  have hunbounded : ∀ N, ∃ n > N, color n = (p₀, b) := by
    intro N
    by_contra h
    push Not at h
    have hsubset : color ⁻¹' ({(p₀, b)} : Set (G.FinkBiasIndex × Bool)) ⊆
        Set.Iic N := by
      intro n hn
      by_contra hnle
      have hnN : N < n := Nat.lt_of_not_ge hnle
      have hcolor : color n = (p₀, b) := by simpa using hn
      exact (h n hnN) hcolor
    exact ((Set.finite_Iic N).subset hsubset).not_infinite
      (Set.infinite_coe_iff.mp hinfinite)
  obtain ⟨φ, hφ, hcolor⟩ := Nat.exists_strictMono_subsequence hunbounded
  cases b with
  | false =>
      refine ⟨p₀, -1, φ, Or.inr rfl, hφ, fun n => ?_⟩
      have hpEq : p (φ n) = p₀ := congrArg Prod.fst (hcolor n)
      have hbEq : sign (φ n) = false := congrArg Prod.snd (hcolor n)
      have hneg : ¬0 ≤ G.finkBiasCoordinate (H (φ n)) p₀ := by
        have hbEq' : decide
            (0 ≤ G.finkBiasCoordinate (H (φ n)) (p (φ n))) = false := by
          simpa only [sign] using hbEq
        have hn := of_decide_eq_false hbEq'
        simpa only [hpEq] using hn
      have habs : |G.finkBiasCoordinate (H (φ n)) p₀| = ‖H (φ n)‖ := by
        simpa only [hpEq] using hp (φ n)
      rw [abs_of_neg (lt_of_not_ge hneg)] at habs
      linarith
  | true =>
      refine ⟨p₀, 1, φ, Or.inl rfl, hφ, fun n => ?_⟩
      have hpEq : p (φ n) = p₀ := congrArg Prod.fst (hcolor n)
      have hbEq : sign (φ n) = true := congrArg Prod.snd (hcolor n)
      have hnonneg : 0 ≤ G.finkBiasCoordinate (H (φ n)) p₀ := by
        have hbEq' : decide
            (0 ≤ G.finkBiasCoordinate (H (φ n)) (p (φ n))) = true := by
          simpa only [sign] using hbEq
        have hn := of_decide_eq_true hbEq'
        simpa only [hpEq] using hn
      have habs : |G.finkBiasCoordinate (H (φ n)) p₀| = ‖H (φ n)‖ := by
        simpa only [hpEq] using hp (φ n)
      rw [abs_of_nonneg hnonneg] at habs
      simpa only [one_mul] using habs

/-- At a signed norm-attaining coordinate, subtracting a boundary direction
with the same signed coordinate leaves the exact bounded value `-σ`. -/
theorem finkCorrectedBias_apply_of_eq_smul_norm
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    (H K : G.State → Payoff ι) (p : G.FinkBiasIndex) (σ : ℝ)
    (hH : G.finkBiasCoordinate H p = σ * ‖H‖)
    (hK : G.finkBiasCoordinate K p = σ) :
    G.finkBiasCoordinate (G.finkCorrectedBias H K) p = -σ := by
  unfold finkBiasCoordinate at hH hK
  unfold finkBiasCoordinate finkCorrectedBias
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hH, hK]
  ring

/-- First corrected relative bias of a discounted Fink point around `W`. -/
def finkCorrectedRelativeBias (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (β : ℝ) (W K : G.State → Payoff ι) {U : ℝ}
    (z : G.finkDomain U) : G.State → Payoff ι :=
  G.finkCorrectedBias (G.finkRelativeBias β W z) K

/-- Error left after the leading boundary direction cancels the magnified
harmonic residual of `W`. -/
def finkPoissonRemainder (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (β : ℝ) (W K : G.State → Payoff ι) {U : ℝ}
    (z : G.finkDomain U) (s : G.State) (who : ι) : ℝ :=
  G.finkProjectiveBiasScale β W z *
      G.finkContinuationResidual W z s who -
    (K s who - G.finkContinuationEU K z s who)

/-- All coordinates of the first Poisson remainder. -/
def finkPoissonRemainderVector (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (β : ℝ) (W K : G.State → Payoff ι) {U : ℝ}
    (z : G.finkDomain U) : G.State → Payoff ι :=
  fun s who => G.finkPoissonRemainder β W K z s who

/-- Successor-value vector under the current decoded Fink profile. -/
def finkContinuationVector (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (K : G.State → Payoff ι) {U : ℝ}
    (z : G.finkDomain U) : G.State → Payoff ι :=
  fun s who => G.finkContinuationEU K z s who

/-- All on-profile continuation residuals of a target vector. -/
def finkContinuationResidualVector (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (W : G.State → Payoff ι) {U : ℝ}
    (z : G.finkDomain U) : G.State → Payoff ι :=
  fun s who => G.finkContinuationResidual W z s who

/-- State transition kernel induced by one decoded stationary Fink profile. -/
def finkStateKernel (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : G.finkDomain U) (s : G.State) : PMF G.State :=
  (pmfPi (G.finkProfile z s)).bind (G.transition s)

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

/-- Mean-ergodic criterion for representing an on-profile forcing by one
finite state potential.  It is enough that every player's forcing have zero
Cesàro component under the limiting stationary state kernel. -/
theorem exists_finkContinuationResidualVector_eq_of_tendsto_cesaro_zero
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : G.finkDomain U) (F : G.State → Payoff ι)
    (hzero : ∀ who, Tendsto (fun T : ℕ =>
      (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T,
        ((Math.MeanErgodic.markovOperator (G.finkStateKernel z)) ^ t)
          (fun s => F s who)) atTop (nhds 0)) :
    ∃ K : G.State → Payoff ι,
      G.finkContinuationResidualVector K z = F := by
  have hplayer : ∀ who, ∃ k : G.State → ℝ, ∀ s,
      expect (G.finkStateKernel z s) k - k s = F s who := by
    intro who
    exact Math.MeanErgodic.exists_poisson_of_tendsto_cesaro_zero
      (G.finkStateKernel z) (fun s => F s who) (hzero who)
  choose k hk using hplayer
  let K : G.State → Payoff ι := fun s who => k who s
  refine ⟨K, ?_⟩
  ext s who
  unfold finkContinuationResidualVector finkContinuationResidual
    finkContinuationEU
  rw [← G.expect_finkStateKernel_eq z s (k who)]
  exact hk who s

/-- Exact mean-ergodic characterization of the range of the Fink
continuation-residual operator. -/
theorem exists_finkContinuationResidualVector_eq_iff_tendsto_cesaro_zero
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : G.finkDomain U) (F : G.State → Payoff ι) :
    (∃ K : G.State → Payoff ι,
        G.finkContinuationResidualVector K z = F) ↔
      ∀ who, Tendsto (fun T : ℕ =>
        (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T,
          ((Math.MeanErgodic.markovOperator (G.finkStateKernel z)) ^ t)
            (fun s => F s who)) atTop (nhds 0) := by
  constructor
  · rintro ⟨K, hK⟩ who
    apply (Math.MeanErgodic.exists_poisson_iff_tendsto_cesaro_zero
      (G.finkStateKernel z) (fun s => F s who)).mp
    refine ⟨fun s => K s who, fun s => ?_⟩
    have hcoord := congrFun (congrFun hK s) who
    unfold finkContinuationResidualVector finkContinuationResidual
      finkContinuationEU at hcoord
    rw [G.expect_finkStateKernel_eq z s (fun s' => K s' who)]
    exact hcoord
  · exact G.exists_finkContinuationResidualVector_eq_of_tendsto_cesaro_zero
      z F

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

/-- The harmonic obstruction in a Fink continuation-residual decomposition
is unique.  In particular it cannot be changed by choosing a different
Poisson potential. -/
theorem finkHarmonicObstruction_unique
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : G.finkDomain U) (F O K O' K' : G.State → Payoff ι)
    (hO : G.finkContinuationResidualVector O z = 0)
    (hdecomp : F = O + G.finkContinuationResidualVector K z)
    (hO' : G.finkContinuationResidualVector O' z = 0)
    (hdecomp' : F = O' + G.finkContinuationResidualVector K' z) :
    O = O' := by
  ext s who
  have ho : ∀ t, expect (G.finkStateKernel z t) (fun s' => O s' who) =
      O t who := by
    intro t
    have hcoord := congrFun (congrFun hO t) who
    unfold finkContinuationResidualVector finkContinuationResidual
      finkContinuationEU at hcoord
    rw [← G.expect_finkStateKernel_eq z t (fun s' => O s' who)] at hcoord
    simp only [Pi.zero_apply] at hcoord
    exact sub_eq_zero.mp hcoord
  have hdecompCoord : ∀ t, F t who = O t who +
      (expect (G.finkStateKernel z t) (fun s' => K s' who) - K t who) := by
    intro t
    have hcoord := congrFun (congrFun hdecomp t) who
    unfold finkContinuationResidualVector finkContinuationResidual
      finkContinuationEU at hcoord
    change F t who = O t who +
      ((expect (pmfPi (G.finkProfile z t)) fun a =>
        expect (G.transition t a) (fun s' => K s' who)) - K t who) at hcoord
    rw [← G.expect_finkStateKernel_eq z t (fun s' => K s' who)] at hcoord
    exact hcoord
  have ho' : ∀ t, expect (G.finkStateKernel z t) (fun s' => O' s' who) =
      O' t who := by
    intro t
    have hcoord := congrFun (congrFun hO' t) who
    unfold finkContinuationResidualVector finkContinuationResidual
      finkContinuationEU at hcoord
    rw [← G.expect_finkStateKernel_eq z t (fun s' => O' s' who)] at hcoord
    simp only [Pi.zero_apply] at hcoord
    exact sub_eq_zero.mp hcoord
  have hdecompCoord' : ∀ t, F t who = O' t who +
      (expect (G.finkStateKernel z t) (fun s' => K' s' who) - K' t who) := by
    intro t
    have hcoord := congrFun (congrFun hdecomp' t) who
    unfold finkContinuationResidualVector finkContinuationResidual
      finkContinuationEU at hcoord
    change F t who = O' t who +
      ((expect (pmfPi (G.finkProfile z t)) fun a =>
        expect (G.transition t a) (fun s' => K' s' who)) - K' t who) at hcoord
    rw [← G.expect_finkStateKernel_eq z t (fun s' => K' s' who)] at hcoord
    exact hcoord
  have hunique := Math.MeanErgodic.harmonic_eq_of_add_poisson_eq
    (G.finkStateKernel z) (fun t => F t who)
    (fun t => O t who) (fun t => K t who)
    (fun t => O' t who) (fun t => K' t who)
    ho hdecompCoord ho' hdecompCoord'
  exact congrFun hunique s

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

/-- Remainder produced by removing direction `L` from a bias `J` whose
Bellman forcing is `a • E`. -/
def finkNextPoissonRemainderVector (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (a : ℝ) (E J L : G.State → Payoff ι) {U : ℝ}
    (z : G.finkDomain U) : G.State → Payoff ι :=
  (a / (1 + ‖J‖)) • E - (L - G.finkContinuationVector L z)

/-- Deviation-side forcing after removing one bias direction.  It is the
exact analogue of `finkNextPoissonRemainderVector` for pure-action gains. -/
def finkNextDeviationGain (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (a : ℝ) (D : G.State → ∀ who : ι, G.Act who → ℝ)
    (J K : G.State → Payoff ι) {U : ℝ} (z : G.finkDomain U)
  (s : G.State) (who : ι) (d : G.Act who) : ℝ :=
  (a / (1 + ‖J‖)) * D s who d +
    G.finkContinuationGain K z s who d

/-- Reference potential represented after removing one projective bias
direction.  Its continuation residual and pure-deviation gain are exactly
the next Poisson and deviation forcings. -/
def finkNextReferenceVector (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι]
    (a : ℝ) (J R K : G.State → Payoff ι) : G.State → Payoff ι :=
  (a / (1 + ‖J‖)) • R + K

/-- Scalar coefficient of the projective direction used to correct the
current reference potential. -/
def finkReferenceCorrectionScale (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] (a : ℝ)
    (J : G.State → Payoff ι) : ℝ :=
  (1 + ‖J‖) / a

/-- Boundary correction applied to a reference potential. -/
def finkReferenceCorrection (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι]
    (a : ℝ) (J K : G.State → Payoff ι) : G.State → Payoff ι :=
  G.finkReferenceCorrectionScale a J • K

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

/-- The zero potential has zero continuation residual. -/
theorem finkContinuationResidualVector_zero
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : G.finkDomain U) :
    G.finkContinuationResidualVector 0 z = 0 := by
  ext s who
  simp [finkContinuationResidualVector, finkContinuationResidual,
    finkContinuationEU]

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

/-- Continuation residuals respect subtraction. -/
theorem finkContinuationResidualVector_sub
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (R K : G.State → Payoff ι) {U : ℝ} (z : G.finkDomain U) :
    G.finkContinuationResidualVector (R - K) z =
      G.finkContinuationResidualVector R z -
        G.finkContinuationResidualVector K z := by
  rw [sub_eq_add_neg, G.finkContinuationResidualVector_add,
    G.finkContinuationResidualVector_neg, sub_eq_add_neg]

/-- Once one stationary Poisson correction is known, every other correction
is obtained from it by adding an on-profile harmonic potential. -/
theorem finkPoissonCorrection_iff_sub_harmonic
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : G.finkDomain U) (F K K' : G.State → Payoff ι)
    (hK : F = -G.finkContinuationResidualVector K z) :
    F = -G.finkContinuationResidualVector K' z ↔
      G.finkContinuationResidualVector (K' - K) z = 0 := by
  constructor
  · intro hK'
    have hneg : -G.finkContinuationResidualVector K' z =
        -G.finkContinuationResidualVector K z := hK'.symm.trans hK
    have hresidual : G.finkContinuationResidualVector K' z =
        G.finkContinuationResidualVector K z := neg_inj.mp hneg
    rw [G.finkContinuationResidualVector_sub, hresidual, sub_self]
  · intro hharmonic
    rw [G.finkContinuationResidualVector_sub] at hharmonic
    have hresidual : G.finkContinuationResidualVector K' z =
        G.finkContinuationResidualVector K z := sub_eq_zero.mp hharmonic
    rw [hresidual]
    exact hK

/-- A nonzero harmonic obstruction rules out every stationary Poisson
representation of the forcing.  Changing the potential can alter only the
coboundary component. -/
theorem not_exists_finkContinuationResidualVector_eq_of_harmonicObstruction_ne
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : G.finkDomain U) (F O K : G.State → Payoff ι)
    (hO : G.finkContinuationResidualVector O z = 0)
    (hdecomp : F = O + G.finkContinuationResidualVector K z)
    (hOne : O ≠ 0) :
    ¬ ∃ L : G.State → Payoff ι,
      G.finkContinuationResidualVector L z = F := by
  rintro ⟨L, hL⟩
  have hzeroDecomp : F = 0 + G.finkContinuationResidualVector L z := by
    simpa only [zero_add] using hL.symm
  have hOzero := G.finkHarmonicObstruction_unique z F O K 0 L
    hO hdecomp (G.finkContinuationResidualVector_zero z) hzeroDecomp
  exact hOne hOzero

/-- The on-profile Poisson equation required by the interior verification
criterion is solvable whenever its forcing has zero Cesàro fixed component
under the limiting stationary state kernel. -/
theorem exists_finkPoissonCorrection_of_tendsto_cesaro_forcing_zero
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : G.finkDomain U) (W H : G.State → Payoff ι)
    (hzero : ∀ who, Tendsto (fun T : ℕ =>
      (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T,
        ((Math.MeanErgodic.markovOperator (G.finkStateKernel z)) ^ t)
          (fun s => G.finkBellmanForcingVector W H z s who))
        atTop (nhds 0)) :
    ∃ K : G.State → Payoff ι,
      G.finkBellmanForcingVector W H z =
        -G.finkContinuationResidualVector K z := by
  obtain ⟨L, hL⟩ :=
    G.exists_finkContinuationResidualVector_eq_of_tendsto_cesaro_zero
      z (G.finkBellmanForcingVector W H z) hzero
  refine ⟨-L, ?_⟩
  have hnegL : -L = (-1 : ℝ) • L := by
    ext s who
    simp
  rw [hnegL]
  rw [G.finkContinuationResidualVector_smul]
  rw [hL]
  simp

/-- A stationary Poisson correction removes the limiting Bellman forcing
exactly when that forcing has no harmonic mean-ergodic component. -/
theorem exists_finkPoissonCorrection_iff_tendsto_cesaro_forcing_zero
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : G.finkDomain U) (W H : G.State → Payoff ι) :
    (∃ K : G.State → Payoff ι,
      G.finkBellmanForcingVector W H z =
        -G.finkContinuationResidualVector K z) ↔
      ∀ who, Tendsto (fun T : ℕ =>
        (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T,
          ((Math.MeanErgodic.markovOperator (G.finkStateKernel z)) ^ t)
            (fun s => G.finkBellmanForcingVector W H z s who))
          atTop (nhds 0) := by
  constructor
  · rintro ⟨K, hK⟩
    apply (G.exists_finkContinuationResidualVector_eq_iff_tendsto_cesaro_zero
      z (G.finkBellmanForcingVector W H z)).mp
    refine ⟨-K, ?_⟩
    calc
      G.finkContinuationResidualVector (-K) z =
          -G.finkContinuationResidualVector K z := by
        exact G.finkContinuationResidualVector_neg K z
      _ = G.finkBellmanForcingVector W H z := hK.symm
  · exact G.exists_finkPoissonCorrection_of_tendsto_cesaro_forcing_zero
      z W H

/-- If the Bellman forcing has a nonzero harmonic component, no stationary
Poisson correction can remove it. -/
theorem not_exists_finkPoissonCorrection_of_harmonicObstruction_ne
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : G.finkDomain U) (W H O K : G.State → Payoff ι)
    (hO : G.finkContinuationResidualVector O z = 0)
    (hdecomp : G.finkBellmanForcingVector W H z =
      O + G.finkContinuationResidualVector K z)
    (hOne : O ≠ 0) :
    ¬ ∃ L : G.State → Payoff ι,
      G.finkBellmanForcingVector W H z =
        -G.finkContinuationResidualVector L z := by
  intro hcorrection
  apply G.not_exists_finkContinuationResidualVector_eq_of_harmonicObstruction_ne
    z (G.finkBellmanForcingVector W H z) O K hO hdecomp hOne
  obtain ⟨L, hL⟩ := hcorrection
  refine ⟨-L, ?_⟩
  rw [G.finkContinuationResidualVector_neg]
  exact hL.symm

/-- Adding the boundary correction to the current reference is the same as
rescaling the updated reference potential. -/
theorem add_finkReferenceCorrection_eq_smul_nextReferenceVector
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    (a : ℝ) (J R K : G.State → Payoff ι) (ha : a ≠ 0) :
    R + G.finkReferenceCorrection a J K =
      G.finkReferenceCorrectionScale a J •
        G.finkNextReferenceVector a J R K := by
  have hmag : 1 + ‖J‖ ≠ 0 := by positivity
  ext s who
  simp only [finkReferenceCorrection, finkReferenceCorrectionScale,
    finkNextReferenceVector, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [ha, hmag]

/-- The Poisson recursion preserves the representation of its forcing as a
continuation residual. -/
theorem finkNextPoissonRemainderVector_eq_continuationResidualVector
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (a : ℝ) (J R K : G.State → Payoff ι) {U : ℝ}
    (z : G.finkDomain U) :
    G.finkNextPoissonRemainderVector a
        (G.finkContinuationResidualVector R z) J K z =
      G.finkContinuationResidualVector
        (G.finkNextReferenceVector a J R K) z := by
  ext s who
  simp only [finkNextPoissonRemainderVector,
    finkContinuationResidualVector, finkContinuationResidual,
    finkContinuationVector, finkNextReferenceVector, Pi.smul_apply,
    Pi.sub_apply, Pi.add_apply, smul_eq_mul]
  rw [G.finkContinuationEU_add, G.finkContinuationEU_smul]
  ring

/-- The deviation recursion preserves the representation of its forcing as
the pure-action continuation gain of the same updated reference potential. -/
theorem finkNextDeviationGain_eq_continuationGain
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (a : ℝ) (J R K : G.State → Payoff ι) {U : ℝ}
    (z : G.finkDomain U) (s : G.State) (who : ι) (d : G.Act who) :
    G.finkNextDeviationGain a
        (fun s who d => G.finkContinuationGain R z s who d)
        J K z s who d =
      G.finkContinuationGain (G.finkNextReferenceVector a J R K)
        z s who d := by
  simp only [finkNextDeviationGain, finkNextReferenceVector]
  rw [G.finkContinuationGain_add, G.finkContinuationGain_smul]

/-- The boundary-corrected reference residual is exactly the next Poisson
forcing multiplied by the correction scale. -/
theorem finkContinuationResidualVector_add_correction
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (a : ℝ) (J R K : G.State → Payoff ι) {U : ℝ}
    (z : G.finkDomain U) (ha : a ≠ 0) :
    G.finkContinuationResidualVector
        (R + G.finkReferenceCorrection a J K) z =
      G.finkReferenceCorrectionScale a J •
        G.finkNextPoissonRemainderVector a
          (G.finkContinuationResidualVector R z) J K z := by
  rw [G.add_finkReferenceCorrection_eq_smul_nextReferenceVector
    a J R K ha]
  rw [G.finkContinuationResidualVector_smul]
  rw [G.finkNextPoissonRemainderVector_eq_continuationResidualVector]

/-- Every pure-deviation gain of the boundary-corrected reference is the
same correction scale times the next deviation forcing. -/
theorem finkContinuationGain_add_correction
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (a : ℝ) (J R K : G.State → Payoff ι) {U : ℝ}
    (z : G.finkDomain U) (ha : a ≠ 0)
    (s : G.State) (who : ι) (d : G.Act who) :
    G.finkContinuationGain
        (R + G.finkReferenceCorrection a J K) z s who d =
      G.finkReferenceCorrectionScale a J *
        G.finkNextDeviationGain a
          (fun s who d => G.finkContinuationGain R z s who d)
          J K z s who d := by
  rw [G.add_finkReferenceCorrection_eq_smul_nextReferenceVector
    a J R K ha]
  rw [G.finkContinuationGain_smul]
  rw [G.finkNextDeviationGain_eq_continuationGain]

/-- If the correction scale and next reference residual vanish, then the
corrected current reference is asymptotically harmonic. -/
theorem tendsto_finkContinuationResidualVector_add_correction_zero
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (a : ℕ → ℝ) (J R : ℕ → G.State → Payoff ι)
    (K : G.State → Payoff ι) {U : ℝ} (z : ℕ → G.finkDomain U)
    (ha : ∀ n, a n ≠ 0)
    (hscale : Tendsto (fun n => G.finkReferenceCorrectionScale
      (a n) (J n)) atTop (nhds 0))
    (hnext : Tendsto (fun n => G.finkContinuationResidualVector
      (G.finkNextReferenceVector (a n) (J n) (R n) K) (z n))
      atTop (nhds 0)) :
    Tendsto (fun n => G.finkContinuationResidualVector
      (R n + G.finkReferenceCorrection (a n) (J n) K) (z n))
      atTop (nhds 0) := by
  have hprod := hscale.smul hnext
  have heq : (fun n => G.finkContinuationResidualVector
      (R n + G.finkReferenceCorrection (a n) (J n) K) (z n)) =
      fun n => G.finkReferenceCorrectionScale (a n) (J n) •
        G.finkContinuationResidualVector
          (G.finkNextReferenceVector (a n) (J n) (R n) K) (z n) := by
    funext n
    rw [G.finkContinuationResidualVector_add_correction
      (a n) (J n) (R n) K (z n) (ha n)]
    rw [G.finkNextPoissonRemainderVector_eq_continuationResidualVector]
  rw [heq]
  simpa only [zero_smul] using hprod

/-- The same hypotheses turn asymptotically nonpositive next-reference gains
into asymptotically nonpositive gains for the corrected current reference. -/
theorem eventually_finkContinuationGain_add_correction_le
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (a : ℕ → ℝ) (J R : ℕ → G.State → Payoff ι)
    (K : G.State → Payoff ι) {U : ℝ} (z : ℕ → G.finkDomain U)
    (ha : ∀ n, a n ≠ 0)
    (hscale0 : ∀ n, 0 ≤ G.finkReferenceCorrectionScale (a n) (J n))
    (hscale : Tendsto (fun n => G.finkReferenceCorrectionScale
      (a n) (J n)) atTop (nhds 0))
    (hnext : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ s who (d : G.Act who),
        G.finkContinuationGain
          (G.finkNextReferenceVector (a n) (J n) (R n) K)
            (z n) s who d ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ s who (d : G.Act who),
        G.finkContinuationGain
          (R n + G.finkReferenceCorrection (a n) (J n) K)
            (z n) s who d ≤ ε := by
  intro ε hε
  have hscaleOne : ∀ᶠ n in atTop,
      G.finkReferenceCorrectionScale (a n) (J n) < 1 :=
    hscale.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hscaleOne, hnext ε hε] with n hnScale hn
  intro s who d
  have hgainEq := G.finkContinuationGain_add_correction
    (a n) (J n) (R n) K (z n) (ha n) s who d
  have hnextEq := G.finkNextDeviationGain_eq_continuationGain
    (a n) (J n) (R n) K (z n) s who d
  rw [hnextEq] at hgainEq
  rw [hgainEq]
  exact (mul_le_mul_of_nonneg_left (hn s who d) (hscale0 n)).trans
    (by nlinarith)

/-- Bias correction only changes the decomposition of the total scheduled
potential: corrected bias plus new scale times new reference is exactly the
old bias plus old scale times old reference. -/
theorem finkCorrectedBias_add_smul_nextReferenceVector
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    (a : ℝ) (J R K : G.State → Payoff ι) :
    G.finkCorrectedBias J K +
        (1 + ‖J‖) • G.finkNextReferenceVector a J R K =
      J + a • R := by
  have hmag : 1 + ‖J‖ ≠ 0 := by positivity
  ext s who
  simp only [finkCorrectedBias, finkNextReferenceVector, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [hmag]
  ring

/-- Initially, relative bias plus the scaled target is exactly the absolute
scheduled Fink bias. -/
theorem finkRelativeBias_add_scale_smul_target
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (β : ℝ) (W : G.State → Payoff ι) {U : ℝ}
    (z : G.finkDomain U) :
    G.finkRelativeBias β W z + (β / (1 - β)) • W =
      (β / (1 - β)) • G.finkValue z := by
  ext s who
  simp only [finkRelativeBias, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

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

/-- The recursive deviation forcing preserves zero own-action mean. -/
theorem expect_finkNextDeviationGain_eq_zero
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (a : ℝ) (D : G.State → ∀ who : ι, G.Act who → ℝ)
    (J K : G.State → Payoff ι) {U : ℝ} (z : G.finkDomain U)
    (s : G.State) (who : ι)
    (hmean : expect (G.finkProfile z s who) (D s who) = 0) :
    expect (G.finkProfile z s who) (fun d =>
      G.finkNextDeviationGain a D J K z s who d) = 0 := by
  unfold finkNextDeviationGain
  rw [expect_add, expect_const_mul, hmean,
    G.expect_finkContinuationGain_eq_zero]
  ring

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

/-- Removing a radial direction is exactly the error of the compactified
bias from that direction, rescaled back to the original magnitude. -/
theorem inv_magnitude_smul_finkCorrectedBias
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    (H K : G.State → Payoff ι) :
    (1 / (1 + ‖H‖)) • G.finkCorrectedBias H K =
      G.compactifyFinkBias H - K := by
  have hmag : 1 + ‖H‖ ≠ 0 := by positivity
  ext s who
  simp only [finkCorrectedBias, compactifyFinkBias, Pi.smul_apply,
    Pi.sub_apply, smul_eq_mul]
  field_simp [hmag]

/-- Norm form of `inv_magnitude_smul_finkCorrectedBias`. -/
theorem norm_finkCorrectedBias_div_magnitude
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    (H K : G.State → Payoff ι) :
    ‖G.finkCorrectedBias H K‖ / (1 + ‖H‖) =
      ‖G.compactifyFinkBias H - K‖ := by
  have heq := congrArg norm (G.inv_magnitude_smul_finkCorrectedBias H K)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity :
    0 ≤ (1 / (1 + ‖H‖) : ℝ))] at heq
  rw [div_eq_mul_inv]
  calc
    ‖G.finkCorrectedBias H K‖ * (1 + ‖H‖)⁻¹ =
        (1 + ‖H‖)⁻¹ * ‖G.finkCorrectedBias H K‖ := by ring
    _ = ‖G.compactifyFinkBias H - K‖ := by
      simpa only [one_mul, one_div] using heq

/-- A corrected bias is genuinely lower order than the bias from which its
leading compactified direction was removed. -/
theorem tendsto_norm_finkCorrectedBias_div_magnitude_zero
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    {H : ℕ → G.State → Payoff ι} {K : G.State → Payoff ι}
    (hlim : Tendsto (G.compactifyFinkBias ∘ H) atTop (nhds K)) :
    Tendsto (fun n => ‖G.finkCorrectedBias (H n) K‖ /
      (1 + ‖H n‖)) atTop (nhds 0) := by
  have hconstant : Tendsto (fun _ : ℕ => K) atTop (nhds K) :=
    tendsto_const_nhds
  have hdiff := (hlim.sub hconstant).norm
  have hdiff' : Tendsto (fun n =>
      ‖G.compactifyFinkBias (H n) - K‖) atTop (nhds 0) := by
    simpa only [Function.comp_def, sub_self, norm_zero] using hdiff
  apply hdiff'.congr'
  exact Filter.Eventually.of_forall fun n => by
    simpa only [Function.comp_def] using
      (G.norm_finkCorrectedBias_div_magnitude (H n) K).symm

/-- If the corrected bias is still unbounded, its magnitude defines a
strictly lower asymptotic scale: the old magnitude divided by the corrected
one tends to infinity. -/
theorem tendsto_finkBias_magnitude_div_corrected_magnitude_atTop
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    {H : ℕ → G.State → Payoff ι} {K : G.State → Payoff ι}
    (hlim : Tendsto (G.compactifyFinkBias ∘ H) atTop (nhds K))
    (hcorrected : Tendsto (fun n => ‖G.finkCorrectedBias (H n) K‖)
      atTop atTop) :
    Tendsto (fun n => (1 + ‖H n‖) /
      (1 + ‖G.finkCorrectedBias (H n) K‖)) atTop atTop := by
  have hratio := G.tendsto_norm_finkCorrectedBias_div_magnitude_zero hlim
  refine tendsto_atTop.2 fun b => ?_
  let B : ℝ := max b 1
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right b 1)
  let δ : ℝ := 1 / (2 * B)
  have hδpos : 0 < δ := by
    dsimp [δ]
    positivity
  filter_upwards
    [hratio.eventually (eventually_lt_nhds hδpos),
      tendsto_atTop.1 hcorrected 1] with n hn hlarge
  have hHmag : 0 < 1 + ‖H n‖ := by positivity
  have hJmag : 0 < 1 + ‖G.finkCorrectedBias (H n) K‖ := by positivity
  have h2B : 0 < 2 * B := by positivity
  have hcross : ‖G.finkCorrectedBias (H n) K‖ * (2 * B) <
      1 + ‖H n‖ := by
    have hfrac : ‖G.finkCorrectedBias (H n) K‖ / (1 + ‖H n‖) <
        (1 : ℝ) / (2 * B) := by
      simpa only [δ] using hn
    simpa only [one_mul] using (div_lt_div_iff₀ hHmag h2B).mp hfrac
  have hBstep : B * (1 + ‖G.finkCorrectedBias (H n) K‖) ≤
      ‖G.finkCorrectedBias (H n) K‖ * (2 * B) := by
    nlinarith
  have hBout : B < (1 + ‖H n‖) /
      (1 + ‖G.finkCorrectedBias (H n) K‖) := by
    rw [lt_div_iff₀ hJmag]
    exact lt_of_le_of_lt hBstep hcross
  exact (le_max_left b 1).trans hBout.le

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

/-- Exact boundary-scale form of the centered on-profile Bellman equation.
It identifies the magnified harmonic residual with the drift of the radially
compactified relative bias, up to terms killed at the projective boundary. -/
theorem finkProjectiveBiasScale_mul_continuationResidual_eq
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (β U : ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : G.finkDomain U)
    (hfix : G.finkMap β U hβ0 hβ1.le hpay z = z)
    (W : G.State → Payoff ι) (s : G.State) (who : ι) :
    G.finkProjectiveBiasScale β W z *
        G.finkContinuationResidual W z s who =
      (1 / (1 + ‖G.finkRelativeBias β W z‖)) *
          G.finkValue z s who +
        G.compactifyFinkBias (G.finkRelativeBias β W z) s who -
        (1 / (1 + ‖G.finkRelativeBias β W z‖)) *
          G.finkStageEU z s who -
        G.finkContinuationEU
          (G.compactifyFinkBias (G.finkRelativeBias β W z)) z s who := by
  have hcenter := G.finkValue_add_relativeBias_eq_finkEU_add
    β U hβ0 hβ1 hpay z hfix W s who
  unfold finkProjectiveBiasScale compactifyFinkBias
  simp only [Pi.smul_apply, smul_eq_mul, G.finkContinuationEU_smul]
  linear_combination -(1 / (1 + ‖G.finkRelativeBias β W z‖)) * hcenter

/-- Subtracting the leading boundary direction from the relative bias
cancels the leading Poisson drift exactly.  The remaining Bellman error is
the bias magnitude times `finkPoissonRemainder`, ready for the next radial
extraction. -/
theorem finkValue_add_correctedBias_eq_stage_add
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (β U : ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : G.finkDomain U)
    (hfix : G.finkMap β U hβ0 hβ1.le hpay z = z)
    (W K : G.State → Payoff ι) (s : G.State) (who : ι) :
    G.finkValue z s who +
        G.finkCorrectedBias (G.finkRelativeBias β W z) K s who =
      G.finkStageEU z s who +
        G.finkContinuationEU
          (G.finkCorrectedBias (G.finkRelativeBias β W z) K)
          z s who +
        (1 + ‖G.finkRelativeBias β W z‖) *
          G.finkPoissonRemainder β W K z s who := by
  have hcenter := G.finkValue_add_relativeBias_eq_finkEU_add
    β U hβ0 hβ1 hpay z hfix W s who
  have hmag : 1 + ‖G.finkRelativeBias β W z‖ ≠ 0 := by
    positivity
  unfold finkCorrectedBias finkPoissonRemainder finkProjectiveBiasScale
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    G.finkContinuationEU_sub, G.finkContinuationEU_smul]
  field_simp [hmag]
  linear_combination hcenter

/-- Generic recursive correction step.  If `J` solves an on-profile Bellman
equation with forcing `a • E`, subtracting its leading radial direction `L`
produces the same equation with the next normalized Poisson remainder. -/
theorem value_add_finkCorrectedBias_eq_stage_add
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    (z : G.finkDomain U) (v a : ℝ)
    (E J L : G.State → Payoff ι) (s : G.State) (who : ι)
    (hbellman : v + J s who =
      G.finkStageEU z s who + G.finkContinuationEU J z s who +
        a * E s who) :
    v + G.finkCorrectedBias J L s who =
      G.finkStageEU z s who +
        G.finkContinuationEU (G.finkCorrectedBias J L) z s who +
        (1 + ‖J‖) *
          G.finkNextPoissonRemainderVector a E J L z s who := by
  have hmag : 1 + ‖J‖ ≠ 0 := by positivity
  unfold finkCorrectedBias finkNextPoissonRemainderVector
    finkContinuationVector
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    G.finkContinuationEU_sub, G.finkContinuationEU_smul]
  field_simp [hmag]
  linear_combination hbellman

/-- Continuation gain of a corrected bias is the old gain minus the radial
direction at the old magnitude. -/
theorem finkContinuationGain_finkCorrectedBias
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (J K : G.State → Payoff ι) {U : ℝ} (z : G.finkDomain U)
    (s : G.State) (who : ι) (d : G.Act who) :
    G.finkContinuationGain (G.finkCorrectedBias J K) z s who d =
      G.finkContinuationGain J z s who d -
        (1 + ‖J‖) * G.finkContinuationGain K z s who d := by
  unfold finkCorrectedBias
  rw [G.finkContinuationGain_sub, G.finkContinuationGain_smul]

/-- Exact deviation-side recursion.  Replacing `J` by its corrected bias
turns the old forcing `a • D` into the next normalized deviation gain. -/
theorem stage_add_correctedGain_add_next_eq
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (a : ℝ) (D : G.State → ∀ who : ι, G.Act who → ℝ)
    (J K : G.State → Payoff ι) {U : ℝ} (z : G.finkDomain U)
    (s : G.State) (who : ι) (d : G.Act who) :
    G.finkStageGain z s who d +
        G.finkContinuationGain (G.finkCorrectedBias J K) z s who d +
        (1 + ‖J‖) * G.finkNextDeviationGain a D J K z s who d =
      G.finkStageGain z s who d + a * D s who d +
        G.finkContinuationGain J z s who d := by
  rw [G.finkContinuationGain_finkCorrectedBias]
  unfold finkNextDeviationGain
  have hmag : 1 + ‖J‖ ≠ 0 := by positivity
  field_simp [hmag]
  ring

/-- The normalized forcing at the next bias scale can be read directly from
the Bellman equation.  This form is suited to taking a boundary limit. -/
theorem finkNextPoissonRemainderVector_eq
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    (z : G.finkDomain U) (v a : ℝ)
    (E J L : G.State → Payoff ι) (s : G.State) (who : ι)
    (hbellman : v + J s who =
      G.finkStageEU z s who + G.finkContinuationEU J z s who +
        a * E s who) :
    G.finkNextPoissonRemainderVector a E J L z s who =
      (1 / (1 + ‖J‖)) * v + G.compactifyFinkBias J s who -
        (1 / (1 + ‖J‖)) * G.finkStageEU z s who -
        G.finkContinuationEU (G.compactifyFinkBias J) z s who -
        (L s who - G.finkContinuationEU L z s who) := by
  have hmag : 1 + ‖J‖ ≠ 0 := by positivity
  unfold finkNextPoissonRemainderVector finkContinuationVector
    compactifyFinkBias
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    G.finkContinuationEU_smul]
  field_simp [hmag]
  linarith [hbellman]

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

/-- A coordinate which stays finite disappears from every lower projective
direction of an unbounded bias family. -/
theorem finkBiasDirection_coordinate_eq_zero_of_tendsto
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    {H : ℕ → G.State → Payoff ι} {K : G.State → Payoff ι}
    (hlim : Tendsto (G.compactifyFinkBias ∘ H) atTop (nhds K))
    (hnorm : Tendsto (fun n => ‖H n‖) atTop atTop)
    (p : G.FinkBiasIndex) {c : ℝ}
    (hp : Tendsto (fun n => G.finkBiasCoordinate (H n) p)
      atTop (nhds c)) :
    G.finkBiasCoordinate K p = 0 := by
  have hscale : Tendsto (fun n => 1 + ‖H n‖) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [tendsto_atTop.1 hnorm (b - 1)] with n hn
    linarith
  have hinv : Tendsto (fun n => 1 / (1 + ‖H n‖)) atTop (nhds 0) := by
    simpa only [Function.comp_def, one_div] using
      tendsto_inv_atTop_zero.comp hscale
  have hscaled : Tendsto (fun n =>
      G.finkBiasCoordinate (G.compactifyFinkBias (H n)) p)
      atTop (nhds 0) := by
    simpa only [compactifyFinkBias, finkBiasCoordinate, Pi.smul_apply,
      smul_eq_mul, zero_mul] using hinv.mul hp
  have hcoord : Tendsto (fun n =>
      G.finkBiasCoordinate (G.compactifyFinkBias (H n)) p)
      atTop (nhds (G.finkBiasCoordinate K p)) := by
    have hc : Continuous (fun J : G.State → Payoff ι =>
        G.finkBiasCoordinate J p) := by
      unfold finkBiasCoordinate
      fun_prop
    have ht := (hc.tendsto K).comp hlim
    simpa only [Function.comp_def] using ht
  exact tendsto_nhds_unique hcoord hscaled

/-- A fixed signed norm-attaining coordinate survives as the same coordinate
of the associated projective boundary direction. -/
theorem finkBiasDirection_coordinate_eq_of_eq_smul_norm
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    {H : ℕ → G.State → Payoff ι} {K : G.State → Payoff ι}
    (hlim : Tendsto (G.compactifyFinkBias ∘ H) atTop (nhds K))
    (hnorm : Tendsto (fun n => ‖H n‖) atTop atTop)
    (p : G.FinkBiasIndex) (σ : ℝ)
    (hp : ∀ n, G.finkBiasCoordinate (H n) p = σ * ‖H n‖) :
    G.finkBiasCoordinate K p = σ := by
  have hscale : Tendsto (fun n => 1 + ‖H n‖) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [tendsto_atTop.1 hnorm (b - 1)] with n hn
    linarith
  have hinv : Tendsto (fun n => 1 / (1 + ‖H n‖)) atTop (nhds 0) := by
    simpa only [Function.comp_def, one_div] using
      tendsto_inv_atTop_zero.comp hscale
  have hradial : Tendsto (fun n => σ * (1 - 1 / (1 + ‖H n‖)))
      atTop (nhds σ) := by
    have hσ : Tendsto (fun _ : ℕ => σ) atTop (nhds σ) := tendsto_const_nhds
    have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa only [sub_zero, mul_one] using hσ.mul (h1.sub hinv)
  have hscaled : Tendsto (fun n =>
      G.finkBiasCoordinate (G.compactifyFinkBias (H n)) p)
      atTop (nhds σ) := by
    apply hradial.congr'
    exact Filter.Eventually.of_forall fun n => by
      unfold compactifyFinkBias finkBiasCoordinate
      simp only [Pi.smul_apply, smul_eq_mul]
      have hpn : H n p.1 p.2 = σ * ‖H n‖ := by
        simpa only [finkBiasCoordinate] using hp n
      rw [hpn]
      have hmag : 1 + ‖H n‖ ≠ 0 := by positivity
      field_simp [hmag]
      ring
  have hcoord : Tendsto (fun n =>
      G.finkBiasCoordinate (G.compactifyFinkBias (H n)) p)
      atTop (nhds (G.finkBiasCoordinate K p)) := by
    have hc : Continuous (fun J : G.State → Payoff ι =>
        G.finkBiasCoordinate J p) := by
      unfold finkBiasCoordinate
      fun_prop
    have ht := (hc.tendsto K).comp hlim
    simpa only [Function.comp_def] using ht
  exact tendsto_nhds_unique hcoord hscaled

/-- Correcting by a direction which vanishes at a protected coordinate
preserves convergence of that coordinate. -/
theorem tendsto_finkCorrectedBias_coordinate_of_direction_eq_zero
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    {H : ℕ → G.State → Payoff ι} (K : G.State → Payoff ι)
    (p : G.FinkBiasIndex) {c : ℝ}
    (hp : Tendsto (fun n => G.finkBiasCoordinate (H n) p)
      atTop (nhds c))
    (hK : G.finkBiasCoordinate K p = 0) :
    Tendsto (fun n =>
      G.finkBiasCoordinate (G.finkCorrectedBias (H n) K) p)
      atTop (nhds c) := by
  unfold finkBiasCoordinate at hK
  simpa only [finkCorrectedBias, finkBiasCoordinate, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, hK, mul_zero, sub_zero] using hp

/-- One protected-coordinate boundary step for the bias hierarchy.  A fixed
signed norm maximizer lies outside the old protected set; after radial
correction its coordinate is exactly constant, while every old protected
coordinate remains convergent. -/
theorem exists_finkBias_boundary_protectedCoordinateExtension
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    (P : Finset G.FinkBiasIndex)
    (H : ℕ → G.State → Payoff ι) (K : G.State → Payoff ι)
    (hlim : Tendsto (G.compactifyFinkBias ∘ H) atTop (nhds K))
    (hKnorm : ‖K‖ = 1)
    (hprotected : ∀ p ∈ P, ∃ c : ℝ,
      Tendsto (fun n => G.finkBiasCoordinate (H n) p) atTop (nhds c)) :
    ∃ (p : G.FinkBiasIndex) (σ : ℝ) (φ : ℕ → ℕ),
      (σ = 1 ∨ σ = -1) ∧ StrictMono φ ∧
      P ⊂ G.extendFinkBiasMask P p ∧
      Tendsto (G.compactifyFinkBias ∘ H ∘ φ) atTop (nhds K) ∧
      G.finkBiasCoordinate K p = σ ∧
      (∀ n, G.finkBiasCoordinate
        (G.finkCorrectedBias (H (φ n)) K) p = -σ) ∧
      ∀ q ∈ G.extendFinkBiasMask P p, ∃ c : ℝ,
        Tendsto (fun n => G.finkBiasCoordinate
          (G.finkCorrectedBias (H (φ n)) K) q) atTop (nhds c) := by
  classical
  have hnorm : Tendsto (fun n => ‖H n‖) atTop atTop :=
    G.tendsto_norm_finkBias_atTop_of_compactify_tendsto_norm_eq_one
      hlim hKnorm
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (tendsto_atTop.1 hnorm 1)
  let τ : ℕ → ℕ := fun n => N + n
  have hτ : StrictMono τ := by
    intro m n hmn
    exact Nat.add_lt_add_left hmn N
  have hneτ : ∀ n, ‖H (τ n)‖ ≠ 0 := by
    intro n
    have hone : 1 ≤ ‖H (τ n)‖ := hN (τ n) (by simp [τ])
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hone)
  obtain ⟨p, σ, ψ, hσ, hψ, hmax⟩ :=
    G.exists_finkBiasCoordinate_eq_smul_norm_subsequence
      (H ∘ τ) (by simpa only [Function.comp_def] using hneτ)
  let φ : ℕ → ℕ := τ ∘ ψ
  have hφ : StrictMono φ := hτ.comp hψ
  have hlimφ : Tendsto (G.compactifyFinkBias ∘ H ∘ φ)
      atTop (nhds K) := hlim.comp hφ.tendsto_atTop
  have hnormφ : Tendsto (fun n => ‖H (φ n)‖) atTop atTop :=
    hnorm.comp hφ.tendsto_atTop
  have hmaxφ : ∀ n,
      G.finkBiasCoordinate (H (φ n)) p = σ * ‖H (φ n)‖ := by
    simpa only [φ, Function.comp_def] using hmax
  have hKcoord : G.finkBiasCoordinate K p = σ :=
    G.finkBiasDirection_coordinate_eq_of_eq_smul_norm
      hlimφ hnormφ p σ hmaxφ
  have hprotectedφ : ∀ q ∈ P, ∃ c : ℝ,
      Tendsto (fun n => G.finkBiasCoordinate (H (φ n)) q)
        atTop (nhds c) := by
    intro q hq
    obtain ⟨c, hc⟩ := hprotected q hq
    exact ⟨c, hc.comp hφ.tendsto_atTop⟩
  have hσne : σ ≠ 0 := by
    rcases hσ with rfl | rfl <;> norm_num
  have hpP : p ∉ P := by
    intro hp
    obtain ⟨c, hc⟩ := hprotectedφ p hp
    have hzero := G.finkBiasDirection_coordinate_eq_zero_of_tendsto
      hlimφ hnormφ p hc
    exact hσne (hKcoord.symm.trans hzero)
  have hcorrectedMax : ∀ n, G.finkBiasCoordinate
      (G.finkCorrectedBias (H (φ n)) K) p = -σ := by
    intro n
    exact G.finkCorrectedBias_apply_of_eq_smul_norm
      (H (φ n)) K p σ (hmaxφ n) hKcoord
  have hcorrectedProtected : ∀ q ∈ G.extendFinkBiasMask P p, ∃ c : ℝ,
      Tendsto (fun n => G.finkBiasCoordinate
        (G.finkCorrectedBias (H (φ n)) K) q) atTop (nhds c) := by
    intro q hq
    by_cases hqp : q = p
    · subst q
      refine ⟨-σ, ?_⟩
      apply tendsto_const_nhds.congr'
      exact Filter.Eventually.of_forall fun n => (hcorrectedMax n).symm
    · have hqP : q ∈ P :=
        ((G.mem_extendFinkBiasMask_iff P p q).mp hq).resolve_left hqp
      obtain ⟨c, hc⟩ := hprotectedφ q hqP
      have hKzero := G.finkBiasDirection_coordinate_eq_zero_of_tendsto
        hlimφ hnormφ q hc
      exact ⟨c,
        G.tendsto_finkCorrectedBias_coordinate_of_direction_eq_zero
          K q hc hKzero⟩
  have hstrict : P ⊂ G.extendFinkBiasMask P p := by
    classical
    simpa only [extendFinkBiasMask] using Finset.ssubset_insert hpP
  exact ⟨p, σ, φ, hσ, hφ, hstrict, hlimφ,
    hKcoord, hcorrectedMax, hcorrectedProtected⟩

/-- A boundary direction of any Bellman bias cancels the forcing at the next
normalized scale.  This is the recursive Poisson-limit step underlying the
bias hierarchy. -/
theorem tendsto_finkNextPoissonRemainderVector_apply_zero_of_boundary
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    {v a : ℕ → ℝ} {vlim : ℝ}
    (hv : Tendsto v atTop (nhds vlim))
    {E J : ℕ → G.State → Payoff ι} (L : G.State → Payoff ι)
    (s : G.State) (who : ι)
    (hbellman : ∀ n, v n + J n s who =
      G.finkStageEU (z n) s who +
        G.finkContinuationEU (J n) (z n) s who +
        a n * E n s who)
    (hJlim : Tendsto (G.compactifyFinkBias ∘ J) atTop (nhds L))
    (hLnorm : ‖L‖ = 1) :
    Tendsto (fun n => G.finkNextPoissonRemainderVector
      (a n) (E n) (J n) L (z n) s who) atTop (nhds 0) := by
  have hnorm : Tendsto (fun n => ‖J n‖) atTop atTop :=
    G.tendsto_norm_finkBias_atTop_of_compactify_tendsto_norm_eq_one
      hJlim hLnorm
  have hscale : Tendsto (fun n => 1 + ‖J n‖) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [tendsto_atTop.1 hnorm (b - 1)] with n hn
    linarith
  have hinv : Tendsto (fun n => 1 / (1 + ‖J n‖)) atTop (nhds 0) := by
    simpa only [Function.comp_def, one_div] using
      tendsto_inv_atTop_zero.comp hscale
  have hvScaled : Tendsto (fun n =>
      (1 / (1 + ‖J n‖)) * v n) atTop (nhds 0) := by
    simpa using hinv.mul hv
  have hstage :=
    ((G.continuous_finkStageEU (U := U) s who).tendsto zlim).comp hz
  have hstageScaled : Tendsto (fun n =>
      (1 / (1 + ‖J n‖)) * G.finkStageEU (z n) s who)
      atTop (nhds 0) := by
    simpa using hinv.mul hstage
  have hcompact : Tendsto (fun n => G.compactifyFinkBias (J n))
      atTop (nhds L) := by
    simpa only [Function.comp_def] using hJlim
  have hcompactCoord : Tendsto
      (fun n => G.compactifyFinkBias (J n) s who) atTop
      (nhds (L s who)) := by
    have hc : Continuous (fun H : G.State → Payoff ι => H s who) := by
      fun_prop
    exact (hc.tendsto L).comp hcompact
  have hpair : Tendsto
      (fun n => (G.compactifyFinkBias (J n), z n)) atTop
      (nhds (L, zlim)) := by
    simpa only [nhds_prod_eq] using hcompact.prodMk hz
  have hcompactEU :=
    ((G.continuous_finkContinuationEU_param (U := U) s who).tendsto
      (L, zlim)).comp hpair
  have hLpair : Tendsto (fun n => (L, z n)) atTop
      (nhds (L, zlim)) := by
    simpa only [nhds_prod_eq] using (tendsto_const_nhds.prodMk hz)
  have hLEU :=
    ((G.continuous_finkContinuationEU_param (U := U) s who).tendsto
      (L, zlim)).comp hLpair
  have hLcoord : Tendsto (fun _ : ℕ => L s who) atTop
      (nhds (L s who)) := tendsto_const_nhds
  have hrhs := (((hvScaled.add hcompactCoord).sub hstageScaled).sub
    hcompactEU).sub (hLcoord.sub hLEU)
  have hrhs' : Tendsto (fun n =>
      (1 / (1 + ‖J n‖)) * v n + G.compactifyFinkBias (J n) s who -
        (1 / (1 + ‖J n‖)) * G.finkStageEU (z n) s who -
        G.finkContinuationEU (G.compactifyFinkBias (J n)) (z n) s who -
        (L s who - G.finkContinuationEU L (z n) s who))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, zero_add, sub_zero, sub_self] using hrhs
  apply hrhs'.congr'
  exact Filter.Eventually.of_forall fun n =>
    (G.finkNextPoissonRemainderVector_eq (z n) (v n) (a n)
      (E n) (J n) L s who (hbellman n)).symm

/-- Finite-dimensional form of the recursive Poisson cancellation. -/
theorem tendsto_finkNextPoissonRemainderVector_zero_of_boundary
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    {v a : ℕ → ℝ} {vlim : ℝ}
    (hv : Tendsto v atTop (nhds vlim))
    {E J : ℕ → G.State → Payoff ι} (L : G.State → Payoff ι)
    (hbellman : ∀ n s who, v n + J n s who =
      G.finkStageEU (z n) s who +
        G.finkContinuationEU (J n) (z n) s who +
        a n * E n s who)
    (hJlim : Tendsto (G.compactifyFinkBias ∘ J) atTop (nhds L))
    (hLnorm : ‖L‖ = 1) :
    Tendsto (fun n => G.finkNextPoissonRemainderVector
      (a n) (E n) (J n) L (z n)) atTop (nhds 0) := by
  apply tendsto_pi_nhds.2
  intro s
  apply tendsto_pi_nhds.2
  intro who
  simpa only [Pi.zero_apply] using
    G.tendsto_finkNextPoissonRemainderVector_apply_zero_of_boundary
      hz hv L s who (fun n => hbellman n s who) hJlim hLnorm

/-- Recursive Poisson cancellation with a state/player-valued Bellman value
family. -/
theorem tendsto_finkNextPoissonRemainderVector_zero_of_boundary_valueVector
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    {V : ℕ → G.State → Payoff ι} {Vlim : G.State → Payoff ι}
    (hV : Tendsto V atTop (nhds Vlim))
    {a : ℕ → ℝ} {E J : ℕ → G.State → Payoff ι}
    (L : G.State → Payoff ι)
    (hbellman : ∀ n s who, V n s who + J n s who =
      G.finkStageEU (z n) s who +
        G.finkContinuationEU (J n) (z n) s who +
        a n * E n s who)
    (hJlim : Tendsto (G.compactifyFinkBias ∘ J) atTop (nhds L))
    (hLnorm : ‖L‖ = 1) :
    Tendsto (fun n => G.finkNextPoissonRemainderVector
      (a n) (E n) (J n) L (z n)) atTop (nhds 0) := by
  apply tendsto_pi_nhds.2
  intro s
  apply tendsto_pi_nhds.2
  intro who
  have hVcoord : Tendsto (fun n => V n s who) atTop
      (nhds (Vlim s who)) := by
    have hc : Continuous (fun W : G.State → Payoff ι => W s who) := by
      fun_prop
    exact (hc.tendsto Vlim).comp hV
  simpa only [Pi.zero_apply] using
    G.tendsto_finkNextPoissonRemainderVector_apply_zero_of_boundary
      hz hVcoord L s who (fun n => hbellman n s who) hJlim hLnorm

/-- Generic deviation-side boundary optimality.  If `J` is the current
Bellman bias and all pure deviations satisfy the centered gain inequality,
then after removing a projective boundary direction the next normalized
deviation gain has asymptotically nonpositive limsup. -/
theorem eventually_finkNextDeviationGain_le_of_boundary
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    {J : ℕ → G.State → Payoff ι} (K : G.State → Payoff ι)
    (hJlim : Tendsto (G.compactifyFinkBias ∘ J) atTop (nhds K))
    (hKnorm : ‖K‖ = 1)
    (a : ℕ → ℝ)
    (D : ℕ → G.State → ∀ who : ι, G.Act who → ℝ)
    (hgain : ∀ n s who (d : G.Act who),
      G.finkStageGain (z n) s who d + a n * D n s who d +
        G.finkContinuationGain (J n) (z n) s who d ≤ 0)
    (s : G.State) (who : ι) (d : G.Act who) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      G.finkNextDeviationGain (a n) (D n) (J n) K (z n) s who d ≤ ε := by
  have hnorm : Tendsto (fun n => ‖J n‖) atTop atTop :=
    G.tendsto_norm_finkBias_atTop_of_compactify_tendsto_norm_eq_one
      hJlim hKnorm
  have hscale : Tendsto (fun n => 1 + ‖J n‖) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [tendsto_atTop.1 hnorm (b - 1)] with n hn
    linarith
  have hinv : Tendsto (fun n => 1 / (1 + ‖J n‖)) atTop (nhds 0) := by
    simpa only [Function.comp_def, one_div] using
      tendsto_inv_atTop_zero.comp hscale
  have hstage := G.tendsto_finkStageGain hz s who d
  have hstageScaled : Tendsto (fun n =>
      (1 / (1 + ‖J n‖)) * G.finkStageGain (z n) s who d)
      atTop (nhds 0) := by
    simpa using hinv.mul hstage
  have hconstant : Tendsto (fun _ : ℕ => K) atTop (nhds K) :=
    tendsto_const_nhds
  have hdiff := hJlim.sub hconstant
  have hcorrectedVector : Tendsto (fun n =>
      (1 / (1 + ‖J n‖)) • G.finkCorrectedBias (J n) K)
      atTop (nhds 0) := by
    have hdiff' : Tendsto (fun n => G.compactifyFinkBias (J n) - K)
        atTop (nhds 0) := by
      simpa only [Function.comp_def, sub_self] using hdiff
    apply hdiff'.congr'
    exact Filter.Eventually.of_forall fun n =>
      (G.inv_magnitude_smul_finkCorrectedBias (J n) K).symm
  have hcorrectedGainRaw := G.tendsto_finkContinuationGain_of_tendsto
    hcorrectedVector hz s who d
  have hcorrectedGain : Tendsto (fun n =>
      (1 / (1 + ‖J n‖)) *
        G.finkContinuationGain (G.finkCorrectedBias (J n) K)
          (z n) s who d) atTop (nhds 0) := by
    have heq : (fun n =>
        (1 / (1 + ‖J n‖)) *
          G.finkContinuationGain (G.finkCorrectedBias (J n) K)
            (z n) s who d) =
        (fun n => G.finkContinuationGain
          ((1 / (1 + ‖J n‖)) • G.finkCorrectedBias (J n) K)
            (z n) s who d) := by
      funext n
      exact (G.finkContinuationGain_smul
        (1 / (1 + ‖J n‖)) (G.finkCorrectedBias (J n) K)
          (z n) s who d).symm
    rw [heq]
    simpa [finkContinuationGain] using hcorrectedGainRaw
  have herror : Tendsto (fun n =>
      (1 / (1 + ‖J n‖)) *
        (G.finkStageGain (z n) s who d +
          G.finkContinuationGain (G.finkCorrectedBias (J n) K)
            (z n) s who d)) atTop (nhds 0) := by
    have ht := hstageScaled.add hcorrectedGain
    have ht' : Tendsto (fun n =>
        (1 / (1 + ‖J n‖)) * G.finkStageGain (z n) s who d +
          (1 / (1 + ‖J n‖)) *
            G.finkContinuationGain (G.finkCorrectedBias (J n) K)
              (z n) s who d) atTop (nhds 0) := by
      simpa only [zero_add] using ht
    convert ht' using 1
    funext n
    ring
  filter_upwards [herror.eventually (Metric.ball_mem_nhds 0 hε)] with n hn
  rw [Real.dist_eq, sub_zero] at hn
  have hmag : 0 < 1 + ‖J n‖ := by positivity
  have hold := hgain n s who d
  have heq := G.stage_add_correctedGain_add_next_eq
    (a n) (D n) (J n) K (z n) s who d
  have hnormalized :
      (1 / (1 + ‖J n‖)) *
          (G.finkStageGain (z n) s who d +
            G.finkContinuationGain (G.finkCorrectedBias (J n) K)
              (z n) s who d) +
        G.finkNextDeviationGain (a n) (D n) (J n) K
          (z n) s who d =
      (1 / (1 + ‖J n‖)) *
        (G.finkStageGain (z n) s who d + a n * D n s who d +
          G.finkContinuationGain (J n) (z n) s who d) := by
    rw [← heq]
    field_simp [ne_of_gt hmag]
  have hrhs : (1 / (1 + ‖J n‖)) *
      (G.finkStageGain (z n) s who d + a n * D n s who d +
        G.finkContinuationGain (J n) (z n) s who d) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hold
  have hsum := hnormalized.trans_le hrhs
  have hlower := (neg_lt_of_abs_lt hn)
  linarith

/-- Finite-coordinate uniform form of recursive deviation-side boundary
optimality. -/
theorem eventually_all_finkNextDeviationGain_le_of_boundary
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    {J : ℕ → G.State → Payoff ι} (K : G.State → Payoff ι)
    (hJlim : Tendsto (G.compactifyFinkBias ∘ J) atTop (nhds K))
    (hKnorm : ‖K‖ = 1)
    (a : ℕ → ℝ)
    (D : ℕ → G.State → ∀ who : ι, G.Act who → ℝ)
    (hgain : ∀ n s who (d : G.Act who),
      G.finkStageGain (z n) s who d + a n * D n s who d +
        G.finkContinuationGain (J n) (z n) s who d ≤ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ s who (d : G.Act who),
      G.finkNextDeviationGain (a n) (D n) (J n) K (z n) s who d ≤ ε := by
  rw [Filter.eventually_all]
  intro s
  rw [Filter.eventually_all]
  intro who
  rw [Filter.eventually_all]
  intro d
  exact G.eventually_finkNextDeviationGain_le_of_boundary
    hz K hJlim hKnorm a D hgain s who d hε

/-- At a projective bias boundary, the magnified harmonic residual of the
target payoff converges to the Poisson drift of the boundary direction. -/
theorem tendsto_finkProjectiveBiasScale_mul_continuationResidual_of_boundary
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {β : ℕ → ℝ} {U : ℝ}
    (hβ0 : ∀ n, 0 ≤ β n) (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (W K : G.State → Payoff ι)
    (hKlim : Tendsto (G.compactifyFinkBias ∘ fun n =>
      G.finkRelativeBias (β n) W (z n)) atTop (nhds K))
    (hKnorm : ‖K‖ = 1) (s : G.State) (who : ι) :
    Tendsto (fun n =>
        G.finkProjectiveBiasScale (β n) W (z n) *
          G.finkContinuationResidual W (z n) s who) atTop
      (nhds (K s who - G.finkContinuationEU K zlim s who)) := by
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
  have hvalue := G.tendsto_finkValue_apply hz s who
  have hvalueScaled : Tendsto (fun n =>
      (1 / (1 + ‖H n‖)) * G.finkValue (z n) s who)
      atTop (nhds 0) := by
    simpa using hinv.mul hvalue
  have hstage :=
    ((G.continuous_finkStageEU (U := U) s who).tendsto zlim).comp hz
  have hstageScaled : Tendsto (fun n =>
      (1 / (1 + ‖H n‖)) * G.finkStageEU (z n) s who)
      atTop (nhds 0) := by
    simpa using hinv.mul hstage
  have hcompact : Tendsto (fun n => G.compactifyFinkBias (H n))
      atTop (nhds K) := by
    simpa only [H, Function.comp_def] using hKlim
  have hcompactCoord : Tendsto
      (fun n => G.compactifyFinkBias (H n) s who) atTop
      (nhds (K s who)) := by
    have hc : Continuous (fun L : G.State → Payoff ι => L s who) := by
      fun_prop
    exact (hc.tendsto K).comp hcompact
  have hpair : Tendsto
      (fun n => (G.compactifyFinkBias (H n), z n)) atTop
      (nhds (K, zlim)) := by
    simpa only [nhds_prod_eq] using hcompact.prodMk hz
  have hcompactEU :=
    ((G.continuous_finkContinuationEU_param (U := U) s who).tendsto
      (K, zlim)).comp hpair
  have hrhs :=
    ((hvalueScaled.add hcompactCoord).sub hstageScaled).sub hcompactEU
  have hrhs' : Tendsto (fun n =>
      (1 / (1 + ‖H n‖)) * G.finkValue (z n) s who +
        G.compactifyFinkBias (H n) s who -
        (1 / (1 + ‖H n‖)) * G.finkStageEU (z n) s who -
        G.finkContinuationEU (G.compactifyFinkBias (H n)) (z n) s who)
      atTop (nhds (K s who - G.finkContinuationEU K zlim s who)) := by
    simpa only [zero_add, sub_zero, Function.comp_def] using hrhs
  apply hrhs'.congr'
  exact Filter.Eventually.of_forall fun n => by
    simpa only [H] using
      (G.finkProjectiveBiasScale_mul_continuationResidual_eq
        (β n) U (hβ0 n) (hβ1 n) hpay (z n) (hfix n) W s who).symm

/-- The first Poisson correction really removes the whole leading boundary
error: its normalized remainder tends to zero along the Fink family. -/
theorem tendsto_finkPoissonRemainder_zero_of_boundary
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {β : ℕ → ℝ} {U : ℝ}
    (hβ0 : ∀ n, 0 ≤ β n) (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (W K : G.State → Payoff ι)
    (hKlim : Tendsto (G.compactifyFinkBias ∘ fun n =>
      G.finkRelativeBias (β n) W (z n)) atTop (nhds K))
    (hKnorm : ‖K‖ = 1) (s : G.State) (who : ι) :
    Tendsto (fun n => G.finkPoissonRemainder
      (β n) W K (z n) s who) atTop (nhds 0) := by
  have hscaled :=
    G.tendsto_finkProjectiveBiasScale_mul_continuationResidual_of_boundary
      hβ0 hβ1 hpay hz hfix W K hKlim hKnorm s who
  have hcontinuation := G.tendsto_finkProfile_continuation hz
    (fun s' => K s' who) s
  have hcontinuation' : Tendsto
      (fun n => G.finkContinuationEU K (z n) s who) atTop
      (nhds (G.finkContinuationEU K zlim s who)) := by
    simpa only [finkContinuationEU] using hcontinuation
  have hconstant : Tendsto (fun _ : ℕ => K s who) atTop
      (nhds (K s who)) := tendsto_const_nhds
  have hdrift := hconstant.sub hcontinuation'
  have ht := hscaled.sub hdrift
  simpa only [finkPoissonRemainder, sub_self] using ht

/-- Finite-dimensional form of the first Poisson cancellation. -/
theorem tendsto_finkPoissonRemainderVector_zero_of_boundary
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {β : ℕ → ℝ} {U : ℝ}
    (hβ0 : ∀ n, 0 ≤ β n) (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (W K : G.State → Payoff ι)
    (hKlim : Tendsto (G.compactifyFinkBias ∘ fun n =>
      G.finkRelativeBias (β n) W (z n)) atTop (nhds K))
    (hKnorm : ‖K‖ = 1) :
    Tendsto (fun n => G.finkPoissonRemainderVector
      (β n) W K (z n)) atTop (nhds 0) := by
  apply tendsto_pi_nhds.2
  intro s
  apply tendsto_pi_nhds.2
  intro who
  simpa only [finkPoissonRemainderVector, Pi.zero_apply] using
    G.tendsto_finkPoissonRemainder_zero_of_boundary
      hβ0 hβ1 hpay hz hfix W K hKlim hKnorm s who

/-- If the first corrected relative bias reaches another projective
boundary, the exact corrected Bellman equation cancels its normalized
forcing as well. -/
theorem tendsto_finkNextPoissonRemainderVector_zero_of_corrected_boundary
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {β : ℕ → ℝ} {U : ℝ}
    (hβ0 : ∀ n, 0 ≤ β n) (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (W K L : G.State → Payoff ι)
    (hLlim : Tendsto (G.compactifyFinkBias ∘ fun n =>
      G.finkCorrectedRelativeBias (β n) W K (z n)) atTop (nhds L))
    (hLnorm : ‖L‖ = 1) :
    Tendsto (fun n => G.finkNextPoissonRemainderVector
      (1 + ‖G.finkRelativeBias (β n) W (z n)‖)
      (G.finkPoissonRemainderVector (β n) W K (z n))
      (G.finkCorrectedRelativeBias (β n) W K (z n)) L (z n))
      atTop (nhds 0) := by
  apply tendsto_pi_nhds.2
  intro s
  apply tendsto_pi_nhds.2
  intro who
  have hv := G.tendsto_finkValue_apply hz s who
  apply G.tendsto_finkNextPoissonRemainderVector_apply_zero_of_boundary
    hz hv L s who
  · intro n
    simpa only [finkCorrectedRelativeBias, finkPoissonRemainderVector] using
      G.finkValue_add_correctedBias_eq_stage_add
        (β n) U (hβ0 n) (hβ1 n) hpay (z n) (hfix n) W K s who
  · exact hLlim
  · exact hLnorm

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

/-- Finite radial-induction principle for state/player bias families.  To
prove a property of every bias sequence, it is enough to prove it when a
subsequence converges and to show that it pulls back across one boundary
correction.  Protected norm-attaining coordinates force the boundary branch
to terminate after finitely many steps. -/
theorem finkBias_finite_radial_induction
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    (Q : (ℕ → G.State → Payoff ι) → Prop)
    (hinterior : ∀ (H : ℕ → G.State → Payoff ι) (φ : ℕ → ℕ)
      (L : G.State → Payoff ι), StrictMono φ →
        Tendsto (H ∘ φ) atTop (nhds L) → Q H)
    (hboundary : ∀ (H : ℕ → G.State → Payoff ι)
      (K : G.State → Payoff ι) (φ : ℕ → ℕ), StrictMono φ →
        Tendsto (G.compactifyFinkBias ∘ H ∘ φ) atTop (nhds K) →
        ‖K‖ = 1 →
        Q (fun n => G.finkCorrectedBias (H (φ n)) K) → Q H)
    (H₀ : ℕ → G.State → Payoff ι) : Q H₀ := by
  classical
  let total : ℕ := Finset.card (Finset.univ : Finset G.FinkBiasIndex)
  have aux : ∀ N : ℕ, ∀ (P : Finset G.FinkBiasIndex)
      (H : ℕ → G.State → Payoff ι),
      total - P.card = N →
      (∀ p ∈ P, ∃ c : ℝ,
        Tendsto (fun n => G.finkBiasCoordinate (H n) p) atTop (nhds c)) →
      Q H := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
        intro P H hN hprotected
        obtain ⟨K, φ, hφ, hcompact, hinteriorCase | hboundaryCase⟩ :=
          G.exists_finkBias_subsequence_interior_or_direction H
        · exact hinterior H φ (G.decompactifyFinkBias K)
            hφ hinteriorCase.2
        · have hprotectedφ : ∀ p ∈ P, ∃ c : ℝ,
              Tendsto (fun n => G.finkBiasCoordinate (H (φ n)) p)
                atTop (nhds c) := by
            intro p hp
            obtain ⟨c, hc⟩ := hprotected p hp
            exact ⟨c, hc.comp hφ.tendsto_atTop⟩
          obtain ⟨p, σ, ψ, hσ, hψ, hstrict, hcompactψ, hKcoord,
              hmax, hprotected'⟩ :=
            G.exists_finkBias_boundary_protectedCoordinateExtension
              P (H ∘ φ) K hcompact hboundaryCase.1 hprotectedφ
          let P' : Finset G.FinkBiasIndex := G.extendFinkBiasMask P p
          let J : ℕ → G.State → Payoff ι := fun n =>
            G.finkCorrectedBias (H (φ (ψ n))) K
          have hcard : P.card < P'.card := by
            exact Finset.card_lt_card (by simpa only [P'] using hstrict)
          have hP'le : P'.card ≤ total := by
            dsimp [total]
            exact Finset.card_le_card (Finset.subset_univ P')
          have hremain : total - P'.card < N := by omega
          have hJprotected : ∀ q ∈ P', ∃ c : ℝ,
              Tendsto (fun n => G.finkBiasCoordinate (J n) q)
                atTop (nhds c) := by
            simpa only [P', J, Function.comp_def] using hprotected'
          have hQJ : Q J :=
            ih (total - P'.card) hremain P' J rfl hJprotected
          apply hboundary H K (φ ∘ ψ) (hφ.comp hψ)
          · simpa only [Function.comp_def] using hcompactψ
          · exact hboundaryCase.1
          · simpa only [J, Function.comp_def] using hQJ
  apply aux total ∅ H₀
  · simp only [Finset.card_empty, Nat.sub_zero]
  · intro p hp
    simp only [Finset.notMem_empty] at hp

/-- A finite lexicographic resolution of a bias family.  An interior node
ends with an ordinarily convergent bias subsequence; a boundary node records
one unit direction and continues with the radially corrected lower-order
bias. -/
inductive FinkBiasResolution (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] :
    (ℕ → G.State → Payoff ι) → Prop
  | interior {H : ℕ → G.State → Payoff ι}
      (φ : ℕ → ℕ) (L : G.State → Payoff ι)
      (hφ : StrictMono φ)
      (hlim : Tendsto (H ∘ φ) atTop (nhds L)) :
      G.FinkBiasResolution H
  | boundary {H : ℕ → G.State → Payoff ι}
      (K : G.State → Payoff ι) (φ : ℕ → ℕ)
      (hφ : StrictMono φ)
      (hlim : Tendsto (G.compactifyFinkBias ∘ H ∘ φ)
        atTop (nhds K))
      (hKnorm : ‖K‖ = 1)
      (tail : G.FinkBiasResolution
        (fun n => G.finkCorrectedBias (H (φ n)) K)) :
      G.FinkBiasResolution H

/-- Every finite-dimensional state/player bias family has a finite
lexicographic radial resolution. -/
theorem exists_finkBiasResolution
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    (H : ℕ → G.State → Payoff ι) :
    G.FinkBiasResolution H := by
  apply G.finkBias_finite_radial_induction
    (Q := fun J => G.FinkBiasResolution J)
  · intro J φ L hφ hlim
    exact FinkBiasResolution.interior φ L hφ hlim
  · intro J K φ hφ hlim hKnorm tail
    exact FinkBiasResolution.boundary K φ hφ hlim hKnorm tail

/-- Sum of a finite family of scalar bias layers at index `n`. -/
def finkBiasLayerSum (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι]
    (layers : List ((ℕ → ℝ) × (G.State → Payoff ι))) (n : ℕ) :
    G.State → Payoff ι :=
  (layers.map fun layer => layer.1 n • layer.2).sum

/-- Sum of the scalar coefficients in a finite bias expansion. -/
def finkBiasScaleSum (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι]
    (layers : List ((ℕ → ℝ) × (G.State → Payoff ι))) (n : ℕ) : ℝ :=
  (layers.map fun layer => layer.1 n).sum

theorem monotone_finkBiasScaleSum
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    (layers : List ((ℕ → ℝ) × (G.State → Payoff ι)))
    (hmono : ∀ layer ∈ layers, Monotone layer.1) :
    Monotone (G.finkBiasScaleSum layers) := by
  intro m n hmn
  induction layers with
  | nil => simp [finkBiasScaleSum]
  | cons layer layers ih =>
      have hlayer : layer.1 m ≤ layer.1 n :=
        hmono layer (by simp) hmn
      have htail : ∀ item ∈ layers, Monotone item.1 := by
        intro item hitem
        exact hmono item (by simp [hitem])
      change layer.1 m + (layers.map fun item => item.1 m).sum ≤
        layer.1 n + (layers.map fun item => item.1 n).sum
      exact add_le_add hlayer (ih htail)

/-- If all unit-direction coefficients increase across one step, the norm
of the corresponding layer change is bounded by the increase of their
scalar sum. -/
theorem norm_finkBiasLayerSum_sub_le_scaleSum_sub
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    (layers : List ((ℕ → ℝ) × (G.State → Payoff ι))) (n : ℕ)
    (hdir : ∀ layer ∈ layers, ‖layer.2‖ = 1)
    (hmono : ∀ layer ∈ layers, layer.1 n ≤ layer.1 (n + 1)) :
    ‖G.finkBiasLayerSum layers (n + 1) -
        G.finkBiasLayerSum layers n‖ ≤
      G.finkBiasScaleSum layers (n + 1) -
        G.finkBiasScaleSum layers n := by
  induction layers with
  | nil => simp [finkBiasLayerSum, finkBiasScaleSum]
  | cons layer layers ih =>
      have hlayerDir : ‖layer.2‖ = 1 := hdir layer (by simp)
      have hlayerMono : layer.1 n ≤ layer.1 (n + 1) :=
        hmono layer (by simp)
      have htailDir : ∀ item ∈ layers, ‖item.2‖ = 1 := by
        intro item hitem
        exact hdir item (by simp [hitem])
      have htailMono : ∀ item ∈ layers,
          item.1 n ≤ item.1 (n + 1) := by
        intro item hitem
        exact hmono item (by simp [hitem])
      have htail := ih htailDir htailMono
      change
        ‖(layer.1 (n + 1) • layer.2 +
              (layers.map fun item => item.1 (n + 1) • item.2).sum) -
            (layer.1 n • layer.2 +
              (layers.map fun item => item.1 n • item.2).sum)‖ ≤
          (layer.1 (n + 1) +
              (layers.map fun item => item.1 (n + 1)).sum) -
            (layer.1 n + (layers.map fun item => item.1 n).sum)
      have heq :
          layer.1 (n + 1) • layer.2 +
                (layers.map fun item => item.1 (n + 1) • item.2).sum -
              (layer.1 n • layer.2 +
                (layers.map fun item => item.1 n • item.2).sum) =
            (layer.1 (n + 1) - layer.1 n) • layer.2 +
              ((layers.map fun item => item.1 (n + 1) • item.2).sum -
                (layers.map fun item => item.1 n • item.2).sum) := by
        module
      rw [heq]
      calc
        ‖(layer.1 (n + 1) - layer.1 n) • layer.2 +
            ((layers.map fun item => item.1 (n + 1) • item.2).sum -
              (layers.map fun item => item.1 n • item.2).sum)‖ ≤
            ‖(layer.1 (n + 1) - layer.1 n) • layer.2‖ +
              ‖(layers.map fun item => item.1 (n + 1) • item.2).sum -
                (layers.map fun item => item.1 n • item.2).sum‖ :=
          norm_add_le _ _
        _ ≤ (layer.1 (n + 1) - layer.1 n) +
              ((layers.map fun item => item.1 (n + 1)).sum -
                (layers.map fun item => item.1 n).sum) := by
          rw [norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (sub_nonneg.mpr hlayerMono), hlayerDir, mul_one]
          exact add_le_add le_rfl htail
        _ = layer.1 (n + 1) +
              (layers.map fun item => item.1 (n + 1)).sum -
            (layer.1 n + (layers.map fun item => item.1 n).sum) := by ring

/-- Predicate asserting an explicit finite expansion extracted from a radial
resolution.  Every unbounded layer has a fixed unit direction and a scalar
coefficient tending to infinity; the final remainder converges ordinarily. -/
def IsFinkBiasExpansion (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι]
    (H : ℕ → G.State → Payoff ι) (φ : ℕ → ℕ)
    (layers : List ((ℕ → ℝ) × (G.State → Payoff ι)))
    (remainder : ℕ → G.State → Payoff ι)
    (remainderLimit : G.State → Payoff ι) : Prop :=
  StrictMono φ ∧
    Tendsto remainder atTop (nhds remainderLimit) ∧
    (∀ layer ∈ layers, ‖layer.2‖ = 1) ∧
    (∀ layer ∈ layers, Tendsto layer.1 atTop atTop) ∧
    ∀ n, H (φ n) = remainder n + G.finkBiasLayerSum layers n

/-- A finite family of divergent real scales and one convergent remainder
admit a common subsequence on which every scale is strictly increasing and
the remainder approaches its limit at a geometric rate. -/
theorem exists_finkBiasExpansion_regularizingSubsequence
    {X : Type} [PseudoMetricSpace X]
    (scales : List (ℕ → ℝ))
    (hscale : ∀ u ∈ scales, Tendsto u atTop atTop)
    {R : ℕ → X} {L : X} (hR : Tendsto R atTop (nhds L)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      (∀ u ∈ scales, StrictMono (u ∘ ψ)) ∧
      ∀ n, dist (R (ψ n)) L < ((2 : ℝ) ^ n)⁻¹ := by
  have hscalesEventually : ∀ k : ℕ,
      ∀ᶠ m in atTop, ∀ u ∈ scales, u k < u m := by
    intro k
    induction scales with
    | nil => simp
    | cons u scales ih =>
        have hu := tendsto_atTop.1 (hscale u (by simp)) (u k + 1)
        have htail : ∀ v ∈ scales, Tendsto v atTop atTop := by
          intro v hv
          exact hscale v (by simp [hv])
        have hi := ih htail
        filter_upwards [hu, hi] with m hum him
        intro v hv
        simp only [List.mem_cons] at hv
        rcases hv with rfl | hv
        · linarith
        · exact him v hv
  have hex : ∀ k n : ℕ, ∃ m : ℕ,
      k < m ∧ (∀ u ∈ scales, u k < u m) ∧
        dist (R m) L < ((2 : ℝ) ^ n)⁻¹ := by
    intro k n
    have hpositive : 0 < ((2 : ℝ) ^ n)⁻¹ := by positivity
    have hclose := hR.eventually (Metric.ball_mem_nhds L hpositive)
    have hindex : ∀ᶠ m in atTop, k < m := eventually_gt_atTop k
    have hev : ∀ᶠ m in atTop,
        k < m ∧ (∀ u ∈ scales, u k < u m) ∧
          dist (R m) L < ((2 : ℝ) ^ n)⁻¹ := by
      filter_upwards [hindex, hscalesEventually k, hclose] with m hkm hsm hrm
      exact ⟨hkm, hsm, by simpa only [Metric.mem_ball] using hrm⟩
    exact hev.exists
  choose next hnext using hex
  let ψ : ℕ → ℕ := fun n => Nat.rec (next 0 0)
    (fun j previous => next previous (j + 1)) n
  have hstep : ∀ n, ψ n < ψ (n + 1) := by
    intro n
    rw [show ψ (n + 1) = next (ψ n) (n + 1) by simp [ψ]]
    exact (hnext (ψ n) (n + 1)).1
  have hψ : StrictMono ψ := strictMono_nat_of_lt_succ hstep
  refine ⟨ψ, hψ, ?_, ?_⟩
  · intro u hu
    apply strictMono_nat_of_lt_succ
    intro n
    change u (ψ n) < u (ψ (n + 1))
    rw [show ψ (n + 1) = next (ψ n) (n + 1) by simp [ψ]]
    exact (hnext (ψ n) (n + 1)).2.1 u hu
  · intro n
    cases n with
    | zero =>
        change dist (R (next 0 0)) L < ((2 : ℝ) ^ 0)⁻¹
        exact (hnext 0 0).2.2
    | succ n =>
        rw [show ψ (n + 1) = next (ψ n) (n + 1) by simp [ψ]]
        exact (hnext (ψ n) (n + 1)).2.2

/-- Every explicit finite expansion can be regularized simultaneously at
all of its scales. -/
theorem IsFinkBiasExpansion.exists_regularizingSubsequence
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    {H : ℕ → G.State → Payoff ι} {φ : ℕ → ℕ}
    {layers : List ((ℕ → ℝ) × (G.State → Payoff ι))}
    {remainder : ℕ → G.State → Payoff ι}
    {remainderLimit : G.State → Payoff ι}
    (hexpansion : G.IsFinkBiasExpansion H φ layers
      remainder remainderLimit) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      (∀ layer ∈ layers, StrictMono (layer.1 ∘ ψ)) ∧
      ∀ n, dist (remainder (ψ n)) remainderLimit <
        ((2 : ℝ) ^ n)⁻¹ := by
  obtain ⟨ψ, hψ, hscales, hrem⟩ :=
    exists_finkBiasExpansion_regularizingSubsequence
      (layers.map Prod.fst)
      (by
        intro u hu
        rw [List.mem_map] at hu
        obtain ⟨layer, hlayer, rfl⟩ := hu
        exact hexpansion.2.2.2.1 layer hlayer)
      hexpansion.2.1
  refine ⟨ψ, hψ, ?_, hrem⟩
  intro layer hlayer
  exact hscales layer.1 (List.mem_map.mpr ⟨layer, hlayer, rfl⟩)

/-- One-step variation bound for a regularized finite bias expansion. -/
theorem IsFinkBiasExpansion.norm_sub_le_remainder_add_scaleIncrement
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    {H : ℕ → G.State → Payoff ι} {φ : ℕ → ℕ}
    {layers : List ((ℕ → ℝ) × (G.State → Payoff ι))}
    {remainder : ℕ → G.State → Payoff ι}
    {remainderLimit : G.State → Payoff ι}
    (hexpansion : G.IsFinkBiasExpansion H φ layers
      remainder remainderLimit)
    (hmono : ∀ layer ∈ layers, StrictMono layer.1) (n : ℕ) :
    ‖H (φ (n + 1)) - H (φ n)‖ ≤
      ‖remainder (n + 1) - remainder n‖ +
        (G.finkBiasScaleSum layers (n + 1) -
          G.finkBiasScaleSum layers n) := by
  rw [hexpansion.2.2.2.2 n, hexpansion.2.2.2.2 (n + 1)]
  have hlayers := G.norm_finkBiasLayerSum_sub_le_scaleSum_sub
    layers n hexpansion.2.2.1
      (fun layer hlayer => (hmono layer hlayer).monotone (Nat.le_succ n))
  have heq :
      remainder (n + 1) + G.finkBiasLayerSum layers (n + 1) -
          (remainder n + G.finkBiasLayerSum layers n) =
        (remainder (n + 1) - remainder n) +
          (G.finkBiasLayerSum layers (n + 1) -
            G.finkBiasLayerSum layers n) := by
    module
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add le_rfl hlayers)

/-- Scalar increments telescope exactly across a finite range. -/
theorem sum_range_succ_sub_eq (f : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, (f (n + 1) - f n) = f N - f 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- Cumulative adjacent variation of a regularized expansion is controlled
by the terminal increase of its finite scalar layers plus the variation of
the convergent remainder. -/
theorem IsFinkBiasExpansion.sum_norm_sub_le
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    {H : ℕ → G.State → Payoff ι} {φ : ℕ → ℕ}
    {layers : List ((ℕ → ℝ) × (G.State → Payoff ι))}
    {remainder : ℕ → G.State → Payoff ι}
    {remainderLimit : G.State → Payoff ι}
    (hexpansion : G.IsFinkBiasExpansion H φ layers
      remainder remainderLimit)
    (hmono : ∀ layer ∈ layers, StrictMono layer.1) (N : ℕ) :
    ∑ n ∈ Finset.range N,
        ‖H (φ (n + 1)) - H (φ n)‖ ≤
      (∑ n ∈ Finset.range N,
        ‖remainder (n + 1) - remainder n‖) +
      (G.finkBiasScaleSum layers N -
        G.finkBiasScaleSum layers 0) := by
  calc
    ∑ n ∈ Finset.range N,
        ‖H (φ (n + 1)) - H (φ n)‖ ≤
        ∑ n ∈ Finset.range N,
          (‖remainder (n + 1) - remainder n‖ +
            (G.finkBiasScaleSum layers (n + 1) -
              G.finkBiasScaleSum layers n)) := by
      exact Finset.sum_le_sum fun n _ =>
        IsFinkBiasExpansion.norm_sub_le_remainder_add_scaleIncrement
          G hexpansion hmono n
    _ = (∑ n ∈ Finset.range N,
          ‖remainder (n + 1) - remainder n‖) +
        ∑ n ∈ Finset.range N,
          (G.finkBiasScaleSum layers (n + 1) -
            G.finkBiasScaleSum layers n) := by
      rw [Finset.sum_add_distrib]
    _ = (∑ n ∈ Finset.range N,
          ‖remainder (n + 1) - remainder n‖) +
        (G.finkBiasScaleSum layers N -
          G.finkBiasScaleSum layers 0) := by
      rw [sum_range_succ_sub_eq]

/-- Geometric convergence makes the total adjacent variation of the
regularized remainder uniformly bounded. -/
theorem sum_norm_sub_le_four_of_geometric_close
    {X : Type} [NormedAddCommGroup X] (R : ℕ → X) (L : X)
    (hclose : ∀ n, dist (R n) L < ((2 : ℝ) ^ n)⁻¹) (N : ℕ) :
    ∑ n ∈ Finset.range N, ‖R (n + 1) - R n‖ ≤ 4 := by
  have hstep : ∀ n, ‖R (n + 1) - R n‖ ≤
      2 * ((2 : ℝ) ^ n)⁻¹ := by
    intro n
    have htriangle : ‖R (n + 1) - R n‖ ≤
        dist (R (n + 1)) L + dist (R n) L := by
      calc
        ‖R (n + 1) - R n‖ = dist (R (n + 1)) (R n) := by
          rw [dist_eq_norm]
        _ ≤ dist (R (n + 1)) L + dist L (R n) :=
          dist_triangle (R (n + 1)) L (R n)
        _ = dist (R (n + 1)) L + dist (R n) L := by
          rw [dist_comm L (R n)]
    have hnext := hclose (n + 1)
    have hcurrent := hclose n
    have hpow : ((2 : ℝ) ^ (n + 1))⁻¹ ≤ ((2 : ℝ) ^ n)⁻¹ := by
      exact inv_pow_le_inv_pow_of_le (by norm_num) (Nat.le_succ n)
    linarith
  have hsum := Finset.sum_le_sum fun n (_ : n ∈ Finset.range N) => hstep n
  have hgeom : (∑ n ∈ Finset.range N, ((2 : ℝ) ^ n)⁻¹) ≤ 2 := by
    simpa only [← inv_pow, one_div] using sum_geometric_two_le N
  calc
    ∑ n ∈ Finset.range N, ‖R (n + 1) - R n‖ ≤
        ∑ n ∈ Finset.range N, 2 * ((2 : ℝ) ^ n)⁻¹ := hsum
    _ = 2 * ∑ n ∈ Finset.range N, ((2 : ℝ) ^ n)⁻¹ := by
      rw [Finset.mul_sum]
    _ ≤ 2 * 2 := mul_le_mul_of_nonneg_left hgeom (by norm_num)
    _ = 4 := by norm_num

/-- Final variation estimate: after regularization, all nonconvergent motion
is charged only once through the terminal increases of finitely many scalar
layers. -/
theorem IsFinkBiasExpansion.sum_norm_sub_le_four_add_scale
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    {H : ℕ → G.State → Payoff ι} {φ : ℕ → ℕ}
    {layers : List ((ℕ → ℝ) × (G.State → Payoff ι))}
    {remainder : ℕ → G.State → Payoff ι}
    {remainderLimit : G.State → Payoff ι}
    (hexpansion : G.IsFinkBiasExpansion H φ layers
      remainder remainderLimit)
    (hmono : ∀ layer ∈ layers, StrictMono layer.1)
    (hclose : ∀ n, dist (remainder n) remainderLimit <
      ((2 : ℝ) ^ n)⁻¹) (N : ℕ) :
    ∑ n ∈ Finset.range N,
        ‖H (φ (n + 1)) - H (φ n)‖ ≤
      4 + (G.finkBiasScaleSum layers N -
        G.finkBiasScaleSum layers 0) := by
  exact (IsFinkBiasExpansion.sum_norm_sub_le G hexpansion hmono N).trans
    (add_le_add
      (sum_norm_sub_le_four_of_geometric_close remainder remainderLimit
        hclose N)
      le_rfl)

/-- A finite radial resolution yields an explicit finite bias expansion. -/
theorem FinkBiasResolution.exists_finkBiasExpansion
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    {H : ℕ → G.State → Payoff ι}
    (hresolution : G.FinkBiasResolution H) :
    ∃ (φ : ℕ → ℕ)
      (layers : List ((ℕ → ℝ) × (G.State → Payoff ι)))
      (remainder : ℕ → G.State → Payoff ι)
      (remainderLimit : G.State → Payoff ι),
      G.IsFinkBiasExpansion H φ layers remainder remainderLimit := by
  induction hresolution with
  | @interior H φ L hφ hlim =>
      refine ⟨φ, [], H ∘ φ, L, hφ, hlim, ?_, ?_, ?_⟩
      · simp
      · simp
      · intro n
        simp [finkBiasLayerSum]
  | @boundary H K φ hφ hcompact hKnorm tail ih =>
      obtain ⟨ψ, layers, remainder, remainderLimit,
        hψ, hrem, hdir, hscale, hdecomp⟩ := ih
      let c : ℕ → ℝ := fun n => 1 + ‖H (φ (ψ n))‖
      have hcompact' : Tendsto
          (G.compactifyFinkBias ∘ fun n => H (φ n)) atTop (nhds K) := by
        simpa only [Function.comp_def] using hcompact
      have hnorm : Tendsto (fun n => ‖H (φ n)‖) atTop atTop :=
        G.tendsto_norm_finkBias_atTop_of_compactify_tendsto_norm_eq_one
          hcompact' hKnorm
      have hc : Tendsto c atTop atTop := by
        have hnorm' := hnorm.comp hψ.tendsto_atTop
        refine tendsto_atTop.2 fun b => ?_
        filter_upwards [tendsto_atTop.1 hnorm' (b - 1)] with n hn
        dsimp [c]
        change b - 1 ≤ ‖H (φ (ψ n))‖ at hn
        linarith
      refine ⟨φ ∘ ψ, (c, K) :: layers, remainder, remainderLimit,
        hφ.comp hψ, hrem, ?_, ?_, ?_⟩
      · intro layer hlayer
        simp only [List.mem_cons] at hlayer
        rcases hlayer with rfl | hlayer
        · exact hKnorm
        · exact hdir layer hlayer
      · intro layer hlayer
        simp only [List.mem_cons] at hlayer
        rcases hlayer with rfl | hlayer
        · exact hc
        · exact hscale layer hlayer
      · intro n
        have htail := hdecomp n
        change G.finkCorrectedBias (H (φ (ψ n))) K =
          remainder n + G.finkBiasLayerSum layers n at htail
        rw [finkBiasLayerSum, List.map_cons, List.sum_cons]
        dsimp only [c, Prod.fst, Prod.snd]
        change H (φ (ψ n)) = remainder n +
          ((1 + ‖H (φ (ψ n))‖) • K +
            (layers.map fun layer => layer.1 n • layer.2).sum)
        calc
          H (φ (ψ n)) =
              G.finkCorrectedBias (H (φ (ψ n))) K +
                (1 + ‖H (φ (ψ n))‖) • K := by
            ext s who
            simp only [finkCorrectedBias, Pi.add_apply, Pi.sub_apply,
              Pi.smul_apply, smul_eq_mul]
            ring
          _ = (remainder n + G.finkBiasLayerSum layers n) +
                (1 + ‖H (φ (ψ n))‖) • K := by rw [htail]
          _ = remainder n +
                ((1 + ‖H (φ (ψ n))‖) • K +
                  (layers.map fun layer => layer.1 n • layer.2).sum) := by
            rw [finkBiasLayerSum]
            abel

/-- Every finite-dimensional bias family has a subsequence whose adjacent
variation is controlled by terminal increases of finitely many monotone
scalar layers, with only a universal constant left from the convergent
remainder. -/
theorem exists_regular_finkBiasExpansion
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    (H : ℕ → G.State → Payoff ι) :
    ∃ (θ : ℕ → ℕ)
      (layers : List ((ℕ → ℝ) × (G.State → Payoff ι)))
      (remainder : ℕ → G.State → Payoff ι)
      (remainderLimit : G.State → Payoff ι),
      G.IsFinkBiasExpansion H θ layers remainder remainderLimit ∧
      (∀ layer ∈ layers, StrictMono layer.1) ∧
      (∀ n, dist (remainder n) remainderLimit < ((2 : ℝ) ^ n)⁻¹) ∧
      ∀ N, ∑ n ∈ Finset.range N,
          ‖H (θ (n + 1)) - H (θ n)‖ ≤
        4 + (G.finkBiasScaleSum layers N -
          G.finkBiasScaleSum layers 0) := by
  obtain ⟨φ, layers, remainder, remainderLimit, hexpansion⟩ :=
    (G.exists_finkBiasResolution H).exists_finkBiasExpansion
  obtain ⟨ψ, hψ, hmono, hclose⟩ :=
    hexpansion.exists_regularizingSubsequence G
  let layers' : List ((ℕ → ℝ) × (G.State → Payoff ι)) :=
    layers.map fun layer => (layer.1 ∘ ψ, layer.2)
  let remainder' : ℕ → G.State → Payoff ι := remainder ∘ ψ
  have hexpansion' : G.IsFinkBiasExpansion H (φ ∘ ψ) layers'
      remainder' remainderLimit := by
    refine ⟨hexpansion.1.comp hψ,
      hexpansion.2.1.comp hψ.tendsto_atTop, ?_, ?_, ?_⟩
    · intro layer' hlayer'
      simp only [layers', List.mem_map] at hlayer'
      obtain ⟨layer, hlayer, rfl⟩ := hlayer'
      exact hexpansion.2.2.1 layer hlayer
    · intro layer' hlayer'
      simp only [layers', List.mem_map] at hlayer'
      obtain ⟨layer, hlayer, rfl⟩ := hlayer'
      exact (hexpansion.2.2.2.1 layer hlayer).comp hψ.tendsto_atTop
    · intro n
      have hdecomp := hexpansion.2.2.2.2 (ψ n)
      change H (φ (ψ n)) = remainder' n +
        G.finkBiasLayerSum layers' n
      rw [hdecomp]
      simp only [remainder', layers', finkBiasLayerSum,
        Function.comp_def, List.map_map]
  have hmono' : ∀ layer ∈ layers', StrictMono layer.1 := by
    intro layer' hlayer'
    simp only [layers', List.mem_map] at hlayer'
    obtain ⟨layer, hlayer, rfl⟩ := hlayer'
    exact hmono layer hlayer
  have hclose' : ∀ n, dist (remainder' n) remainderLimit <
      ((2 : ℝ) ^ n)⁻¹ := by
    intro n
    exact hclose n
  refine ⟨φ ∘ ψ, layers', remainder', remainderLimit,
    hexpansion', hmono', hclose', ?_⟩
  intro N
  exact hexpansion'.sum_norm_sub_le_four_add_scale G hmono' hclose' N

/-- A divergent external scale can be regularized together with every radial
scale in a finite bias expansion.  This is the form needed when the bias is
centered at a vanishing-discount limit: the external scale is
`β / (1 - β)`. -/
theorem exists_regular_finkBiasExpansion_with_scale
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    (H : ℕ → G.State → Payoff ι) (a : ℕ → ℝ)
    (ha : Tendsto a atTop atTop) :
    ∃ (θ : ℕ → ℕ)
      (layers : List ((ℕ → ℝ) × (G.State → Payoff ι)))
      (remainder : ℕ → G.State → Payoff ι)
      (remainderLimit : G.State → Payoff ι),
      G.IsFinkBiasExpansion H θ layers remainder remainderLimit ∧
      StrictMono (a ∘ θ) ∧
      (∀ layer ∈ layers, StrictMono layer.1) ∧
      (∀ n, dist (remainder n) remainderLimit < ((2 : ℝ) ^ n)⁻¹) ∧
      ∀ N, ∑ n ∈ Finset.range N,
          ‖H (θ (n + 1)) - H (θ n)‖ ≤
        4 + (G.finkBiasScaleSum layers N -
          G.finkBiasScaleSum layers 0) := by
  obtain ⟨φ, layers, remainder, remainderLimit, hexpansion⟩ :=
    (G.exists_finkBiasResolution H).exists_finkBiasExpansion
  obtain ⟨ψ, hψ, hscales, hclose⟩ :=
    exists_finkBiasExpansion_regularizingSubsequence
      ((a ∘ φ) :: layers.map Prod.fst)
      (by
        intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | hu
        · exact ha.comp hexpansion.1.tendsto_atTop
        · rw [List.mem_map] at hu
          obtain ⟨layer, hlayer, rfl⟩ := hu
          exact hexpansion.2.2.2.1 layer hlayer)
      hexpansion.2.1
  let layers' : List ((ℕ → ℝ) × (G.State → Payoff ι)) :=
    layers.map fun layer => (layer.1 ∘ ψ, layer.2)
  let remainder' : ℕ → G.State → Payoff ι := remainder ∘ ψ
  have hexpansion' : G.IsFinkBiasExpansion H (φ ∘ ψ) layers'
      remainder' remainderLimit := by
    refine ⟨hexpansion.1.comp hψ,
      hexpansion.2.1.comp hψ.tendsto_atTop, ?_, ?_, ?_⟩
    · intro layer' hlayer'
      simp only [layers', List.mem_map] at hlayer'
      obtain ⟨layer, hlayer, rfl⟩ := hlayer'
      exact hexpansion.2.2.1 layer hlayer
    · intro layer' hlayer'
      simp only [layers', List.mem_map] at hlayer'
      obtain ⟨layer, hlayer, rfl⟩ := hlayer'
      exact (hexpansion.2.2.2.1 layer hlayer).comp hψ.tendsto_atTop
    · intro n
      have hdecomp := hexpansion.2.2.2.2 (ψ n)
      change H (φ (ψ n)) = remainder' n +
        G.finkBiasLayerSum layers' n
      rw [hdecomp]
      simp only [remainder', layers', finkBiasLayerSum,
        Function.comp_def, List.map_map]
  have ha' : StrictMono (a ∘ (φ ∘ ψ)) := by
    simpa only [Function.comp_assoc] using
      hscales (a ∘ φ) (by simp)
  have hmono' : ∀ layer ∈ layers', StrictMono layer.1 := by
    intro layer' hlayer'
    simp only [layers', List.mem_map] at hlayer'
    obtain ⟨layer, hlayer, rfl⟩ := hlayer'
    exact hscales layer.1 (by
      simp only [List.mem_cons, List.mem_map]
      exact Or.inr ⟨layer, hlayer, rfl⟩)
  have hclose' : ∀ n, dist (remainder' n) remainderLimit <
      ((2 : ℝ) ^ n)⁻¹ := hclose
  refine ⟨φ ∘ ψ, layers', remainder', remainderLimit,
    hexpansion', ha', hmono', hclose', ?_⟩
  intro N
  exact hexpansion'.sum_norm_sub_le_four_add_scale G hmono' hclose' N

/-- A finite bias resolution together with the normalized Poisson
cancellation forced by the Bellman equation at every boundary node. -/
inductive FinkPoissonResolution (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)] {U : ℝ} :
    (ℕ → G.finkDomain U) →
    (ℕ → G.State → Payoff ι) →
    (ℕ → ℝ) →
    (ℕ → G.State → Payoff ι) →
    (ℕ → G.State → Payoff ι) → Prop
  | interior
      {z : ℕ → G.finkDomain U} {V : ℕ → G.State → Payoff ι}
      {a : ℕ → ℝ} {E J : ℕ → G.State → Payoff ι}
      (φ : ℕ → ℕ) (Jlim : G.State → Payoff ι)
      (hφ : StrictMono φ)
      (hJlim : Tendsto (J ∘ φ) atTop (nhds Jlim)) :
      G.FinkPoissonResolution z V a E J
  | boundary
      {z : ℕ → G.finkDomain U} {V : ℕ → G.State → Payoff ι}
      {a : ℕ → ℝ} {E J : ℕ → G.State → Payoff ι}
      (K : G.State → Payoff ι) (φ : ℕ → ℕ)
      (hφ : StrictMono φ)
      (hJlim : Tendsto (G.compactifyFinkBias ∘ J ∘ φ)
        atTop (nhds K))
      (hKnorm : ‖K‖ = 1)
      (hnext : Tendsto (fun n => G.finkNextPoissonRemainderVector
        (a (φ n)) (E (φ n)) (J (φ n)) K (z (φ n)))
        atTop (nhds 0))
      (tail : G.FinkPoissonResolution
        (z ∘ φ) (V ∘ φ)
        (fun n => 1 + ‖J (φ n)‖)
        (fun n => G.finkNextPoissonRemainderVector
          (a (φ n)) (E (φ n)) (J (φ n)) K (z (φ n)))
        (fun n => G.finkCorrectedBias (J (φ n)) K)) :
      G.FinkPoissonResolution z V a E J

/-- A finite radial resolution of a Bellman bias automatically upgrades to
a finite Poisson resolution: every boundary direction cancels the whole
normalized forcing before the recursion continues. -/
theorem FinkBiasResolution.toFinkPoissonResolution
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)] {J : ℕ → G.State → Payoff ι}
    (hresolution : G.FinkBiasResolution J)
    {U : ℝ} {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    {V : ℕ → G.State → Payoff ι} {Vlim : G.State → Payoff ι}
    (hV : Tendsto V atTop (nhds Vlim))
    {a : ℕ → ℝ} {E : ℕ → G.State → Payoff ι}
    (hbellman : ∀ n s who, V n s who + J n s who =
      G.finkStageEU (z n) s who +
        G.finkContinuationEU (J n) (z n) s who +
        a n * E n s who) :
    G.FinkPoissonResolution z V a E J := by
  induction hresolution generalizing U z zlim V Vlim a E with
  | @interior J φ Jlim hφ hJlim =>
      exact FinkPoissonResolution.interior φ Jlim hφ hJlim
  | @boundary J K φ hφ hJlim hKnorm tail ih =>
      have hzφ : Tendsto (z ∘ φ) atTop (nhds zlim) :=
        hz.comp hφ.tendsto_atTop
      have hVφ : Tendsto (V ∘ φ) atTop (nhds Vlim) :=
        hV.comp hφ.tendsto_atTop
      have hJlim' : Tendsto (G.compactifyFinkBias ∘ fun n => J (φ n))
          atTop (nhds K) := by
        simpa only [Function.comp_def] using hJlim
      have hnext :=
        G.tendsto_finkNextPoissonRemainderVector_zero_of_boundary_valueVector
          hzφ hVφ K (fun n s who => hbellman (φ n) s who)
            hJlim' hKnorm
      have hbellmanNext : ∀ n s who,
          V (φ n) s who + G.finkCorrectedBias (J (φ n)) K s who =
            G.finkStageEU (z (φ n)) s who +
              G.finkContinuationEU
                (G.finkCorrectedBias (J (φ n)) K) (z (φ n)) s who +
              (1 + ‖J (φ n)‖) *
                G.finkNextPoissonRemainderVector
                  (a (φ n)) (E (φ n)) (J (φ n)) K (z (φ n)) s who := by
        intro n s who
        exact G.value_add_finkCorrectedBias_eq_stage_add
          (z (φ n)) (V (φ n) s who) (a (φ n))
            (E (φ n)) (J (φ n)) K s who (hbellman (φ n) s who)
      have htail := ih hzφ hVφ hbellmanNext
      exact FinkPoissonResolution.boundary K φ hφ hJlim hKnorm hnext htail

/-- Every convergent finite-dimensional Bellman family has a finite Poisson
resolution. -/
theorem exists_finkPoissonResolution
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    {V : ℕ → G.State → Payoff ι} {Vlim : G.State → Payoff ι}
    (hV : Tendsto V atTop (nhds Vlim))
    {a : ℕ → ℝ} {E J : ℕ → G.State → Payoff ι}
    (hbellman : ∀ n s who, V n s who + J n s who =
      G.finkStageEU (z n) s who +
        G.finkContinuationEU (J n) (z n) s who +
        a n * E n s who) :
    G.FinkPoissonResolution z V a E J :=
  FinkBiasResolution.toFinkPoissonResolution
    (G := G) (hresolution := G.exists_finkBiasResolution J) hz hV hbellman

/-- Discounted Fink fixed points admit a finite exact Poisson hierarchy for
their relative biases around any target vector `W`. -/
theorem exists_finkRelativeBiasPoissonResolution
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {β : ℕ → ℝ} {U : ℝ}
    (hβ0 : ∀ n, 0 ≤ β n) (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (W : G.State → Payoff ι) :
    G.FinkPoissonResolution z (fun n => G.finkValue (z n))
      (fun n => β n / (1 - β n))
      (fun n => G.finkContinuationResidualVector W (z n))
      (fun n => G.finkRelativeBias (β n) W (z n)) := by
  apply G.exists_finkPoissonResolution hz (G.tendsto_finkValue hz)
  intro n s who
  simpa only [finkContinuationResidualVector] using
    G.finkValue_add_relativeBias_eq_finkEU_add
      (β n) U (hβ0 n) (hβ1 n) hpay (z n) (hfix n) W s who

/-- A finite resolution carrying both sides of verification: the on-profile
Poisson remainder vanishes at every boundary scale, and every pure-deviation
forcing is asymptotically nonpositive there. -/
inductive FinkVerifiedResolution (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} :
    (ℕ → G.finkDomain U) →
    (ℕ → G.State → Payoff ι) →
    (ℕ → ℝ) →
    (ℕ → G.State → Payoff ι) →
    (ℕ → G.State → Payoff ι) →
    (ℕ → G.State → ∀ who : ι, G.Act who → ℝ) → Prop
  | interior
      {z : ℕ → G.finkDomain U} {V : ℕ → G.State → Payoff ι}
      {a : ℕ → ℝ} {E J : ℕ → G.State → Payoff ι}
      {D : ℕ → G.State → ∀ who : ι, G.Act who → ℝ}
      (φ : ℕ → ℕ) (Jlim : G.State → Payoff ι)
      (hφ : StrictMono φ)
      (hJlim : Tendsto (J ∘ φ) atTop (nhds Jlim))
      (hmean : ∀ n s who,
        expect (G.finkProfile (z n) s who) (D n s who) = 0) :
      G.FinkVerifiedResolution z V a E J D
  | boundary
      {z : ℕ → G.finkDomain U} {V : ℕ → G.State → Payoff ι}
      {a : ℕ → ℝ} {E J : ℕ → G.State → Payoff ι}
      {D : ℕ → G.State → ∀ who : ι, G.Act who → ℝ}
      (K : G.State → Payoff ι) (φ : ℕ → ℕ)
      (hφ : StrictMono φ)
      (hJlim : Tendsto (G.compactifyFinkBias ∘ J ∘ φ)
        atTop (nhds K))
      (hKnorm : ‖K‖ = 1)
      (hmean : ∀ n s who,
        expect (G.finkProfile (z n) s who) (D n s who) = 0)
      (hnextPoisson : Tendsto (fun n => G.finkNextPoissonRemainderVector
        (a (φ n)) (E (φ n)) (J (φ n)) K (z (φ n)))
        atTop (nhds 0))
      (hnextGain : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        ∀ s who (d : G.Act who),
          G.finkNextDeviationGain (a (φ n)) (D (φ n))
            (J (φ n)) K (z (φ n)) s who d ≤ ε)
      (tail : G.FinkVerifiedResolution
        (z ∘ φ) (V ∘ φ)
        (fun n => 1 + ‖J (φ n)‖)
        (fun n => G.finkNextPoissonRemainderVector
          (a (φ n)) (E (φ n)) (J (φ n)) K (z (φ n)))
        (fun n => G.finkCorrectedBias (J (φ n)) K)
        (fun n s who d => G.finkNextDeviationGain
          (a (φ n)) (D (φ n)) (J (φ n)) K (z (φ n)) s who d)) :
      G.FinkVerifiedResolution z V a E J D

/-- Verified hierarchy with its underlying reference potential made explicit.
At every boundary, the next Poisson forcing and deviation forcing are the
continuation residual and continuation gain of the same updated potential. -/
inductive FinkVerifiedReferenceResolution (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} :
    (ℕ → G.finkDomain U) →
    (ℕ → G.State → Payoff ι) →
    (ℕ → ℝ) →
    (ℕ → G.State → Payoff ι) →
    (ℕ → G.State → Payoff ι) → Prop
  | interior
      {z : ℕ → G.finkDomain U} {V : ℕ → G.State → Payoff ι}
      {a : ℕ → ℝ} {J R : ℕ → G.State → Payoff ι}
      (φ : ℕ → ℕ) (Jlim : G.State → Payoff ι)
      (hφ : StrictMono φ)
      (hJlim : Tendsto (J ∘ φ) atTop (nhds Jlim)) :
      G.FinkVerifiedReferenceResolution z V a J R
  | boundary
      {z : ℕ → G.finkDomain U} {V : ℕ → G.State → Payoff ι}
      {a : ℕ → ℝ} {J R : ℕ → G.State → Payoff ι}
      (K : G.State → Payoff ι) (φ : ℕ → ℕ)
      (hφ : StrictMono φ)
      (hJlim : Tendsto (G.compactifyFinkBias ∘ J ∘ φ)
        atTop (nhds K))
      (hKnorm : ‖K‖ = 1)
      (hnextResidual : Tendsto (fun n =>
        G.finkContinuationResidualVector
          (G.finkNextReferenceVector (a (φ n)) (J (φ n))
            (R (φ n)) K) (z (φ n))) atTop (nhds 0))
      (hnextGain : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        ∀ s who (d : G.Act who),
          G.finkContinuationGain
            (G.finkNextReferenceVector (a (φ n)) (J (φ n))
              (R (φ n)) K) (z (φ n)) s who d ≤ ε)
      (tail : G.FinkVerifiedReferenceResolution
        (z ∘ φ) (V ∘ φ)
        (fun n => 1 + ‖J (φ n)‖)
        (fun n => G.finkCorrectedBias (J (φ n)) K)
        (fun n => G.finkNextReferenceVector
          (a (φ n)) (J (φ n)) (R (φ n)) K)) :
      G.FinkVerifiedReferenceResolution z V a J R

/-- A verified reference hierarchy already gives the correction needed at its
root boundary.  Either the root bias is precompact along a subsequence, or a
single projective correction tends to zero while making the root reference
asymptotically harmonic and asymptotically excessive against every pure
deviation. -/
theorem FinkVerifiedReferenceResolution.rootCorrection_dichotomy
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {V J R : ℕ → G.State → Payoff ι}
    {a : ℕ → ℝ}
    (hresolution : G.FinkVerifiedReferenceResolution z V a J R)
    (ha : ∀ n, a n ≠ 0)
    (hscale0 : ∀ n, 0 ≤ G.finkReferenceCorrectionScale (a n) (J n))
    (hscale : Tendsto (fun n => G.finkReferenceCorrectionScale
      (a n) (J n)) atTop (nhds 0)) :
    (∃ (φ : ℕ → ℕ) (Jlim : G.State → Payoff ι),
      StrictMono φ ∧ Tendsto (J ∘ φ) atTop (nhds Jlim)) ∨
    ∃ (K : G.State → Payoff ι) (φ : ℕ → ℕ),
      StrictMono φ ∧ ‖K‖ = 1 ∧
      Tendsto (fun n => G.finkReferenceCorrection
        (a (φ n)) (J (φ n)) K) atTop (nhds 0) ∧
      Tendsto (fun n => G.finkContinuationResidualVector
        (R (φ n) + G.finkReferenceCorrection
          (a (φ n)) (J (φ n)) K) (z (φ n))) atTop (nhds 0) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        ∀ s who (d : G.Act who),
          G.finkContinuationGain
            (R (φ n) + G.finkReferenceCorrection
              (a (φ n)) (J (φ n)) K)
            (z (φ n)) s who d ≤ ε := by
  cases hresolution with
  | interior φ Jlim hφ hJlim =>
      exact Or.inl ⟨φ, Jlim, hφ, hJlim⟩
  | boundary K φ hφ hJlim hKnorm hnextResidual hnextGain tail =>
      right
      have hscaleφ : Tendsto (fun n => G.finkReferenceCorrectionScale
          (a (φ n)) (J (φ n))) atTop (nhds 0) := by
        simpa only [Function.comp_def] using
          hscale.comp hφ.tendsto_atTop
      have hcorrection : Tendsto (fun n => G.finkReferenceCorrection
          (a (φ n)) (J (φ n)) K) atTop (nhds 0) := by
        simpa only [finkReferenceCorrection, zero_smul] using
          hscaleφ.smul_const K
      have hresidual :=
        G.tendsto_finkContinuationResidualVector_add_correction_zero
          (fun n => a (φ n)) (fun n => J (φ n))
          (fun n => R (φ n)) K (fun n => z (φ n))
          (fun n => ha (φ n)) hscaleφ hnextResidual
      have hgain := G.eventually_finkContinuationGain_add_correction_le
        (fun n => a (φ n)) (fun n => J (φ n))
        (fun n => R (φ n)) K (fun n => z (φ n))
        (fun n => ha (φ n)) (fun n => hscale0 (φ n))
        hscaleφ hnextGain
      exact ⟨K, φ, hφ, hKnorm, hcorrection, hresidual, hgain⟩

/-- Upgrade a verified hierarchy to the reference-potential presentation
whenever its two forcing families are represented by one potential. -/
theorem FinkVerifiedResolution.toFinkVerifiedReferenceResolution
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {V : ℕ → G.State → Payoff ι}
    {a : ℕ → ℝ} {E J : ℕ → G.State → Payoff ι}
    {D : ℕ → G.State → ∀ who : ι, G.Act who → ℝ}
    (hresolution : G.FinkVerifiedResolution z V a E J D)
    (R : ℕ → G.State → Payoff ι)
    (hE : ∀ n, E n = G.finkContinuationResidualVector (R n) (z n))
    (hD : ∀ n s who (d : G.Act who),
      D n s who d = G.finkContinuationGain (R n) (z n) s who d) :
    G.FinkVerifiedReferenceResolution z V a J R := by
  induction hresolution generalizing R with
  | @interior z V a E J D φ Jlim hφ hJlim hmean =>
      exact FinkVerifiedReferenceResolution.interior φ Jlim hφ hJlim
  | @boundary z V a E J D K φ hφ hJlim hKnorm hmean
      hnextPoisson hnextGain tail ih =>
      let Rnext : ℕ → G.State → Payoff ι := fun n =>
        G.finkNextReferenceVector
          (a (φ n)) (J (φ n)) (R (φ n)) K
      have hnextResidual' : Tendsto (fun n =>
          G.finkContinuationResidualVector (Rnext n) (z (φ n)))
          atTop (nhds 0) := by
        apply hnextPoisson.congr'
        exact Filter.Eventually.of_forall fun n => by
          dsimp only [Rnext]
          rw [hE (φ n)]
          exact G.finkNextPoissonRemainderVector_eq_continuationResidualVector
            (a (φ n)) (J (φ n)) (R (φ n)) K (z (φ n))
      have hnextGain' : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
          ∀ s who (d : G.Act who),
            G.finkContinuationGain (Rnext n) (z (φ n)) s who d ≤ ε := by
        intro ε hε
        filter_upwards [hnextGain ε hε] with n hn
        intro s who d
        calc
          G.finkContinuationGain (Rnext n) (z (φ n)) s who d =
              G.finkNextDeviationGain (a (φ n))
                (fun s who d =>
                  G.finkContinuationGain (R (φ n)) (z (φ n)) s who d)
                (J (φ n)) K (z (φ n)) s who d :=
            (G.finkNextDeviationGain_eq_continuationGain
              (a (φ n)) (J (φ n)) (R (φ n)) K
                (z (φ n)) s who d).symm
          _ = G.finkNextDeviationGain (a (φ n)) (D (φ n))
                (J (φ n)) K (z (φ n)) s who d := by
            simp only [finkNextDeviationGain, hD]
          _ ≤ ε := hn s who d
      have hEtail : ∀ n,
          G.finkNextPoissonRemainderVector
              (a (φ n)) (E (φ n)) (J (φ n)) K (z (φ n)) =
            G.finkContinuationResidualVector (Rnext n) (z (φ n)) := by
        intro n
        rw [hE (φ n)]
        exact G.finkNextPoissonRemainderVector_eq_continuationResidualVector
          (a (φ n)) (J (φ n)) (R (φ n)) K (z (φ n))
      have hDtail : ∀ n s who (d : G.Act who),
          G.finkNextDeviationGain (a (φ n)) (D (φ n))
              (J (φ n)) K (z (φ n)) s who d =
            G.finkContinuationGain (Rnext n) (z (φ n)) s who d := by
        intro n s who d
        calc
          G.finkNextDeviationGain (a (φ n)) (D (φ n))
              (J (φ n)) K (z (φ n)) s who d =
              G.finkNextDeviationGain (a (φ n))
                (fun s who d =>
                  G.finkContinuationGain (R (φ n)) (z (φ n)) s who d)
                (J (φ n)) K (z (φ n)) s who d := by
            simp only [finkNextDeviationGain, hD]
          _ = G.finkContinuationGain (Rnext n) (z (φ n)) s who d := by
            exact G.finkNextDeviationGain_eq_continuationGain
              (a (φ n)) (J (φ n)) (R (φ n)) K
                (z (φ n)) s who d
      have htail := ih Rnext hEtail hDtail
      exact FinkVerifiedReferenceResolution.boundary K φ hφ hJlim hKnorm
        hnextResidual' hnextGain' htail

/-- A finite radial bias resolution upgrades to a finite verified resolution
when supplied with its Bellman equations and centered pure-deviation
inequalities. -/
theorem FinkBiasResolution.toFinkVerifiedResolution
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {J : ℕ → G.State → Payoff ι}
    (hresolution : G.FinkBiasResolution J)
    {U : ℝ} {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    {V : ℕ → G.State → Payoff ι} {Vlim : G.State → Payoff ι}
    (hV : Tendsto V atTop (nhds Vlim))
    {a : ℕ → ℝ} {E : ℕ → G.State → Payoff ι}
    {D : ℕ → G.State → ∀ who : ι, G.Act who → ℝ}
    (hmean : ∀ n s who,
      expect (G.finkProfile (z n) s who) (D n s who) = 0)
    (hbellman : ∀ n s who, V n s who + J n s who =
      G.finkStageEU (z n) s who +
        G.finkContinuationEU (J n) (z n) s who +
        a n * E n s who)
    (hgain : ∀ n s who (d : G.Act who),
      G.finkStageGain (z n) s who d + a n * D n s who d +
        G.finkContinuationGain (J n) (z n) s who d ≤ 0) :
    G.FinkVerifiedResolution z V a E J D := by
  induction hresolution generalizing U z zlim V Vlim a E D with
  | @interior J φ Jlim hφ hJlim =>
      exact FinkVerifiedResolution.interior φ Jlim hφ hJlim hmean
  | @boundary J K φ hφ hJlim hKnorm tail ih =>
      have hzφ : Tendsto (z ∘ φ) atTop (nhds zlim) :=
        hz.comp hφ.tendsto_atTop
      have hVφ : Tendsto (V ∘ φ) atTop (nhds Vlim) :=
        hV.comp hφ.tendsto_atTop
      have hJlim' : Tendsto (G.compactifyFinkBias ∘ fun n => J (φ n))
          atTop (nhds K) := by
        simpa only [Function.comp_def] using hJlim
      have hnextPoisson :=
        G.tendsto_finkNextPoissonRemainderVector_zero_of_boundary_valueVector
          hzφ hVφ K (fun n s who => hbellman (φ n) s who)
            hJlim' hKnorm
      have hnextGain : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
          ∀ s who (d : G.Act who),
            G.finkNextDeviationGain (a (φ n)) (D (φ n))
              (J (φ n)) K (z (φ n)) s who d ≤ ε := by
        intro ε hε
        exact G.eventually_all_finkNextDeviationGain_le_of_boundary
          hzφ K hJlim' hKnorm (a ∘ φ) (D ∘ φ)
            (fun n s who d => hgain (φ n) s who d) hε
      have hmeanNext : ∀ n s who,
          expect (G.finkProfile (z (φ n)) s who) (fun d =>
            G.finkNextDeviationGain (a (φ n)) (D (φ n))
              (J (φ n)) K (z (φ n)) s who d) = 0 := by
        intro n s who
        exact G.expect_finkNextDeviationGain_eq_zero
          (a (φ n)) (D (φ n)) (J (φ n)) K (z (φ n)) s who
            (hmean (φ n) s who)
      have hbellmanNext : ∀ n s who,
          V (φ n) s who + G.finkCorrectedBias (J (φ n)) K s who =
            G.finkStageEU (z (φ n)) s who +
              G.finkContinuationEU
                (G.finkCorrectedBias (J (φ n)) K) (z (φ n)) s who +
              (1 + ‖J (φ n)‖) *
                G.finkNextPoissonRemainderVector
                  (a (φ n)) (E (φ n)) (J (φ n)) K (z (φ n)) s who := by
        intro n s who
        exact G.value_add_finkCorrectedBias_eq_stage_add
          (z (φ n)) (V (φ n) s who) (a (φ n))
            (E (φ n)) (J (φ n)) K s who (hbellman (φ n) s who)
      have hgainNext : ∀ n s who (d : G.Act who),
          G.finkStageGain (z (φ n)) s who d +
              (1 + ‖J (φ n)‖) *
                G.finkNextDeviationGain (a (φ n)) (D (φ n))
                  (J (φ n)) K (z (φ n)) s who d +
              G.finkContinuationGain (G.finkCorrectedBias (J (φ n)) K)
                (z (φ n)) s who d ≤ 0 := by
        intro n s who d
        have heq := G.stage_add_correctedGain_add_next_eq
          (a (φ n)) (D (φ n)) (J (φ n)) K (z (φ n)) s who d
        calc
          G.finkStageGain (z (φ n)) s who d +
                (1 + ‖J (φ n)‖) *
                  G.finkNextDeviationGain (a (φ n)) (D (φ n))
                    (J (φ n)) K (z (φ n)) s who d +
                G.finkContinuationGain (G.finkCorrectedBias (J (φ n)) K)
                  (z (φ n)) s who d =
              G.finkStageGain (z (φ n)) s who d +
                G.finkContinuationGain (G.finkCorrectedBias (J (φ n)) K)
                  (z (φ n)) s who d +
                (1 + ‖J (φ n)‖) *
                  G.finkNextDeviationGain (a (φ n)) (D (φ n))
                    (J (φ n)) K (z (φ n)) s who d := by ring
          _ = G.finkStageGain (z (φ n)) s who d +
                a (φ n) * D (φ n) s who d +
                G.finkContinuationGain (J (φ n)) (z (φ n)) s who d := heq
          _ ≤ 0 := hgain (φ n) s who d
      have htail := ih hzφ hVφ hmeanNext hbellmanNext hgainNext
      exact FinkVerifiedResolution.boundary K φ hφ hJlim hKnorm
        hmean hnextPoisson hnextGain htail

/-- The relative biases of discounted Fink fixed points admit a finite
verified hierarchy around any target vector `W`. -/
theorem exists_finkRelativeBiasVerifiedResolution
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {β : ℕ → ℝ} {U : ℝ}
    (hβ0 : ∀ n, 0 ≤ β n) (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (W : G.State → Payoff ι) :
    G.FinkVerifiedResolution z (fun n => G.finkValue (z n))
      (fun n => β n / (1 - β n))
      (fun n => G.finkContinuationResidualVector W (z n))
      (fun n => G.finkRelativeBias (β n) W (z n))
      (fun n s who d => G.finkContinuationGain W (z n) s who d) := by
  apply FinkBiasResolution.toFinkVerifiedResolution
    (G := G) (hresolution := G.exists_finkBiasResolution
      (fun n => G.finkRelativeBias (β n) W (z n)))
    hz (G.tendsto_finkValue hz)
  · intro n s who
    exact G.expect_finkContinuationGain_eq_zero W (z n) s who
  · intro n s who
    simpa only [finkContinuationResidualVector] using
      G.finkValue_add_relativeBias_eq_finkEU_add
        (β n) U (hβ0 n) (hβ1 n) hpay (z n) (hfix n) W s who
  · intro n s who d
    exact G.finkCenteredGain_nonpos_of_finkMap_fixedPoint
      (β n) U (hβ0 n) (hβ1 n) hpay (z n) (hfix n) W s who d

/-- Reference-potential form of the verified relative-bias hierarchy.  It
starts from the target `W` itself and records the exact updated reference
potential at every radial boundary. -/
theorem exists_finkRelativeBiasVerifiedReferenceResolution
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {β : ℕ → ℝ} {U : ℝ}
    (hβ0 : ∀ n, 0 ≤ β n) (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (W : G.State → Payoff ι) :
    G.FinkVerifiedReferenceResolution z (fun n => G.finkValue (z n))
      (fun n => β n / (1 - β n))
      (fun n => G.finkRelativeBias (β n) W (z n))
      (fun _ => W) := by
  apply (G.exists_finkRelativeBiasVerifiedResolution
    hβ0 hβ1 hpay hz hfix W).toFinkVerifiedReferenceResolution G
  · intro n
    rfl
  · intro n s who d
    rfl

/-- The first Poisson-corrected relative bias admits the same projective
dichotomy.  The extraction preserves the Fink point, leading direction, and
vanishing normalized Poisson remainder, so the boundary branch can be
iterated without losing any certificate already obtained. -/
theorem exists_finkCorrectedRelativeBias_subsequence_interior_or_direction
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {β : ℕ → ℝ} {U : ℝ}
    (hβ0 : ∀ n, 0 ≤ β n) (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (W K : G.State → Payoff ι)
    (hKlim : Tendsto (G.compactifyFinkBias ∘ fun n =>
      G.finkRelativeBias (β n) W (z n)) atTop (nhds K))
    (hKnorm : ‖K‖ = 1) :
    ∃ (L : G.State → Payoff ι) (φ : ℕ → ℕ),
      StrictMono φ ∧
      Tendsto (z ∘ φ) atTop (nhds zlim) ∧
      Tendsto ((G.compactifyFinkBias ∘ fun n =>
        G.finkRelativeBias (β n) W (z n)) ∘ φ) atTop (nhds K) ∧
      Tendsto ((fun n => G.finkPoissonRemainderVector
        (β n) W K (z n)) ∘ φ) atTop (nhds 0) ∧
      Tendsto (G.compactifyFinkBias ∘
        (fun n => G.finkCorrectedRelativeBias (β n) W K (z n)) ∘ φ)
          atTop (nhds L) ∧
      ((‖L‖ < 1 ∧ Tendsto
          ((fun n => G.finkCorrectedRelativeBias (β n) W K (z n)) ∘ φ)
            atTop (nhds (G.decompactifyFinkBias L))) ∨
        (‖L‖ = 1 ∧ Tendsto (fun n =>
          ‖G.finkCorrectedRelativeBias (β (φ n)) W K (z (φ n))‖)
            atTop atTop ∧ Tendsto (fun n =>
          (1 + ‖G.finkRelativeBias (β (φ n)) W (z (φ n))‖) /
            (1 + ‖G.finkCorrectedRelativeBias
              (β (φ n)) W K (z (φ n))‖)) atTop atTop ∧
          Tendsto (fun n => G.finkNextPoissonRemainderVector
            (1 + ‖G.finkRelativeBias (β (φ n)) W (z (φ n))‖)
            (G.finkPoissonRemainderVector
              (β (φ n)) W K (z (φ n)))
            (G.finkCorrectedRelativeBias
              (β (φ n)) W K (z (φ n))) L (z (φ n)))
            atTop (nhds 0))) := by
  let J : ℕ → G.State → Payoff ι := fun n =>
    G.finkCorrectedRelativeBias (β n) W K (z n)
  obtain ⟨L, φ, hφ, hLlim, hLalternative⟩ :=
    G.exists_finkBias_subsequence_interior_or_direction J
  have hzφ : Tendsto (z ∘ φ) atTop (nhds zlim) :=
    hz.comp hφ.tendsto_atTop
  have hKφ := hKlim.comp hφ.tendsto_atTop
  have hrem := G.tendsto_finkPoissonRemainderVector_zero_of_boundary
    hβ0 hβ1 hpay hz hfix W K hKlim hKnorm
  have hremφ := hrem.comp hφ.tendsto_atTop
  refine ⟨L, φ, hφ, hzφ, hKφ, hremφ, ?_, ?_⟩
  · simpa only [J, Function.comp_def] using hLlim
  · rcases hLalternative with hLint | ⟨hLnorm, hJtop⟩
    · left
      simpa only [J, Function.comp_def] using hLint
    · right
      refine ⟨hLnorm, ?_, ?_, ?_⟩
      · simpa only [J, Function.comp_def] using hJtop
      · have hscale :=
          G.tendsto_finkBias_magnitude_div_corrected_magnitude_atTop
            (H := fun n => G.finkRelativeBias
              (β (φ n)) W (z (φ n))) (K := K) ?_ ?_
        · simpa only [finkCorrectedRelativeBias] using hscale
        · simpa only [Function.comp_def] using hKφ
        · simpa only [J, Function.comp_def, finkCorrectedRelativeBias] using hJtop
      · have hnext :=
          G.tendsto_finkNextPoissonRemainderVector_zero_of_corrected_boundary
            (β := β ∘ φ) (z := z ∘ φ)
            (fun n => hβ0 (φ n)) (fun n => hβ1 (φ n)) hpay hzφ
            (fun n => by simpa only [Function.comp_def] using hfix (φ n))
            W K L ?_ hLnorm
        · simpa only [Function.comp_def] using hnext
        · simpa only [J, Function.comp_def] using hLlim

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

/-- Terminal lexicographic gain certificate.  Outside a finite mask disjoint
from the limiting support, every first-boundary projective gain converges to
the negative of a finite nonnegative loss.  The terminal loss is zero on all
limiting-support coordinates. -/
theorem exists_terminal_finkProjectiveGain_subsequence
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
      (R : G.FinkPureActionVector),
      Disjoint P (G.finkSupportIndices zlim) ∧ StrictMono φ ∧
      Tendsto (z ∘ φ) atTop (nhds zlim) ∧
      Tendsto ((G.compactifyFinkBias ∘
        fun n => G.finkRelativeBias (β n) W (z n)) ∘ φ)
          atTop (nhds K) ∧
      (∀ s who (d : G.Act who), 0 ≤ R s who d) ∧
      (∀ p ∈ G.finkSupportIndices zlim,
        R p.1 p.2.1 p.2.2 = 0) ∧
      ∀ p ∉ P, Tendsto (fun n =>
        G.finkProjectiveGainVector (β (φ n)) W K (z (φ n))
          p.1 p.2.1 p.2.2) atTop
            (nhds (-R p.1 p.2.1 p.2.2)) := by
  obtain ⟨P, φ, R, hPS, hφ, hzφ, hKφ, hloss⟩ :=
    G.exists_terminal_maskedFinkProjectiveLoss_subsequence
      hβ0 hβ1 hpay hz hfix W K hKlim hKnorm
  have hlossCoord (p : G.FinkPureActionIndex) : Tendsto (fun n =>
      G.maskFinkActionVector P
        (G.finkProjectiveLossVector (β (φ n)) W K (z (φ n)))
          p.1 p.2.1 p.2.2) atTop (nhds (R p.1 p.2.1 p.2.2)) := by
    have hc : Continuous (fun Q : G.FinkPureActionVector =>
        Q p.1 p.2.1 p.2.2) := by
      fun_prop
    have ht := (hc.tendsto R).comp hloss
    simpa only [Function.comp_def] using ht
  have hRnonneg : ∀ s who (d : G.Act who), 0 ≤ R s who d := by
    intro s who d
    let p : G.FinkPureActionIndex := ⟨s, ⟨who, d⟩⟩
    apply ge_of_tendsto' (hlossCoord p)
    intro n
    apply G.maskFinkActionVector_nonneg
    intro s' who' d'
    exact G.finkProjectiveLossVector_nonneg
      (β (φ n)) W K (z (φ n)) s' who' d'
  have hRsupport : ∀ p ∈ G.finkSupportIndices zlim,
      R p.1 p.2.1 p.2.2 = 0 := by
    intro p hp
    have hpP : p ∉ P := by
      intro hp'
      exact Finset.disjoint_left.mp hPS hp' hp
    have horiginal :=
      (G.tendsto_finkProjectiveLossVector_zero_of_limit_support
        hβ0 hβ1 hpay hz hfix W K hKlim hKnorm
          p.1 p.2.1 p.2.2
          ((G.mem_finkSupportIndices zlim p).mp hp)).comp hφ.tendsto_atTop
    have hmasked : Tendsto (fun n =>
        G.maskFinkActionVector P
          (G.finkProjectiveLossVector (β (φ n)) W K (z (φ n)))
            p.1 p.2.1 p.2.2) atTop (nhds 0) := by
      have heq : (fun n => G.maskFinkActionVector P
          (G.finkProjectiveLossVector (β (φ n)) W K (z (φ n)))
            p.1 p.2.1 p.2.2) =
          (fun n => G.finkProjectiveLossVector
            (β (φ n)) W K (z (φ n)) p.1 p.2.1 p.2.2) := by
        funext n
        exact G.maskFinkActionVector_apply_of_not_mem P _
          p.1 p.2.1 p.2.2 hpP
      rw [heq]
      exact horiginal
    exact tendsto_nhds_unique (hlossCoord p) hmasked
  refine ⟨P, φ, R, hPS, hφ, hzφ, hKφ,
    hRnonneg, hRsupport, ?_⟩
  intro p hpP
  have hlossOriginal : Tendsto (fun n =>
      G.finkProjectiveLossVector (β (φ n)) W K (z (φ n))
        p.1 p.2.1 p.2.2) atTop (nhds (R p.1 p.2.1 p.2.2)) := by
    have heq : (fun n => G.maskFinkActionVector P
        (G.finkProjectiveLossVector (β (φ n)) W K (z (φ n)))
          p.1 p.2.1 p.2.2) =
        (fun n => G.finkProjectiveLossVector
          (β (φ n)) W K (z (φ n)) p.1 p.2.1 p.2.2) := by
      funext n
      exact G.maskFinkActionVector_apply_of_not_mem P _
        p.1 p.2.1 p.2.2 hpP
    rw [← heq]
    exact hlossCoord p
  have hpositivePart : Tendsto (fun n => max
      (G.finkProjectiveGainVector (β (φ n)) W K (z (φ n))
        p.1 p.2.1 p.2.2) 0) atTop (nhds 0) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    have hhalf : 0 < ε / 2 := by linarith
    have hupper := G.eventually_all_finkProjectiveGainVector_le_of_boundary
      hβ0 hβ1 hpay hz hfix W K hKlim hKnorm hhalf
    have hupperφ := hφ.tendsto_atTop.eventually hupper
    apply Filter.eventually_atTop.mp
    filter_upwards [hupperφ] with n hn
    have hnonneg : 0 ≤ max
        (G.finkProjectiveGainVector (β (φ n)) W K (z (φ n))
          p.1 p.2.1 p.2.2) 0 := le_max_right _ _
    have hle : max
        (G.finkProjectiveGainVector (β (φ n)) W K (z (φ n))
          p.1 p.2.1 p.2.2) 0 ≤ ε / 2 := by
      exact max_le (hn p.1 p.2.1 p.2.2) hhalf.le
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
    linarith
  have hdiff := hpositivePart.sub hlossOriginal
  have hdiff' : Tendsto (fun n => max
      (G.finkProjectiveGainVector (β (φ n)) W K (z (φ n))
        p.1 p.2.1 p.2.2) 0 -
      G.finkProjectiveLossVector (β (φ n)) W K (z (φ n))
        p.1 p.2.1 p.2.2) atTop
      (nhds (-R p.1 p.2.1 p.2.2)) := by
    simpa only [zero_sub] using hdiff
  apply hdiff'.congr'
  apply Filter.Eventually.of_forall
  intro n
  unfold finkProjectiveLossVector
  exact max_zero_sub_max_neg_zero_eq_self _

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

/-- At a boundary node, the summed positive pure gains of the corrected
reference are exactly the correction scale times those of the next reference. -/
theorem finkPositiveContinuationGainSum_add_correction
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (a : ℝ) (J R K : G.State → Payoff ι) {U : ℝ}
    (z : G.finkDomain U) (ha : a ≠ 0)
    (hscale : 0 ≤ G.finkReferenceCorrectionScale a J) :
    G.finkPositiveContinuationGainSum
        (R + G.finkReferenceCorrection a J K) z =
      G.finkReferenceCorrectionScale a J *
        G.finkPositiveContinuationGainSum
          (G.finkNextReferenceVector a J R K) z := by
  classical
  unfold finkPositiveContinuationGainSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hgain := G.finkContinuationGain_add_correction
    a J R K z ha p.1 p.2.1 p.2.2
  rw [G.finkNextDeviationGain_eq_continuationGain] at hgain
  rw [hgain]
  let x := G.finkContinuationGain
    (G.finkNextReferenceVector a J R K) z p.1 p.2.1 p.2.2
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx, max_eq_left (mul_nonneg hscale hx)]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [max_eq_right hx',
      max_eq_right (mul_nonpos_of_nonneg_of_nonpos hscale hx')]
    ring

/-- Consequently the complete same-point hold error factors through one
boundary by the same scalar.  This is the exact hierarchy-side rate identity
needed by the block-length-weighted calendar condition. -/
theorem finkCorrectedReferenceHoldError_eq_scale_mul
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (a : ℝ) (J R K : G.State → Payoff ι) {U : ℝ}
    (z : G.finkDomain U) (ha : a ≠ 0)
    (hscale : 0 ≤ G.finkReferenceCorrectionScale a J) :
    ‖G.finkContinuationResidualVector
        (R + G.finkReferenceCorrection a J K) z‖ +
      G.finkPositiveContinuationGainSum
        (R + G.finkReferenceCorrection a J K) z =
      G.finkReferenceCorrectionScale a J *
        (‖G.finkContinuationResidualVector
            (G.finkNextReferenceVector a J R K) z‖ +
          G.finkPositiveContinuationGainSum
            (G.finkNextReferenceVector a J R K) z) := by
  have hresidual := G.finkContinuationResidualVector_add_correction
    a J R K z ha
  rw [G.finkNextPoissonRemainderVector_eq_continuationResidualVector]
    at hresidual
  have hresidualNorm :
      ‖G.finkContinuationResidualVector
          (R + G.finkReferenceCorrection a J K) z‖ =
        G.finkReferenceCorrectionScale a J *
          ‖G.finkContinuationResidualVector
            (G.finkNextReferenceVector a J R K) z‖ := by
    rw [hresidual, norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale]
  rw [hresidualNorm,
    G.finkPositiveContinuationGainSum_add_correction
      a J R K z ha hscale]
  ring

/-- Uniform asymptotic nonpositivity of the finitely many pure gains is
equivalent to vanishing of their summed positive parts in the direction used
below. -/
theorem tendsto_finkPositiveContinuationGainSum_zero
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (C : ℕ → G.State → Payoff ι) {U : ℝ}
    (z : ℕ → G.finkDomain U)
    (hgain : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ s who (d : G.Act who),
        G.finkContinuationGain (C n) (z n) s who d ≤ ε) :
    Tendsto (fun n => G.finkPositiveContinuationGainSum (C n) (z n))
      atTop (nhds 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  let card : ℝ := Fintype.card G.FinkPureActionIndex
  let δ : ℝ := ε / (card + 1)
  have hcard0 : 0 ≤ card := by
    dsimp only [card]
    positivity
  have hδ : 0 < δ := div_pos hε (by linarith)
  apply Filter.eventually_atTop.mp
  filter_upwards [hgain δ hδ] with n hn
  have hsum0 : 0 ≤ G.finkPositiveContinuationGainSum (C n) (z n) := by
    unfold finkPositiveContinuationGainSum
    exact Finset.sum_nonneg fun p _ => le_max_right _ _
  have hsum : G.finkPositiveContinuationGainSum (C n) (z n) ≤
      Fintype.card G.FinkPureActionIndex * δ := by
    unfold finkPositiveContinuationGainSum
    calc
      ∑ p : G.FinkPureActionIndex,
          max (G.finkContinuationGain (C n) (z n)
            p.1 p.2.1 p.2.2) 0 ≤
          ∑ _p : G.FinkPureActionIndex, δ := by
        apply Finset.sum_le_sum
        intro p hp
        exact max_le (hn p.1 p.2.1 p.2.2) hδ.le
      _ = Fintype.card G.FinkPureActionIndex * δ := by
        simp
  have hcardδ : Fintype.card G.FinkPureActionIndex * δ < ε := by
    change card * (ε / (card + 1)) < ε
    rw [show card * (ε / (card + 1)) =
      (card * ε) / (card + 1) by ring]
    rw [div_lt_iff₀ (by linarith : 0 < card + 1)]
    nlinarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hsum0]
  exact hsum.trans_lt hcardδ

/-- Along a boundary family, corrected hold error is little-o of its
correction scale: after division by that scale it is exactly the next-layer
hold error, which vanishes by the verified hierarchy certificates. -/
theorem tendsto_finkCorrectedReferenceHoldError_div_scale_zero
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (a : ℕ → ℝ) (J R : ℕ → G.State → Payoff ι)
    (K : G.State → Payoff ι) {U : ℝ} (z : ℕ → G.finkDomain U)
    (ha : ∀ n, a n ≠ 0)
    (hscalePos : ∀ n, 0 < G.finkReferenceCorrectionScale (a n) (J n))
    (hnextResidual : Tendsto (fun n =>
      G.finkContinuationResidualVector
        (G.finkNextReferenceVector (a n) (J n) (R n) K) (z n))
      atTop (nhds 0))
    (hnextGain : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ s who (d : G.Act who),
        G.finkContinuationGain
          (G.finkNextReferenceVector (a n) (J n) (R n) K)
          (z n) s who d ≤ ε) :
    Tendsto (fun n =>
      (‖G.finkContinuationResidualVector
          (R n + G.finkReferenceCorrection (a n) (J n) K) (z n)‖ +
        G.finkPositiveContinuationGainSum
          (R n + G.finkReferenceCorrection (a n) (J n) K) (z n)) /
      G.finkReferenceCorrectionScale (a n) (J n))
      atTop (nhds 0) := by
  have hresidualNorm : Tendsto (fun n =>
      ‖G.finkContinuationResidualVector
        (G.finkNextReferenceVector (a n) (J n) (R n) K) (z n)‖)
      atTop (nhds 0) := by
    simpa only [norm_zero] using hnextResidual.norm
  have hgainSum := G.tendsto_finkPositiveContinuationGainSum_zero
    (fun n => G.finkNextReferenceVector (a n) (J n) (R n) K)
    z hnextGain
  have hnextHold := hresidualNorm.add hgainSum
  have hnextHoldZero : Tendsto (fun n =>
      ‖G.finkContinuationResidualVector
        (G.finkNextReferenceVector (a n) (J n) (R n) K) (z n)‖ +
      G.finkPositiveContinuationGainSum
        (G.finkNextReferenceVector (a n) (J n) (R n) K) (z n))
      atTop (nhds 0) := by
    simpa using hnextHold
  apply hnextHoldZero.congr'
  exact Filter.Eventually.of_forall fun n => by
    have hfactor := G.finkCorrectedReferenceHoldError_eq_scale_mul
      (a n) (J n) (R n) K (z n) (ha n) (hscalePos n).le
    simp only
    rw [hfactor]
    field_simp [ne_of_gt (hscalePos n)]

/-- Error paid on every calendar stage that holds one corrected Fink point
fixed.  Unlike correction motion, this term is repeated during waits. -/
noncomputable def finkCorrectedTargetHoldError
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (W : G.State → Payoff ι) (R : ℕ → G.State → Payoff ι)
    {U : ℝ} (z : ℕ → G.finkDomain U) (t : ℕ) : ℝ :=
  ‖G.finkContinuationResidualVector (W + R t) (z t)‖ +
    G.finkPositiveContinuationGainSum (W + R t) (z t)

theorem finkCorrectedTargetHoldError_nonneg
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (W : G.State → Payoff ι) (R : ℕ → G.State → Payoff ι)
    {U : ℝ} (z : ℕ → G.finkDomain U) (t : ℕ) :
    0 ≤ G.finkCorrectedTargetHoldError W R z t := by
  unfold finkCorrectedTargetHoldError finkPositiveContinuationGainSum
  positivity

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

theorem finkCorrectedTargetStepError_eq_hold_add_motion
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (W : G.State → Payoff ι) (R : ℕ → G.State → Payoff ι)
    {U : ℝ} (z : ℕ → G.finkDomain U) (t : ℕ) :
    G.finkCorrectedTargetStepError W R z t =
      G.finkCorrectedTargetHoldError W R z t +
        ‖R (t + 1) - R t‖ := by
  rfl

theorem finkCorrectedTargetStepError_nonneg
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (W : G.State → Payoff ι) (R : ℕ → G.State → Payoff ι)
    {U : ℝ} (z : ℕ → G.finkDomain U) (t : ℕ) :
    0 ≤ G.finkCorrectedTargetStepError W R z t := by
  unfold finkCorrectedTargetStepError finkPositiveContinuationGainSum
  positivity

/-- If corrections, same-index residuals, and positive deviation gains all
vanish, then the actual adjacent corrected-target step error vanishes.  This
is the precise non-summable input delivered by the hierarchy. -/
theorem tendsto_finkCorrectedTargetStepError_zero
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (W : G.State → Payoff ι) (R : ℕ → G.State → Payoff ι)
    {U : ℝ} (z : ℕ → G.finkDomain U)
    (hR : Tendsto R atTop (nhds 0))
    (hresidual : Tendsto (fun n => G.finkContinuationResidualVector
      (W + R n) (z n)) atTop (nhds 0))
    (hgain : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ s who (d : G.Act who),
        G.finkContinuationGain (W + R n) (z n) s who d ≤ ε) :
    Tendsto (fun n => G.finkCorrectedTargetStepError W R z n)
      atTop (nhds 0) := by
  have hresidualNorm : Tendsto (fun n =>
      ‖G.finkContinuationResidualVector (W + R n) (z n)‖)
      atTop (nhds 0) := by
    simpa only [norm_zero] using hresidual.norm
  have hgainSum := G.tendsto_finkPositiveContinuationGainSum_zero
    (fun n => W + R n) z hgain
  have hRsucc : Tendsto (fun n => R (n + 1)) atTop (nhds 0) :=
    hR.comp (tendsto_add_atTop_nat 1)
  have hmove : Tendsto (fun n => ‖R (n + 1) - R n‖)
      atTop (nhds 0) := by
    simpa using (hRsucc.sub hR).norm
  simpa only [finkCorrectedTargetStepError, zero_add] using
    (hresidualNorm.add hgainSum).add hmove

/-- A harmonic and pure-deviation excessive limiting profile has vanishing
zero-correction step error along every convergent Fink-domain sequence.  This
is the analytic input needed by the interior annealing branch. -/
theorem tendsto_zeroCorrectionStepError_of_harmonic_excessive_limit
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
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who) :
    Tendsto (fun n => G.finkCorrectedTargetStepError W
      (fun _ => 0) z n) atTop (nhds 0) := by
  have hR : Tendsto (fun _ : ℕ => (0 : G.State → Payoff ι))
      atTop (nhds 0) := tendsto_const_nhds
  have hresidual : Tendsto (fun n =>
      G.finkContinuationResidualVector
        (W + (fun _ => 0) n) (z n)) atTop (nhds 0) := by
    apply tendsto_pi_nhds.2
    intro s
    apply tendsto_pi_nhds.2
    intro who
    have ht := G.tendsto_finkProfile_continuation hz
      (fun s' => W s' who) s
    rw [← hharmonic s who] at ht
    have ht' := ht.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => W s who)
        atTop (nhds (W s who)))
    simpa only [finkContinuationResidualVector, finkContinuationResidual,
      finkContinuationEU, Pi.add_apply, Pi.zero_apply, add_zero, sub_self]
      using ht'
  have hgain : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ s who (d : G.Act who),
        G.finkContinuationGain (W + (fun _ => 0) n) (z n)
          s who d ≤ ε := by
    intro ε hε
    have hclose := G.eventually_finkProfile_harmonic_excessive_close
      hz W hharmonic hexcessive (show 0 < ε / 2 by linarith)
    filter_upwards [hclose] with n hn
    intro s who d
    have hon := hn.1 s who
    have hdev := hn.2 s who (PMF.pure d)
    rw [abs_le] at hon
    unfold finkContinuationGain
    simp only [Pi.add_apply, Pi.zero_apply, add_zero]
    linarith
  exact G.tendsto_finkCorrectedTargetStepError_zero W
    (fun _ => 0) z hR hresidual hgain

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

/-- The asymptotic reference certificates admit a fast subsequence on which
the actual adjacent corrected-target errors are summable with arbitrarily
small total mass.  This proves the drift half of calendar selection without
making any claim about the scaled-bias switching cost of that subsequence. -/
theorem exists_strictMono_summable_finkCorrectedTargetStepError_subsequence
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (W : G.State → Payoff ι) (R : ℕ → G.State → Payoff ι)
    {U : ℝ} (z : ℕ → G.finkDomain U)
    (hR : Tendsto R atTop (nhds 0))
    (hresidual : Tendsto (fun n => G.finkContinuationResidualVector
      (W + R n) (z n)) atTop (nhds 0))
    (hgain : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ s who (d : G.Act who),
        G.finkContinuationGain (W + R n) (z n) s who d ≤ ε)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ‖R (ψ 0)‖ ≤ ε ∧
      Summable (fun n => G.finkCorrectedTargetStepError W
        (R ∘ ψ) (z ∘ ψ) n) ∧
      ∑' n, G.finkCorrectedTargetStepError W
        (R ∘ ψ) (z ∘ ψ) n ≤ ε := by
  let δ : ℕ → ℝ := fun n => ε / 8 / 2 ^ n
  have hδpos : ∀ n, 0 < δ n := fun n => by
    dsimp only [δ]
    positivity
  have hRnorm : Tendsto (fun n => ‖R n‖) atTop (nhds 0) := by
    simpa only [norm_zero] using hR.norm
  have hresidualNorm : Tendsto (fun n =>
      ‖G.finkContinuationResidualVector (W + R n) (z n)‖)
      atTop (nhds 0) := by
    simpa only [norm_zero] using hresidual.norm
  have hgainSum := G.tendsto_finkPositiveContinuationGainSum_zero
    (fun n => W + R n) z hgain
  let P : ℕ → ℕ → Prop := fun n k =>
    ‖R k‖ ≤ δ n ∧
      ‖G.finkContinuationResidualVector (W + R k) (z k)‖ ≤ δ n ∧
      G.finkPositiveContinuationGainSum (W + R k) (z k) ≤ δ n
  have hev : ∀ n, ∀ᶠ k in atTop, P n k := by
    intro n
    have hRsmall : ∀ᶠ k in atTop, ‖R k‖ ≤ δ n :=
      (hRnorm.eventually (Iio_mem_nhds (hδpos n))).mono
        fun _ hk => hk.le
    have hressmall : ∀ᶠ k in atTop,
        ‖G.finkContinuationResidualVector (W + R k) (z k)‖ ≤ δ n :=
      (hresidualNorm.eventually (Iio_mem_nhds (hδpos n))).mono
        fun _ hk => hk.le
    have hgainsmall : ∀ᶠ k in atTop,
        G.finkPositiveContinuationGainSum (W + R k) (z k) ≤ δ n :=
      (hgainSum.eventually (Iio_mem_nhds (hδpos n))).mono
        fun _ hk => hk.le
    filter_upwards [hRsmall, hressmall, hgainsmall] with k hkR hkres hkgain
    exact ⟨hkR, hkres, hkgain⟩
  have hexN : ∀ n, ∃ N, ∀ k, N ≤ k → P n k := fun n =>
    Filter.eventually_atTop.mp (hev n)
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
  have hψstep : ∀ n, ψ n < ψ (n + 1) := by
    intro n
    rw [show ψ (n + 1) = max (N (n + 1)) (ψ n + 1) by simp [ψ]]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  have hP : ∀ n, P n (ψ n) := fun n => hN n (ψ n) (hNle n)
  have hδmono : ∀ n, δ (n + 1) ≤ δ n := by
    intro n
    dsimp only [δ]
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (n + 1))
      (by positivity : (0 : ℝ) < 2 ^ n)).2
    rw [pow_succ]
    nlinarith [hε, pow_pos (by norm_num : (0 : ℝ) < 2) n]
  have herror : ∀ n, G.finkCorrectedTargetStepError W
      (R ∘ ψ) (z ∘ ψ) n ≤ ε / 2 / 2 ^ n := by
    intro n
    have hmove : ‖R (ψ (n + 1)) - R (ψ n)‖ ≤
        δ (n + 1) + δ n := by
      exact (norm_sub_le _ _).trans
        (add_le_add (hP (n + 1)).1 (hP n).1)
    calc
      G.finkCorrectedTargetStepError W (R ∘ ψ) (z ∘ ψ) n =
          ‖G.finkContinuationResidualVector
            (W + R (ψ n)) (z (ψ n))‖ +
          G.finkPositiveContinuationGainSum
            (W + R (ψ n)) (z (ψ n)) +
          ‖R (ψ (n + 1)) - R (ψ n)‖ := by
        rfl
      _ ≤ δ n + δ n + (δ (n + 1) + δ n) := by
        exact add_le_add (add_le_add (hP n).2.1 (hP n).2.2) hmove
      _ ≤ 4 * δ n := by linarith [hδmono n]
      _ = ε / 2 / 2 ^ n := by
        dsimp only [δ]
        ring
  have hsummable : Summable (fun n => G.finkCorrectedTargetStepError W
      (R ∘ ψ) (z ∘ ψ) n) := by
    apply Summable.of_nonneg_of_le
    · exact fun n => G.finkCorrectedTargetStepError_nonneg
        W (R ∘ ψ) (z ∘ ψ) n
    · exact herror
    · exact summable_geometric_two' ε
  have htotal : ∑' n, G.finkCorrectedTargetStepError W
      (R ∘ ψ) (z ∘ ψ) n ≤ ε := by
    calc
      ∑' n, G.finkCorrectedTargetStepError W
          (R ∘ ψ) (z ∘ ψ) n ≤
          ∑' n : ℕ, ε / 2 / 2 ^ n :=
        hsummable.tsum_le_tsum herror (summable_geometric_two' ε)
      _ = ε := tsum_geometric_two' ε
  have hRzero : ‖R (ψ 0)‖ ≤ ε := by
    calc
      ‖R (ψ 0)‖ ≤ δ 0 := (hP 0).1
      _ ≤ ε := by
        dsimp only [δ]
        norm_num
        linarith
  exact ⟨ψ, strictMono_nat_of_lt_succ hψstep, hRzero,
    hsummable, htotal⟩

/-- The fast extraction can simultaneously make any additional nonnegative
defect tending to zero summable.  Applied to the next-reference hold error,
this supplies both small series required by the root rate-compatible calendar
criterion on one common subsequence. -/
theorem exists_strictMono_summable_finkCorrectedTargetStepError_and_aux_subsequence
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (W : G.State → Payoff ι) (R : ℕ → G.State → Payoff ι)
    {U : ℝ} (z : ℕ → G.finkDomain U)
    (hR : Tendsto R atTop (nhds 0))
    (hresidual : Tendsto (fun n => G.finkContinuationResidualVector
      (W + R n) (z n)) atTop (nhds 0))
    (hgain : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ s who (d : G.Act who),
        G.finkContinuationGain (W + R n) (z n) s who d ≤ ε)
    (aux : ℕ → ℝ) (haux0 : ∀ n, 0 ≤ aux n)
    (haux : Tendsto aux atTop (nhds 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ‖R (ψ 0)‖ ≤ ε ∧
      Summable (fun n => G.finkCorrectedTargetStepError W
        (R ∘ ψ) (z ∘ ψ) n) ∧
      ∑' n, G.finkCorrectedTargetStepError W
        (R ∘ ψ) (z ∘ ψ) n ≤ ε ∧
      Summable (aux ∘ ψ) ∧ ∑' n, aux (ψ n) ≤ ε := by
  let δ : ℕ → ℝ := fun n => ε / 8 / 2 ^ n
  have hδpos : ∀ n, 0 < δ n := fun n => by
    dsimp only [δ]
    positivity
  have hRnorm : Tendsto (fun n => ‖R n‖) atTop (nhds 0) := by
    simpa only [norm_zero] using hR.norm
  have hresidualNorm : Tendsto (fun n =>
      ‖G.finkContinuationResidualVector (W + R n) (z n)‖)
      atTop (nhds 0) := by
    simpa only [norm_zero] using hresidual.norm
  have hgainSum := G.tendsto_finkPositiveContinuationGainSum_zero
    (fun n => W + R n) z hgain
  let P : ℕ → ℕ → Prop := fun n k =>
    ‖R k‖ ≤ δ n ∧
      ‖G.finkContinuationResidualVector (W + R k) (z k)‖ ≤ δ n ∧
      G.finkPositiveContinuationGainSum (W + R k) (z k) ≤ δ n ∧
      aux k ≤ δ n
  have hev : ∀ n, ∀ᶠ k in atTop, P n k := by
    intro n
    have hRsmall : ∀ᶠ k in atTop, ‖R k‖ ≤ δ n :=
      (hRnorm.eventually (Iio_mem_nhds (hδpos n))).mono
        fun _ hk => hk.le
    have hressmall : ∀ᶠ k in atTop,
        ‖G.finkContinuationResidualVector (W + R k) (z k)‖ ≤ δ n :=
      (hresidualNorm.eventually (Iio_mem_nhds (hδpos n))).mono
        fun _ hk => hk.le
    have hgainsmall : ∀ᶠ k in atTop,
        G.finkPositiveContinuationGainSum (W + R k) (z k) ≤ δ n :=
      (hgainSum.eventually (Iio_mem_nhds (hδpos n))).mono
        fun _ hk => hk.le
    have hauxsmall : ∀ᶠ k in atTop, aux k ≤ δ n :=
      (haux.eventually (Iio_mem_nhds (hδpos n))).mono
        fun _ hk => hk.le
    filter_upwards [hRsmall, hressmall, hgainsmall, hauxsmall]
      with k hkR hkres hkgain hkaux
    exact ⟨hkR, hkres, hkgain, hkaux⟩
  have hexN : ∀ n, ∃ N, ∀ k, N ≤ k → P n k := fun n =>
    Filter.eventually_atTop.mp (hev n)
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
  have hψstep : ∀ n, ψ n < ψ (n + 1) := by
    intro n
    rw [show ψ (n + 1) = max (N (n + 1)) (ψ n + 1) by simp [ψ]]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  have hP : ∀ n, P n (ψ n) := fun n => hN n (ψ n) (hNle n)
  have hδmono : ∀ n, δ (n + 1) ≤ δ n := by
    intro n
    dsimp only [δ]
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (n + 1))
      (by positivity : (0 : ℝ) < 2 ^ n)).2
    rw [pow_succ]
    nlinarith [hε, pow_pos (by norm_num : (0 : ℝ) < 2) n]
  have herror : ∀ n, G.finkCorrectedTargetStepError W
      (R ∘ ψ) (z ∘ ψ) n ≤ ε / 2 / 2 ^ n := by
    intro n
    have hmove : ‖R (ψ (n + 1)) - R (ψ n)‖ ≤
        δ (n + 1) + δ n := by
      exact (norm_sub_le _ _).trans
        (add_le_add (hP (n + 1)).1 (hP n).1)
    calc
      G.finkCorrectedTargetStepError W (R ∘ ψ) (z ∘ ψ) n =
          ‖G.finkContinuationResidualVector
            (W + R (ψ n)) (z (ψ n))‖ +
          G.finkPositiveContinuationGainSum
            (W + R (ψ n)) (z (ψ n)) +
          ‖R (ψ (n + 1)) - R (ψ n)‖ := by
        rfl
      _ ≤ δ n + δ n + (δ (n + 1) + δ n) := by
        exact add_le_add
          (add_le_add (hP n).2.1 (hP n).2.2.1) hmove
      _ ≤ 4 * δ n := by linarith [hδmono n]
      _ = ε / 2 / 2 ^ n := by
        dsimp only [δ]
        ring
  have hfast : Summable (fun n => G.finkCorrectedTargetStepError W
      (R ∘ ψ) (z ∘ ψ) n) := by
    apply Summable.of_nonneg_of_le
    · exact fun n => G.finkCorrectedTargetStepError_nonneg
        W (R ∘ ψ) (z ∘ ψ) n
    · exact herror
    · exact summable_geometric_two' ε
  have hfastTotal : ∑' n, G.finkCorrectedTargetStepError W
      (R ∘ ψ) (z ∘ ψ) n ≤ ε := by
    calc
      _ ≤ ∑' n : ℕ, ε / 2 / 2 ^ n :=
        hfast.tsum_le_tsum herror (summable_geometric_two' ε)
      _ = ε := tsum_geometric_two' ε
  have hauxBound : ∀ n, aux (ψ n) ≤ ε / 2 / 2 ^ n := by
    intro n
    calc
      aux (ψ n) ≤ δ n := (hP n).2.2.2
      _ ≤ ε / 2 / 2 ^ n := by
        dsimp only [δ]
        have hpow : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
        exact div_le_div_of_nonneg_right (by linarith) hpow.le
  have hauxSum : Summable (aux ∘ ψ) := by
    apply Summable.of_nonneg_of_le
    · exact fun n => haux0 (ψ n)
    · simpa only [Function.comp_apply] using hauxBound
    · exact summable_geometric_two' ε
  have hauxTotal : ∑' n, aux (ψ n) ≤ ε := by
    calc
      _ ≤ ∑' n : ℕ, ε / 2 / 2 ^ n :=
        hauxSum.tsum_le_tsum hauxBound (summable_geometric_two' ε)
      _ = ε := tsum_geometric_two' ε
  have hRzero : ‖R (ψ 0)‖ ≤ ε := by
    calc
      ‖R (ψ 0)‖ ≤ δ 0 := (hP 0).1
      _ ≤ ε := by
        dsimp only [δ]
        norm_num
        linarith
  exact ⟨ψ, strictMono_nat_of_lt_succ hψstep, hRzero,
    hfast, hfastTotal, hauxSum, hauxTotal⟩

/-- A defect tending to zero can be thinned fast enough to absorb any
prescribed nonnegative weight on the *new subsequence index*.  The weight may
be unbounded; choosing the subsequence point at stage `n` after seeing `D n`
makes the weighted series geometric. -/
theorem exists_strictMono_summable_weighted_subsequence
    (aux D : ℕ → ℝ) (haux0 : ∀ n, 0 ≤ aux n)
    (haux : Tendsto aux atTop (nhds 0)) (hD0 : ∀ n, 0 ≤ D n) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Summable (fun n => D n * aux (ψ n)) := by
  let δ : ℕ → ℝ := fun n => (1 / (D n + 1)) / (2 : ℝ) ^ n
  have hδpos : ∀ n, 0 < δ n := fun n => by
    dsimp only [δ]
    exact div_pos (div_pos zero_lt_one (by linarith [hD0 n]))
      (pow_pos (by norm_num) n)
  have hev : ∀ n, ∀ᶠ k in atTop, aux k ≤ δ n := by
    intro n
    exact (haux.eventually (Iio_mem_nhds (hδpos n))).mono
      fun _ hk => hk.le
  have hexN : ∀ n, ∃ N, ∀ k, N ≤ k → aux k ≤ δ n := fun n =>
    Filter.eventually_atTop.mp (hev n)
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
  have hψstep : ∀ n, ψ n < ψ (n + 1) := by
    intro n
    rw [show ψ (n + 1) = max (N (n + 1)) (ψ n + 1) by simp [ψ]]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  have hauxBound : ∀ n, aux (ψ n) ≤ δ n := fun n =>
    hN n (ψ n) (hNle n)
  have hweighted : ∀ n, D n * aux (ψ n) ≤
      (1 : ℝ) / (2 : ℝ) ^ n := by
    intro n
    calc
      D n * aux (ψ n) ≤ D n * δ n :=
        mul_le_mul_of_nonneg_left (hauxBound n) (hD0 n)
      _ = (D n / (D n + 1)) / (2 : ℝ) ^ n := by
        dsimp only [δ]
        ring
      _ ≤ (1 : ℝ) / (2 : ℝ) ^ n := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact (div_le_one (by linarith [hD0 n])).2 (by linarith)
  have hgeom : Summable (fun n : ℕ => (1 : ℝ) / (2 : ℝ) ^ n) := by
    convert summable_geometric_two' (2 : ℝ) using 1
    funext n
    norm_num
  have hsum : Summable (fun n => D n * aux (ψ n)) := by
    apply Summable.of_nonneg_of_le
    · exact fun n => mul_nonneg (hD0 n) (haux0 (ψ n))
    · exact hweighted
    · exact hgeom
  exact ⟨ψ, strictMono_nat_of_lt_succ hψstep, hsum⟩

/-- Zero-correction specialization for an interior hierarchy branch.  A
vanishing root step error can be thinned so that both the ordinary step series
and the series weighted by any prescribed nonnegative block envelope are
summable on one strict subsequence. -/
theorem exists_strictMono_summable_zeroCorrectionStepError_weighted
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (W : G.State → Payoff ι) {U : ℝ} (z : ℕ → G.finkDomain U)
    (D : ℕ → ℝ) (hD0 : ∀ n, 0 ≤ D n)
    (hstep0 : Tendsto (fun n => G.finkCorrectedTargetStepError W
      (fun _ => 0) z n) atTop (nhds 0)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Summable (fun n => G.finkCorrectedTargetStepError W
        ((fun _ => 0) ∘ ψ) (z ∘ ψ) n) ∧
      Summable (fun n => D n * G.finkCorrectedTargetStepError W
        ((fun _ => 0) ∘ ψ) (z ∘ ψ) n) := by
  let e : ℕ → ℝ := fun n => G.finkCorrectedTargetStepError W
    (fun _ => 0) z n
  let E : ℕ → ℝ := fun n => D n + 1
  have he0 : ∀ n, 0 ≤ e n := fun n =>
    G.finkCorrectedTargetStepError_nonneg W (fun _ => 0) z n
  have hE0 : ∀ n, 0 ≤ E n := fun n => by dsimp only [E]; linarith [hD0 n]
  obtain ⟨ψ, hψ, hweighted⟩ :=
    exists_strictMono_summable_weighted_subsequence e E he0
      (by simpa only [e] using hstep0) hE0
  have heLe : ∀ n, e (ψ n) ≤ E n * e (ψ n) := by
    intro n
    have := mul_le_mul_of_nonneg_right (show 1 ≤ E n by
      dsimp only [E]; linarith [hD0 n]) (he0 (ψ n))
    simpa only [one_mul] using this
  have hDLe : ∀ n, D n * e (ψ n) ≤ E n * e (ψ n) := by
    intro n
    exact mul_le_mul_of_nonneg_right (by dsimp only [E]; linarith)
      (he0 (ψ n))
  have heSum : Summable (fun n => e (ψ n)) :=
    Summable.of_nonneg_of_le (fun n => he0 (ψ n)) heLe hweighted
  have hDSum : Summable (fun n => D n * e (ψ n)) :=
    Summable.of_nonneg_of_le
      (fun n => mul_nonneg (hD0 n) (he0 (ψ n))) hDLe hweighted
  refine ⟨ψ, hψ, ?_, ?_⟩
  · simpa only [e, finkCorrectedTargetStepError, Function.comp_def,
      sub_self, norm_zero, add_zero] using heSum
  · simpa only [e, finkCorrectedTargetStepError, Function.comp_def,
      sub_self, norm_zero, add_zero] using hDSum

/-- An eventual pointwise majorant is enough to transfer summability of a
weighted nonnegative series.  Finitely many exceptional initial indices are
absorbed by shifting the series. -/
theorem summable_mul_of_eventually_le_weight
    (f L D : ℕ → ℝ) (hf0 : ∀ n, 0 ≤ f n) (hL0 : ∀ n, 0 ≤ L n)
    (hweighted : Summable (fun n => D n * f n))
    (hle : ∀ᶠ n in atTop, L n ≤ D n) :
    Summable (fun n => L n * f n) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hle
  apply (summable_nat_add_iff N).mp
  refine Summable.of_nonneg_of_le
    (f := fun n => D (n + N) * f (n + N)) ?_ ?_ ?_
  · exact fun n => mul_nonneg (hL0 (n + N)) (hf0 (n + N))
  · intro n
    exact mul_le_mul_of_nonneg_right
      (hN (n + N) (Nat.le_add_left N n)) (hf0 (n + N))
  · exact (summable_nat_add_iff N).mpr hweighted

/-- A long correction jump costs no more than the variation along all crossed
adjacent edges. -/
theorem norm_sub_le_sum_Ico_norm_sub
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    (R : ℕ → G.State → Payoff ι) {m n : ℕ} (hmn : m ≤ n) :
    ‖R n - R m‖ ≤
      ∑ k ∈ Finset.Ico m n, ‖R (k + 1) - R k‖ := by
  have htel : ∑ k ∈ Finset.Ico m n, (R (k + 1) - R k) =
      R n - R m := by
    rw [Finset.sum_Ico_eq_sub _ hmn,
      Finset.sum_range_sub, Finset.sum_range_sub]
    abel
  rw [← htel]
  exact norm_sum_le _ _

/-- Successive jumps of a strict subsequence use disjoint intervals of the
original correction path. -/
theorem sum_range_norm_sub_strictMono_le_sum_Ico
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    (R : ℕ → G.State → Payoff ι) (θ : ℕ → ℕ) (hθ : StrictMono θ)
    (N : ℕ) :
    ∑ k ∈ Finset.range N, ‖R (θ (k + 1)) - R (θ k)‖ ≤
      ∑ j ∈ Finset.Ico (θ 0) (θ N), ‖R (j + 1) - R j‖ := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      calc
        (∑ k ∈ Finset.range N, ‖R (θ (k + 1)) - R (θ k)‖) +
            ‖R (θ (N + 1)) - R (θ N)‖ ≤
          (∑ j ∈ Finset.Ico (θ 0) (θ N), ‖R (j + 1) - R j‖) +
            ∑ j ∈ Finset.Ico (θ N) (θ (N + 1)),
              ‖R (j + 1) - R j‖ := by
          exact add_le_add ih
            (norm_sub_le_sum_Ico_norm_sub G R
              (hθ.monotone (Nat.le_succ N)))
        _ = ∑ j ∈ Finset.Ico (θ 0) (θ (N + 1)),
              ‖R (j + 1) - R j‖ := by
          exact Finset.sum_Ico_consecutive _
            (hθ.monotone (Nat.zero_le N))
            (hθ.monotone (Nat.le_succ N))

/-- Corrected-target summability is stable under every further strict
subsequence, and its total mass cannot increase.  This permits the annealing
regularization to thin a fast hierarchy branch without reopening the drift
budget. -/
theorem summable_finkCorrectedTargetStepError_strictMono
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (W : G.State → Payoff ι) (R : ℕ → G.State → Payoff ι)
    {U : ℝ} (z : ℕ → G.finkDomain U)
    (hstep : Summable (fun n =>
      G.finkCorrectedTargetStepError W R z n))
    (θ : ℕ → ℕ) (hθ : StrictMono θ) :
    Summable (fun n => G.finkCorrectedTargetStepError W
        (R ∘ θ) (z ∘ θ) n) ∧
      ∑' n, G.finkCorrectedTargetStepError W
          (R ∘ θ) (z ∘ θ) n ≤
        ∑' n, G.finkCorrectedTargetStepError W R z n := by
  let hold : ℕ → ℝ := fun n => G.finkCorrectedTargetHoldError W R z n
  let move : ℕ → ℝ := fun n => ‖R (n + 1) - R n‖
  let jump : ℕ → ℝ := fun n => ‖R (θ (n + 1)) - R (θ n)‖
  have hhold0 : ∀ n, 0 ≤ hold n := fun n =>
    G.finkCorrectedTargetHoldError_nonneg W R z n
  have hmove0 : ∀ n, 0 ≤ move n := fun n => norm_nonneg _
  have hjump0 : ∀ n, 0 ≤ jump n := fun n => norm_nonneg _
  have hholdLe : ∀ n, hold n ≤
      G.finkCorrectedTargetStepError W R z n := by
    intro n
    rw [G.finkCorrectedTargetStepError_eq_hold_add_motion]
    exact le_add_of_nonneg_right (norm_nonneg _)
  have hmoveLe : ∀ n, move n ≤
      G.finkCorrectedTargetStepError W R z n := by
    intro n
    rw [G.finkCorrectedTargetStepError_eq_hold_add_motion]
    exact le_add_of_nonneg_left
      (G.finkCorrectedTargetHoldError_nonneg W R z n)
  have hhold : Summable hold :=
    Summable.of_nonneg_of_le hhold0 hholdLe hstep
  have hmove : Summable move :=
    Summable.of_nonneg_of_le hmove0 hmoveLe hstep
  have hholdSub : Summable (hold ∘ θ) :=
    hhold.comp_injective hθ.injective
  have hjumpPrefix : ∀ N, ∑ n ∈ Finset.range N, jump n ≤ ∑' n, move n := by
    intro N
    calc
      ∑ n ∈ Finset.range N, jump n ≤
          ∑ j ∈ Finset.Ico (θ 0) (θ N), move j := by
        simpa only [jump, move] using
          sum_range_norm_sub_strictMono_le_sum_Ico G R θ hθ N
      _ ≤ ∑' n, move n :=
        hmove.sum_le_tsum _ (fun n hn => hmove0 n)
  have hjump : Summable jump :=
    summable_of_sum_range_le hjump0 hjumpPrefix
  have hnewEq : (fun n => G.finkCorrectedTargetStepError W
      (R ∘ θ) (z ∘ θ) n) = fun n => (hold ∘ θ) n + jump n := by
    funext n
    rw [G.finkCorrectedTargetStepError_eq_hold_add_motion]
    rfl
  have hnew : Summable (fun n => G.finkCorrectedTargetStepError W
      (R ∘ θ) (z ∘ θ) n) := by
    rw [hnewEq]
    exact hholdSub.add hjump
  have hholdTotal : ∑' n, (hold ∘ θ) n ≤ ∑' n, hold n :=
    tsum_comp_le_tsum_of_inj hhold hhold0 hθ.injective
  have hjumpTotal : ∑' n, jump n ≤ ∑' n, move n :=
    Real.tsum_le_of_sum_range_le hjump0 hjumpPrefix
  have horiginalEq : (fun n => G.finkCorrectedTargetStepError W R z n) =
      fun n => hold n + move n := by
    funext n
    rw [G.finkCorrectedTargetStepError_eq_hold_add_motion]
  refine ⟨hnew, ?_⟩
  rw [hnewEq, hholdSub.tsum_add hjump, horiginalEq,
    hhold.tsum_add hmove]
  exact add_le_add hholdTotal hjumpTotal

/-- After a corrected branch has been made summable, it may be thinned again
to make any vanishing auxiliary defect summable against a prescribed
nonnegative index weight.  Corrected drift remains summable and its total
cannot increase. -/
theorem exists_strictMono_preserving_finkCorrectedError_weightingAux
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (W : G.State → Payoff ι) (R : ℕ → G.State → Payoff ι)
    {U : ℝ} (z : ℕ → G.finkDomain U)
    (hstep : Summable (fun n =>
      G.finkCorrectedTargetStepError W R z n))
    (aux D : ℕ → ℝ) (haux0 : ∀ n, 0 ≤ aux n)
    (haux : Tendsto aux atTop (nhds 0)) (hD0 : ∀ n, 0 ≤ D n) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Summable (fun n => G.finkCorrectedTargetStepError W
        (R ∘ ψ) (z ∘ ψ) n) ∧
      (∑' n, G.finkCorrectedTargetStepError W
          (R ∘ ψ) (z ∘ ψ) n) ≤
        ∑' n, G.finkCorrectedTargetStepError W R z n ∧
      Summable (fun n => D n * aux (ψ n)) := by
  obtain ⟨ψ, hψ, hweighted⟩ :=
    exists_strictMono_summable_weighted_subsequence aux D haux0 haux hD0
  have hpreserved :=
    G.summable_finkCorrectedTargetStepError_strictMono W R z hstep ψ hψ
  exact ⟨ψ, hψ, hpreserved.1, hpreserved.2, hweighted⟩

/-- Information-preserving form of the root correction dichotomy.  In the
boundary branch it retains the vanishing next-reference hold defect instead
of projecting it away after deriving the corrected root certificates. -/
theorem FinkVerifiedReferenceResolution.rootCorrection_and_nextHold_dichotomy
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {V J R : ℕ → G.State → Payoff ι}
    {a : ℕ → ℝ}
    (hresolution : G.FinkVerifiedReferenceResolution z V a J R)
    (ha : ∀ n, a n ≠ 0)
    (hscale0 : ∀ n, 0 ≤ G.finkReferenceCorrectionScale (a n) (J n))
    (hscale : Tendsto (fun n => G.finkReferenceCorrectionScale
      (a n) (J n)) atTop (nhds 0)) :
    (∃ (φ : ℕ → ℕ) (Jlim : G.State → Payoff ι),
      StrictMono φ ∧ Tendsto (J ∘ φ) atTop (nhds Jlim)) ∨
    ∃ (K : G.State → Payoff ι) (φ : ℕ → ℕ),
      StrictMono φ ∧ ‖K‖ = 1 ∧
      Tendsto (fun n => G.finkReferenceCorrection
        (a (φ n)) (J (φ n)) K) atTop (nhds 0) ∧
      Tendsto (fun n => G.finkContinuationResidualVector
        (R (φ n) + G.finkReferenceCorrection
          (a (φ n)) (J (φ n)) K) (z (φ n))) atTop (nhds 0) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        ∀ s who (d : G.Act who),
          G.finkContinuationGain
            (R (φ n) + G.finkReferenceCorrection
              (a (φ n)) (J (φ n)) K)
            (z (φ n)) s who d ≤ ε) ∧
      Tendsto (fun n =>
        ‖G.finkContinuationResidualVector
            (G.finkNextReferenceVector (a (φ n)) (J (φ n))
              (R (φ n)) K) (z (φ n))‖ +
          G.finkPositiveContinuationGainSum
            (G.finkNextReferenceVector (a (φ n)) (J (φ n))
              (R (φ n)) K) (z (φ n))) atTop (nhds 0) := by
  cases hresolution with
  | interior φ Jlim hφ hJlim =>
      exact Or.inl ⟨φ, Jlim, hφ, hJlim⟩
  | boundary K φ hφ hJlim hKnorm hnextResidual hnextGain tail =>
      right
      have hscaleφ : Tendsto (fun n => G.finkReferenceCorrectionScale
          (a (φ n)) (J (φ n))) atTop (nhds 0) := by
        simpa only [Function.comp_def] using
          hscale.comp hφ.tendsto_atTop
      have hcorrection : Tendsto (fun n => G.finkReferenceCorrection
          (a (φ n)) (J (φ n)) K) atTop (nhds 0) := by
        simpa only [finkReferenceCorrection, zero_smul] using
          hscaleφ.smul_const K
      have hresidual :=
        G.tendsto_finkContinuationResidualVector_add_correction_zero
          (fun n => a (φ n)) (fun n => J (φ n))
          (fun n => R (φ n)) K (fun n => z (φ n))
          (fun n => ha (φ n)) hscaleφ hnextResidual
      have hgain := G.eventually_finkContinuationGain_add_correction_le
        (fun n => a (φ n)) (fun n => J (φ n))
        (fun n => R (φ n)) K (fun n => z (φ n))
        (fun n => ha (φ n)) (fun n => hscale0 (φ n))
        hscaleφ hnextGain
      have hnextResidualNorm : Tendsto (fun n =>
          ‖G.finkContinuationResidualVector
            (G.finkNextReferenceVector (a (φ n)) (J (φ n))
              (R (φ n)) K) (z (φ n))‖) atTop (nhds 0) := by
        simpa only [norm_zero] using hnextResidual.norm
      have hnextGainSum := G.tendsto_finkPositiveContinuationGainSum_zero
        (fun n => G.finkNextReferenceVector
          (a (φ n)) (J (φ n)) (R (φ n)) K)
        (z ∘ φ) hnextGain
      have hnextHold : Tendsto (fun n =>
          ‖G.finkContinuationResidualVector
            (G.finkNextReferenceVector (a (φ n)) (J (φ n))
              (R (φ n)) K) (z (φ n))‖ +
          G.finkPositiveContinuationGainSum
            (G.finkNextReferenceVector (a (φ n)) (J (φ n))
              (R (φ n)) K) (z (φ n))) atTop (nhds 0) := by
        simpa only [Function.comp_apply, zero_add] using
          hnextResidualNorm.add hnextGainSum
      exact ⟨K, φ, hφ, hKnorm, hcorrection, hresidual,
        hgain, hnextHold⟩

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

/-- The unnormalized discount scale diverges when discounts approach one
from below. -/
theorem tendsto_finkDiscountScale_atTop (β : ℕ → ℝ)
    (hβ1 : ∀ n, β n < 1) (hβlim : Tendsto β atTop (nhds 1)) :
    Tendsto (fun n => β n / (1 - β n)) atTop atTop := by
  have hden : Tendsto (fun n => (1 : ℝ) - β n) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hβlim
  have hdenPos : ∀ᶠ n in atTop, 1 - β n ∈ Set.Ioi (0 : ℝ) := by
    exact Filter.Eventually.of_forall fun n => by
      simpa only [Set.mem_Ioi] using sub_pos.mpr (hβ1 n)
  have hdenGT : Tendsto (fun n => (1 : ℝ) - β n) atTop
      (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hden hdenPos
  have hinv : Tendsto (fun n => (1 - β n)⁻¹) atTop atTop :=
    hdenGT.inv_tendsto_nhdsGT_zero
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [tendsto_atTop.1 hinv (b + 1)] with n hn
  have hne : 1 - β n ≠ 0 := ne_of_gt (sub_pos.mpr (hβ1 n))
  have hid : β n / (1 - β n) = (1 - β n)⁻¹ - 1 := by
    field_simp [hne]
    ring
  rw [hid]
  linarith

/-- Exact root correction scale: inverse discount horizon plus the current
value error.  Thus every boundary hold error is this scalar times its
next-reference hold error. -/
theorem finkReferenceCorrectionScale_relativeBias_eq
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℝ) (hβpos : 0 < β) (hβ1 : β < 1)
    (W : G.State → Payoff ι) {U : ℝ} (z : G.finkDomain U) :
    G.finkReferenceCorrectionScale (β / (1 - β))
        (G.finkRelativeBias β W z) =
      (1 - β) / β + ‖G.finkValue z - W‖ := by
  let a : ℝ := β / (1 - β)
  have haPos : 0 < a := div_pos hβpos (sub_pos.mpr hβ1)
  have hrelative : G.finkRelativeBias β W z =
      a • (G.finkValue z - W) := by
    ext s who
    simp only [finkRelativeBias, a, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul]
  change (1 + ‖G.finkRelativeBias β W z‖) / a =
    (1 - β) / β + ‖G.finkValue z - W‖
  rw [hrelative, norm_smul, Real.norm_eq_abs, abs_of_pos haPos]
  dsimp only [a]
  field_simp [ne_of_gt hβpos, ne_of_gt (sub_pos.mpr hβ1)]

/-- Root specialization of the boundary hold-error factorization.  The only
root rate is the inverse discount horizon plus the value error; all remaining
size belongs to the next finite hierarchy layer. -/
theorem finkRelativeBoundaryHoldError_eq
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (β : ℝ) (hβpos : 0 < β) (hβ1 : β < 1)
    (W K : G.State → Payoff ι) {U : ℝ} (z : G.finkDomain U) :
    ‖G.finkContinuationResidualVector
        (W + G.finkReferenceCorrection (β / (1 - β))
          (G.finkRelativeBias β W z) K) z‖ +
      G.finkPositiveContinuationGainSum
        (W + G.finkReferenceCorrection (β / (1 - β))
          (G.finkRelativeBias β W z) K) z =
      ((1 - β) / β + ‖G.finkValue z - W‖) *
        (‖G.finkContinuationResidualVector
            (G.finkNextReferenceVector (β / (1 - β))
              (G.finkRelativeBias β W z) W K) z‖ +
          G.finkPositiveContinuationGainSum
            (G.finkNextReferenceVector (β / (1 - β))
              (G.finkRelativeBias β W z) W K) z) := by
  have ha : β / (1 - β) ≠ 0 :=
    div_ne_zero (ne_of_gt hβpos) (ne_of_gt (sub_pos.mpr hβ1))
  have hscale : 0 ≤ G.finkReferenceCorrectionScale (β / (1 - β))
      (G.finkRelativeBias β W z) := by
    unfold finkReferenceCorrectionScale
    exact div_nonneg (by positivity)
      (div_nonneg hβpos.le (sub_pos.mpr hβ1).le)
  have hfactor := G.finkCorrectedReferenceHoldError_eq_scale_mul
    (β / (1 - β)) (G.finkRelativeBias β W z) W K z ha hscale
  rw [G.finkReferenceCorrectionScale_relativeBias_eq
    β hβpos hβ1 W z] at hfactor
  exact hfactor

/-- Canonical root correction sequence attached to a discounted Fink family
and a fixed unit boundary direction. -/
noncomputable def finkRootCorrection
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (W K : G.State → Payoff ι) {U : ℝ}
    (z : ℕ → G.finkDomain U) (n : ℕ) : G.State → Payoff ι :=
  G.finkReferenceCorrection (β n / (1 - β n))
    (G.finkRelativeBias (β n) W (z n)) K

/-- Hold defect of the next reference exposed by the root correction
factorization. -/
noncomputable def finkNextReferenceHoldError
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (W K : G.State → Payoff ι) {U : ℝ}
    (z : ℕ → G.finkDomain U) (n : ℕ) : ℝ :=
  ‖G.finkContinuationResidualVector
      (G.finkNextReferenceVector (β n / (1 - β n))
        (G.finkRelativeBias (β n) W (z n)) W K) (z n)‖ +
    G.finkPositiveContinuationGainSum
      (G.finkNextReferenceVector (β n / (1 - β n))
        (G.finkRelativeBias (β n) W (z n)) W K) (z n)

/-- Along a verified root boundary, the corrected hold error is little-o of
the inverse discount horizon plus the value error.  This is the asymptotic
rate, rather than just pointwise convergence, exposed by the next hierarchy
layer. -/
theorem tendsto_finkRelativeBoundaryHoldError_div_rootScale_zero
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (hβpos : ∀ n, 0 < β n) (hβ1 : ∀ n, β n < 1)
    (W K : G.State → Payoff ι) {U : ℝ} (z : ℕ → G.finkDomain U)
    (hnextResidual : Tendsto (fun n =>
      G.finkContinuationResidualVector
        (G.finkNextReferenceVector (β n / (1 - β n))
          (G.finkRelativeBias (β n) W (z n)) W K) (z n))
      atTop (nhds 0))
    (hnextGain : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ s who (d : G.Act who),
        G.finkContinuationGain
          (G.finkNextReferenceVector (β n / (1 - β n))
            (G.finkRelativeBias (β n) W (z n)) W K)
          (z n) s who d ≤ ε) :
    Tendsto (fun n =>
      (‖G.finkContinuationResidualVector
          (W + G.finkReferenceCorrection (β n / (1 - β n))
            (G.finkRelativeBias (β n) W (z n)) K) (z n)‖ +
        G.finkPositiveContinuationGainSum
          (W + G.finkReferenceCorrection (β n / (1 - β n))
            (G.finkRelativeBias (β n) W (z n)) K) (z n)) /
      ((1 - β n) / β n + ‖G.finkValue (z n) - W‖))
      atTop (nhds 0) := by
  have ha : ∀ n, β n / (1 - β n) ≠ 0 := fun n =>
    div_ne_zero (ne_of_gt (hβpos n)) (ne_of_gt (sub_pos.mpr (hβ1 n)))
  have hscalePos : ∀ n, 0 < G.finkReferenceCorrectionScale
      (β n / (1 - β n))
      (G.finkRelativeBias (β n) W (z n)) := by
    intro n
    rw [G.finkReferenceCorrectionScale_relativeBias_eq
      (β n) (hβpos n) (hβ1 n) W (z n)]
    exact add_pos_of_pos_of_nonneg
      (div_pos (sub_pos.mpr (hβ1 n)) (hβpos n)) (norm_nonneg _)
  have h := G.tendsto_finkCorrectedReferenceHoldError_div_scale_zero
    (fun n => β n / (1 - β n))
    (fun n => G.finkRelativeBias (β n) W (z n))
    (fun _ => W) K z ha hscalePos hnextResidual hnextGain
  apply h.congr'
  exact Filter.Eventually.of_forall fun n => by
    simp only
    rw [G.finkReferenceCorrectionScale_relativeBias_eq
      (β n) (hβpos n) (hβ1 n) W (z n)]

/-- For a relative Fink bias around its value limit, the coefficient of every
unit boundary correction tends to zero.  Quantitatively it is exactly the
reciprocal root discount scale plus the norm of the value error. -/
theorem tendsto_finkReferenceCorrectionScale_relativeBias_zero
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (hβpos : ∀ n, 0 < β n) (hβ1 : ∀ n, β n < 1)
    (hβlim : Tendsto β atTop (nhds 1)) {U : ℝ}
    (z : ℕ → G.finkDomain U) (W : G.State → Payoff ι)
    (hV : Tendsto (fun n => G.finkValue (z n)) atTop (nhds W)) :
    Tendsto (fun n => G.finkReferenceCorrectionScale
      (β n / (1 - β n)) (G.finkRelativeBias (β n) W (z n)))
      atTop (nhds 0) := by
  let a : ℕ → ℝ := fun n => β n / (1 - β n)
  have haPos : ∀ n, 0 < a n := fun n =>
    div_pos (hβpos n) (sub_pos.mpr (hβ1 n))
  have haLim : Tendsto a atTop atTop := by
    exact tendsto_finkDiscountScale_atTop β hβ1 hβlim
  have haInv : Tendsto (fun n => (a n)⁻¹) atTop (nhds 0) :=
    haLim.inv_tendsto_atTop
  have hdiff : Tendsto
      (fun n => ‖G.finkValue (z n) - W‖) atTop (nhds 0) := by
    simpa using (hV.sub (tendsto_const_nhds (x := W))).norm
  have heq : (fun n => G.finkReferenceCorrectionScale
      (β n / (1 - β n)) (G.finkRelativeBias (β n) W (z n))) =
      fun n => (a n)⁻¹ + ‖G.finkValue (z n) - W‖ := by
    funext n
    have hrelative : G.finkRelativeBias (β n) W (z n) =
        a n • (G.finkValue (z n) - W) := by
      ext s who
      simp only [finkRelativeBias, a, Pi.smul_apply, Pi.sub_apply,
        smul_eq_mul]
    change (1 + ‖G.finkRelativeBias (β n) W (z n)‖) / a n =
      (a n)⁻¹ + ‖G.finkValue (z n) - W‖
    rw [hrelative, norm_smul,
      Real.norm_eq_abs, abs_of_pos (haPos n)]
    field_simp [ne_of_gt (haPos n)]
  rw [heq]
  simpa only [zero_add] using haInv.add hdiff

/-- The boundary correction vector itself therefore vanishes for every fixed
unit direction (indeed, for every fixed direction). -/
theorem tendsto_finkReferenceCorrection_relativeBias_zero
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (hβpos : ∀ n, 0 < β n) (hβ1 : ∀ n, β n < 1)
    (hβlim : Tendsto β atTop (nhds 1)) {U : ℝ}
    (z : ℕ → G.finkDomain U) (W K : G.State → Payoff ι)
    (hV : Tendsto (fun n => G.finkValue (z n)) atTop (nhds W)) :
    Tendsto (fun n => G.finkReferenceCorrection
      (β n / (1 - β n)) (G.finkRelativeBias (β n) W (z n)) K)
      atTop (nhds 0) := by
  have hs := G.tendsto_finkReferenceCorrectionScale_relativeBias_zero
    β hβpos hβ1 hβlim z W hV
  simpa only [finkReferenceCorrection, zero_smul] using hs.smul_const K

/-- At the root of the relative-bias hierarchy, every boundary correction is
automatically negligible as the discount tends to one.  Thus the verified
hierarchy yields either a convergent relative-bias subsequence or corrected
targets converging back to `W` whose continuation residuals vanish and whose
pure-deviation continuation gains are asymptotically nonpositive. -/
theorem FinkVerifiedReferenceResolution.relativeBias_rootCorrection_dichotomy
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (hβpos : ∀ n, 0 < β n) (hβ1 : ∀ n, β n < 1)
    (hβlim : Tendsto β atTop (nhds 1)) {U : ℝ}
    (z : ℕ → G.finkDomain U) (W : G.State → Payoff ι)
    (hV : Tendsto (fun n => G.finkValue (z n)) atTop (nhds W))
    (hresolution : G.FinkVerifiedReferenceResolution z
      (fun n => G.finkValue (z n))
      (fun n => β n / (1 - β n))
      (fun n => G.finkRelativeBias (β n) W (z n))
      (fun _ => W)) :
    (∃ (φ : ℕ → ℕ) (Jlim : G.State → Payoff ι),
      StrictMono φ ∧ Tendsto (fun n =>
        G.finkRelativeBias (β (φ n)) W (z (φ n)))
          atTop (nhds Jlim)) ∨
    ∃ (K : G.State → Payoff ι) (φ : ℕ → ℕ),
      StrictMono φ ∧ ‖K‖ = 1 ∧
      Tendsto (fun n => G.finkReferenceCorrection
        (β (φ n) / (1 - β (φ n)))
        (G.finkRelativeBias (β (φ n)) W (z (φ n))) K)
        atTop (nhds 0) ∧
      Tendsto (fun n => G.finkContinuationResidualVector
        (W + G.finkReferenceCorrection
          (β (φ n) / (1 - β (φ n)))
          (G.finkRelativeBias (β (φ n)) W (z (φ n))) K)
        (z (φ n))) atTop (nhds 0) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        ∀ s who (d : G.Act who),
          G.finkContinuationGain
            (W + G.finkReferenceCorrection
              (β (φ n) / (1 - β (φ n)))
              (G.finkRelativeBias (β (φ n)) W (z (φ n))) K)
            (z (φ n)) s who d ≤ ε := by
  have ha : ∀ n, β n / (1 - β n) ≠ 0 := fun n =>
    div_ne_zero (ne_of_gt (hβpos n)) (ne_of_gt (sub_pos.mpr (hβ1 n)))
  have hscale0 : ∀ n, 0 ≤ G.finkReferenceCorrectionScale
      (β n / (1 - β n))
      (G.finkRelativeBias (β n) W (z n)) := by
    intro n
    unfold finkReferenceCorrectionScale
    exact div_nonneg (by positivity)
      (div_nonneg (hβpos n).le (sub_pos.mpr (hβ1 n)).le)
  have hscale := G.tendsto_finkReferenceCorrectionScale_relativeBias_zero
    β hβpos hβ1 hβlim z W hV
  simpa only [Function.comp_def] using
    hresolution.rootCorrection_dichotomy G ha hscale0 hscale

/-- Scalar-error form of `relativeBias_rootCorrection_dichotomy`.  In the
boundary branch the hierarchy produces exactly the time-dependent step error
used by the corrected-target verifier, and that error tends to zero. -/
theorem FinkVerifiedReferenceResolution.relativeBias_rootStepError_dichotomy
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (hβpos : ∀ n, 0 < β n) (hβ1 : ∀ n, β n < 1)
    (hβlim : Tendsto β atTop (nhds 1)) {U : ℝ}
    (z : ℕ → G.finkDomain U) (W : G.State → Payoff ι)
    (hV : Tendsto (fun n => G.finkValue (z n)) atTop (nhds W))
    (hresolution : G.FinkVerifiedReferenceResolution z
      (fun n => G.finkValue (z n))
      (fun n => β n / (1 - β n))
      (fun n => G.finkRelativeBias (β n) W (z n))
      (fun _ => W)) :
    (∃ (φ : ℕ → ℕ) (Jlim : G.State → Payoff ι),
      StrictMono φ ∧ Tendsto (fun n =>
        G.finkRelativeBias (β (φ n)) W (z (φ n)))
          atTop (nhds Jlim)) ∨
    ∃ (K : G.State → Payoff ι) (φ : ℕ → ℕ),
      StrictMono φ ∧ ‖K‖ = 1 ∧
      let R : ℕ → G.State → Payoff ι := fun n =>
        G.finkReferenceCorrection
          (β (φ n) / (1 - β (φ n)))
          (G.finkRelativeBias (β (φ n)) W (z (φ n))) K
      Tendsto R atTop (nhds 0) ∧
        Tendsto (fun n => G.finkCorrectedTargetStepError W R
          (fun k => z (φ k)) n) atTop (nhds 0) := by
  rcases hresolution.relativeBias_rootCorrection_dichotomy G
      β hβpos hβ1 hβlim z W hV with hinterior | hboundary
  · exact Or.inl hinterior
  · right
    obtain ⟨K, φ, hφ, hKnorm, hR, hresidual, hgain⟩ := hboundary
    let R : ℕ → G.State → Payoff ι := fun n =>
      G.finkReferenceCorrection
        (β (φ n) / (1 - β (φ n)))
        (G.finkRelativeBias (β (φ n)) W (z (φ n))) K
    have hstep : Tendsto (fun n => G.finkCorrectedTargetStepError W R
        (fun k => z (φ k)) n) atTop (nhds 0) := by
      exact G.tendsto_finkCorrectedTargetStepError_zero W R
        (fun k => z (φ k)) hR hresidual hgain
    exact ⟨K, φ, hφ, hKnorm, hR, hstep⟩

/-- Fast-drift form of the root dichotomy.  For every error budget, the
boundary branch has a further strict subsequence whose corrected-target step
errors are summable below that budget.  Its compatibility with the slow
relative-bias switch calendar is the remaining selection problem. -/
theorem FinkVerifiedReferenceResolution.relativeBias_rootSummableStep_dichotomy
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (hβpos : ∀ n, 0 < β n) (hβ1 : ∀ n, β n < 1)
    (hβlim : Tendsto β atTop (nhds 1)) {U : ℝ}
    (z : ℕ → G.finkDomain U) (W : G.State → Payoff ι)
    (hV : Tendsto (fun n => G.finkValue (z n)) atTop (nhds W))
    (hresolution : G.FinkVerifiedReferenceResolution z
      (fun n => G.finkValue (z n))
      (fun n => β n / (1 - β n))
      (fun n => G.finkRelativeBias (β n) W (z n))
      (fun _ => W))
    (ε : ℝ) (hε : 0 < ε) :
    (∃ (φ : ℕ → ℕ) (Jlim : G.State → Payoff ι),
      StrictMono φ ∧ Tendsto (fun n =>
        G.finkRelativeBias (β (φ n)) W (z (φ n)))
          atTop (nhds Jlim)) ∨
    ∃ (K : G.State → Payoff ι) (θ : ℕ → ℕ),
      StrictMono θ ∧ ‖K‖ = 1 ∧
      let R : ℕ → G.State → Payoff ι := fun n =>
        G.finkReferenceCorrection
          (β (θ n) / (1 - β (θ n)))
          (G.finkRelativeBias (β (θ n)) W (z (θ n))) K
      ‖R 0‖ ≤ ε ∧
        Summable (fun n => G.finkCorrectedTargetStepError W R
          (z ∘ θ) n) ∧
        ∑' n, G.finkCorrectedTargetStepError W R (z ∘ θ) n ≤ ε := by
  rcases hresolution.relativeBias_rootCorrection_dichotomy G
      β hβpos hβ1 hβlim z W hV with hinterior | hboundary
  · exact Or.inl hinterior
  · right
    obtain ⟨K, φ, hφ, hKnorm, hR, hresidual, hgain⟩ := hboundary
    let R : ℕ → G.State → Payoff ι := fun n =>
      G.finkReferenceCorrection
        (β (φ n) / (1 - β (φ n)))
        (G.finkRelativeBias (β (φ n)) W (z (φ n))) K
    obtain ⟨ψ, hψ, hRzero, hsummable, htotal⟩ :=
      G.exists_strictMono_summable_finkCorrectedTargetStepError_subsequence
        W R (fun n => z (φ n)) hR hresidual hgain ε hε
    let θ : ℕ → ℕ := φ ∘ ψ
    have hθ : StrictMono θ := hφ.comp hψ
    refine ⟨K, θ, hθ, hKnorm, ?_, ?_, ?_⟩
    · simpa only [R, θ, Function.comp_apply] using hRzero
    · simpa only [R, θ, Function.comp_apply, Function.comp_def] using hsummable
    · simpa only [R, θ, Function.comp_apply, Function.comp_def] using htotal

/-- Joint fast-series form of the root dichotomy.  The boundary branch has a
single strict subsequence on which both corrected adjacent drift and the
next-reference hold defect are summable with arbitrarily small totals.  Only
compatibility of this subsequence with the annealing threshold increments
remains. -/
theorem FinkVerifiedReferenceResolution.relativeBias_rootSummableStepAndNextHold_dichotomy
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (hβpos : ∀ n, 0 < β n) (hβ1 : ∀ n, β n < 1)
    (hβlim : Tendsto β atTop (nhds 1)) {U : ℝ}
    (z : ℕ → G.finkDomain U) (W : G.State → Payoff ι)
    (hV : Tendsto (fun n => G.finkValue (z n)) atTop (nhds W))
    (hresolution : G.FinkVerifiedReferenceResolution z
      (fun n => G.finkValue (z n))
      (fun n => β n / (1 - β n))
      (fun n => G.finkRelativeBias (β n) W (z n))
      (fun _ => W))
    (ε : ℝ) (hε : 0 < ε) :
    (∃ (φ : ℕ → ℕ) (Jlim : G.State → Payoff ι),
      StrictMono φ ∧ Tendsto (fun n =>
        G.finkRelativeBias (β (φ n)) W (z (φ n)))
          atTop (nhds Jlim)) ∨
    ∃ (K : G.State → Payoff ι) (θ : ℕ → ℕ),
      StrictMono θ ∧ ‖K‖ = 1 ∧
      ‖G.finkRootCorrection β W K z (θ 0)‖ ≤ ε ∧
      Summable (fun n => G.finkCorrectedTargetStepError W
        (G.finkRootCorrection β W K z ∘ θ) (z ∘ θ) n) ∧
      ∑' n, G.finkCorrectedTargetStepError W
        (G.finkRootCorrection β W K z ∘ θ) (z ∘ θ) n ≤ ε ∧
      Summable (G.finkNextReferenceHoldError β W K z ∘ θ) ∧
      ∑' n, G.finkNextReferenceHoldError β W K z (θ n) ≤ ε := by
  have ha : ∀ n, β n / (1 - β n) ≠ 0 := fun n =>
    div_ne_zero (ne_of_gt (hβpos n)) (ne_of_gt (sub_pos.mpr (hβ1 n)))
  have hscale0 : ∀ n, 0 ≤ G.finkReferenceCorrectionScale
      (β n / (1 - β n))
      (G.finkRelativeBias (β n) W (z n)) := by
    intro n
    unfold finkReferenceCorrectionScale
    exact div_nonneg (by positivity)
      (div_nonneg (hβpos n).le (sub_pos.mpr (hβ1 n)).le)
  have hscale := G.tendsto_finkReferenceCorrectionScale_relativeBias_zero
    β hβpos hβ1 hβlim z W hV
  rcases hresolution.rootCorrection_and_nextHold_dichotomy
      G ha hscale0 hscale with hinterior | hboundary
  · left
    simpa only [Function.comp_def] using hinterior
  · right
    obtain ⟨K, φ, hφ, hKnorm, hR, hresidual, hgain,
      hnextHoldRaw⟩ := hboundary
    let R : ℕ → G.State → Payoff ι := fun n =>
      G.finkRootCorrection β W K z (φ n)
    let aux : ℕ → ℝ := fun n =>
      G.finkNextReferenceHoldError β W K z (φ n)
    have hnextHold : Tendsto aux atTop (nhds 0) := by
      simpa only [aux, finkNextReferenceHoldError] using hnextHoldRaw
    have haux0 : ∀ n, 0 ≤ aux n := by
      intro n
      dsimp only [aux, finkNextReferenceHoldError]
      exact add_nonneg (norm_nonneg _) (by
        unfold finkPositiveContinuationGainSum
        exact Finset.sum_nonneg fun p hp => le_max_right _ _)
    obtain ⟨ψ, hψ, hRzero, hfast, hfastTotal,
        hauxSum, hauxTotal⟩ :=
      G.exists_strictMono_summable_finkCorrectedTargetStepError_and_aux_subsequence
        W R (z ∘ φ) hR hresidual hgain aux haux0 hnextHold ε hε
    let θ : ℕ → ℕ := φ ∘ ψ
    have hθ : StrictMono θ := hφ.comp hψ
    refine ⟨K, θ, hθ, hKnorm, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [R, θ, finkRootCorrection, Function.comp_apply] using hRzero
    · simpa only [R, θ, Function.comp_def] using hfast
    · simpa only [R, θ, Function.comp_def] using hfastTotal
    · simpa only [aux, θ, Function.comp_def] using hauxSum
    · simpa only [aux, θ, Function.comp_apply] using hauxTotal

/-- Weighted joint-series form of the root dichotomy.  For every prescribed
nonnegative layer envelope `D`, the boundary branch can be chosen so that its
next-reference defect is summable after multiplication by `D`, while the
corrected adjacent drift remains summable on the same strict subsequence. -/
theorem FinkVerifiedReferenceResolution.relativeBias_rootSummableStepAndWeightedNextHold_dichotomy
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (hβpos : ∀ n, 0 < β n) (hβ1 : ∀ n, β n < 1)
    (hβlim : Tendsto β atTop (nhds 1)) {U : ℝ}
    (z : ℕ → G.finkDomain U) (W : G.State → Payoff ι)
    (hV : Tendsto (fun n => G.finkValue (z n)) atTop (nhds W))
    (hresolution : G.FinkVerifiedReferenceResolution z
      (fun n => G.finkValue (z n))
      (fun n => β n / (1 - β n))
      (fun n => G.finkRelativeBias (β n) W (z n))
      (fun _ => W))
    (D : ℕ → ℝ) (hD0 : ∀ n, 0 ≤ D n) :
    (∃ (φ : ℕ → ℕ) (Jlim : G.State → Payoff ι),
      StrictMono φ ∧ Tendsto (fun n =>
        G.finkRelativeBias (β (φ n)) W (z (φ n)))
          atTop (nhds Jlim)) ∨
    ∃ (K : G.State → Payoff ι) (θ : ℕ → ℕ),
      StrictMono θ ∧ ‖K‖ = 1 ∧
      Summable (fun n => G.finkCorrectedTargetStepError W
        (G.finkRootCorrection β W K z ∘ θ) (z ∘ θ) n) ∧
      Summable (fun n => D n *
        G.finkNextReferenceHoldError β W K z (θ n)) := by
  rcases hresolution.relativeBias_rootSummableStepAndNextHold_dichotomy
      G β hβpos hβ1 hβlim z W hV (1 : ℝ) (by norm_num) with
    hinterior | hboundary
  · exact Or.inl hinterior
  · right
    obtain ⟨K, θ, hθ, hKnorm, hRzero, hfast, hfastTotal,
      hnext, hnextTotal⟩ := hboundary
    let R : ℕ → G.State → Payoff ι :=
      G.finkRootCorrection β W K z ∘ θ
    let zθ : ℕ → G.finkDomain U := z ∘ θ
    let aux : ℕ → ℝ := G.finkNextReferenceHoldError β W K z ∘ θ
    have haux0 : ∀ n, 0 ≤ aux n := by
      intro n
      unfold aux finkNextReferenceHoldError finkPositiveContinuationGainSum
      exact add_nonneg (norm_nonneg _)
        (Finset.sum_nonneg fun p hp => le_max_right _ _)
    have haux : Tendsto aux atTop (nhds 0) := by
      exact hnext.tendsto_atTop_zero
    obtain ⟨ψ, hψ, hfast', hfastTotal', hweighted⟩ :=
      G.exists_strictMono_preserving_finkCorrectedError_weightingAux
        W R zθ (by simpa only [R, zθ] using hfast)
        aux D haux0 haux hD0
    let Θ : ℕ → ℕ := θ ∘ ψ
    have hΘ : StrictMono Θ := hθ.comp hψ
    refine ⟨K, Θ, hΘ, hKnorm, ?_, ?_⟩
    · simpa only [R, zθ, Θ, Function.comp_def] using hfast'
    · simpa only [aux, Θ, Function.comp_def] using hweighted

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

theorem ceil_slowCalendarThreshold_le_start (B : ℕ → ℝ) (n : ℕ) :
    Nat.ceil (((n : ℕ) : ℝ) * |B n|) ≤ slowCalendarStart B n := by
  exact Nat.ceil_le.mpr (slowCalendarStart_cost_le B n)

/-- Sharp block estimate: because the current activation threshold has
already been met, a layer is held only for one stage or for the positive
increment of the integer activation thresholds. -/
theorem slowCalendarBlockLength_le_max_ceil_sub (B : ℕ → ℝ) (n : ℕ) :
    slowCalendarBlockLength B n ≤ max 1
      (Nat.ceil ((((n + 1 : ℕ) : ℝ) * |B (n + 1)|)) -
        Nat.ceil (((n : ℕ) : ℝ) * |B n|)) := by
  have hthreshold := ceil_slowCalendarThreshold_le_start B n
  rw [slowCalendarBlockLength, slowCalendarStart]
  omega

/-- Any nonnegative scale satisfying a bound against successive activation
threshold increments satisfies the concrete calendar's bounded-dilation
condition. -/
theorem slowCalendarBlockLength_mul_le_of_thresholdIncrement
    (B scale : ℕ → ℝ) (hscale : ∀ n, 0 ≤ scale n) (C : ℝ)
    (hincrement : ∀ n,
      ((max 1
        (Nat.ceil ((((n + 1 : ℕ) : ℝ) * |B (n + 1)|)) -
          Nat.ceil (((n : ℕ) : ℝ) * |B n|)) : ℕ) : ℝ) * scale n ≤ C) :
    ∀ n, (slowCalendarBlockLength B n : ℝ) * scale n ≤ C := by
  intro n
  have hblock : (slowCalendarBlockLength B n : ℝ) ≤
      ((max 1
        (Nat.ceil ((((n + 1 : ℕ) : ℝ) * |B (n + 1)|)) -
          Nat.ceil (((n : ℕ) : ℝ) * |B n|)) : ℕ) : ℝ) := by
    exact_mod_cast slowCalendarBlockLength_le_max_ceil_sub B n
  exact (mul_le_mul_of_nonneg_right hblock (hscale n)).trans
    (hincrement n)

/-- A block cannot be longer than one plus the next layer's raw activation
threshold.  This removes the recursively defined activation time from rate
estimates for the concrete slow calendar. -/
theorem slowCalendarBlockLength_le_ceil_add_one (B : ℕ → ℝ) (n : ℕ) :
    slowCalendarBlockLength B n ≤
      Nat.ceil ((((n + 1 : ℕ) : ℝ) * |B (n + 1)|)) + 1 := by
  rw [slowCalendarBlockLength, slowCalendarStart]
  omega

/-- Real-valued version of `slowCalendarBlockLength_le_ceil_add_one`, with
the ceiling absorbed into an explicit additive constant. -/
theorem slowCalendarBlockLength_cast_le (B : ℕ → ℝ) (n : ℕ) :
    (slowCalendarBlockLength B n : ℝ) ≤
      ((n + 1 : ℕ) : ℝ) * |B (n + 1)| + 2 := by
  let x : ℝ := ((n + 1 : ℕ) : ℝ) * |B (n + 1)|
  have hx : 0 ≤ x := mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
  have hnat := slowCalendarBlockLength_le_ceil_add_one B n
  have hcast : (slowCalendarBlockLength B n : ℝ) ≤
      (Nat.ceil x : ℝ) + 1 := by
    exact_mod_cast hnat
  have hceil : (Nat.ceil x : ℝ) ≤ x + 1 :=
    (Nat.ceil_lt_add_one hx).le
  dsimp only [x] at hcast hceil ⊢
  linarith

/-- At activation times, the total repeated cost is exactly the weighted sum
of layer costs by their block lengths. -/
theorem sum_slowUnitStepCalendar_at_start
    (B h : ℕ → ℝ) (N : ℕ) :
    ∑ t ∈ Finset.range (slowCalendarStart B N),
        h (slowUnitStepCalendar B t) =
      ∑ n ∈ Finset.range N, (slowCalendarBlockLength B n : ℝ) * h n := by
  induction N with
  | zero => simp [slowCalendarStart]
  | succ N ih =>
      let L := slowCalendarBlockLength B N
      have hstart : slowCalendarStart B N + L =
          slowCalendarStart B (N + 1) :=
        slowCalendarStart_add_blockLength B N
      have hblock : ∑ t ∈ Finset.range L,
          h (slowUnitStepCalendar B (slowCalendarStart B N + t)) =
          (L : ℝ) * h N := by
        calc
          ∑ t ∈ Finset.range L,
              h (slowUnitStepCalendar B (slowCalendarStart B N + t)) =
              ∑ _t ∈ Finset.range L, h N := by
            apply Finset.sum_congr rfl
            intro t ht
            congr 1
            apply (slowUnitStepCalendar_eq_iff B
              (slowCalendarStart B N + t) N).2
            constructor
            · omega
            · have htL : t < L := Finset.mem_range.mp ht
              omega
          _ = (L : ℝ) * h N := by simp
      rw [← hstart, Finset.sum_range_add, ih, hblock,
        Finset.sum_range_succ]

theorem monotone_slowUnitStepCalendar (B : ℕ → ℝ) :
    Monotone (slowUnitStepCalendar B) := by
  intro s t hst
  unfold slowUnitStepCalendar
  exact Nat.findGreatest_mono (fun _ hn => hn.trans hst) hst

theorem slowUnitStepCalendar_step (B : ℕ → ℝ) (t : ℕ) :
    slowUnitStepCalendar B (t + 1) = slowUnitStepCalendar B t ∨
      slowUnitStepCalendar B (t + 1) = slowUnitStepCalendar B t + 1 := by
  let v := slowUnitStepCalendar B t
  let w := slowUnitStepCalendar B (t + 1)
  have hvw : v ≤ w := monotone_slowUnitStepCalendar B (Nat.le_succ t)
  have hwle : w ≤ t + 1 := Nat.findGreatest_le _
  have hwStart : slowCalendarStart B w ≤ t + 1 :=
    slowCalendarStart_slowUnitStepCalendar_le B (t + 1)
  have hwv : w ≤ v + 1 := by
    by_contra hnot
    have hv1w : v + 1 < w := by omega
    have hv1t : v + 1 ≤ t := by omega
    have hstartLt : slowCalendarStart B (v + 1) <
        slowCalendarStart B w :=
      strictMono_slowCalendarStart B hv1w
    have hstartLe : slowCalendarStart B (v + 1) ≤ t := by omega
    have hgreatest : v + 1 ≤ slowUnitStepCalendar B t :=
      Nat.le_findGreatest hv1t hstartLe
    change v + 1 ≤ v at hgreatest
    omega
  change w = v ∨ w = v + 1
  omega

theorem tendsto_slowUnitStepCalendar_atTop (B : ℕ → ℝ) :
    Tendsto (slowUnitStepCalendar B) atTop atTop := by
  refine tendsto_atTop.2 fun n => ?_
  filter_upwards [eventually_ge_atTop (slowCalendarStart B n)] with t ht
  have hnt : n ≤ t :=
    (strictMono_slowCalendarStart B).id_le n |>.trans ht
  exact Nat.le_findGreatest hnt ht

/-- Every prescribed scalar endpoint cost is sublinear along its associated
slow unit-step calendar. -/
theorem tendsto_slowUnitStepCalendar_absCost_div_zero (B : ℕ → ℝ) :
    Tendsto (fun T : ℕ => (T : ℝ)⁻¹ * |B (slowUnitStepCalendar B T)|)
      atTop (nhds 0) := by
  have hν := tendsto_slowUnitStepCalendar_atTop B
  have hinv : Tendsto
      (fun T : ℕ => ((slowUnitStepCalendar B T : ℕ) : ℝ)⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp hν)
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun T =>
      mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg T)) (abs_nonneg _)
  · have hνpos : ∀ᶠ T in atTop, 0 < slowUnitStepCalendar B T :=
      (tendsto_atTop.1 hν 1).mono fun T hT => Nat.zero_lt_of_lt hT
    have hTpos : ∀ᶠ T in atTop, 0 < T := eventually_gt_atTop 0
    filter_upwards [hνpos, hTpos] with T hνT hT
    let n := slowUnitStepCalendar B T
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hνT
    have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
    have hcost := slowCalendarStart_cost_le B n
    have hstart := slowCalendarStart_slowUnitStepCalendar_le B T
    have hcostT : (n : ℝ) * |B n| ≤ (T : ℝ) :=
      hcost.trans (by exact_mod_cast hstart)
    change (T : ℝ)⁻¹ * |B n| ≤ (n : ℝ)⁻¹
    rw [← div_eq_inv_mul, ← one_div]
    apply (div_le_iff₀ hTreal).2
    rw [one_div, inv_mul_eq_div]
    exact (le_div_iff₀ hnreal).2 (by simpa [mul_comm] using hcostT)
  · exact hinv

theorem tendsto_slowUnitStepCalendar_cost_div_zero (B : ℕ → ℝ) :
    Tendsto (fun T : ℕ => (T : ℝ)⁻¹ * B (slowUnitStepCalendar B T))
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  convert tendsto_slowUnitStepCalendar_absCost_div_zero B using 1
  ext T
  simp only [Function.comp_apply, abs_mul]
  rw [abs_of_nonneg (show 0 ≤ ((T : ℝ)⁻¹) from
    inv_nonneg.mpr (Nat.cast_nonneg T))]

/-- A calendar that starts at zero and either waits or advances by one charges
each crossed edge exactly once. -/
theorem sum_unitStepCalendar_eq (ν : ℕ → ℕ) (e : ℕ → ℝ)
    (hν0 : ν 0 = 0)
    (hstep : ∀ t, ν (t + 1) = ν t ∨ ν (t + 1) = ν t + 1)
    (T : ℕ) :
    ∑ t ∈ Finset.range T,
        (if ν (t + 1) = ν t then 0 else e (ν t)) =
      ∑ n ∈ Finset.range (ν T), e n := by
  induction T with
  | zero => simp [hν0]
  | succ T ih =>
      rw [Finset.sum_range_succ, ih]
      rcases hstep T with hwait | hadvance
      · simp [hwait]
      · rw [hadvance, Finset.sum_range_succ]
        simp

/-- Exact drift accounting for a unit-step block calendar.  Hold errors are
paid once per calendar stage, whereas correction motion is paid exactly once
per crossed subsequence edge. -/
theorem sum_finkCorrectedTargetStepError_unitStep
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (W : G.State → Payoff ι) (R : ℕ → G.State → Payoff ι)
    {U : ℝ} (z : ℕ → G.finkDomain U)
    (ν : ℕ → ℕ) (hν0 : ν 0 = 0)
    (hstep : ∀ t, ν (t + 1) = ν t ∨ ν (t + 1) = ν t + 1)
    (T : ℕ) :
    ∑ t ∈ Finset.range T,
        G.finkCorrectedTargetStepError W (R ∘ ν) (z ∘ ν) t =
      ∑ t ∈ Finset.range T,
        G.finkCorrectedTargetHoldError W R z (ν t) +
      ∑ n ∈ Finset.range (ν T), ‖R (n + 1) - R n‖ := by
  have hmotion : ∀ t,
      ‖R (ν (t + 1)) - R (ν t)‖ =
        if ν (t + 1) = ν t then 0 else ‖R (ν t + 1) - R (ν t)‖ := by
    intro t
    rcases hstep t with hwait | hadvance
    · simp [hwait]
    · simp [hadvance]
  calc
    ∑ t ∈ Finset.range T,
        G.finkCorrectedTargetStepError W (R ∘ ν) (z ∘ ν) t =
        ∑ t ∈ Finset.range T,
          (G.finkCorrectedTargetHoldError W R z (ν t) +
            ‖R (ν (t + 1)) - R (ν t)‖) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [G.finkCorrectedTargetStepError_eq_hold_add_motion]
      rfl
    _ = (∑ t ∈ Finset.range T,
          G.finkCorrectedTargetHoldError W R z (ν t)) +
        ∑ t ∈ Finset.range T,
          ‖R (ν (t + 1)) - R (ν t)‖ := by
      rw [Finset.sum_add_distrib]
    _ = (∑ t ∈ Finset.range T,
          G.finkCorrectedTargetHoldError W R z (ν t)) +
        ∑ t ∈ Finset.range T,
          (if ν (t + 1) = ν t then 0
          else ‖R (ν t + 1) - R (ν t)‖) := by
      congr 1
      exact Finset.sum_congr rfl fun t _ => hmotion t
    _ = (∑ t ∈ Finset.range T,
          G.finkCorrectedTargetHoldError W R z (ν t)) +
        ∑ n ∈ Finset.range (ν T), ‖R (n + 1) - R n‖ := by
      rw [sum_unitStepCalendar_eq ν
        (fun n => ‖R (n + 1) - R n‖) hν0 hstep T]

/-- Once the fast subsequence has summable adjacent step error, slowing it
adds only the repeated hold-error bill.  Correction motion itself never costs
more than its original fast-subsequence total. -/
theorem sum_finkCorrectedTargetStepError_unitStep_le_hold_add_tsum
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (W : G.State → Payoff ι) (R : ℕ → G.State → Payoff ι)
    {U : ℝ} (z : ℕ → G.finkDomain U)
    (ν : ℕ → ℕ) (hν0 : ν 0 = 0)
    (hstep : ∀ t, ν (t + 1) = ν t ∨ ν (t + 1) = ν t + 1)
    (hsummable : Summable (fun n =>
      G.finkCorrectedTargetStepError W R z n))
    (T : ℕ) :
    ∑ t ∈ Finset.range T,
        G.finkCorrectedTargetStepError W (R ∘ ν) (z ∘ ν) t ≤
      ∑ t ∈ Finset.range T,
        G.finkCorrectedTargetHoldError W R z (ν t) +
      ∑' n, G.finkCorrectedTargetStepError W R z n := by
  rw [G.sum_finkCorrectedTargetStepError_unitStep
    W R z ν hν0 hstep T]
  apply add_le_add le_rfl
  calc
    ∑ n ∈ Finset.range (ν T), ‖R (n + 1) - R n‖ ≤
        ∑ n ∈ Finset.range (ν T),
          G.finkCorrectedTargetStepError W R z n := by
      apply Finset.sum_le_sum
      intro n hn
      rw [G.finkCorrectedTargetStepError_eq_hold_add_motion]
      exact le_add_of_nonneg_left
        (G.finkCorrectedTargetHoldError_nonneg W R z n)
    _ ≤ ∑' n, G.finkCorrectedTargetStepError W R z n := by
      exact hsummable.sum_le_tsum (Finset.range (ν T))
        (fun n _ => G.finkCorrectedTargetStepError_nonneg W R z n)

/-- For the concrete slow calendar, the unresolved repeated-drift bill is
exactly the block-length-weighted hold error.  The fast adjacent correction
bill remains bounded by its original `tsum`. -/
theorem sum_finkCorrectedTargetStepError_slowCalendar_at_start_le
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (W : G.State → Payoff ι) (R : ℕ → G.State → Payoff ι)
    {U : ℝ} (z : ℕ → G.finkDomain U) (B : ℕ → ℝ)
    (hsummable : Summable (fun n =>
      G.finkCorrectedTargetStepError W R z n))
    (N : ℕ) :
    ∑ t ∈ Finset.range (slowCalendarStart B N),
        G.finkCorrectedTargetStepError W
          (R ∘ slowUnitStepCalendar B)
          (z ∘ slowUnitStepCalendar B) t ≤
      ∑ n ∈ Finset.range N, (slowCalendarBlockLength B n : ℝ) *
        G.finkCorrectedTargetHoldError W R z n +
      ∑' n, G.finkCorrectedTargetStepError W R z n := by
  have hbound :=
    G.sum_finkCorrectedTargetStepError_unitStep_le_hold_add_tsum
      W R z (slowUnitStepCalendar B)
      (slowUnitStepCalendar_zero B)
      (slowUnitStepCalendar_step B) hsummable (slowCalendarStart B N)
  rw [sum_slowUnitStepCalendar_at_start B
    (fun n => G.finkCorrectedTargetHoldError W R z n) N] at hbound
  exact hbound

/-- Summability of the block-length-weighted hold errors is sufficient to
transport the fast corrected subsequence through the concrete slow calendar.
The resulting total error is bounded by the weighted hold total plus the fast
adjacent-step total. -/
theorem summable_finkCorrectedTargetStepError_slowCalendar
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (W : G.State → Payoff ι) (R : ℕ → G.State → Payoff ι)
    {U : ℝ} (z : ℕ → G.finkDomain U) (B : ℕ → ℝ)
    (hfast : Summable (fun n =>
      G.finkCorrectedTargetStepError W R z n))
    (hhold : Summable (fun n => (slowCalendarBlockLength B n : ℝ) *
      G.finkCorrectedTargetHoldError W R z n)) :
    Summable (fun t => G.finkCorrectedTargetStepError W
        (R ∘ slowUnitStepCalendar B)
        (z ∘ slowUnitStepCalendar B) t) ∧
      ∑' t, G.finkCorrectedTargetStepError W
          (R ∘ slowUnitStepCalendar B)
          (z ∘ slowUnitStepCalendar B) t ≤
        (∑' n, (slowCalendarBlockLength B n : ℝ) *
          G.finkCorrectedTargetHoldError W R z n) +
        ∑' n, G.finkCorrectedTargetStepError W R z n := by
  let ν := slowUnitStepCalendar B
  let e : ℕ → ℝ := fun t =>
    G.finkCorrectedTargetStepError W (R ∘ ν) (z ∘ ν) t
  let w : ℕ → ℝ := fun n => (slowCalendarBlockLength B n : ℝ) *
    G.finkCorrectedTargetHoldError W R z n
  have he0 : ∀ t, 0 ≤ e t := fun t =>
    G.finkCorrectedTargetStepError_nonneg W (R ∘ ν) (z ∘ ν) t
  have hw0 : ∀ n, 0 ≤ w n := fun n => mul_nonneg
    (Nat.cast_nonneg _) (G.finkCorrectedTargetHoldError_nonneg W R z n)
  have hprefix : ∀ T, ∑ t ∈ Finset.range T, e t ≤
      (∑' n, w n) + ∑' n,
        G.finkCorrectedTargetStepError W R z n := by
    intro T
    let N := ν T + 1
    have hTstart : T < slowCalendarStart B N := by
      have hinterval := (slowUnitStepCalendar_eq_iff B T (ν T)).1 rfl
      exact hinterval.2
    have hmono : ∑ t ∈ Finset.range T, e t ≤
        ∑ t ∈ Finset.range (slowCalendarStart B N), e t := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono hTstart.le) (fun t ht hnot => he0 t)
    have hactivation :=
      G.sum_finkCorrectedTargetStepError_slowCalendar_at_start_le
        W R z B hfast N
    have hweighted : ∑ n ∈ Finset.range N, w n ≤ ∑' n, w n :=
      hhold.sum_le_tsum (Finset.range N) (fun n _ => hw0 n)
    calc
      ∑ t ∈ Finset.range T, e t ≤
          ∑ t ∈ Finset.range (slowCalendarStart B N), e t := hmono
      _ ≤ ∑ n ∈ Finset.range N, w n +
          ∑' n, G.finkCorrectedTargetStepError W R z n := by
        simpa only [e, ν, w] using hactivation
      _ ≤ (∑' n, w n) +
          ∑' n, G.finkCorrectedTargetStepError W R z n :=
        add_le_add hweighted le_rfl
  have hesum : Summable e :=
    summable_of_sum_range_le he0 hprefix
  have hetotal : ∑' t, e t ≤ (∑' n, w n) +
      ∑' n, G.finkCorrectedTargetStepError W R z n :=
    Real.tsum_le_of_sum_range_le he0 hprefix
  simpa only [e, ν, w] using And.intro hesum hetotal

/-- A bounded calendar dilation relative to the root correction scale turns
summable next-layer hold defects into a summable repeated root hold bill.
This is the precise sufficient rate condition left by the slow-calendar
construction: the block length may grow, but not faster than the reciprocal
root scale along the selected boundary branch. -/
theorem summable_finkRelativeBoundaryWeightedHoldError_of_boundedDilation
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (B : ℕ → ℝ) (β : ℕ → ℝ)
    (hβpos : ∀ n, 0 < β n) (hβ1 : ∀ n, β n < 1)
    (W K : G.State → Payoff ι) {U : ℝ} (z : ℕ → G.finkDomain U)
    (hnext : Summable (fun n =>
      ‖G.finkContinuationResidualVector
          (G.finkNextReferenceVector (β n / (1 - β n))
            (G.finkRelativeBias (β n) W (z n)) W K) (z n)‖ +
        G.finkPositiveContinuationGainSum
          (G.finkNextReferenceVector (β n / (1 - β n))
            (G.finkRelativeBias (β n) W (z n)) W K) (z n)))
    (C : ℝ)
    (hdilation : ∀ n,
      (slowCalendarBlockLength B n : ℝ) *
        ((1 - β n) / β n + ‖G.finkValue (z n) - W‖) ≤ C) :
    Summable (fun n => (slowCalendarBlockLength B n : ℝ) *
      (‖G.finkContinuationResidualVector
          (W + G.finkReferenceCorrection (β n / (1 - β n))
            (G.finkRelativeBias (β n) W (z n)) K) (z n)‖ +
        G.finkPositiveContinuationGainSum
          (W + G.finkReferenceCorrection (β n / (1 - β n))
            (G.finkRelativeBias (β n) W (z n)) K) (z n))) := by
  refine Summable.of_nonneg_of_le (f := fun n => C *
    (‖G.finkContinuationResidualVector
        (G.finkNextReferenceVector (β n / (1 - β n))
          (G.finkRelativeBias (β n) W (z n)) W K) (z n)‖ +
      G.finkPositiveContinuationGainSum
        (G.finkNextReferenceVector (β n / (1 - β n))
          (G.finkRelativeBias (β n) W (z n)) W K) (z n))) ?_ ?_
    (hnext.mul_left C)
  · intro n
    exact mul_nonneg (Nat.cast_nonneg _)
      (add_nonneg (norm_nonneg _) (by
        unfold finkPositiveContinuationGainSum
        exact Finset.sum_nonneg fun p hp => le_max_right _ _))
  · intro n
    rw [G.finkRelativeBoundaryHoldError_eq
      (β n) (hβpos n) (hβ1 n) W K (z n)]
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hdilation n)
      (add_nonneg (norm_nonneg _) (by
        unfold finkPositiveContinuationGainSum
        exact Finset.sum_nonneg fun p hp => le_max_right _ _))

/-- Only eventual bounded dilation is needed for summability.  Arbitrarily bad
finitely many initial blocks contribute a finite amount and disappear after a
fixed shift. -/
theorem summable_finkRelativeBoundaryWeightedHoldError_of_eventuallyBoundedDilation
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (B : ℕ → ℝ) (β : ℕ → ℝ)
    (hβpos : ∀ n, 0 < β n) (hβ1 : ∀ n, β n < 1)
    (W K : G.State → Payoff ι) {U : ℝ} (z : ℕ → G.finkDomain U)
    (hnext : Summable (fun n =>
      ‖G.finkContinuationResidualVector
          (G.finkNextReferenceVector (β n / (1 - β n))
            (G.finkRelativeBias (β n) W (z n)) W K) (z n)‖ +
        G.finkPositiveContinuationGainSum
          (G.finkNextReferenceVector (β n / (1 - β n))
            (G.finkRelativeBias (β n) W (z n)) W K) (z n)))
    (C : ℝ)
    (hdilation : ∀ᶠ n in atTop,
      (slowCalendarBlockLength B n : ℝ) *
        ((1 - β n) / β n + ‖G.finkValue (z n) - W‖) ≤ C) :
    Summable (fun n => (slowCalendarBlockLength B n : ℝ) *
      (‖G.finkContinuationResidualVector
          (W + G.finkReferenceCorrection (β n / (1 - β n))
            (G.finkRelativeBias (β n) W (z n)) K) (z n)‖ +
        G.finkPositiveContinuationGainSum
          (W + G.finkReferenceCorrection (β n / (1 - β n))
            (G.finkRelativeBias (β n) W (z n)) K) (z n))) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hdilation
  apply (summable_nat_add_iff N).mp
  refine Summable.of_nonneg_of_le (f := fun n => C *
    (‖G.finkContinuationResidualVector
        (G.finkNextReferenceVector (β (n + N) / (1 - β (n + N)))
          (G.finkRelativeBias (β (n + N)) W (z (n + N))) W K)
        (z (n + N))‖ +
      G.finkPositiveContinuationGainSum
        (G.finkNextReferenceVector (β (n + N) / (1 - β (n + N)))
          (G.finkRelativeBias (β (n + N)) W (z (n + N))) W K)
        (z (n + N)))) ?_ ?_ ?_
  · intro n
    exact mul_nonneg (Nat.cast_nonneg _)
      (add_nonneg (norm_nonneg _) (by
        unfold finkPositiveContinuationGainSum
        exact Finset.sum_nonneg fun p hp => le_max_right _ _))
  · intro n
    rw [G.finkRelativeBoundaryHoldError_eq
      (β (n + N)) (hβpos (n + N)) (hβ1 (n + N)) W K (z (n + N))]
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hN (n + N) (Nat.le_add_left N n))
      (add_nonneg (norm_nonneg _) (by
        unfold finkPositiveContinuationGainSum
        exact Finset.sum_nonneg fun p hp => le_max_right _ _))
  · exact ((summable_nat_add_iff N).mpr hnext).mul_left C

/-- Variable-dilation version of the rate bridge.  Dilation need not be
bounded: it may grow according to `D`, provided the next-layer defect remains
summable after multiplication by that majorant.  This is strictly more
flexible than the constant-`C` criterion. -/
theorem summable_finkRelativeBoundaryRootBill_of_dilationMajorant
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (B : ℕ → ℝ) (β : ℕ → ℝ)
    (hβpos : ∀ n, 0 < β n) (hβ1 : ∀ n, β n < 1)
    (W K : G.State → Payoff ι) {U : ℝ} (z : ℕ → G.finkDomain U)
    (D : ℕ → ℝ)
    (hweightedNext : Summable (fun n =>
      D n * G.finkNextReferenceHoldError β W K z n))
    (hdilation : ∀ᶠ n in atTop,
      (slowCalendarBlockLength B n : ℝ) *
        ((1 - β n) / β n + ‖G.finkValue (z n) - W‖) ≤ D n) :
    Summable (fun n => (slowCalendarBlockLength B n : ℝ) *
      (((1 - β n) / β n + ‖G.finkValue (z n) - W‖) *
        G.finkNextReferenceHoldError β W K z n)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hdilation
  apply (summable_nat_add_iff N).mp
  refine Summable.of_nonneg_of_le
    (f := fun n => D (n + N) *
      G.finkNextReferenceHoldError β W K z (n + N)) ?_ ?_ ?_
  · intro n
    exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
      (add_nonneg
        (div_nonneg (sub_pos.mpr (hβ1 (n + N))).le (hβpos (n + N)).le)
        (norm_nonneg _))
      (by
        unfold finkNextReferenceHoldError finkPositiveContinuationGainSum
        exact add_nonneg (norm_nonneg _)
          (Finset.sum_nonneg fun p hp => le_max_right _ _)))
  · intro n
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (hN (n + N) (Nat.le_add_left N n)) (by
        unfold finkNextReferenceHoldError finkPositiveContinuationGainSum
        exact add_nonneg (norm_nonneg _)
          (Finset.sum_nonneg fun p hp => le_max_right _ _))
  · exact (summable_nat_add_iff N).mpr hweightedNext

/-- Quantitative form of the bounded-dilation hold estimate.  The whole
repeated root bill is at most the dilation bound times the total next-layer
hold defect. -/
theorem tsum_finkRelativeBoundaryWeightedHoldError_le_of_boundedDilation
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (B : ℕ → ℝ) (β : ℕ → ℝ)
    (hβpos : ∀ n, 0 < β n) (hβ1 : ∀ n, β n < 1)
    (W K : G.State → Payoff ι) {U : ℝ} (z : ℕ → G.finkDomain U)
    (hnext : Summable (fun n =>
      ‖G.finkContinuationResidualVector
          (G.finkNextReferenceVector (β n / (1 - β n))
            (G.finkRelativeBias (β n) W (z n)) W K) (z n)‖ +
        G.finkPositiveContinuationGainSum
          (G.finkNextReferenceVector (β n / (1 - β n))
            (G.finkRelativeBias (β n) W (z n)) W K) (z n)))
    (C : ℝ)
    (hdilation : ∀ n,
      (slowCalendarBlockLength B n : ℝ) *
        ((1 - β n) / β n + ‖G.finkValue (z n) - W‖) ≤ C) :
    ∑' n, (slowCalendarBlockLength B n : ℝ) *
      (‖G.finkContinuationResidualVector
          (W + G.finkReferenceCorrection (β n / (1 - β n))
            (G.finkRelativeBias (β n) W (z n)) K) (z n)‖ +
        G.finkPositiveContinuationGainSum
          (W + G.finkReferenceCorrection (β n / (1 - β n))
            (G.finkRelativeBias (β n) W (z n)) K) (z n)) ≤
      C * ∑' n,
        (‖G.finkContinuationResidualVector
            (G.finkNextReferenceVector (β n / (1 - β n))
              (G.finkRelativeBias (β n) W (z n)) W K) (z n)‖ +
          G.finkPositiveContinuationGainSum
            (G.finkNextReferenceVector (β n / (1 - β n))
              (G.finkRelativeBias (β n) W (z n)) W K) (z n)) := by
  have hweighted :=
    G.summable_finkRelativeBoundaryWeightedHoldError_of_boundedDilation
      B β hβpos hβ1 W K z hnext C hdilation
  calc
    _ ≤ ∑' n, C *
        (‖G.finkContinuationResidualVector
            (G.finkNextReferenceVector (β n / (1 - β n))
              (G.finkRelativeBias (β n) W (z n)) W K) (z n)‖ +
          G.finkPositiveContinuationGainSum
            (G.finkNextReferenceVector (β n / (1 - β n))
              (G.finkRelativeBias (β n) W (z n)) W K) (z n)) := by
      apply hweighted.tsum_le_tsum
      · intro n
        rw [G.finkRelativeBoundaryHoldError_eq
          (β n) (hβpos n) (hβ1 n) W K (z n)]
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hdilation n)
          (add_nonneg (norm_nonneg _) (by
            unfold finkPositiveContinuationGainSum
            exact Finset.sum_nonneg fun p hp => le_max_right _ _))
      · exact hnext.mul_left C
    _ = _ := by rw [tsum_mul_left]

/-- End-to-end slow-calendar form of the bounded-dilation criterion.  Fast
adjacent corrected drift and summable next-layer defects remain summable
after annealing whenever the calendar dilation is bounded in root-scale
units. -/
theorem summable_finkRelativeBoundaryStepError_slowCalendar_of_boundedDilation
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (B : ℕ → ℝ) (β : ℕ → ℝ)
    (hβpos : ∀ n, 0 < β n) (hβ1 : ∀ n, β n < 1)
    (W K : G.State → Payoff ι) {U : ℝ} (z : ℕ → G.finkDomain U)
    (hfast : Summable (fun n => G.finkCorrectedTargetStepError W
      (fun m => G.finkReferenceCorrection (β m / (1 - β m))
        (G.finkRelativeBias (β m) W (z m)) K) z n))
    (hnext : Summable (fun n =>
      ‖G.finkContinuationResidualVector
          (G.finkNextReferenceVector (β n / (1 - β n))
            (G.finkRelativeBias (β n) W (z n)) W K) (z n)‖ +
        G.finkPositiveContinuationGainSum
          (G.finkNextReferenceVector (β n / (1 - β n))
            (G.finkRelativeBias (β n) W (z n)) W K) (z n)))
    (C : ℝ)
    (hdilation : ∀ n,
      (slowCalendarBlockLength B n : ℝ) *
        ((1 - β n) / β n + ‖G.finkValue (z n) - W‖) ≤ C) :
    Summable (fun t => G.finkCorrectedTargetStepError W
      ((fun m => G.finkReferenceCorrection (β m / (1 - β m))
        (G.finkRelativeBias (β m) W (z m)) K) ∘
          slowUnitStepCalendar B)
      (z ∘ slowUnitStepCalendar B) t) := by
  let R : ℕ → G.State → Payoff ι := fun n =>
    G.finkReferenceCorrection (β n / (1 - β n))
      (G.finkRelativeBias (β n) W (z n)) K
  have hhold : Summable (fun n => (slowCalendarBlockLength B n : ℝ) *
      G.finkCorrectedTargetHoldError W R z n) := by
    have h :=
      G.summable_finkRelativeBoundaryWeightedHoldError_of_boundedDilation
        B β hβpos hβ1 W K z hnext C hdilation
    simpa only [finkCorrectedTargetHoldError, R] using h
  have hslow := G.summable_finkCorrectedTargetStepError_slowCalendar
    W R z B (by simpa only [R] using hfast) hhold
  simpa only [R] using hslow.1

/-- End-to-end slow-calendar criterion with an eventual rate bound.  The
calendar may have any finite number of badly dilated initial blocks. -/
theorem summable_finkRelativeBoundaryStepError_slowCalendar_of_eventuallyBoundedDilation
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (B : ℕ → ℝ) (β : ℕ → ℝ)
    (hβpos : ∀ n, 0 < β n) (hβ1 : ∀ n, β n < 1)
    (W K : G.State → Payoff ι) {U : ℝ} (z : ℕ → G.finkDomain U)
    (hfast : Summable (fun n => G.finkCorrectedTargetStepError W
      (fun m => G.finkReferenceCorrection (β m / (1 - β m))
        (G.finkRelativeBias (β m) W (z m)) K) z n))
    (hnext : Summable (fun n =>
      ‖G.finkContinuationResidualVector
          (G.finkNextReferenceVector (β n / (1 - β n))
            (G.finkRelativeBias (β n) W (z n)) W K) (z n)‖ +
        G.finkPositiveContinuationGainSum
          (G.finkNextReferenceVector (β n / (1 - β n))
            (G.finkRelativeBias (β n) W (z n)) W K) (z n)))
    (C : ℝ)
    (hdilation : ∀ᶠ n in atTop,
      (slowCalendarBlockLength B n : ℝ) *
        ((1 - β n) / β n + ‖G.finkValue (z n) - W‖) ≤ C) :
    Summable (fun t => G.finkCorrectedTargetStepError W
      ((fun m => G.finkReferenceCorrection (β m / (1 - β m))
        (G.finkRelativeBias (β m) W (z m)) K) ∘
          slowUnitStepCalendar B)
      (z ∘ slowUnitStepCalendar B) t) := by
  let R : ℕ → G.State → Payoff ι := fun n =>
    G.finkReferenceCorrection (β n / (1 - β n))
      (G.finkRelativeBias (β n) W (z n)) K
  have hhold : Summable (fun n => (slowCalendarBlockLength B n : ℝ) *
      G.finkCorrectedTargetHoldError W R z n) := by
    have h :=
      G.summable_finkRelativeBoundaryWeightedHoldError_of_eventuallyBoundedDilation
        B β hβpos hβ1 W K z hnext C hdilation
    simpa only [finkCorrectedTargetHoldError, R] using h
  have hslow := G.summable_finkCorrectedTargetStepError_slowCalendar
    W R z B (by simpa only [R] using hfast) hhold
  simpa only [R] using hslow.1

/-- Quantitative end-to-end form: after slowing, total corrected drift is
bounded by the fast adjacent bill plus `C` times the next-layer hold bill. -/
theorem tsum_finkRelativeBoundaryStepError_slowCalendar_le_of_boundedDilation
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (B : ℕ → ℝ) (β : ℕ → ℝ)
    (hβpos : ∀ n, 0 < β n) (hβ1 : ∀ n, β n < 1)
    (W K : G.State → Payoff ι) {U : ℝ} (z : ℕ → G.finkDomain U)
    (hfast : Summable (fun n => G.finkCorrectedTargetStepError W
      (fun m => G.finkReferenceCorrection (β m / (1 - β m))
        (G.finkRelativeBias (β m) W (z m)) K) z n))
    (hnext : Summable (fun n =>
      ‖G.finkContinuationResidualVector
          (G.finkNextReferenceVector (β n / (1 - β n))
            (G.finkRelativeBias (β n) W (z n)) W K) (z n)‖ +
        G.finkPositiveContinuationGainSum
          (G.finkNextReferenceVector (β n / (1 - β n))
            (G.finkRelativeBias (β n) W (z n)) W K) (z n)))
    (C : ℝ)
    (hdilation : ∀ n,
      (slowCalendarBlockLength B n : ℝ) *
        ((1 - β n) / β n + ‖G.finkValue (z n) - W‖) ≤ C) :
    ∑' t, G.finkCorrectedTargetStepError W
      ((fun m => G.finkReferenceCorrection (β m / (1 - β m))
        (G.finkRelativeBias (β m) W (z m)) K) ∘
          slowUnitStepCalendar B)
      (z ∘ slowUnitStepCalendar B) t ≤
      C * ∑' n,
        (‖G.finkContinuationResidualVector
            (G.finkNextReferenceVector (β n / (1 - β n))
              (G.finkRelativeBias (β n) W (z n)) W K) (z n)‖ +
          G.finkPositiveContinuationGainSum
            (G.finkNextReferenceVector (β n / (1 - β n))
              (G.finkRelativeBias (β n) W (z n)) W K) (z n)) +
      ∑' n, G.finkCorrectedTargetStepError W
        (fun m => G.finkReferenceCorrection (β m / (1 - β m))
          (G.finkRelativeBias (β m) W (z m)) K) z n := by
  let R : ℕ → G.State → Payoff ι := fun n =>
    G.finkReferenceCorrection (β n / (1 - β n))
      (G.finkRelativeBias (β n) W (z n)) K
  have hhold : Summable (fun n => (slowCalendarBlockLength B n : ℝ) *
      G.finkCorrectedTargetHoldError W R z n) := by
    have h :=
      G.summable_finkRelativeBoundaryWeightedHoldError_of_boundedDilation
        B β hβpos hβ1 W K z hnext C hdilation
    simpa only [finkCorrectedTargetHoldError, R] using h
  have hslow := G.summable_finkCorrectedTargetStepError_slowCalendar
    W R z B (by simpa only [R] using hfast) hhold
  have hweighted :=
    G.tsum_finkRelativeBoundaryWeightedHoldError_le_of_boundedDilation
      B β hβpos hβ1 W K z hnext C hdilation
  calc
    _ ≤ (∑' n, (slowCalendarBlockLength B n : ℝ) *
          G.finkCorrectedTargetHoldError W R z n) +
        ∑' n, G.finkCorrectedTargetStepError W R z n := by
      simpa only [R] using hslow.2
    _ ≤ _ := by
      exact add_le_add
        (by simpa only [finkCorrectedTargetHoldError, R] using hweighted)
        le_rfl

/-- A directly checkable version of the slow-calendar rate bridge.  It is
enough to control the next annealing cost against the current root scale;
the recursive block lengths then satisfy bounded dilation automatically. -/
theorem summable_finkRelativeBoundaryStepError_slowCalendar_of_adjacentGrowth
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (B : ℕ → ℝ) (β : ℕ → ℝ)
    (hβpos : ∀ n, 0 < β n) (hβ1 : ∀ n, β n < 1)
    (W K : G.State → Payoff ι) {U : ℝ} (z : ℕ → G.finkDomain U)
    (hfast : Summable (fun n => G.finkCorrectedTargetStepError W
      (fun m => G.finkReferenceCorrection (β m / (1 - β m))
        (G.finkRelativeBias (β m) W (z m)) K) z n))
    (hnext : Summable (fun n =>
      ‖G.finkContinuationResidualVector
          (G.finkNextReferenceVector (β n / (1 - β n))
            (G.finkRelativeBias (β n) W (z n)) W K) (z n)‖ +
        G.finkPositiveContinuationGainSum
          (G.finkNextReferenceVector (β n / (1 - β n))
            (G.finkRelativeBias (β n) W (z n)) W K) (z n)))
    (C : ℝ)
    (hadjacent : ∀ n,
      (((n + 1 : ℕ) : ℝ) * |B (n + 1)| + 2) *
        ((1 - β n) / β n + ‖G.finkValue (z n) - W‖) ≤ C) :
    Summable (fun t => G.finkCorrectedTargetStepError W
      ((fun m => G.finkReferenceCorrection (β m / (1 - β m))
        (G.finkRelativeBias (β m) W (z m)) K) ∘
          slowUnitStepCalendar B)
      (z ∘ slowUnitStepCalendar B) t) := by
  apply G.summable_finkRelativeBoundaryStepError_slowCalendar_of_boundedDilation
    B β hβpos hβ1 W K z hfast hnext C
  intro n
  have hscale0 : 0 ≤ (1 - β n) / β n +
      ‖G.finkValue (z n) - W‖ :=
    add_nonneg
      (div_nonneg (sub_pos.mpr (hβ1 n)).le (hβpos n).le)
      (norm_nonneg _)
  exact (mul_le_mul_of_nonneg_right
    (slowCalendarBlockLength_cast_le B n) hscale0).trans
      (hadjacent n)

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

/-- Repeating the indices of a Fink subsequence according to a unit-step
calendar preserves the exact edge-charge telescope. -/
theorem sum_indexedFinkRelativeSwitchError_unitStep
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ) {U₀ : ℝ}
    (z : ℕ → G.finkDomain U₀) (W : G.State → Payoff ι)
    (θ ν : ℕ → ℕ) (hν0 : ν 0 = 0)
    (hstep : ∀ t, ν (t + 1) = ν t ∨ ν (t + 1) = ν t + 1)
    (T : ℕ) :
    ∑ t ∈ Finset.range T,
        G.indexedFinkRelativeSwitchError β U z W (θ ∘ ν) t =
      ∑ n ∈ Finset.range (ν T),
        G.indexedFinkRelativeSwitchError β U z W θ n := by
  have hpoint : ∀ t,
      G.indexedFinkRelativeSwitchError β U z W (θ ∘ ν) t =
        if ν (t + 1) = ν t then 0
        else G.indexedFinkRelativeSwitchError β U z W θ (ν t) := by
    intro t
    by_cases hwait : ν (t + 1) = ν t
    · simp [indexedFinkRelativeSwitchError, hwait, Function.comp_apply]
    · have hadvance := (hstep t).resolve_left hwait
      rw [if_neg hwait]
      simp only [indexedFinkRelativeSwitchError, Function.comp_apply, hadvance]
  calc
    ∑ t ∈ Finset.range T,
        G.indexedFinkRelativeSwitchError β U z W (θ ∘ ν) t =
        ∑ t ∈ Finset.range T,
          (if ν (t + 1) = ν t then 0
          else G.indexedFinkRelativeSwitchError β U z W θ (ν t)) := by
      exact Finset.sum_congr rfl fun t _ => hpoint t
    _ = ∑ n ∈ Finset.range (ν T),
        G.indexedFinkRelativeSwitchError β U z W θ n :=
      sum_unitStepCalendar_eq ν
        (G.indexedFinkRelativeSwitchError β U z W θ) hν0 hstep T

/-- Along one subsequence, both the centered Fink bias and the root discount
scale have finite monotone-layer variation.  Consequently the entire sharp
switch charge telescopes to endpoint increases of finitely many scalar
scales, up to the universal variation constant of the convergent remainder. -/
theorem exists_regular_indexedFinkRelativeSwitchBound
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ) {U₀ : ℝ}
    (z : ℕ → G.finkDomain U₀) (W : G.State → Payoff ι)
    (hβ1 : ∀ n, β n < 1) (hβlim : Tendsto β atTop (nhds 1)) :
    ∃ (θ : ℕ → ℕ)
      (layers : List ((ℕ → ℝ) × (G.State → Payoff ι)))
      (remainder : ℕ → G.State → Payoff ι)
      (remainderLimit : G.State → Payoff ι),
      G.IsFinkBiasExpansion
          (fun n => G.finkRelativeBias (β n) W (z n))
          θ layers remainder remainderLimit ∧
      StrictMono
        ((fun n => β n / (1 - β n)) ∘ θ) ∧
      (∀ layer ∈ layers, StrictMono layer.1) ∧
      (∀ n, dist (remainder n) remainderLimit < ((2 : ℝ) ^ n)⁻¹) ∧
      ∀ N, ∑ t ∈ Finset.range N,
          G.indexedFinkRelativeSwitchError β U z W θ t ≤
        4 + (G.finkBiasScaleSum layers N -
          G.finkBiasScaleSum layers 0) +
        (β (θ N) / (1 - β (θ N)) -
          β (θ 0) / (1 - β (θ 0))) * U := by
  let a : ℕ → ℝ := fun n => β n / (1 - β n)
  let H : ℕ → G.State → Payoff ι :=
    fun n => G.finkRelativeBias (β n) W (z n)
  have ha : Tendsto a atTop atTop := by
    simpa only [a] using tendsto_finkDiscountScale_atTop β hβ1 hβlim
  obtain ⟨θ, layers, remainder, remainderLimit,
      hexpansion, haMono, hmono, hclose, hvariation⟩ :=
    G.exists_regular_finkBiasExpansion_with_scale H a ha
  refine ⟨θ, layers, remainder, remainderLimit, hexpansion,
    ?_, hmono, hclose, ?_⟩
  · exact haMono
  · intro N
    have haStep : ∀ n, a (θ n) ≤ a (θ (n + 1)) := by
      intro n
      exact haMono.monotone (Nat.le_succ n)
    have hscaleSum :
        ∑ t ∈ Finset.range N,
            |a (θ (t + 1)) - a (θ t)| * U =
          (a (θ N) - a (θ 0)) * U := by
      rw [← Finset.sum_mul]
      congr 1
      calc
        ∑ t ∈ Finset.range N, |a (θ (t + 1)) - a (θ t)| =
            ∑ t ∈ Finset.range N, (a (θ (t + 1)) - a (θ t)) := by
          apply Finset.sum_congr rfl
          intro t ht
          exact abs_of_nonneg (sub_nonneg.mpr (haStep t))
        _ = a (θ N) - a (θ 0) := by
          simpa only [Function.comp_apply] using
            sum_range_succ_sub_eq (a ∘ θ) N
    change
      ∑ t ∈ Finset.range N,
          (‖H (θ (t + 1)) - H (θ t)‖ +
            |a (θ (t + 1)) - a (θ t)| * U) ≤ _
    rw [Finset.sum_add_distrib, hscaleSum]
    simpa only [a, H] using
      add_le_add (hvariation N) (le_refl ((a (θ N) - a (θ 0)) * U))

/-- Regularizing the relative-bias expansion may thin an already-fast
hierarchy branch, but it preserves both nonnegative error series and cannot
increase either total. -/
theorem exists_regular_indexedFinkRelativeSwitchBound_preservingErrors
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ) {U₀ : ℝ}
    (z : ℕ → G.finkDomain U₀) (W : G.State → Payoff ι)
    (R : ℕ → G.State → Payoff ι) (aux : ℕ → ℝ)
    (hβ1 : ∀ n, β n < 1) (hβlim : Tendsto β atTop (nhds 1))
    (hfast : Summable (fun n =>
      G.finkCorrectedTargetStepError W R z n))
    (haux0 : ∀ n, 0 ≤ aux n) (haux : Summable aux) :
    ∃ (θ : ℕ → ℕ)
      (layers : List ((ℕ → ℝ) × (G.State → Payoff ι)))
      (remainder : ℕ → G.State → Payoff ι)
      (remainderLimit : G.State → Payoff ι),
      G.IsFinkBiasExpansion
          (fun n => G.finkRelativeBias (β n) W (z n))
          θ layers remainder remainderLimit ∧
      StrictMono
        ((fun n => β n / (1 - β n)) ∘ θ) ∧
      (∀ layer ∈ layers, StrictMono layer.1) ∧
      (∀ n, dist (remainder n) remainderLimit < ((2 : ℝ) ^ n)⁻¹) ∧
      (∀ N, ∑ t ∈ Finset.range N,
          G.indexedFinkRelativeSwitchError β U z W θ t ≤
        4 + (G.finkBiasScaleSum layers N -
          G.finkBiasScaleSum layers 0) +
        (β (θ N) / (1 - β (θ N)) -
          β (θ 0) / (1 - β (θ 0))) * U) ∧
      Summable (fun n => G.finkCorrectedTargetStepError W
        (R ∘ θ) (z ∘ θ) n) ∧
      (∑' n, G.finkCorrectedTargetStepError W
          (R ∘ θ) (z ∘ θ) n) ≤
        ∑' n, G.finkCorrectedTargetStepError W R z n ∧
      Summable (aux ∘ θ) ∧
      (∑' n, aux (θ n)) ≤ ∑' n, aux n := by
  obtain ⟨θ, layers, remainder, remainderLimit,
      hexpansion, haMono, hmono, hclose, hbound⟩ :=
    G.exists_regular_indexedFinkRelativeSwitchBound
      β U z W hβ1 hβlim
  have hθ : StrictMono θ := hexpansion.1
  have hfast' := G.summable_finkCorrectedTargetStepError_strictMono
    W R z hfast θ hθ
  have haux' : Summable (aux ∘ θ) :=
    haux.comp_injective hθ.injective
  have hauxTotal : (∑' n, aux (θ n)) ≤ ∑' n, aux n := by
    simpa only [Function.comp_def] using
      tsum_comp_le_tsum_of_inj haux haux0 hθ.injective
  exact ⟨θ, layers, remainder, remainderLimit,
    hexpansion, haMono, hmono, hclose, hbound,
    hfast'.1, hfast'.2, haux', hauxTotal⟩

/-- Block-calendar form of the regularized switch bound.  Waiting is free;
after any number of calendar stages, the total charge depends only on the
last radial layer reached. -/
theorem exists_regular_indexedFinkRelativeSwitchBound_unitStep
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ) {U₀ : ℝ}
    (z : ℕ → G.finkDomain U₀) (W : G.State → Payoff ι)
    (hβ1 : ∀ n, β n < 1) (hβlim : Tendsto β atTop (nhds 1)) :
    ∃ (θ : ℕ → ℕ)
      (layers : List ((ℕ → ℝ) × (G.State → Payoff ι)))
      (remainder : ℕ → G.State → Payoff ι)
      (remainderLimit : G.State → Payoff ι),
      G.IsFinkBiasExpansion
          (fun n => G.finkRelativeBias (β n) W (z n))
          θ layers remainder remainderLimit ∧
      StrictMono
        ((fun n => β n / (1 - β n)) ∘ θ) ∧
      (∀ layer ∈ layers, StrictMono layer.1) ∧
      (∀ n, dist (remainder n) remainderLimit < ((2 : ℝ) ^ n)⁻¹) ∧
      ∀ (ν : ℕ → ℕ), ν 0 = 0 →
        (∀ t, ν (t + 1) = ν t ∨ ν (t + 1) = ν t + 1) →
        ∀ T, ∑ t ∈ Finset.range T,
            G.indexedFinkRelativeSwitchError β U z W (θ ∘ ν) t ≤
          4 + (G.finkBiasScaleSum layers (ν T) -
            G.finkBiasScaleSum layers 0) +
          (β (θ (ν T)) / (1 - β (θ (ν T))) -
            β (θ 0) / (1 - β (θ 0))) * U := by
  obtain ⟨θ, layers, remainder, remainderLimit,
      hexpansion, haMono, hmono, hclose, hbound⟩ :=
    G.exists_regular_indexedFinkRelativeSwitchBound
      β U z W hβ1 hβlim
  refine ⟨θ, layers, remainder, remainderLimit,
    hexpansion, haMono, hmono, hclose, ?_⟩
  intro ν hν0 hstep T
  rw [G.sum_indexedFinkRelativeSwitchError_unitStep
    β U z W θ ν hν0 hstep T]
  exact hbound (ν T)

/-- The sharp Fink switching cost and the terminal scaled bias always admit
a common slow annealing calendar.  Thus the first, purely bias-theoretic half
of relative calendar selectability is unconditional. -/
theorem exists_finkRelativeAnnealingCalendar
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ) {U₀ : ℝ}
    (z : ℕ → G.finkDomain U₀) (W : G.State → Payoff ι)
    (hU : 0 ≤ U) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n < 1) (hβlim : Tendsto β atTop (nhds 1)) :
    ∃ κ : ℕ → ℕ,
      Tendsto κ atTop atTop ∧
      Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
        finkScaledBiasBound β U (κ T)) atTop (nhds 0) ∧
      Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
        ∑ t ∈ Finset.range T,
          G.indexedFinkRelativeSwitchError β U z W κ t)
        atTop (nhds 0) := by
  obtain ⟨θ, layers, remainder, remainderLimit,
      hexpansion, haMono, hmono, hclose, hbound⟩ :=
    G.exists_regular_indexedFinkRelativeSwitchBound_unitStep
      β U z W hβ1 hβlim
  let a : ℕ → ℝ := fun n => β (θ n) / (1 - β (θ n))
  let E : ℕ → ℝ := fun n =>
    4 + (G.finkBiasScaleSum layers n -
      G.finkBiasScaleSum layers 0) + (a n - a 0) * U
  let B : ℕ → ℝ := fun n => finkScaledBiasBound β U (θ n) + E n
  let ν : ℕ → ℕ := slowUnitStepCalendar B
  let κ : ℕ → ℕ := θ ∘ ν
  have hscaleMono : Monotone (G.finkBiasScaleSum layers) :=
    G.monotone_finkBiasScaleSum layers fun layer hlayer =>
      (hmono layer hlayer).monotone
  have haMono' : Monotone a := by
    simpa only [a, Function.comp_def] using haMono.monotone
  have hterminalNonneg : ∀ n, 0 ≤ finkScaledBiasBound β U (θ n) := by
    intro n
    exact mul_nonneg
      (div_nonneg (hβ0 (θ n)) (by linarith [hβ1 (θ n)])) hU
  have hEnonneg : ∀ n, 0 ≤ E n := by
    intro n
    have hlayer : 0 ≤ G.finkBiasScaleSum layers n -
        G.finkBiasScaleSum layers 0 :=
      sub_nonneg.mpr (hscaleMono (Nat.zero_le n))
    have hroot : 0 ≤ a n - a 0 :=
      sub_nonneg.mpr (haMono' (Nat.zero_le n))
    dsimp only [E]
    positivity
  have hterminalLeB : ∀ n,
      finkScaledBiasBound β U (θ n) ≤ B n := by
    intro n
    exact le_add_of_nonneg_right (hEnonneg n)
  have hELeB : ∀ n, E n ≤ B n := by
    intro n
    exact le_add_of_nonneg_left (hterminalNonneg n)
  have hνlim : Tendsto ν atTop atTop := by
    exact tendsto_slowUnitStepCalendar_atTop B
  have hκlim : Tendsto κ atTop atTop := by
    exact hexpansion.1.tendsto_atTop.comp hνlim
  have hBlim : Tendsto (fun T : ℕ => (T : ℝ)⁻¹ * B (ν T))
      atTop (nhds 0) := by
    exact tendsto_slowUnitStepCalendar_cost_div_zero B
  have hterminalLim : Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
      finkScaledBiasBound β U (κ T)) atTop (nhds 0) := by
    apply squeeze_zero
    · intro T
      exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg T))
        (hterminalNonneg (ν T))
    · intro T
      exact mul_le_mul_of_nonneg_left (hterminalLeB (ν T))
        (inv_nonneg.mpr (Nat.cast_nonneg T))
    · simpa only [κ, Function.comp_apply] using hBlim
  have hswitchNonneg : ∀ T, 0 ≤
      ∑ t ∈ Finset.range T,
        G.indexedFinkRelativeSwitchError β U z W κ t := by
    intro T
    apply Finset.sum_nonneg
    intro t ht
    unfold indexedFinkRelativeSwitchError
    exact add_nonneg (norm_nonneg _)
      (mul_nonneg (abs_nonneg _) hU)
  have hswitchLeB : ∀ T,
      ∑ t ∈ Finset.range T,
          G.indexedFinkRelativeSwitchError β U z W κ t ≤ B (ν T) := by
    intro T
    have hswitch := hbound ν (by simp [ν])
      (fun t => by simpa only [ν] using slowUnitStepCalendar_step B t) T
    have hswitchE :
        ∑ t ∈ Finset.range T,
            G.indexedFinkRelativeSwitchError β U z W κ t ≤ E (ν T) := by
      simpa only [κ, E, a, Function.comp_apply] using hswitch
    exact hswitchE.trans (hELeB (ν T))
  have hswitchLim : Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
      ∑ t ∈ Finset.range T,
        G.indexedFinkRelativeSwitchError β U z W κ t)
      atTop (nhds 0) := by
    apply squeeze_zero
    · intro T
      exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg T))
        (hswitchNonneg T)
    · intro T
      exact mul_le_mul_of_nonneg_left (hswitchLeB T)
        (inv_nonneg.mpr (Nat.cast_nonneg T))
    · exact hBlim
  exact ⟨κ, hκlim, hterminalLim, hswitchLim⟩

/-- Annealing data that preserves an already-fast hierarchy branch.  The
returned calendar is explicitly a slow unit-step calendar over a regularizing
strict subsequence, while both supplied nonnegative error totals can only
decrease under that regularization. -/
theorem exists_finkRelativeAnnealingCalendar_preservingErrors
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ) {U₀ : ℝ}
    (z : ℕ → G.finkDomain U₀) (W : G.State → Payoff ι)
    (R : ℕ → G.State → Payoff ι) (aux : ℕ → ℝ)
    (hU : 0 ≤ U) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n < 1) (hβlim : Tendsto β atTop (nhds 1))
    (hfast : Summable (fun n =>
      G.finkCorrectedTargetStepError W R z n))
    (haux0 : ∀ n, 0 ≤ aux n) (haux : Summable aux) :
    ∃ (θ : ℕ → ℕ) (B : ℕ → ℝ),
      let κ := θ ∘ slowUnitStepCalendar B
      Tendsto κ atTop atTop ∧
      Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
        finkScaledBiasBound β U (κ T)) atTop (nhds 0) ∧
      Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
        ∑ t ∈ Finset.range T,
          G.indexedFinkRelativeSwitchError β U z W κ t)
        atTop (nhds 0) ∧
      Summable (fun n => G.finkCorrectedTargetStepError W
        (R ∘ θ) (z ∘ θ) n) ∧
      (∑' n, G.finkCorrectedTargetStepError W
          (R ∘ θ) (z ∘ θ) n) ≤
        ∑' n, G.finkCorrectedTargetStepError W R z n ∧
      Summable (aux ∘ θ) ∧
      (∑' n, aux (θ n)) ≤ ∑' n, aux n := by
  obtain ⟨θ, layers, remainder, remainderLimit,
      hexpansion, haMono, hmono, hclose, hbound,
      hfast', hfastTotal, haux', hauxTotal⟩ :=
    G.exists_regular_indexedFinkRelativeSwitchBound_preservingErrors
      β U z W R aux hβ1 hβlim hfast haux0 haux
  let a : ℕ → ℝ := fun n => β (θ n) / (1 - β (θ n))
  let E : ℕ → ℝ := fun n =>
    4 + (G.finkBiasScaleSum layers n -
      G.finkBiasScaleSum layers 0) + (a n - a 0) * U
  let B : ℕ → ℝ := fun n => finkScaledBiasBound β U (θ n) + E n
  let ν : ℕ → ℕ := slowUnitStepCalendar B
  let κ : ℕ → ℕ := θ ∘ ν
  have hscaleMono : Monotone (G.finkBiasScaleSum layers) :=
    G.monotone_finkBiasScaleSum layers fun layer hlayer =>
      (hmono layer hlayer).monotone
  have haMono' : Monotone a := by
    simpa only [a, Function.comp_def] using haMono.monotone
  have hterminalNonneg : ∀ n, 0 ≤ finkScaledBiasBound β U (θ n) := by
    intro n
    exact mul_nonneg
      (div_nonneg (hβ0 (θ n)) (by linarith [hβ1 (θ n)])) hU
  have hEnonneg : ∀ n, 0 ≤ E n := by
    intro n
    have hlayer : 0 ≤ G.finkBiasScaleSum layers n -
        G.finkBiasScaleSum layers 0 :=
      sub_nonneg.mpr (hscaleMono (Nat.zero_le n))
    have hroot : 0 ≤ a n - a 0 :=
      sub_nonneg.mpr (haMono' (Nat.zero_le n))
    dsimp only [E]
    positivity
  have hterminalLeB : ∀ n,
      finkScaledBiasBound β U (θ n) ≤ B n := by
    intro n
    exact le_add_of_nonneg_right (hEnonneg n)
  have hELeB : ∀ n, E n ≤ B n := by
    intro n
    exact le_add_of_nonneg_left (hterminalNonneg n)
  have hνlim : Tendsto ν atTop atTop :=
    tendsto_slowUnitStepCalendar_atTop B
  have hκlim : Tendsto κ atTop atTop :=
    hexpansion.1.tendsto_atTop.comp hνlim
  have hBlim : Tendsto (fun T : ℕ => (T : ℝ)⁻¹ * B (ν T))
      atTop (nhds 0) :=
    tendsto_slowUnitStepCalendar_cost_div_zero B
  have hterminalLim : Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
      finkScaledBiasBound β U (κ T)) atTop (nhds 0) := by
    apply squeeze_zero
    · intro T
      exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg T))
        (hterminalNonneg (ν T))
    · intro T
      exact mul_le_mul_of_nonneg_left (hterminalLeB (ν T))
        (inv_nonneg.mpr (Nat.cast_nonneg T))
    · simpa only [κ, Function.comp_apply] using hBlim
  have hswitchNonneg : ∀ T, 0 ≤
      ∑ t ∈ Finset.range T,
        G.indexedFinkRelativeSwitchError β U z W κ t := by
    intro T
    apply Finset.sum_nonneg
    intro t ht
    unfold indexedFinkRelativeSwitchError
    exact add_nonneg (norm_nonneg _)
      (mul_nonneg (abs_nonneg _) hU)
  have hswitchLeB : ∀ T,
      ∑ t ∈ Finset.range T,
          G.indexedFinkRelativeSwitchError β U z W κ t ≤ B (ν T) := by
    intro T
    have hswitch :
        ∑ t ∈ Finset.range T,
            G.indexedFinkRelativeSwitchError β U z W κ t ≤ E (ν T) := by
      rw [G.sum_indexedFinkRelativeSwitchError_unitStep
        β U z W θ ν (by simp [ν])
        (fun t => by simpa only [ν] using slowUnitStepCalendar_step B t) T]
      simpa only [E, a] using hbound (ν T)
    exact hswitch.trans (hELeB (ν T))
  have hswitchLim : Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
      ∑ t ∈ Finset.range T,
        G.indexedFinkRelativeSwitchError β U z W κ t)
      atTop (nhds 0) := by
    apply squeeze_zero
    · intro T
      exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg T))
        (hswitchNonneg T)
    · intro T
      exact mul_le_mul_of_nonneg_left (hswitchLeB T)
        (inv_nonneg.mpr (Nat.cast_nonneg T))
    · exact hBlim
  exact ⟨θ, B, hκlim, hterminalLim, hswitchLim,
    hfast', hfastTotal, haux', hauxTotal⟩

/-- Weighted-error form of annealing preservation.  If `D n * aux n` is
already summable, regularization transports the weight with the selected
index, yielding the summable series `D (θ n) * aux (θ n)` on the returned
annealing branch. -/
theorem exists_finkRelativeAnnealingCalendar_preservingWeightedErrors
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ) {U₀ : ℝ}
    (z : ℕ → G.finkDomain U₀) (W : G.State → Payoff ι)
    (R : ℕ → G.State → Payoff ι) (aux D : ℕ → ℝ)
    (hU : 0 ≤ U) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n < 1) (hβlim : Tendsto β atTop (nhds 1))
    (hfast : Summable (fun n =>
      G.finkCorrectedTargetStepError W R z n))
    (haux0 : ∀ n, 0 ≤ aux n) (hD0 : ∀ n, 0 ≤ D n)
    (hweighted : Summable (fun n => D n * aux n)) :
    ∃ (θ : ℕ → ℕ) (B : ℕ → ℝ),
      let κ := θ ∘ slowUnitStepCalendar B
      Tendsto κ atTop atTop ∧
      Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
        finkScaledBiasBound β U (κ T)) atTop (nhds 0) ∧
      Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
        ∑ t ∈ Finset.range T,
          G.indexedFinkRelativeSwitchError β U z W κ t)
          atTop (nhds 0) ∧
      Summable (fun n => G.finkCorrectedTargetStepError W
        (R ∘ θ) (z ∘ θ) n) ∧
      Summable (fun n => D (θ n) * aux (θ n)) := by
  let weightedAux : ℕ → ℝ := fun n => D n * aux n
  have hweighted0 : ∀ n, 0 ≤ weightedAux n := fun n =>
    mul_nonneg (hD0 n) (haux0 n)
  obtain ⟨θ, B, hκ, hterminal, hswitch, hfast', hfastTotal,
      hweighted', hweightedTotal⟩ :=
    G.exists_finkRelativeAnnealingCalendar_preservingErrors
      β U z W R weightedAux hU hβ0 hβ1 hβlim hfast
        hweighted0 (by simpa only [weightedAux] using hweighted)
  refine ⟨θ, B, hκ, hterminal, hswitch, hfast', ?_⟩
  simpa only [weightedAux, Function.comp_def] using hweighted'

/-- Interior annealing package with an arbitrary block envelope.  Starting
from a vanishing zero-correction step error, the first subsequence makes both
its ordinary and `D`-weighted series summable; annealing regularization then
preserves those series.  The only missing input for the corresponding
selectability theorem is eventual domination of the returned block lengths
by the transported envelope `D ∘ θ`. -/
theorem exists_finkRelativeAnnealingCalendar_zeroCorrection_weighted
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (M : ℝ) {U : ℝ}
    (z : ℕ → G.finkDomain U) (W : G.State → Payoff ι)
    (hM : 0 ≤ M) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n < 1) (hβlim : Tendsto β atTop (nhds 1))
    (D : ℕ → ℝ) (hD0 : ∀ n, 0 ≤ D n)
    (hstep0 : Tendsto (fun n => G.finkCorrectedTargetStepError W
      (fun _ => 0) z n) atTop (nhds 0)) :
    ∃ (ψ θ : ℕ → ℕ) (B : ℕ → ℝ),
      StrictMono ψ ∧
      let Θ := ψ ∘ θ
      let κ := Θ ∘ slowUnitStepCalendar B
      Tendsto κ atTop atTop ∧
      Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
        finkScaledBiasBound β M (κ T)) atTop (nhds 0) ∧
      Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
        ∑ t ∈ Finset.range T,
          G.indexedFinkRelativeSwitchError β M z W κ t)
          atTop (nhds 0) ∧
      Summable (fun n => G.finkCorrectedTargetStepError W
        ((fun _ => 0) ∘ Θ) (z ∘ Θ) n) ∧
      Summable (fun n => D (θ n) *
        G.finkCorrectedTargetStepError W
          ((fun _ => 0) ∘ Θ) (z ∘ Θ) n) := by
  obtain ⟨ψ, hψ, hfast, hweighted⟩ :=
    G.exists_strictMono_summable_zeroCorrectionStepError_weighted
      W z D hD0 hstep0
  let βψ : ℕ → ℝ := β ∘ ψ
  let zψ : ℕ → G.finkDomain U := z ∘ ψ
  let R₀ : ℕ → G.State → Payoff ι := fun _ => 0
  let auxψ : ℕ → ℝ := fun n =>
    G.finkCorrectedTargetStepError W R₀ zψ n
  have hfastψ : Summable (fun n =>
      G.finkCorrectedTargetStepError W R₀ zψ n) := by
    simpa only [R₀, zψ, finkCorrectedTargetStepError,
      Function.comp_def, sub_self, norm_zero, add_zero] using hfast
  have haux0 : ∀ n, 0 ≤ auxψ n := fun n =>
    G.finkCorrectedTargetStepError_nonneg W R₀ zψ n
  have hweightedψ : Summable (fun n => D n * auxψ n) := by
    simpa only [auxψ, R₀, zψ, finkCorrectedTargetStepError,
      Function.comp_def, sub_self, norm_zero, add_zero] using hweighted
  obtain ⟨θ, B, hκ, hterminal, hswitch, hfast', hweighted'⟩ :=
    G.exists_finkRelativeAnnealingCalendar_preservingWeightedErrors
      βψ M zψ W R₀ auxψ D hM
      (fun n => hβ0 (ψ n)) (fun n => hβ1 (ψ n))
      (by simpa only [βψ, Function.comp_def] using
        hβlim.comp hψ.tendsto_atTop)
      hfastψ haux0 hD0 hweightedψ
  let Θ : ℕ → ℕ := ψ ∘ θ
  have hΘcalendar : Tendsto (Θ ∘ slowUnitStepCalendar B)
      atTop atTop := by
    simpa only [Θ, Function.comp_def] using hψ.tendsto_atTop.comp hκ
  refine ⟨ψ, θ, B, hψ, hΘcalendar, ?_, ?_, ?_, ?_⟩
  · simpa only [βψ, Θ, finkScaledBiasBound, Function.comp_def]
      using hterminal
  · simpa only [βψ, zψ, Θ, indexedFinkRelativeSwitchError,
      Function.comp_def] using hswitch
  · simpa only [R₀, zψ, Θ, finkCorrectedTargetStepError,
      Function.comp_def, sub_self, norm_zero, add_zero] using hfast'
  · simpa only [auxψ, R₀, zψ, Θ,
      finkCorrectedTargetStepError, Function.comp_def, sub_self, norm_zero,
      add_zero] using hweighted'

/-- The verified hierarchy and annealing construction can be joined while
retaining an arbitrary prescribed dilation envelope.  In the boundary branch
everything needed for corrected selectability is produced except comparison
of the concrete calendar block length with the transported weight
`D (θ n)`. -/
theorem FinkVerifiedReferenceResolution.relativeBias_weightedAnnealing_dichotomy
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (hβpos : ∀ n, 0 < β n) (hβ1 : ∀ n, β n < 1)
    (hβlim : Tendsto β atTop (nhds 1))
    (M : ℝ) (hM : 0 ≤ M) {U : ℝ}
    (z : ℕ → G.finkDomain U) (W : G.State → Payoff ι)
    (hV : Tendsto (fun n => G.finkValue (z n)) atTop (nhds W))
    (hresolution : G.FinkVerifiedReferenceResolution z
      (fun n => G.finkValue (z n))
      (fun n => β n / (1 - β n))
      (fun n => G.finkRelativeBias (β n) W (z n))
      (fun _ => W))
    (D : ℕ → ℝ) (hD0 : ∀ n, 0 ≤ D n) :
    (∃ (φ : ℕ → ℕ) (Jlim : G.State → Payoff ι),
      StrictMono φ ∧ Tendsto (fun n =>
        G.finkRelativeBias (β (φ n)) W (z (φ n)))
          atTop (nhds Jlim)) ∨
    ∃ (K : G.State → Payoff ι) (φ θ : ℕ → ℕ) (B : ℕ → ℝ),
      StrictMono φ ∧ ‖K‖ = 1 ∧
      let Θ := φ ∘ θ
      let κ := Θ ∘ slowUnitStepCalendar B
      Tendsto κ atTop atTop ∧
      Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
        finkScaledBiasBound β M (κ T)) atTop (nhds 0) ∧
      Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
        ∑ t ∈ Finset.range T,
          G.indexedFinkRelativeSwitchError β M z W κ t)
          atTop (nhds 0) ∧
      Summable (fun n => G.finkCorrectedTargetStepError W
        (G.finkRootCorrection β W K z ∘ Θ) (z ∘ Θ) n) ∧
      Summable (fun n => D (θ n) *
        G.finkNextReferenceHoldError β W K z (Θ n)) := by
  rcases hresolution.relativeBias_rootSummableStepAndWeightedNextHold_dichotomy
      G β hβpos hβ1 hβlim z W hV D hD0 with hinterior | hboundary
  · exact Or.inl hinterior
  · right
    obtain ⟨K, φ, hφ, hKnorm, hfast, hweighted⟩ := hboundary
    let βφ : ℕ → ℝ := β ∘ φ
    let zφ : ℕ → G.finkDomain U := z ∘ φ
    let Rφ : ℕ → G.State → Payoff ι :=
      G.finkRootCorrection β W K z ∘ φ
    let auxφ : ℕ → ℝ := G.finkNextReferenceHoldError β W K z ∘ φ
    have haux0 : ∀ n, 0 ≤ auxφ n := by
      intro n
      unfold auxφ finkNextReferenceHoldError finkPositiveContinuationGainSum
      exact add_nonneg (norm_nonneg _)
        (Finset.sum_nonneg fun p hp => le_max_right _ _)
    obtain ⟨θ, B, hκ, hterminal, hswitch, hfast', hweighted'⟩ :=
      G.exists_finkRelativeAnnealingCalendar_preservingWeightedErrors
        βφ M zφ W Rφ auxφ D hM
        (fun n => (hβpos (φ n)).le) (fun n => hβ1 (φ n))
        (by simpa only [βφ, Function.comp_def] using
          hβlim.comp hφ.tendsto_atTop)
        (by simpa only [Rφ, zφ, Function.comp_def] using hfast)
        haux0 hD0 (by simpa only [auxφ, Function.comp_def] using hweighted)
    let Θ : ℕ → ℕ := φ ∘ θ
    have hΘcalendar : Tendsto (Θ ∘ slowUnitStepCalendar B) atTop atTop := by
      simpa only [Θ, Function.comp_def] using hφ.tendsto_atTop.comp hκ
    refine ⟨K, φ, θ, B, hφ, hKnorm, hΘcalendar, ?_, ?_, ?_, ?_⟩
    · simpa only [βφ, Θ, finkScaledBiasBound, Function.comp_def] using hterminal
    · simpa only [βφ, zφ, Θ, indexedFinkRelativeSwitchError,
        Function.comp_def] using hswitch
    · simpa only [Rφ, zφ, Θ, Function.comp_def] using hfast'
    · simpa only [auxφ, Θ, Function.comp_def] using hweighted'

/-- Full annealing package.  Any ordinary value-error convergence survives
the slow calendar, while the exact boundary-plus-switch expression tends to
zero.  Only accumulated transition drift is absent from this package. -/
theorem exists_finkRelativeAnnealingCalendar_with_valueError
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ) {U₀ : ℝ}
    (z : ℕ → G.finkDomain U₀) (W : G.State → Payoff ι)
    (q : ℕ → ℝ) (hq : Tendsto q atTop (nhds 0))
    (hU : 0 ≤ U) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n < 1) (hβlim : Tendsto β atTop (nhds 1)) :
    ∃ κ : ℕ → ℕ,
      Tendsto κ atTop atTop ∧
      Tendsto (fun T : ℕ =>
        (finkScaledBiasBound β U (κ 0) +
            finkScaledBiasBound β U (κ T)) / (T : ℝ) +
          (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
            G.indexedFinkRelativeSwitchError β U z W κ t)
        atTop (nhds 0) ∧
      Tendsto (q ∘ κ) atTop (nhds 0) := by
  obtain ⟨κ, hκ, hterminal, hswitch⟩ :=
    G.exists_finkRelativeAnnealingCalendar
      β U z W hU hβ0 hβ1 hβlim
  have hinitial : Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
      finkScaledBiasBound β U (κ 0)) atTop (nhds 0) := by
    have ht := tendsto_const_div_atTop_nhds_zero_nat
      (finkScaledBiasBound β U (κ 0))
    simpa only [div_eq_inv_mul] using ht
  have hbias := (hinitial.add hterminal).add hswitch
  refine ⟨κ, hκ, ?_, hq.comp hκ⟩
  convert hbias using 1
  · funext T
    rw [div_eq_inv_mul]
    ring
  · simp

/-- Replacing calendar time `T` by `T + S` does not change a normalized
vanishing terminal cost. -/
theorem tendsto_inv_mul_timeShift_zero (f : ℕ → ℝ) (S : ℕ)
    (hf : Tendsto (fun T : ℕ => (T : ℝ)⁻¹ * f T)
      atTop (nhds 0)) :
    Tendsto (fun T : ℕ => (T : ℝ)⁻¹ * f (T + S))
      atTop (nhds 0) := by
  have hratio : Tendsto (fun T : ℕ =>
      (((T + S : ℕ) : ℝ) / (T : ℝ))) atTop (nhds 1) := by
    have hsmall := tendsto_const_div_atTop_nhds_zero_nat (S : ℝ)
    have hone := (tendsto_const_nhds (x := (1 : ℝ))).add hsmall
    have hone' : Tendsto (fun T : ℕ => 1 + (S : ℝ) / (T : ℝ))
        atTop (nhds 1) := by
      simpa only [add_zero] using hone
    apply hone'.congr'
    filter_upwards [eventually_gt_atTop 0] with T hT
    have hTreal : (T : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hT)
    rw [Nat.cast_add]
    field_simp [hTreal]
  have hcomp := hf.comp (tendsto_add_atTop_nat S)
  have hprod := hratio.mul hcomp
  have hprod' : Tendsto (fun T : ℕ =>
      (((T + S : ℕ) : ℝ) / (T : ℝ)) *
        (((T + S : ℕ) : ℝ)⁻¹ * f (T + S)))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, one_mul] using hprod
  apply hprod'.congr'
  filter_upwards [eventually_gt_atTop 0] with T hT
  have hTreal : (T : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hT)
  have hTSreal : (((T + S : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le hT (Nat.le_add_right T S)))
  field_simp [hTreal, hTSreal]

/-- A fixed time shift also preserves vanishing normalized prefix sums. -/
theorem tendsto_inv_mul_sum_range_timeShift_zero (e : ℕ → ℝ) (S : ℕ)
    (he : Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
      ∑ t ∈ Finset.range T, e t) atTop (nhds 0)) :
    Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
      ∑ t ∈ Finset.range T, e (t + S)) atTop (nhds 0) := by
  let P : ℕ → ℝ := fun T => ∑ t ∈ Finset.range T, e t
  have hP : Tendsto (fun T : ℕ => (T : ℝ)⁻¹ * P T)
      atTop (nhds 0) := by
    simpa only [P] using he
  have hPshift := tendsto_inv_mul_timeShift_zero P S hP
  have hconst : Tendsto (fun T : ℕ => (T : ℝ)⁻¹ * P S)
      atTop (nhds 0) := by
    have ht := tendsto_const_div_atTop_nhds_zero_nat (P S)
    simpa only [div_eq_inv_mul] using ht
  have hdiff := hPshift.sub hconst
  have hsum : ∀ T, ∑ t ∈ Finset.range T, e (t + S) =
      P (T + S) - P S := by
    intro T
    induction T with
    | zero => simp [P]
    | succ T ih =>
        rw [Finset.sum_range_succ, ih]
        rw [show T + 1 + S = (T + S) + 1 by omega]
        simp only [P, Finset.sum_range_succ]
        ring
  have hdiffZero : Tendsto (fun T : ℕ =>
      (T : ℝ)⁻¹ * P (T + S) - (T : ℝ)⁻¹ * P S)
      atTop (nhds 0) := by
    simpa only [sub_zero] using hdiff
  apply hdiffZero.congr'
  exact Filter.Eventually.of_forall fun T => by
    simp only
    rw [hsum T]
    ring

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

/-- Summable-step sufficient criterion for corrected calendar selectability.
It separates the final construction into the already-proved annealing limits,
ordinary value/correction convergence, and an arbitrarily small total mass of
the canonical corrected-target step error. -/
theorem isIndexedFinkCorrectedCalendarSelectable_of_summableStepError
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ) {U₀ : ℝ}
    (z : ℕ → G.finkDomain U₀) (W : G.State → Payoff ι)
    (R : ℕ → G.State → Payoff ι) (q : ℕ → ℝ)
    (hcalendar : ∀ ε : ℝ, 0 < ε → ∃ κ : ℕ → ℕ,
      Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
        finkScaledBiasBound β U (κ T)) atTop (nhds 0) ∧
      Tendsto (fun T : ℕ => (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
        G.indexedFinkRelativeSwitchError β U z W κ t)
          atTop (nhds 0) ∧
      Tendsto (q ∘ κ) atTop (nhds 0) ∧
      Tendsto (fun t => ‖R (κ t)‖) atTop (nhds 0) ∧
      ‖R (κ 0)‖ ≤ ε ∧
      Summable (fun t => G.finkCorrectedTargetStepError W
        (R ∘ κ) (z ∘ κ) t) ∧
      ∑' t, G.finkCorrectedTargetStepError W
        (R ∘ κ) (z ∘ κ) t ≤ ε) :
    G.IsIndexedFinkCorrectedCalendarSelectable β U z W R q := by
  intro η hη
  have hquarter : 0 < η / 4 := by linarith
  obtain ⟨κ, hterminal, hswitch, hq, hR, hRzero,
      hrsum, hrTotal⟩ := hcalendar (η / 4) hquarter
  let r : ℕ → ℝ := fun t => G.finkCorrectedTargetStepError W
    (R ∘ κ) (z ∘ κ) t
  have hr0 : ∀ t, 0 ≤ r t := fun t =>
    G.finkCorrectedTargetStepError_nonneg W (R ∘ κ) (z ∘ κ) t
  have hqavg : Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
      ∑ t ∈ Finset.range T, q (κ t)) atTop (nhds 0) := by
    simpa only [Function.comp_apply] using hq.cesaro
  have hRavg : Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
      ∑ t ∈ Finset.range T, ‖R (κ t)‖) atTop (nhds 0) := by
    simpa only [Function.comp_apply] using hR.cesaro
  have hinitial : Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
      finkScaledBiasBound β U (κ 0)) atTop (nhds 0) := by
    have ht := tendsto_const_div_atTop_nhds_zero_nat
      (finkScaledBiasBound β U (κ 0))
    simpa only [div_eq_inv_mul] using ht
  have hbias : Tendsto (fun T : ℕ =>
      (finkScaledBiasBound β U (κ 0) +
          finkScaledBiasBound β U (κ T)) / (T : ℝ) +
        (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
          G.indexedFinkRelativeSwitchError β U z W κ t)
      atTop (nhds 0) := by
    have ht := (hinitial.add hterminal).add hswitch
    convert ht using 1
    · funext T
      rw [div_eq_inv_mul]
      ring
    · simp
  obtain ⟨Nb, hNb⟩ := Metric.tendsto_atTop.mp hbias η hη
  obtain ⟨Nq, hNq⟩ := Metric.tendsto_atTop.mp hqavg
    (η / 4) hquarter
  obtain ⟨NR, hNR⟩ := Metric.tendsto_atTop.mp hRavg
    (η / 4) hquarter
  let T₀ := max 1 (max Nb (max Nq NR))
  refine ⟨κ, T₀, fun T hT => ?_⟩
  have hTone : 1 ≤ T := le_trans (le_max_left _ _) hT
  have hTpos : 0 < T := Nat.zero_lt_of_lt hTone
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hTpos
  have hNbT : Nb ≤ T :=
    le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) hT)
  have hNqT : Nq ≤ T :=
    le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) hT))
  have hNRT : NR ≤ T :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) hT))
  have hbiasLe :
      (finkScaledBiasBound β U (κ 0) +
          finkScaledBiasBound β U (κ T)) / (T : ℝ) +
        (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
          G.indexedFinkRelativeSwitchError β U z W κ t ≤ η := by
    have hb := hNb T hNbT
    rw [Real.dist_eq, sub_zero] at hb
    exact (le_abs_self _).trans hb.le
  have hqLe : (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
      q (κ t) ≤ η / 4 := by
    have ht := hNq T hNqT
    rw [Real.dist_eq, sub_zero] at ht
    exact (le_abs_self _).trans ht.le
  have hRLe : (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
      ‖R (κ t)‖ ≤ η / 4 := by
    have ht := hNR T hNRT
    rw [Real.dist_eq, sub_zero] at ht
    exact (le_abs_self _).trans ht.le
  have hprefix : ∀ t, ∑ k ∈ Finset.range t, r k ≤ ∑' k, r k := by
    intro t
    exact hrsum.sum_le_tsum (Finset.range t) (fun k _ => hr0 k)
  have hsum : (∑ t ∈ Finset.range T,
      (q (κ t) + ‖R (κ 0)‖ + ‖R (κ t)‖ +
        ∑ k ∈ Finset.range t, r k)) ≤
      ∑ t ∈ Finset.range T,
        (q (κ t) + ‖R (κ 0)‖ + ‖R (κ t)‖ + ∑' k, r k) := by
    exact Finset.sum_le_sum fun t _ =>
      add_le_add le_rfl (hprefix t)
  have hmul := mul_le_mul_of_nonneg_left hsum
    (inv_nonneg.mpr hTreal.le)
  have htarget : (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
      (q (κ t) + ‖R (κ 0)‖ + ‖R (κ t)‖ +
        ∑ k ∈ Finset.range t, r k) ≤ η := by
    calc
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
          (q (κ t) + ‖R (κ 0)‖ + ‖R (κ t)‖ +
            ∑ k ∈ Finset.range t, r k) ≤
          (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
            (q (κ t) + ‖R (κ 0)‖ + ‖R (κ t)‖ + ∑' k, r k) := hmul
      _ = (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, q (κ t) +
          ‖R (κ 0)‖ +
          (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, ‖R (κ t)‖ +
          ∑' k, r k := by
        simp_rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp [ne_of_gt hTreal]
      _ ≤ η / 4 + η / 4 + η / 4 + η / 4 := by
        exact add_le_add (add_le_add (add_le_add hqLe hRzero) hRLe)
          hrTotal
      _ = η := by ring
  exact ⟨hTpos, hbiasLe, htarget⟩

/-- One fixed annealing calendar with summable corrected drift already gives
corrected calendar selectability.  For a requested error budget, start the
same calendar sufficiently far in its summable tail; finite time shifts
preserve all normalized annealing limits. -/
theorem isIndexedFinkCorrectedCalendarSelectable_of_oneSummableCalendar
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ) {U₀ : ℝ}
    (z : ℕ → G.finkDomain U₀) (W : G.State → Payoff ι)
    (R : ℕ → G.State → Payoff ι) (q : ℕ → ℝ)
    (κ : ℕ → ℕ)
    (hterminal : Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
      finkScaledBiasBound β U (κ T)) atTop (nhds 0))
    (hswitch : Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
      ∑ t ∈ Finset.range T,
        G.indexedFinkRelativeSwitchError β U z W κ t)
      atTop (nhds 0))
    (hq : Tendsto (q ∘ κ) atTop (nhds 0))
    (hR : Tendsto (fun t => ‖R (κ t)‖) atTop (nhds 0))
    (hstep : Summable (fun t => G.finkCorrectedTargetStepError W
      (R ∘ κ) (z ∘ κ) t)) :
    G.IsIndexedFinkCorrectedCalendarSelectable β U z W R q := by
  apply G.isIndexedFinkCorrectedCalendarSelectable_of_summableStepError
  intro ε hε
  let r : ℕ → ℝ := fun t => G.finkCorrectedTargetStepError W
    (R ∘ κ) (z ∘ κ) t
  have hrsum : Summable r := by simpa only [r] using hstep
  have htail : Tendsto (fun S : ℕ => ∑' t : ℕ, r (t + S))
      atTop (nhds 0) := tendsto_sum_nat_add r
  obtain ⟨NR, hNR⟩ := Metric.tendsto_atTop.mp hR ε hε
  obtain ⟨Ne, hNe⟩ := Metric.tendsto_atTop.mp htail ε hε
  let S := max NR Ne
  have hRzero : ‖R (κ S)‖ ≤ ε := by
    have ht := hNR S (le_max_left _ _)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at ht
    exact ht.le
  have htailTotal : (∑' t : ℕ, r (t + S)) ≤ ε := by
    have ht := hNe S (le_max_right _ _)
    rw [Real.dist_eq, sub_zero] at ht
    exact (le_abs_self _).trans ht.le
  let κS : ℕ → ℕ := fun t => κ (t + S)
  have hterminalS : Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
      finkScaledBiasBound β U (κS T)) atTop (nhds 0) := by
    simpa only [κS] using
      (tendsto_inv_mul_timeShift_zero
        (fun n => finkScaledBiasBound β U (κ n)) S hterminal)
  let e : ℕ → ℝ := fun t =>
    G.indexedFinkRelativeSwitchError β U z W κ t
  have hswitchTail : Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
      ∑ t ∈ Finset.range T, e (t + S)) atTop (nhds 0) :=
    tendsto_inv_mul_sum_range_timeShift_zero e S (by
      simpa only [e] using hswitch)
  have hswitchS : Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
      ∑ t ∈ Finset.range T,
        G.indexedFinkRelativeSwitchError β U z W κS t)
      atTop (nhds 0) := by
    simpa only [e, κS, indexedFinkRelativeSwitchError,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hswitchTail
  have hqS : Tendsto (q ∘ κS) atTop (nhds 0) := by
    simpa only [κS, Function.comp_def] using
      hq.comp (tendsto_add_atTop_nat S)
  have hRS : Tendsto (fun t => ‖R (κS t)‖) atTop (nhds 0) := by
    simpa only [κS, Function.comp_def] using
      hR.comp (tendsto_add_atTop_nat S)
  have hstepEq : ∀ t,
      G.finkCorrectedTargetStepError W (R ∘ κS) (z ∘ κS) t =
        r (t + S) := by
    intro t
    simp only [r, κS, finkCorrectedTargetStepError, Function.comp_apply,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have htailSummable : Summable (fun t => r (t + S)) :=
    (summable_nat_add_iff S).mpr hrsum
  refine ⟨κS, hterminalS, hswitchS, hqS, hRS, ?_, ?_, ?_⟩
  · simpa only [κS, zero_add] using hRzero
  · exact htailSummable.congr (fun t => (hstepEq t).symm)
  · rw [tsum_congr hstepEq]
    exact htailTotal

/-- Slow-calendar sufficient criterion for corrected selectability.  It joins
a fast hierarchy subsequence to the concrete wait/advance calendar: the only
drift budget required is the weighted repeated hold bill plus the fast edge
bill. -/
theorem isIndexedFinkCorrectedCalendarSelectable_of_slowCalendar
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ) {U₀ : ℝ}
    (z : ℕ → G.finkDomain U₀) (W : G.State → Payoff ι)
    (R : ℕ → G.State → Payoff ι) (q : ℕ → ℝ)
    (hcalendar : ∀ ε : ℝ, 0 < ε →
      ∃ (θ : ℕ → ℕ) (B : ℕ → ℝ),
        let ν := slowUnitStepCalendar B
        let κ := θ ∘ ν
        Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
          finkScaledBiasBound β U (κ T)) atTop (nhds 0) ∧
        Tendsto (fun T : ℕ => (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
          G.indexedFinkRelativeSwitchError β U z W κ t)
            atTop (nhds 0) ∧
        Tendsto (q ∘ κ) atTop (nhds 0) ∧
        Tendsto (fun t => ‖R (κ t)‖) atTop (nhds 0) ∧
        ‖R (θ 0)‖ ≤ ε ∧
        Summable (fun n => G.finkCorrectedTargetStepError W
          (R ∘ θ) (z ∘ θ) n) ∧
        Summable (fun n => (slowCalendarBlockLength B n : ℝ) *
          G.finkCorrectedTargetHoldError W (R ∘ θ) (z ∘ θ) n) ∧
        (∑' n, (slowCalendarBlockLength B n : ℝ) *
            G.finkCorrectedTargetHoldError W (R ∘ θ) (z ∘ θ) n) +
          ∑' n, G.finkCorrectedTargetStepError W
            (R ∘ θ) (z ∘ θ) n ≤ ε) :
    G.IsIndexedFinkCorrectedCalendarSelectable β U z W R q := by
  apply G.isIndexedFinkCorrectedCalendarSelectable_of_summableStepError
  intro ε hε
  obtain ⟨θ, B, hterminal, hswitch, hq, hR, hRzero,
      hfast, hhold, htotal⟩ := hcalendar ε hε
  let ν := slowUnitStepCalendar B
  let κ := θ ∘ ν
  have hslow := G.summable_finkCorrectedTargetStepError_slowCalendar
    W (R ∘ θ) (z ∘ θ) B hfast hhold
  refine ⟨κ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [κ, ν] using hterminal
  · simpa only [κ, ν] using hswitch
  · simpa only [κ, ν] using hq
  · simpa only [κ, ν] using hR
  · simpa only [κ, ν, slowUnitStepCalendar_zero,
      Function.comp_apply] using hRzero
  · simpa only [κ, ν, Function.comp_def] using hslow.1
  · have hbound := hslow.2.trans htotal
    simpa only [κ, ν, Function.comp_def] using hbound

/-- Exact root-series form of the one-calendar criterion.  The genuinely
needed hypothesis is summability of block length times root scale times the
next-layer defect; uniform bounded dilation is only one way to obtain it. -/
theorem isIndexedFinkCorrectedCalendarSelectable_of_oneSummableRootBillBranch
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (hβpos : ∀ n, 0 < β n) (hβ1 : ∀ n, β n < 1)
    (hβlim : Tendsto β atTop (nhds 1))
    (U : ℝ) {U₀ : ℝ} (z : ℕ → G.finkDomain U₀)
    (W K : G.State → Payoff ι) (q : ℕ → ℝ)
    (hV : Tendsto (fun n => G.finkValue (z n)) atTop (nhds W))
    (hq : Tendsto q atTop (nhds 0))
    (θ : ℕ → ℕ) (B : ℕ → ℝ)
    (hκ : Tendsto (θ ∘ slowUnitStepCalendar B) atTop atTop)
    (hterminal : Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
      finkScaledBiasBound β U ((θ ∘ slowUnitStepCalendar B) T))
        atTop (nhds 0))
    (hswitch : Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
      ∑ t ∈ Finset.range T, G.indexedFinkRelativeSwitchError
        β U z W (θ ∘ slowUnitStepCalendar B) t) atTop (nhds 0))
    (hfast : Summable (fun n => G.finkCorrectedTargetStepError W
      (G.finkRootCorrection β W K z ∘ θ) (z ∘ θ) n))
    (hbill : Summable (fun n => (slowCalendarBlockLength B n : ℝ) *
      (((1 - β (θ n)) / β (θ n) +
          ‖G.finkValue (z (θ n)) - W‖) *
        G.finkNextReferenceHoldError β W K z (θ n)))) :
    G.IsIndexedFinkCorrectedCalendarSelectable β U z W
      (G.finkRootCorrection β W K z) q := by
  let ν := slowUnitStepCalendar B
  let κ := θ ∘ ν
  have hhold : Summable (fun n => (slowCalendarBlockLength B n : ℝ) *
      G.finkCorrectedTargetHoldError W
        (G.finkRootCorrection β W K z ∘ θ) (z ∘ θ) n) := by
    apply hbill.congr
    intro n
    have hfactor := G.finkRelativeBoundaryHoldError_eq
      (β (θ n)) (hβpos (θ n)) (hβ1 (θ n)) W K (z (θ n))
    simpa only [finkCorrectedTargetHoldError, finkRootCorrection,
      finkNextReferenceHoldError, Function.comp_apply] using
        congrArg (fun x => (slowCalendarBlockLength B n : ℝ) * x) hfactor.symm
  have hslow := G.summable_finkCorrectedTargetStepError_slowCalendar
    W (G.finkRootCorrection β W K z ∘ θ) (z ∘ θ) B hfast hhold
  have hslow' : Summable (fun t => G.finkCorrectedTargetStepError W
      (G.finkRootCorrection β W K z ∘ κ) (z ∘ κ) t) := by
    simpa only [κ, ν, Function.comp_def] using hslow.1
  have hroot := G.tendsto_finkReferenceCorrection_relativeBias_zero
    β hβpos hβ1 hβlim z W K hV
  have hrootNorm : Tendsto (fun n => ‖G.finkRootCorrection β W K z n‖)
      atTop (nhds 0) := by
    simpa only [finkRootCorrection, norm_zero] using hroot.norm
  apply G.isIndexedFinkCorrectedCalendarSelectable_of_oneSummableCalendar
    β U z W (G.finkRootCorrection β W K z) q κ
  · simpa only [κ, ν] using hterminal
  · simpa only [κ, ν] using hswitch
  · exact hq.comp (by simpa only [κ, ν] using hκ)
  · exact hrootNorm.comp (by simpa only [κ, ν] using hκ)
  · exact hslow'

/-- Interior-branch analogue of the root-bill criterion.  With zero
correction, a step is just its same-point hold error.  If that error was
selected summably against a block envelope `D`, eventual domination of the
actual block lengths by `D` makes the slowed calendar summable. -/
theorem isIndexedFinkCorrectedCalendarSelectable_of_oneWeightedZeroCorrectionBranch
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ) {U₀ : ℝ}
    (z : ℕ → G.finkDomain U₀) (W : G.State → Payoff ι)
    (q : ℕ → ℝ) (hq : Tendsto q atTop (nhds 0))
    (θ : ℕ → ℕ) (B D : ℕ → ℝ)
    (hκ : Tendsto (θ ∘ slowUnitStepCalendar B) atTop atTop)
    (hterminal : Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
      finkScaledBiasBound β U ((θ ∘ slowUnitStepCalendar B) T))
        atTop (nhds 0))
    (hswitch : Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
      ∑ t ∈ Finset.range T, G.indexedFinkRelativeSwitchError
        β U z W (θ ∘ slowUnitStepCalendar B) t) atTop (nhds 0))
    (hfast : Summable (fun n => G.finkCorrectedTargetStepError W
      ((fun _ => 0) ∘ θ) (z ∘ θ) n))
    (hweighted : Summable (fun n => D n *
      G.finkCorrectedTargetStepError W
        ((fun _ => 0) ∘ θ) (z ∘ θ) n))
    (hdilation : ∀ᶠ n in atTop, (slowCalendarBlockLength B n : ℝ) ≤ D n) :
    G.IsIndexedFinkCorrectedCalendarSelectable β U z W (fun _ => 0) q := by
  let zθ : ℕ → G.finkDomain U₀ := z ∘ θ
  let R₀ : ℕ → G.State → Payoff ι := fun _ => 0
  have hweightedHold : Summable (fun n => D n *
      G.finkCorrectedTargetHoldError W R₀ zθ n) := by
    simpa only [R₀, zθ, finkCorrectedTargetStepError,
      finkCorrectedTargetHoldError, Function.comp_def, sub_self, norm_zero,
      add_zero] using hweighted
  have hhold : Summable (fun n => (slowCalendarBlockLength B n : ℝ) *
      G.finkCorrectedTargetHoldError W R₀ zθ n) := by
    apply summable_mul_of_eventually_le_weight
      (fun n => G.finkCorrectedTargetHoldError W R₀ zθ n)
      (fun n => (slowCalendarBlockLength B n : ℝ)) D
    · exact fun n => G.finkCorrectedTargetHoldError_nonneg W R₀ zθ n
    · exact fun n => Nat.cast_nonneg _
    · exact hweightedHold
    · exact hdilation
  have hslow := G.summable_finkCorrectedTargetStepError_slowCalendar
    W R₀ zθ B (by
      simpa only [R₀, zθ, finkCorrectedTargetStepError,
        Function.comp_def, sub_self, norm_zero, add_zero] using hfast) hhold
  let κ := θ ∘ slowUnitStepCalendar B
  have hslow' : Summable (fun t => G.finkCorrectedTargetStepError W
      ((fun _ => 0) ∘ κ) (z ∘ κ) t) := by
    simpa only [κ, R₀, zθ, Function.comp_def] using hslow.1
  apply G.isIndexedFinkCorrectedCalendarSelectable_of_oneSummableCalendar
    β U z W (fun _ => 0) q κ
  · simpa only [κ] using hterminal
  · simpa only [κ] using hswitch
  · exact hq.comp (by simpa only [κ] using hκ)
  · simpa only [norm_zero] using
      (tendsto_const_nhds (x := (0 : ℝ)))
  · exact hslow'

/-- Variable-envelope form of the global branch criterion.  The concrete
calendar dilation may grow without bound, as long as it is eventually below
`D` and the next-reference defect has already been selected summably against
that same envelope. -/
theorem isIndexedFinkCorrectedCalendarSelectable_of_oneDilationMajorantBranch
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (hβpos : ∀ n, 0 < β n) (hβ1 : ∀ n, β n < 1)
    (hβlim : Tendsto β atTop (nhds 1))
    (U : ℝ) {U₀ : ℝ} (z : ℕ → G.finkDomain U₀)
    (W K : G.State → Payoff ι) (q : ℕ → ℝ)
    (hV : Tendsto (fun n => G.finkValue (z n)) atTop (nhds W))
    (hq : Tendsto q atTop (nhds 0))
    (θ : ℕ → ℕ) (B D : ℕ → ℝ)
    (hκ : Tendsto (θ ∘ slowUnitStepCalendar B) atTop atTop)
    (hterminal : Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
      finkScaledBiasBound β U ((θ ∘ slowUnitStepCalendar B) T))
        atTop (nhds 0))
    (hswitch : Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
      ∑ t ∈ Finset.range T, G.indexedFinkRelativeSwitchError
        β U z W (θ ∘ slowUnitStepCalendar B) t) atTop (nhds 0))
    (hfast : Summable (fun n => G.finkCorrectedTargetStepError W
      (G.finkRootCorrection β W K z ∘ θ) (z ∘ θ) n))
    (hweighted : Summable (fun n => D n *
      G.finkNextReferenceHoldError β W K z (θ n)))
    (hdilation : ∀ᶠ n in atTop, (slowCalendarBlockLength B n : ℝ) *
      ((1 - β (θ n)) / β (θ n) +
        ‖G.finkValue (z (θ n)) - W‖) ≤ D n) :
    G.IsIndexedFinkCorrectedCalendarSelectable β U z W
      (G.finkRootCorrection β W K z) q := by
  have hweighted' : Summable (fun n => D n *
      G.finkNextReferenceHoldError (β ∘ θ) W K (z ∘ θ) n) := by
    simpa only [finkNextReferenceHoldError, Function.comp_def] using hweighted
  have hbill :=
    G.summable_finkRelativeBoundaryRootBill_of_dilationMajorant
      B (β ∘ θ) (fun n => hβpos (θ n)) (fun n => hβ1 (θ n))
      W K (z ∘ θ) D hweighted' hdilation
  apply G.isIndexedFinkCorrectedCalendarSelectable_of_oneSummableRootBillBranch
    β hβpos hβ1 hβlim U z W K q hV hq θ B hκ hterminal hswitch hfast
  simpa only [finkNextReferenceHoldError, Function.comp_def] using hbill

/-- Global bounded-dilation form of the root criterion.  Unlike the
error-budgeted criterion below, this needs only one annealing branch: its
summable slowed drift can be made arbitrarily small by starting in a late
tail of that same branch. -/
theorem isIndexedFinkCorrectedCalendarSelectable_of_oneBoundedDilationBranch
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (hβpos : ∀ n, 0 < β n) (hβ1 : ∀ n, β n < 1)
    (hβlim : Tendsto β atTop (nhds 1))
    (U : ℝ) {U₀ : ℝ} (z : ℕ → G.finkDomain U₀)
    (W K : G.State → Payoff ι) (q : ℕ → ℝ)
    (hV : Tendsto (fun n => G.finkValue (z n)) atTop (nhds W))
    (hq : Tendsto q atTop (nhds 0))
    (θ : ℕ → ℕ) (B : ℕ → ℝ) (C : ℝ)
    (hκ : Tendsto (θ ∘ slowUnitStepCalendar B) atTop atTop)
    (hterminal : Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
      finkScaledBiasBound β U ((θ ∘ slowUnitStepCalendar B) T))
        atTop (nhds 0))
    (hswitch : Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
      ∑ t ∈ Finset.range T, G.indexedFinkRelativeSwitchError
        β U z W (θ ∘ slowUnitStepCalendar B) t) atTop (nhds 0))
    (hfast : Summable (fun n => G.finkCorrectedTargetStepError W
      (G.finkRootCorrection β W K z ∘ θ) (z ∘ θ) n))
    (hnext : Summable (G.finkNextReferenceHoldError β W K z ∘ θ))
    (hdilation : ∀ᶠ n in atTop, (slowCalendarBlockLength B n : ℝ) *
      ((1 - β (θ n)) / β (θ n) +
        ‖G.finkValue (z (θ n)) - W‖) ≤ C) :
    G.IsIndexedFinkCorrectedCalendarSelectable β U z W
      (G.finkRootCorrection β W K z) q := by
  have hweightedNext : Summable (fun n => C *
      G.finkNextReferenceHoldError (β ∘ θ) W K (z ∘ θ) n) := by
    simpa only [finkNextReferenceHoldError, Function.comp_def] using
      hnext.mul_left C
  have hbill :=
    G.summable_finkRelativeBoundaryRootBill_of_dilationMajorant
      B (β ∘ θ) (fun n => hβpos (θ n)) (fun n => hβ1 (θ n))
      W K (z ∘ θ) (fun _ => C) hweightedNext hdilation
  apply G.isIndexedFinkCorrectedCalendarSelectable_of_oneSummableRootBillBranch
    β hβpos hβ1 hβlim U z W K q hV hq θ B hκ hterminal hswitch hfast
  simpa only [finkNextReferenceHoldError, Function.comp_def] using hbill

/-- Root-rate form of the slow-calendar criterion.  A rate-compatible root
boundary branch is enough for corrected calendar selectability: its fast edge
bill and `C` times its next-reference hold bill must fit in the requested
error budget. -/
theorem isIndexedFinkCorrectedCalendarSelectable_of_rootRateCompatibleSlowCalendar
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (hβpos : ∀ n, 0 < β n) (hβ1 : ∀ n, β n < 1)
    (U : ℝ) {U₀ : ℝ} (z : ℕ → G.finkDomain U₀)
    (W K : G.State → Payoff ι) (q : ℕ → ℝ)
    (hcalendar : ∀ ε : ℝ, 0 < ε →
      ∃ (θ : ℕ → ℕ) (B : ℕ → ℝ) (C : ℝ),
        let ν := slowUnitStepCalendar B
        let κ := θ ∘ ν
        Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
          finkScaledBiasBound β U (κ T)) atTop (nhds 0) ∧
        Tendsto (fun T : ℕ => (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
          G.indexedFinkRelativeSwitchError β U z W κ t)
            atTop (nhds 0) ∧
        Tendsto (q ∘ κ) atTop (nhds 0) ∧
        Tendsto (fun t => ‖G.finkRootCorrection β W K z (κ t)‖)
          atTop (nhds 0) ∧
        ‖G.finkRootCorrection β W K z (θ 0)‖ ≤ ε ∧
        Summable (fun n => G.finkCorrectedTargetStepError W
          (G.finkRootCorrection β W K z ∘ θ) (z ∘ θ) n) ∧
        Summable (G.finkNextReferenceHoldError β W K z ∘ θ) ∧
        (∀ n, (slowCalendarBlockLength B n : ℝ) *
          ((1 - β (θ n)) / β (θ n) +
            ‖G.finkValue (z (θ n)) - W‖) ≤ C) ∧
        C * ∑' n, G.finkNextReferenceHoldError β W K z (θ n) +
          ∑' n, G.finkCorrectedTargetStepError W
            (G.finkRootCorrection β W K z ∘ θ) (z ∘ θ) n ≤ ε) :
    G.IsIndexedFinkCorrectedCalendarSelectable β U z W
      (G.finkRootCorrection β W K z) q := by
  apply G.isIndexedFinkCorrectedCalendarSelectable_of_slowCalendar
  intro ε hε
  obtain ⟨θ, B, C, hterminal, hswitch, hq, hR, hRzero,
      hfast, hnext, hdilation, hbudget⟩ := hcalendar ε hε
  have hnext' : Summable (fun n =>
      ‖G.finkContinuationResidualVector
          (G.finkNextReferenceVector
            ((β ∘ θ) n / (1 - (β ∘ θ) n))
            (G.finkRelativeBias ((β ∘ θ) n) W ((z ∘ θ) n)) W K)
          ((z ∘ θ) n)‖ +
        G.finkPositiveContinuationGainSum
          (G.finkNextReferenceVector
            ((β ∘ θ) n / (1 - (β ∘ θ) n))
            (G.finkRelativeBias ((β ∘ θ) n) W ((z ∘ θ) n)) W K)
          ((z ∘ θ) n)) := by
    simpa only [finkNextReferenceHoldError, Function.comp_def] using hnext
  have hholdExplicit :=
    G.summable_finkRelativeBoundaryWeightedHoldError_of_boundedDilation
      B (β ∘ θ) (fun n => hβpos (θ n)) (fun n => hβ1 (θ n))
      W K (z ∘ θ) hnext' C hdilation
  have hhold : Summable (fun n => (slowCalendarBlockLength B n : ℝ) *
      G.finkCorrectedTargetHoldError W
        (G.finkRootCorrection β W K z ∘ θ) (z ∘ θ) n) := by
    simpa only [finkCorrectedTargetHoldError, finkRootCorrection,
      Function.comp_apply] using hholdExplicit
  have hweightedExplicit :=
    G.tsum_finkRelativeBoundaryWeightedHoldError_le_of_boundedDilation
      B (β ∘ θ) (fun n => hβpos (θ n)) (fun n => hβ1 (θ n))
      W K (z ∘ θ) hnext' C hdilation
  have hweighted :
      ∑' n, (slowCalendarBlockLength B n : ℝ) *
          G.finkCorrectedTargetHoldError W
            (G.finkRootCorrection β W K z ∘ θ) (z ∘ θ) n ≤
        C * ∑' n, G.finkNextReferenceHoldError β W K z (θ n) := by
    simpa only [finkCorrectedTargetHoldError, finkRootCorrection,
      finkNextReferenceHoldError, Function.comp_apply] using hweightedExplicit
  refine ⟨θ, B, hterminal, hswitch, hq, hR, hRzero,
    hfast, hhold, ?_⟩
  exact (add_le_add hweighted le_rfl).trans hbudget

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

/-- Relative-bias version of the summable-drift criterion.  Together with
`exists_finkRelativeAnnealingCalendar_with_valueError`, this isolates the
remaining selection problem to finding calendars with arbitrarily small
summable transition drift. -/
theorem isIndexedFinkRelativeCalendarSelectable_of_summableDrift
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ) {U₀ : ℝ}
    (z : ℕ → G.finkDomain U₀) (W : G.State → Payoff ι)
    (q r : ℕ → ℝ)
    (hcalendar : ∀ ε : ℝ, 0 < ε → ∃ κ : ℕ → ℕ,
      Tendsto (fun T : ℕ => (T : ℝ)⁻¹ * finkScaledBiasBound β U (κ T))
        atTop (nhds 0) ∧
      Tendsto (fun T : ℕ => (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
        G.indexedFinkRelativeSwitchError β U z W κ t)
          atTop (nhds 0) ∧
      Tendsto (q ∘ κ) atTop (nhds 0) ∧
      (∀ t, 0 ≤ r (κ t)) ∧ Summable (r ∘ κ) ∧
      ∑' t, r (κ t) ≤ ε) :
    G.IsIndexedFinkRelativeCalendarSelectable β U z W q r := by
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
          G.indexedFinkRelativeSwitchError β U z W κ t)
      atTop (nhds 0) := by
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
  have hNbT : Nb ≤ T :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hT)
  have hNqT : Nq ≤ T :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hT)
  have hbiasLe :
      (finkScaledBiasBound β U (κ 0) +
          finkScaledBiasBound β U (κ T)) / (T : ℝ) +
        (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
          G.indexedFinkRelativeSwitchError β U z W κ t ≤ η := by
    have hb := hNb T hNbT
    rw [Real.dist_eq, sub_zero] at hb
    exact (le_abs_self _).trans hb.le
  have hqLe : (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
      q (κ t) ≤ η / 2 := by
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
    have hmul := mul_le_mul_of_nonneg_left hsum
      (inv_nonneg.mpr hTreal.le)
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
