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

/-- A common upper bound for all pure unilateral continuation deviations is
also an upper bound for every mixed unilateral deviation. -/
theorem mixedDeviationContinuation_le_of_pure_bound
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (x : G.StationaryMixedProfile)
    (W : G.State → Payoff ι) (s : G.State) (who : ι) (c : ℝ)
    (hpure : ∀ d : G.Act who,
      expect (pmfPi (Function.update (x s) who (PMF.pure d)))
          (fun a => expect (G.transition s a) (fun s' => W s' who)) ≤ c)
    (dev : PMF (G.Act who)) :
    expect (pmfPi (Function.update (x s) who dev))
        (fun a => expect (G.transition s a) (fun s' => W s' who)) ≤ c := by
  let f : G.JointAct → ℝ := fun a =>
    expect (G.transition s a) (fun s' => W s' who)
  calc
    expect (pmfPi (Function.update (x s) who dev)) f =
        expect dev (fun d =>
          expect (pmfPi (Function.update (x s) who (PMF.pure d))) f) := by
      rw [pmfPi_update_bind, expect_bind]
    _ ≤ expect dev (fun _ => c) := expect_mono dev _ _ hpure
    _ = c := expect_const dev c

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
    filter_upwards [hv, hd] with k hk hdk
    exact ⟨hk, hdk⟩
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
      ∀ n,
        (∀ s who,
          |G.finkValue (z n) s who - G.finkValue zlim s who| ≤
            (((n + 1 : ℕ) : ℝ))⁻¹) ∧
        (∀ s who,
          |expect (pmfPi (G.finkProfile (z n) s)) (fun a =>
              expect (G.transition s a)
                (fun s' => G.finkValue zlim s' who)) -
            G.finkValue zlim s who| ≤ (((n + 1 : ℕ) : ℝ))⁻¹) ∧
        ∀ s who (dev : PMF (G.Act who)),
          expect (pmfPi (Function.update (G.finkProfile (z n) s) who dev))
              (fun a => expect (G.transition s a)
                (fun s' => G.finkValue zlim s' who)) ≤
            G.finkValue zlim s who + (((n + 1 : ℕ) : ℝ))⁻¹ := by
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
  refine ⟨β, z, zlim, hβ0, hβ1, ?_, ?_, ?_⟩
  · intro n
    simpa [β, z] using hfix (φ (ψ n))
  · have ht := hβlim.comp hψ.tendsto_atTop
    simpa only [β, Function.comp_def] using ht
  · intro n
    simpa only [z, Function.comp_apply] using happrox n

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
