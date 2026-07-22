/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.FinkSchedule

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

end StochasticGame
end GameTheory
