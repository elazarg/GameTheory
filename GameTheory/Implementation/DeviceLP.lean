/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Implementation.Device
import Math.LinearProgramming.Certificates

/-!
# Linear-programming form of recommendation-device pointwise payments

This file connects the semantic on-path-payment feasibility predicate from
`GameTheory.Implementation.Device` to the local finite LP API.  It uses the
packing form `A x ≤ b, x ≥ 0` for a fixed pointwise budget `k`; the price is
the infimum over the budgets whose packing LP is feasible.  It also packages
semantic weighted lower-bound certificates as explicit raw dual/Farkas vectors
for the finite matrix encoding.
-/

open scoped BigOperators

namespace GameTheory

open Math.Probability
open Math.ProbabilityMassFunction

namespace KernelGame

variable {ι : Type} (G : KernelGame ι)

/-- Payment variables for the recommendation-device pointwise LP. -/
abbrev RecommendationPaymentLPCol : Type :=
  Profile G × ι

/-- Budget rows plus conditional-incentive rows for the recommendation-payment
LP.  Incentive rows are indexed by a player, an observed recommendation, and a
constant replacement action.  Rows with zero-probability recommendations are
made trivial by the matrix and RHS definitions below. -/
abbrev RecommendationPaymentLPRow : Type :=
  Profile G ⊕ (Σ i : ι, G.Strategy i × G.Strategy i)

/-- Turn a semantic payment array into the LP column vector. -/
def recommendationPaymentLPVector (p : Profile G → Payoff ι) :
    G.RecommendationPaymentLPCol → ℝ :=
  fun col => p col.1 col.2

/-- Matrix for the fixed-budget packing LP associated to pointwise
recommendation-device payments. -/
noncomputable def recommendationPaymentLPA [DecidableEq ι]
    (μ : PMF (Profile G)) :
    G.RecommendationPaymentLPRow → G.RecommendationPaymentLPCol → ℝ := by
  classical
  exact
    fun row col =>
      match row, col with
      | Sum.inl θ, (θ', _) =>
          if μ θ = 0 then 0 else if θ' = θ then 1 else 0
      | Sum.inr r, (θ, j) =>
          let i := r.1
          let si := r.2.1
          if hmass : pmfMass (μ := μ) (fun ω : Profile G => si = ω i) ≠ 0 then
            if θ i = si then
              if j = i then
                -((pmfCond (μ := μ) (fun ω : Profile G => si = ω i) hmass) θ).toReal
              else 0
            else 0
          else 0

/-- Right-hand side for the fixed-budget packing LP associated to pointwise
recommendation-device payments. -/
noncomputable def recommendationPaymentLPb [DecidableEq ι]
    (μ : PMF (Profile G)) (k : ℝ) : G.RecommendationPaymentLPRow → ℝ
  | Sum.inl θ => if μ θ = 0 then 0 else k
  | Sum.inr r =>
      let i := r.1
      let si := r.2.1
      let a := r.2.2
      if hmass : pmfMass (μ := μ) (fun ω : Profile G => si = ω i) ≠ 0 then
        -expect (pmfCond (μ := μ) (fun ω : Profile G => si = ω i) hmass)
          (fun θ => G.eu (Function.update θ i a) i - G.eu θ i)
      else 0

/-- Raw dual vector associated to semantic weighted certificate data.  The
budget rows receive the `γ` weights and the incentive rows receive the `λ`
weights. -/
noncomputable def recommendationPaymentDualVector
    (lam : (i : ι) → G.Strategy i → G.Strategy i → ℝ)
    (γ : Profile G → ℝ) :
    G.RecommendationPaymentLPRow → ℝ
  | Sum.inl θ => γ θ
  | Sum.inr r => lam r.1 r.2.1 r.2.2

theorem recommendationPaymentLPA_rowEval_budget [DecidableEq ι]
    [Fintype ι] [Fintype (Profile G)]
    {μ : PMF (Profile G)} {p : Profile G → Payoff ι} (θ : Profile G) :
    Math.LinearProgramming.rowEval (G.recommendationPaymentLPA μ)
        (G.recommendationPaymentLPVector p) (Sum.inl θ) =
      if μ θ = 0 then 0 else ∑ i, p θ i := by
  classical
  by_cases hθ : μ θ = 0
  · simp [Math.LinearProgramming.rowEval, recommendationPaymentLPA,
      recommendationPaymentLPVector, hθ]
  · rw [Math.LinearProgramming.rowEval]
    simp [recommendationPaymentLPA, recommendationPaymentLPVector, hθ,
      Fintype.sum_prod_type]

theorem recommendationPaymentLPA_rowEval_incentive [DecidableEq ι]
    [Fintype ι] [Fintype (Profile G)] {μ : PMF (Profile G)}
    {p : Profile G → Payoff ι} (i : ι) (si a : G.Strategy i) :
    Math.LinearProgramming.rowEval (G.recommendationPaymentLPA μ)
        (G.recommendationPaymentLPVector p)
        (Sum.inr (Sigma.mk i (si, a))) =
      if hmass : pmfMass (μ := μ) (fun θ : Profile G => si = θ i) ≠ 0 then
        -expect (pmfCond (μ := μ) (fun θ : Profile G => si = θ i) hmass)
          (fun θ => p θ i)
      else 0 := by
  classical
  by_cases hmass : pmfMass (μ := μ) (fun θ : Profile G => si = θ i) ≠ 0
  · rw [Math.LinearProgramming.rowEval]
    have hmask :
        (∑ θ : Profile G,
            if si = θ i then
              -(p θ i *
                ((if si = θ i then μ θ else 0).toReal /
                  (pmfMass (μ := μ) (fun ω : Profile G => si = ω i)).toReal))
            else 0) =
          -∑ θ : Profile G,
            p θ i *
              ((if si = θ i then μ θ else 0).toReal /
                (pmfMass (μ := μ) (fun ω : Profile G => si = ω i)).toReal) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro θ _
      by_cases hθ : si = θ i <;> simp [hθ]
    simpa [recommendationPaymentLPA, recommendationPaymentLPVector, hmass,
      Fintype.sum_prod_type, expect_eq_sum, pmfMask, eq_comm, mul_comm] using hmask
  · simp [Math.LinearProgramming.rowEval, recommendationPaymentLPA,
      recommendationPaymentLPVector, hmass]

theorem recommendationPaymentLPFeasible_iff [DecidableEq ι]
    [Fintype ι] [Fintype (Profile G)]
    {μ : PMF (Profile G)} {p : Profile G → Payoff ι} {k : ℝ} :
    Math.LinearProgramming.PrimalFeasible
        (G.recommendationPaymentLPA μ) (G.recommendationPaymentLPb μ k)
        (G.recommendationPaymentLPVector p) ↔
      G.RecommendationPaymentFeasible μ p k := by
  classical
  constructor
  · intro hLP
    refine ⟨?_, ?_, ?_⟩
    · intro θ i
      exact hLP.1 (θ, i)
    · intro θ hθ
      have hrow := hLP.2 (Sum.inl θ)
      rw [G.recommendationPaymentLPA_rowEval_budget θ] at hrow
      exact (show ∑ i, p θ i ≤ k from by
        simpa [recommendationPaymentLPb, hθ] using hrow)
    · intro i si hsi a
      have hrow := hLP.2 (Sum.inr (Sigma.mk i (si, a)))
      rw [G.recommendationPaymentLPA_rowEval_incentive i si a] at hrow
      simp [recommendationPaymentLPb, hsi] at hrow
      linarith
  · intro hp
    refine ⟨?_, ?_⟩
    · intro col
      exact hp.1 col.1 col.2
    · intro row
      cases row with
      | inl θ =>
          rw [G.recommendationPaymentLPA_rowEval_budget θ]
          by_cases hθ : μ θ = 0
          · simp [recommendationPaymentLPb, hθ]
          · simp [recommendationPaymentLPb, hθ, hp.2.1 θ hθ]
      | inr r =>
          rcases r with ⟨i, si, a⟩
          rw [G.recommendationPaymentLPA_rowEval_incentive i si a]
          by_cases hsi : pmfMass (μ := μ) (fun θ : Profile G => si = θ i) ≠ 0
          · simp [recommendationPaymentLPb, hsi]
            linarith [hp.2.2 i si hsi a]
          · simp [recommendationPaymentLPb, hsi]

theorem recommendationPaymentFeasible_iff_lpFeasible [DecidableEq ι]
    [Fintype ι] [Fintype (Profile G)]
    {μ : PMF (Profile G)} {p : Profile G → Payoff ι} {k : ℝ} :
    G.RecommendationPaymentFeasible μ p k ↔
      Math.LinearProgramming.PrimalFeasible
        (G.recommendationPaymentLPA μ) (G.recommendationPaymentLPb μ k)
        (G.recommendationPaymentLPVector p) :=
  (G.recommendationPaymentLPFeasible_iff).symm

/-- Weak-duality certificate for the recommendation-payment LP.  A dual
feasible vector for the zero objective has nonnegative value at every feasible
budget. -/
theorem recommendationPaymentLP_dualValue_nonneg_of_feasible [DecidableEq ι]
    [Fintype ι] [Fintype (Profile G)] [∀ i, Fintype (G.Strategy i)]
    {μ : PMF (Profile G)} {p : Profile G → Payoff ι} {k : ℝ}
    {y : G.RecommendationPaymentLPRow → ℝ}
    (hp : G.RecommendationPaymentFeasible μ p k)
    (hy : Math.LinearProgramming.DualFeasible
      (G.recommendationPaymentLPA μ) (fun _ : G.RecommendationPaymentLPCol => 0) y) :
    0 ≤ Math.LinearProgramming.dualValue (G.recommendationPaymentLPb μ k) y := by
  classical
  have hx : Math.LinearProgramming.PrimalFeasible
      (G.recommendationPaymentLPA μ) (G.recommendationPaymentLPb μ k)
      (G.recommendationPaymentLPVector p) :=
    (G.recommendationPaymentFeasible_iff_lpFeasible).mp hp
  have hweak := Math.LinearProgramming.weak_duality hx hy
  have hzero : Math.LinearProgramming.primalValue
      (fun _ : G.RecommendationPaymentLPCol => 0)
      (G.recommendationPaymentLPVector p) = 0 := by
    simp [Math.LinearProgramming.primalValue, Math.LinearProgramming.dot]
  linarith

/-- A negative zero-objective dual value certifies infeasibility of the
fixed-budget recommendation-payment LP. -/
theorem not_recommendationPaymentFeasible_of_dualValue_neg [DecidableEq ι]
    [Fintype ι] [Fintype (Profile G)] [∀ i, Fintype (G.Strategy i)]
    {μ : PMF (Profile G)} {p : Profile G → Payoff ι} {k : ℝ}
    {y : G.RecommendationPaymentLPRow → ℝ}
    (hy : Math.LinearProgramming.DualFeasible
      (G.recommendationPaymentLPA μ) (fun _ : G.RecommendationPaymentLPCol => 0) y)
    (hneg : Math.LinearProgramming.dualValue (G.recommendationPaymentLPb μ k) y < 0) :
    ¬ G.RecommendationPaymentFeasible μ p k := by
  intro hp
  have hnonneg := G.recommendationPaymentLP_dualValue_nonneg_of_feasible hp hy
  linarith

/-- A negative zero-objective dual value certifies that `k` is not a feasible
pointwise recommendation-payment budget. -/
theorem not_mem_recommendationPaymentImplementationCosts_of_dualValue_neg
    [DecidableEq ι] [Fintype ι] [Fintype (Profile G)] [∀ i, Fintype (G.Strategy i)]
    {μ : PMF (Profile G)} {k : ℝ} {y : G.RecommendationPaymentLPRow → ℝ}
    (hy : Math.LinearProgramming.DualFeasible
      (G.recommendationPaymentLPA μ) (fun _ : G.RecommendationPaymentLPCol => 0) y)
    (hneg : Math.LinearProgramming.dualValue (G.recommendationPaymentLPb μ k) y < 0) :
    k ∉ G.recommendationPaymentImplementationCosts μ := by
  intro hk
  rcases hk with ⟨p, hp⟩
  exact G.not_recommendationPaymentFeasible_of_dualValue_neg hy hneg hp

/-- Conversely, every infeasible fixed-budget recommendation-payment LP has a
negative zero-objective dual certificate. -/
theorem exists_dualValue_neg_of_not_mem_recommendationPaymentImplementationCosts
    [DecidableEq ι] [Fintype ι] [Fintype (Profile G)] [∀ i, Fintype (G.Strategy i)]
    {μ : PMF (Profile G)} {k : ℝ}
    (hk : k ∉ G.recommendationPaymentImplementationCosts μ) :
    ∃ y : G.RecommendationPaymentLPRow → ℝ,
      Math.LinearProgramming.DualFeasible
        (G.recommendationPaymentLPA μ) (fun _ : G.RecommendationPaymentLPCol => 0) y ∧
      Math.LinearProgramming.dualValue (G.recommendationPaymentLPb μ k) y < 0 := by
  classical
  refine Math.LinearProgramming.exists_dual_certificate_of_not_exists_primalFeasible ?_
  rintro ⟨x, hx⟩
  let p : Profile G → Payoff ι := fun θ i => x (θ, i)
  have hxvec :
      Math.LinearProgramming.PrimalFeasible
        (G.recommendationPaymentLPA μ) (G.recommendationPaymentLPb μ k)
        (G.recommendationPaymentLPVector p) := by
    convert hx using 1
    ext col
    rcases col with ⟨θ, i⟩
    rfl
  have hp : G.RecommendationPaymentFeasible μ p k :=
    (G.recommendationPaymentLPFeasible_iff).mp hxvec
  exact hk ⟨p, hp⟩

/-- Fixed-budget recommendation-payment infeasibility is equivalent to a
negative zero-objective dual/Farkas certificate. -/
theorem not_mem_recommendationPaymentImplementationCosts_iff_exists_dualValue_neg
    [DecidableEq ι] [Fintype ι] [Fintype (Profile G)] [∀ i, Fintype (G.Strategy i)]
    {μ : PMF (Profile G)} {k : ℝ} :
    k ∉ G.recommendationPaymentImplementationCosts μ ↔
      ∃ y : G.RecommendationPaymentLPRow → ℝ,
        Math.LinearProgramming.DualFeasible
          (G.recommendationPaymentLPA μ) (fun _ : G.RecommendationPaymentLPCol => 0) y ∧
        Math.LinearProgramming.dualValue (G.recommendationPaymentLPb μ k) y < 0 := by
  constructor
  · exact G.exists_dualValue_neg_of_not_mem_recommendationPaymentImplementationCosts
  · rintro ⟨y, hy, hneg⟩
    exact G.not_mem_recommendationPaymentImplementationCosts_of_dualValue_neg hy hneg

/-- If every budget below `L` has a negative zero-objective dual certificate,
then `L` is a lower bound on the pointwise recommendation-payment price. -/
theorem le_recommendationPaymentImplPrice_of_dual_certificates [DecidableEq ι]
    [Fintype ι] [Fintype (Profile G)] [∀ i, Fintype (G.Strategy i)]
    {μ : PMF (Profile G)} {L : ℝ}
    (hne : (G.recommendationPaymentImplementationCosts μ).Nonempty)
    (hcert : ∀ k, k < L →
      ∃ y : G.RecommendationPaymentLPRow → ℝ,
        Math.LinearProgramming.DualFeasible
          (G.recommendationPaymentLPA μ) (fun _ : G.RecommendationPaymentLPCol => 0) y ∧
        Math.LinearProgramming.dualValue (G.recommendationPaymentLPb μ k) y < 0) :
    L ≤ G.recommendationPaymentImplPrice μ := by
  refine G.le_recommendationPaymentImplPrice_of_forall_le hne ?_
  intro k hk
  exact le_of_not_gt fun hklt => by
    rcases hcert k hklt with ⟨y, hy, hneg⟩
    exact G.not_mem_recommendationPaymentImplementationCosts_of_dualValue_neg hy hneg hk

/-- The semantic incentive coefficient is the same conditional probability used
in the LP matrix, with zero coefficient outside the conditioning event. -/
theorem recommendationPaymentIncentiveCoeff_eq_if [DecidableEq ι]
    [∀ i, DecidableEq (G.Strategy i)]
    {μ : PMF (Profile G)} (i : ι) (si a : G.Strategy i) (θ : Profile G) :
    G.recommendationPaymentIncentiveCoeff μ i si a θ =
      if θ i = si then
        if hmass : pmfMass (μ := μ) (fun ω : Profile G => si = ω i) ≠ 0 then
          ((pmfCond (μ := μ) (fun ω : Profile G => si = ω i) hmass) θ).toReal
        else 0
      else 0 := by
  classical
  by_cases hθ : θ i = si
  · simp [recommendationPaymentIncentiveCoeff, hθ, eq_comm]
  · by_cases hmass : pmfMass (μ := μ) (fun ω : Profile G => si = ω i) ≠ 0
    · rw [recommendationPaymentIncentiveCoeff]
      simp only [dif_pos hmass]
      rw [pmfCond_apply]
      have hmask : pmfMask (μ := μ) (fun ω : Profile G => si = ω i) θ = 0 := by
        have hnot : ¬ si = θ i := by
          exact fun h => hθ h.symm
        simp [pmfMask, hnot]
      simp [hmask]
    · simp [recommendationPaymentIncentiveCoeff, hmass]

/-- Dual value of the raw vector associated to weighted certificate data. -/
theorem recommendationPaymentDualVector_dualValue [DecidableEq ι]
    [Fintype ι] [Fintype (Profile G)] [∀ i, Fintype (G.Strategy i)]
    {μ : PMF (Profile G)} {k : ℝ}
    (lam : (i : ι) → G.Strategy i → G.Strategy i → ℝ)
    (γ : Profile G → ℝ)
    (hγ_zero : ∀ θ, μ θ = 0 → γ θ = 0) :
    Math.LinearProgramming.dualValue (G.recommendationPaymentLPb μ k)
        (G.recommendationPaymentDualVector lam γ) =
      k * (∑ θ : Profile G, γ θ) -
        ∑ i, ∑ si : G.Strategy i, ∑ a : G.Strategy i,
          lam i si a * G.recommendationPaymentIncentiveGain μ i si a := by
  classical
  rw [Math.LinearProgramming.dualValue, Math.LinearProgramming.dot]
  rw [Fintype.sum_sum_type]
  rw [Fintype.sum_sigma]
  have hbudget :
      (∑ θ : Profile G,
          G.recommendationPaymentLPb μ k (Sum.inl θ) *
            G.recommendationPaymentDualVector lam γ (Sum.inl θ)) =
        k * ∑ θ : Profile G, γ θ := by
    calc
      (∑ θ : Profile G,
          G.recommendationPaymentLPb μ k (Sum.inl θ) *
            G.recommendationPaymentDualVector lam γ (Sum.inl θ))
          = ∑ θ : Profile G, k * γ θ := by
              refine Finset.sum_congr rfl ?_
              intro θ _
              by_cases hθ : μ θ = 0
              · simp [recommendationPaymentLPb, recommendationPaymentDualVector,
                  hθ, hγ_zero θ hθ]
              · simp [recommendationPaymentLPb, recommendationPaymentDualVector, hθ]
      _ = k * ∑ θ : Profile G, γ θ := by
              rw [Finset.mul_sum]
  have hincentive :
      (∑ i : ι, ∑ x : G.Strategy i × G.Strategy i,
          G.recommendationPaymentLPb μ k (Sum.inr (Sigma.mk i x)) *
            G.recommendationPaymentDualVector lam γ (Sum.inr (Sigma.mk i x))) =
        -∑ i, ∑ si : G.Strategy i, ∑ a : G.Strategy i,
          lam i si a * G.recommendationPaymentIncentiveGain μ i si a := by
    calc
      (∑ i : ι, ∑ x : G.Strategy i × G.Strategy i,
          G.recommendationPaymentLPb μ k (Sum.inr (Sigma.mk i x)) *
            G.recommendationPaymentDualVector lam γ (Sum.inr (Sigma.mk i x)))
          =
        ∑ i, ∑ si : G.Strategy i, ∑ a : G.Strategy i,
          (-G.recommendationPaymentIncentiveGain μ i si a) * lam i si a := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl ?_
            intro si _
            refine Finset.sum_congr rfl ?_
            intro a _
            by_cases hmass :
                pmfMass (μ := μ) (fun ω : Profile G => si = ω i) ≠ 0
            · simp [recommendationPaymentLPb, recommendationPaymentDualVector,
                recommendationPaymentIncentiveGain, hmass]
            · simp [recommendationPaymentLPb, recommendationPaymentDualVector,
                recommendationPaymentIncentiveGain, hmass]
      _ = -∑ i, ∑ si : G.Strategy i, ∑ a : G.Strategy i,
          lam i si a * G.recommendationPaymentIncentiveGain μ i si a := by
            simp [Finset.sum_neg_distrib, mul_comm]
  rw [hbudget, hincentive]
  ring

/-- Semantic weighted-certificate inequalities make the associated raw vector
dual-feasible for the matrix recommendation-payment LP. -/
theorem recommendationPaymentDualVector_dualFeasible [DecidableEq ι]
    [Fintype ι] [Fintype (Profile G)] [∀ i, Fintype (G.Strategy i)]
    {μ : PMF (Profile G)}
    (lam : (i : ι) → G.Strategy i → G.Strategy i → ℝ)
    (γ : Profile G → ℝ)
    (hlam_nonneg : ∀ i si a, 0 ≤ lam i si a)
    (hγ_nonneg : ∀ θ, 0 ≤ γ θ)
    (hγ_zero : ∀ θ, μ θ = 0 → γ θ = 0)
    (hcoeff : ∀ θ i,
      (∑ si : G.Strategy i, ∑ a : G.Strategy i,
        lam i si a * G.recommendationPaymentIncentiveCoeff μ i si a θ) ≤ γ θ) :
    Math.LinearProgramming.DualFeasible
      (G.recommendationPaymentLPA μ) (fun _ : G.RecommendationPaymentLPCol => 0)
      (G.recommendationPaymentDualVector lam γ) := by
  classical
  refine ⟨?_, ?_⟩
  · intro row
    cases row with
    | inl θ => exact hγ_nonneg θ
    | inr r =>
        exact hlam_nonneg r.1 r.2.1 r.2.2
  · intro col
    rcases col with ⟨θ, j⟩
    rw [Math.LinearProgramming.colEval]
    rw [Fintype.sum_sum_type]
    rw [Fintype.sum_sigma]
    have hbudget :
        (∑ θ' : Profile G,
            G.recommendationPaymentDualVector lam γ (Sum.inl θ') *
              G.recommendationPaymentLPA μ (Sum.inl θ') (θ, j)) =
          if μ θ = 0 then 0 else γ θ := by
      by_cases hθ : μ θ = 0
      · rw [if_pos hθ]
        refine Finset.sum_eq_zero ?_
        intro θ' _
        by_cases hEq : θ = θ'
        · subst θ'
          simp [recommendationPaymentDualVector, recommendationPaymentLPA, hθ]
        · simp [recommendationPaymentDualVector, recommendationPaymentLPA, hEq]
      · rw [if_neg hθ]
        rw [Finset.sum_eq_single θ]
        · simp [recommendationPaymentDualVector, recommendationPaymentLPA, hθ]
        · intro θ' _ hne
          have hEq : ¬ θ = θ' := by
            exact fun h => hne h.symm
          simp [recommendationPaymentDualVector, recommendationPaymentLPA, hEq]
        · intro hnot
          exact False.elim (hnot (Finset.mem_univ θ))
    have hincentive :
        (∑ i : ι, ∑ x : G.Strategy i × G.Strategy i,
            G.recommendationPaymentDualVector lam γ (Sum.inr (Sigma.mk i x)) *
              G.recommendationPaymentLPA μ (Sum.inr (Sigma.mk i x)) (θ, j)) =
          -∑ si : G.Strategy j, ∑ a : G.Strategy j,
            lam j si a * G.recommendationPaymentIncentiveCoeff μ j si a θ := by
      rw [Finset.sum_eq_single j]
      · rw [Fintype.sum_prod_type]
        calc
          (∑ si : G.Strategy j, ∑ a : G.Strategy j,
              G.recommendationPaymentDualVector lam γ (Sum.inr (Sigma.mk j (si, a))) *
                G.recommendationPaymentLPA μ (Sum.inr (Sigma.mk j (si, a))) (θ, j))
              =
            ∑ si : G.Strategy j, ∑ a : G.Strategy j,
              lam j si a *
                (if hmass :
                    pmfMass (μ := μ) (fun ω : Profile G => si = ω j) ≠ 0 then
                  if θ j = si then
                    -((pmfCond (μ := μ) (fun ω : Profile G => si = ω j) hmass) θ).toReal
                  else 0
                else 0) := by
                refine Finset.sum_congr rfl ?_
                intro si _
                refine Finset.sum_congr rfl ?_
                intro a _
                simp [recommendationPaymentDualVector, recommendationPaymentLPA]
          _ =
            -∑ si : G.Strategy j, ∑ a : G.Strategy j,
              lam j si a * G.recommendationPaymentIncentiveCoeff μ j si a θ := by
                rw [← Finset.sum_neg_distrib]
                refine Finset.sum_congr rfl ?_
                intro si _
                rw [← Finset.sum_neg_distrib]
                refine Finset.sum_congr rfl ?_
                intro a _
                rw [G.recommendationPaymentIncentiveCoeff_eq_if j si a θ]
                by_cases hθsi : θ j = si
                · by_cases hmass :
                    pmfMass (μ := μ) (fun ω : Profile G => si = ω j) ≠ 0
                  · simp [hθsi, hmass]
                  · simp [hθsi, hmass]
                · simp [hθsi]
      · intro i _ hij
        rw [Fintype.sum_prod_type]
        refine Finset.sum_eq_zero ?_
        intro si _
        refine Finset.sum_eq_zero ?_
        intro a _
        have hji : ¬ j = i := fun h => hij h.symm
        simp [recommendationPaymentDualVector, recommendationPaymentLPA, hji]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ j))
    rw [hbudget, hincentive]
    by_cases hθ : μ θ = 0
    · rw [if_pos hθ]
      have hle := hcoeff θ j
      rw [hγ_zero θ hθ] at hle
      linarith
    · rw [if_neg hθ]
      have hle := hcoeff θ j
      linarith

/-- Raw LP/Farkas form of the semantic weighted-certificate lower bound.  This
packages the weights as explicit dual vectors for the finite matrix encoding
and proves infeasibility below `L` by weak duality. -/
theorem le_recommendationPaymentImplPrice_of_weighted_lp_certificate [DecidableEq ι]
    [Fintype ι] [Fintype (Profile G)] [∀ i, Fintype (G.Strategy i)]
    {μ : PMF (Profile G)} {L : ℝ}
    (hne : (G.recommendationPaymentImplementationCosts μ).Nonempty)
    (lam : (i : ι) → G.Strategy i → G.Strategy i → ℝ)
    (γ : Profile G → ℝ)
    (hlam_nonneg : ∀ i si a, 0 ≤ lam i si a)
    (hγ_nonneg : ∀ θ, 0 ≤ γ θ)
    (hγ_zero : ∀ θ, μ θ = 0 → γ θ = 0)
    (hγ_sum : (∑ θ : Profile G, γ θ) = 1)
    (hcoeff : ∀ θ i,
      (∑ si : G.Strategy i, ∑ a : G.Strategy i,
        lam i si a * G.recommendationPaymentIncentiveCoeff μ i si a θ) ≤ γ θ)
    (hvalue : L ≤
      ∑ i, ∑ si : G.Strategy i, ∑ a : G.Strategy i,
        lam i si a * G.recommendationPaymentIncentiveGain μ i si a) :
    L ≤ G.recommendationPaymentImplPrice μ := by
  classical
  refine G.le_recommendationPaymentImplPrice_of_dual_certificates hne ?_
  intro k hk
  refine ⟨G.recommendationPaymentDualVector lam γ, ?_, ?_⟩
  · exact G.recommendationPaymentDualVector_dualFeasible
      lam γ hlam_nonneg hγ_nonneg hγ_zero hcoeff
  · rw [G.recommendationPaymentDualVector_dualValue lam γ hγ_zero, hγ_sum, mul_one]
    linarith

end KernelGame

end GameTheory
