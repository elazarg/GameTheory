/-
# Pointwise convergence of finite-support laws

This is the shared analytic interface for canonical `FinDist` laws.  It sits
above the probability representation and below game- or protocol-specific
consumers.  On finite carriers, pointwise mass convergence commutes with
expectation and finite independent products.
-/

import Mathlib.Topology.Instances.Real.Lemmas
import GameTheory.Probability.FinDist

noncomputable section

namespace GameTheory.Analysis

open Filter GameTheory Probability

/-- Pointwise convergence of finite-support laws through their real-valued
probability weights. -/
def FinDistConvergesPointwise {α : Type*}
    (sequence : ℕ → FinDist α) (target : FinDist α) : Prop :=
  ∀ value : α,
    Tendsto (fun n => (sequence n).prob value) atTop
      (nhds (target.prob value))

/-- A constant sequence of finite laws converges pointwise to that law. -/
theorem finDistConvergesPointwise_const {α : Type*} (law : FinDist α) :
    FinDistConvergesPointwise (fun _ => law) law :=
  fun _ => tendsto_const_nhds

/-- On a finite carrier, pointwise convergence of masses implies convergence
of every real expectation. -/
theorem FinDistConvergesPointwise.expect {α : Type*} [Fintype α]
    {sequence : ℕ → FinDist α} {target : FinDist α}
    (h : FinDistConvergesPointwise sequence target) (observable : α → ℝ) :
    Tendsto (fun n => (sequence n).expect observable) atTop
      (nhds (target.expect observable)) := by
  simp_rw [FinDist.expect_eq_sum]
  exact tendsto_finsetSum Finset.univ fun value _ =>
    (h value).mul_const (observable value)

/-- Pointwise-convergent coordinate laws have a pointwise-convergent finite
independent product. -/
theorem FinDistConvergesPointwise.pi {ι : Type*} [Fintype ι]
    {A : ι → Type*} {sequence : ℕ → ∀ i, FinDist (A i)} {target : ∀ i, FinDist (A i)}
    (h : ∀ i, FinDistConvergesPointwise (fun n => sequence n i) (target i)) :
    FinDistConvergesPointwise (fun n => FinDist.pi (sequence n)) (FinDist.pi target) := by
  intro profile
  simp_rw [FinDist.prob_pi]
  simpa using tendsto_finsetProd Finset.univ fun i _ => h i (profile i)

end GameTheory.Analysis
