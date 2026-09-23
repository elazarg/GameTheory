/-
# Pointwise convergence of finite-support laws

On finite carriers, pointwise mass convergence commutes with expectation and
finite independent products.
-/

import Mathlib.Topology.Instances.Real.Lemmas
import GameTheory.Math.Probability.FinDist

noncomputable section

namespace GameTheory.Math.Probability

open Filter

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

/-- Passing to a strictly increasing subsequence preserves pointwise mass
convergence. -/
theorem FinDistConvergesPointwise.subseq {α : Type*}
    {sequence : ℕ → FinDist α} {target : FinDist α}
    (h : FinDistConvergesPointwise sequence target)
    {subseq : ℕ → ℕ} (hsubseq : StrictMono subseq) :
    FinDistConvergesPointwise (fun n => sequence (subseq n)) target :=
  fun value => (h value).comp hsubseq.tendsto_atTop

/-- On a finite carrier, expectation converges when both the law and the
observable converge pointwise. -/
theorem FinDistConvergesPointwise.expect_varying {α : Type*} [Fintype α]
    {sequence : ℕ → FinDist α} {target : FinDist α}
    (h : FinDistConvergesPointwise sequence target)
    {observable : ℕ → α → ℝ} {targetObservable : α → ℝ}
    (hobservable : ∀ value,
      Tendsto (fun n => observable n value) atTop (nhds (targetObservable value))) :
    Tendsto (fun n => (sequence n).expect (observable n)) atTop
      (nhds (target.expect targetObservable)) := by
  simp_rw [FinDist.expect_eq_sum]
  exact tendsto_finsetSum Finset.univ fun value _ =>
    (h value).mul (hobservable value)

/-- Sequential composition preserves pointwise mass convergence on a finite
source carrier. The target carrier need not be finite. -/
theorem FinDistConvergesPointwise.bind {α β : Type*} [Fintype α]
    {sequence : ℕ → FinDist α} {target : FinDist α}
    (h : FinDistConvergesPointwise sequence target)
    {kernel : ℕ → α → FinDist β} {targetKernel : α → FinDist β}
    (hkernel : ∀ value,
      FinDistConvergesPointwise (fun n => kernel n value) (targetKernel value)) :
    FinDistConvergesPointwise (fun n => (sequence n).bind (kernel n))
      (target.bind targetKernel) := by
  intro value
  simp_rw [FinDist.prob_bind]
  exact h.expect_varying fun source => hkernel source value

/-- Pushforward preserves pointwise mass convergence on a finite source
carrier. The target carrier need not be finite. -/
theorem FinDistConvergesPointwise.map {α β : Type*} [Fintype α]
    {sequence : ℕ → FinDist α} {target : FinDist α}
    (h : FinDistConvergesPointwise sequence target) (f : α → β) :
    FinDistConvergesPointwise (fun n => (sequence n).map f) (target.map f) :=
  h.bind fun value => finDistConvergesPointwise_const (FinDist.pure (f value))

/-- A vanishing mixture with a fixed law converges to its other fixed branch.
The carrier need not be finite. -/
theorem finDistConvergesPointwise_mix_zero {α : Type*}
    (weight : ℕ → ℝ) (h0 : ∀ n, 0 ≤ weight n) (h1 : ∀ n, weight n ≤ 1)
    (hweight : Tendsto weight atTop (nhds 0)) (first second : FinDist α) :
    FinDistConvergesPointwise
      (fun n => FinDist.mix (weight n) (h0 n) (h1 n) first second) second := by
  intro value
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have h := (hweight.mul_const (first.prob value)).add
    ((hone.sub hweight).mul_const (second.prob value))
  simpa only [FinDist.prob_mix, zero_mul, sub_zero, one_mul, zero_add] using h

end GameTheory.Math.Probability
