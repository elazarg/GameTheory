import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Math.ProbabilityMassFunction

/-!
# Iterated PMF kernel

A probabilistic analogue of `Function.iterate` for PMF kernels:
`Math.PMFIter.iter step n b` is the distribution of `step` applied `n`
times starting from `b`.

The combinator factors out a pattern that appears inlined across several
kernel-iteration definitions in this library (see e.g.
`Math.ParameterizedChain.pureRun`, `StepwiseGame.runDist`,
`Languages.MAID.SOS.iterDist`).
-/

set_option autoImplicit false

namespace Math
namespace PMFIter

open Math.ProbabilityMassFunction

variable {B : Type*}

/-- Iterated PMF kernel: `iter step n b` is the distribution of `step`
applied `n` times starting from `b`. -/
noncomputable def iter (step : B → PMF B) : Nat → B → PMF B
  | 0,     b => PMF.pure b
  | n + 1, b => (step b).bind (iter step n)

@[simp] theorem iter_zero (step : B → PMF B) (b : B) :
    iter step 0 b = PMF.pure b := rfl

theorem iter_succ (step : B → PMF B) (b : B) (n : Nat) :
    iter step (n + 1) b = (step b).bind (iter step n) := rfl

theorem iter_succ' (step : B → PMF B) (b : B) (n : Nat) :
    iter step (n + 1) b = (iter step n b).bind step := by
  induction n generalizing b with
  | zero =>
    change (step b).bind PMF.pure = (PMF.pure b).bind step
    rw [PMF.bind_pure, PMF.pure_bind]
  | succ n ih =>
    change (step b).bind (iter step (n + 1))
        = ((step b).bind (iter step n)).bind step
    rw [PMF.bind_bind]
    congr 1
    funext b'
    exact ih b'

/-- If `step b` is a fixed point of the kernel, iteration from `b` stays
at `b`. -/
theorem iter_of_terminal {step : B → PMF B} {b : B}
    (h : step b = PMF.pure b) (n : Nat) :
    iter step n b = PMF.pure b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iter_succ, h, PMF.pure_bind]
    exact ih

/-- Extra fuel beyond the closure budget is harmless when every state in
the support of `iter step n b` is a fixed point of `step`. -/
theorem iter_stable_after_terminal
    {step : B → PMF B} {b : B} {n m : Nat}
    (h : ∀ b' ∈ (iter step n b).support, step b' = PMF.pure b')
    (hle : n ≤ m) :
    iter step m b = iter step n b := by
  induction m, hle using Nat.le_induction with
  | base => rfl
  | succ k _ ih =>
    rw [iter_succ', ih,
        bind_congr_on_support (iter step n b) step PMF.pure h]
    exact PMF.bind_pure _

-- ============================================================================
-- Functional kernel homomorphism
-- ============================================================================

variable {A : Type*}

/-- Functional kernel homomorphism: a state projection `f : B → A` that
intertwines `step₂` with `step₁` — taking a step in `B` and projecting
yields the same distribution as projecting first and stepping in `A`. -/
def IsKernelHom (f : B → A) (step₁ : A → PMF A) (step₂ : B → PMF B) : Prop :=
  ∀ b, step₁ (f b) = (step₂ b).map f

/-- Iteration commutes with a functional kernel homomorphism: iterating
`step₂` from `b` and projecting via `f` agrees with iterating `step₁`
from `f b`. -/
theorem iter_map_of_hom {f : B → A}
    {step₁ : A → PMF A} {step₂ : B → PMF B}
    (h : IsKernelHom f step₁ step₂) (n : Nat) (b : B) :
    iter step₁ n (f b) = (iter step₂ n b).map f := by
  induction n generalizing b with
  | zero => simp [PMF.pure_map]
  | succ n ih =>
    rw [iter_succ, h b, PMF.bind_map, iter_succ, PMF.map_bind]
    congr 1
    funext b'
    exact ih b'

end PMFIter
end Math
