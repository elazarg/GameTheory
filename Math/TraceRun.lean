import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Math.ProbabilityMassFunction

/-!
# State-trace run

A bounded "history-recorded" Kleisli iteration: starting from `[s₀]`,
apply a trace-aware step kernel `k` times, appending each new state to
the running trace. This is the abstraction inlined as
`Math.ParameterizedChain.pureRun`, `Dynamics.runDist`, and
`ObsModelCore.runDist` (in their unparameterized cores).

Companion to `Math.PMFIter` (which iterates a state-only kernel
without retaining history).
-/

set_option autoImplicit false

namespace Math
namespace TraceRun

variable {σ τ : Type*}

/-- Bounded state-trace run. Starting from `[s₀]`, apply `step` `k` times,
appending each new state to the running trace. -/
noncomputable def traceRun (step : List σ → PMF σ) (s₀ : σ) :
    Nat → PMF (List σ)
  | 0 => PMF.pure [s₀]
  | k + 1 => (traceRun step s₀ k).bind
      (fun ss => (step ss).bind (fun t => PMF.pure (ss ++ [t])))

@[simp] theorem traceRun_zero (step : List σ → PMF σ) (s₀ : σ) :
    traceRun step s₀ 0 = PMF.pure [s₀] := rfl

theorem traceRun_succ (step : List σ → PMF σ) (s₀ : σ) (k : Nat) :
    traceRun step s₀ (k + 1) =
      (traceRun step s₀ k).bind
        (fun ss => (step ss).bind (fun t => PMF.pure (ss ++ [t]))) := rfl

-- ============================================================================
-- Functional trace-kernel homomorphism
-- ============================================================================

/-- Functional trace-kernel homomorphism: a per-state projection `f : τ → σ`
intertwining the trace kernels via `List.map f`. -/
def IsTraceKernelHom (f : τ → σ)
    (step₁ : List σ → PMF σ) (step₂ : List τ → PMF τ) : Prop :=
  ∀ ts : List τ, step₁ (ts.map f) = (step₂ ts).map f

/-- Trace-run commutes with a functional trace-kernel homomorphism: running
`step₂` from `t₀` and projecting each trace via `List.map f` agrees with
running `step₁` from `f t₀`. -/
theorem traceRun_map_of_hom
    {f : τ → σ}
    {step₁ : List σ → PMF σ} {step₂ : List τ → PMF τ}
    (h : IsTraceKernelHom f step₁ step₂) (t₀ : τ) (k : Nat) :
    traceRun step₁ (f t₀) k = (traceRun step₂ t₀ k).map (List.map f) := by
  induction k with
  | zero =>
    simp [traceRun, PMF.pure_map]
  | succ k ih =>
    rw [traceRun_succ, traceRun_succ, ih, PMF.map_bind, PMF.bind_map]
    congr 1
    funext ts
    simp only [Function.comp]
    rw [h ts, PMF.bind_map, PMF.map_bind]
    congr 1
    funext t
    simp [PMF.pure_map, List.map_append, Function.comp]

end TraceRun
end Math
