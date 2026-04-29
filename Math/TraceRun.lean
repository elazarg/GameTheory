import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Math.Coupling
import Math.ProbabilityMassFunction

/-!
# State-trace run

A bounded "history-recorded" Kleisli iteration: starting from `[s₀]`,
apply a trace-aware step kernel `k` times, appending each new state to
the running trace.

This is the abstraction inlined as `Math.ParameterizedChain.pureRun`,
`Dynamics.runDist`, and `ObsModelCore.runDist` (in their unparameterized
cores). Companion to `Math.PMFIter` (which iterates a state-only kernel
without retaining history).

Probabilistic bisimulation lifts through `traceRun` just as it does for
state-only iteration: see `traceRun_HasCoupling_of_bisim`.
-/

set_option autoImplicit false

namespace Math
namespace TraceRun

open Math.Coupling
open Math.ProbabilityMassFunction (pushforward)

variable {σ τ : Type*}

/-- Bounded state-trace run. Starting from `[s₀]`, apply `step` `k` times,
appending each new state to the running trace. -/
noncomputable def traceRun (step : List σ → PMF σ) (s₀ : σ) :
    Nat → PMF (List σ)
  | 0 => PMF.pure [s₀]
  | k + 1 => (traceRun step s₀ k).bind
      (fun ss => pushforward (step ss) (fun t => ss ++ [t]))

@[simp] theorem traceRun_zero (step : List σ → PMF σ) (s₀ : σ) :
    traceRun step s₀ 0 = PMF.pure [s₀] := rfl

theorem traceRun_succ (step : List σ → PMF σ) (s₀ : σ) (k : Nat) :
    traceRun step s₀ (k + 1) =
      (traceRun step s₀ k).bind
        (fun ss => (step ss).bind (fun t => PMF.pure (ss ++ [t]))) := rfl

-- ============================================================================
-- Probabilistic bisimulation on trace kernels
-- ============================================================================

/-- Probabilistic bisimulation between two trace-aware PMF kernels: a
relation on traces such that for every related pair of traces, the
next-state distributions admit a coupling making the *extended* traces
related. -/
structure TraceKernelBisim (step₁ : List σ → PMF σ) (step₂ : List τ → PMF τ) where
  rel : List σ → List τ → Prop
  step_compat : ∀ ss ts, rel ss ts →
    HasCoupling (fun s t => rel (ss ++ [s]) (ts ++ [t])) (step₁ ss) (step₂ ts)

/-- Trace-run lifts probabilistic bisimulation: if `bs.rel [s₀] [t₀]`
holds, the `k`-step trace distributions admit a coupling supported on
`bs.rel`. -/
noncomputable def traceRun_HasCoupling_of_bisim
    {step₁ : List σ → PMF σ} {step₂ : List τ → PMF τ}
    (bs : TraceKernelBisim step₁ step₂) (s₀ : σ) (t₀ : τ)
    (h : bs.rel [s₀] [t₀]) (k : Nat) :
    HasCoupling bs.rel (traceRun step₁ s₀ k) (traceRun step₂ t₀ k) := by
  induction k with
  | zero =>
    simp only [traceRun_zero]
    exact HasCoupling.pure [s₀] [t₀] h
  | succ k ih =>
    rw [traceRun_succ, traceRun_succ]
    refine ih.bind (fun ss ts h_st => ?_)
    refine (bs.step_compat ss ts h_st).bind (fun s t h_inner => ?_)
    exact HasCoupling.pure (ss ++ [s]) (ts ++ [t]) h_inner

-- ============================================================================
-- Functional special case
-- ============================================================================

/-- Functional trace-kernel homomorphism: a per-state projection `f : τ → σ`
intertwining the trace kernels via `List.map f`. -/
def IsTraceKernelHom (f : τ → σ)
    (step₁ : List σ → PMF σ) (step₂ : List τ → PMF τ) : Prop :=
  ∀ ts : List τ, step₁ (ts.map f) = (step₂ ts).map f

/-- A functional trace-kernel homomorphism induces a probabilistic
trace-bisimulation with relation `fun ss ts => ss = ts.map f`. -/
noncomputable def TraceKernelBisim.ofTraceKernelHom
    {f : τ → σ} {step₁ : List σ → PMF σ} {step₂ : List τ → PMF τ}
    (h : IsTraceKernelHom f step₁ step₂) :
    TraceKernelBisim step₁ step₂ where
  rel := fun ss ts => ss = ts.map f
  step_compat := fun ss ts h_st => by
    subst h_st
    rw [h ts]
    refine HasCoupling.mono ?_ (HasCoupling.ofProj (step₂ ts))
    intro s t hst
    simp [List.map_append, hst]

/-- Trace-run commutes with a functional trace-kernel homomorphism.
Corollary of `traceRun_HasCoupling_of_bisim` via the projection bridge. -/
theorem traceRun_map_of_hom
    {f : τ → σ}
    {step₁ : List σ → PMF σ} {step₂ : List τ → PMF τ}
    (h : IsTraceKernelHom f step₁ step₂) (t₀ : τ) (k : Nat) :
    traceRun step₁ (f t₀) k = (traceRun step₂ t₀ k).map (List.map f) :=
  hasCoupling_proj_iff_map_eq.mp
    ⟨traceRun_HasCoupling_of_bisim
      (TraceKernelBisim.ofTraceKernelHom h) (f t₀) t₀ rfl k⟩

-- ============================================================================
-- Pointwise structural lemmas
-- ============================================================================

theorem append_singleton_inj {α : Type*} {as bs : List α} {a b : α}
    (h : as ++ [a] = bs ++ [b]) : as = bs ∧ a = b :=
  ⟨List.append_inj_left' h (by simp),
   by have := List.append_inj_right' h (by simp); simpa using this⟩

open Classical in
/-- At successor step, `traceRun` decomposes as prefix-reach times one-step
transition. -/
theorem traceRun_succ_append (step : List σ → PMF σ) (s₀ : σ)
    (k : Nat) (ss : List σ) (t : σ) :
    traceRun step s₀ (k + 1) (ss ++ [t]) =
      traceRun step s₀ k ss * step ss t := by
  rw [traceRun_succ, PMF.bind_apply]
  have hterm : ∀ ss' : List σ, ss' ≠ ss →
      traceRun step s₀ k ss' *
        ((step ss').bind (fun t' => PMF.pure (ss' ++ [t']))) (ss ++ [t]) = 0 := by
    intro ss' hne
    suffices ((step ss').bind (fun t' => PMF.pure (ss' ++ [t']))) (ss ++ [t]) = 0 by
      rw [this, mul_zero]
    simp only [PMF.bind_apply, PMF.pure_apply]
    rw [ENNReal.tsum_eq_zero]
    intro t'
    rw [if_neg (fun h => hne (append_singleton_inj h).1.symm), mul_zero]
  rw [tsum_eq_single ss (fun ss' hne => hterm ss' hne)]
  congr 1
  simp only [PMF.bind_apply, PMF.pure_apply]
  rw [tsum_eq_single t (fun t' ht' => by
    rw [if_neg (fun h => ht' (append_singleton_inj h).2.symm), mul_zero])]
  simp

open Classical in
/-- `traceRun` at successor step assigns zero probability to the empty trace. -/
theorem traceRun_succ_nil (step : List σ → PMF σ) (s₀ : σ) (k : Nat) :
    traceRun step s₀ (k + 1) [] = 0 := by
  rw [traceRun_succ, PMF.bind_apply]
  rw [ENNReal.tsum_eq_zero]
  intro ss
  suffices ((step ss).bind (fun t => PMF.pure (ss ++ [t]))) [] = 0 by
    rw [this, mul_zero]
  simp only [PMF.bind_apply, PMF.pure_apply]
  rw [ENNReal.tsum_eq_zero]
  intro t
  simp [show ([] : List σ) ≠ ss ++ [t] from List.ne_nil_of_length_pos (by simp)]

open Classical in
/-- Traces with nonzero `traceRun` probability have length exactly `n + 1`. -/
theorem traceRun_length (step : List σ → PMF σ) (s₀ : σ)
    (n : Nat) (ss : List σ)
    (h : traceRun step s₀ n ss ≠ 0) : ss.length = n + 1 := by
  induction n generalizing ss with
  | zero =>
    have hss : ss = [s₀] := by
      by_contra hne
      exact h (by simp [traceRun, PMF.pure_apply, hne])
    simp [hss]
  | succ k ih =>
    rcases List.eq_nil_or_concat ss with rfl | ⟨p, t, rfl⟩
    · exact absurd (traceRun_succ_nil step s₀ k) h
    · simp only [List.concat_eq_append, traceRun_succ_append] at h
      have hp : traceRun step s₀ k p ≠ 0 := left_ne_zero_of_mul h
      simp [List.length_append, ih p hp]

open Classical in
/-- On a nonzero-probability trace, each per-step transition has nonzero
probability. -/
theorem traceRun_step_nonzero (step : List σ → PMF σ) (s₀ : σ)
    (k : Nat) (ss : List σ)
    (h : traceRun step s₀ k ss ≠ 0)
    (j : Nat) (hj : j + 1 < ss.length) :
    step (ss.take (j + 1)) ss[j + 1] ≠ 0 := by
  have hlen := traceRun_length step s₀ k ss h
  induction k generalizing ss j with
  | zero => omega
  | succ m ih =>
    have hne : ss ≠ [] := by intro he; simp [he] at hlen
    obtain ⟨pre, t, hss_eq⟩ : ∃ pre t, ss = pre ++ [t] :=
      ⟨ss.dropLast, ss.getLast hne, (List.dropLast_append_getLast hne).symm⟩
    subst hss_eq
    have hplen : pre.length = m + 1 := by simp at hlen; omega
    rw [traceRun_succ_append] at h
    have hpre : traceRun step s₀ m pre ≠ 0 := left_ne_zero_of_mul h
    have hstep_last : step pre t ≠ 0 := right_ne_zero_of_mul h
    by_cases hjlast : j + 1 = pre.length
    · suffices step (List.take (j + 1) (pre ++ [t])) (pre ++ [t])[j + 1] ≠ 0 from this
      rw [List.take_append_of_le_length (by omega)]
      rw [List.getElem_append_right (by omega)]
      simp only [List.getElem_singleton, ne_eq]
      have : List.take pre.length pre = pre := List.take_length
      rw [hjlast, this]
      exact hstep_last
    · have hjpre : j + 1 < pre.length := by simp at hj; omega
      suffices step (List.take (j + 1) (pre ++ [t])) (pre ++ [t])[j + 1] ≠ 0 from this
      rw [List.take_append_of_le_length (by omega)]
      rw [List.getElem_append_left hjpre]
      exact ih pre hpre j hjpre hplen

end TraceRun
end Math
