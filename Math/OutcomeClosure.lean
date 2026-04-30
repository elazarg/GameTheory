import Math.PMFIter
import Math.ProbabilityMassFunction

/-!
# Outcome closure for stopped PMF processes

This file packages the common continuation-value argument for a finite
stochastic process.  If every nonterminal step preserves a semantic
continuation value and a rank decreases on supported transitions, then running
the stopped process for enough fuel and projecting terminal states to outcomes
returns the initial continuation value.
-/

set_option autoImplicit false

namespace Math
namespace OutcomeClosure

open Math.ProbabilityMassFunction

variable {S Ω : Type*}

/-- A finite stopped stochastic process equipped with a semantic continuation
value.  The field `value s` is the final outcome distribution from `s`; it is
preserved by one nonterminal step and collapses to `observe s` at terminal
states. -/
structure ValueProcess (S Ω : Type*) where
  terminal : S → Prop
  step : S → PMF S
  rank : S → Nat
  observe : S → Ω
  value : S → PMF Ω
  terminal_of_rank_zero : ∀ s, rank s = 0 → terminal s
  terminal_value : ∀ s, terminal s → value s = PMF.pure (observe s)
  step_value : ∀ s, ¬ terminal s → (step s).bind value = value s
  step_rank : ∀ s t, ¬ terminal s → step s t ≠ 0 → rank t + 1 = rank s

namespace ValueProcess

/-- The stopped kernel: terminal states self-loop, nonterminal states use the
underlying process step. -/
noncomputable def stoppedStep (R : ValueProcess S Ω) (s : S) : PMF S :=
  by
    classical
    exact if R.terminal s then PMF.pure s else R.step s

/-- Finite run of the stopped process. -/
noncomputable def run (R : ValueProcess S Ω) (n : Nat) (s : S) : PMF S :=
  Math.PMFIter.iter R.stoppedStep n s

@[simp] theorem run_zero (R : ValueProcess S Ω) (s : S) :
    R.run 0 s = PMF.pure s := rfl

theorem run_succ (R : ValueProcess S Ω) (n : Nat) (s : S) :
    R.run (n + 1) s = (R.stoppedStep s).bind (R.run n) := rfl

@[simp] theorem stoppedStep_terminal
    (R : ValueProcess S Ω) {s : S} (hterm : R.terminal s) :
    R.stoppedStep s = PMF.pure s := by
  classical
  simp [stoppedStep, hterm]

@[simp] theorem stoppedStep_nonterminal
    (R : ValueProcess S Ω) {s : S} (hterm : ¬ R.terminal s) :
    R.stoppedStep s = R.step s := by
  classical
  simp [stoppedStep, hterm]

theorem run_terminal
    (R : ValueProcess S Ω) (n : Nat) {s : S} (hterm : R.terminal s) :
    R.run n s = PMF.pure s := by
  unfold run
  exact Math.PMFIter.iter_of_terminal (R.stoppedStep_terminal hterm) n

theorem run_succ_nonterminal
    (R : ValueProcess S Ω) (n : Nat) {s : S} (hterm : ¬ R.terminal s) :
    R.run (n + 1) s = (R.step s).bind (R.run n) := by
  rw [run_succ, R.stoppedStep_nonterminal hterm]

/-- One stopped step preserves the continuation value. -/
theorem stoppedStep_bind_value (R : ValueProcess S Ω) (s : S) :
    (R.stoppedStep s).bind R.value = R.value s := by
  by_cases hterm : R.terminal s
  · rw [R.stoppedStep_terminal hterm]
    simp
  · rw [R.stoppedStep_nonterminal hterm]
    exact R.step_value s hterm

/-- Any finite stopped run preserves the continuation value. -/
theorem run_bind_value (R : ValueProcess S Ω) :
    ∀ n s, (R.run n s).bind R.value = R.value s := by
  intro n
  induction n with
  | zero =>
      intro s
      simp [run]
  | succ n ih =>
      intro s
      rw [run_succ, PMF.bind_bind]
      conv_lhs =>
        arg 2
        intro t
        rw [ih t]
      exact R.stoppedStep_bind_value s

/-- With enough fuel, every supported destination of the stopped run is
terminal. -/
theorem support_terminal_of_rank_le (R : ValueProcess S Ω) :
    ∀ n s t, R.rank s ≤ n → t ∈ (R.run n s).support → R.terminal t := by
  intro n
  induction n with
  | zero =>
      intro s t hn ht
      have htEq : t = s := by
        simpa using ht
      subst t
      exact R.terminal_of_rank_zero s (Nat.eq_zero_of_le_zero hn)
  | succ n ih =>
      intro s t hn ht
      by_cases hterm : R.terminal s
      · rw [R.run_terminal (n + 1) hterm] at ht
        have htEq : t = s := by
          simpa using ht
        subst t
        exact hterm
      · rw [R.run_succ_nonterminal n hterm] at ht
        rw [PMF.mem_support_bind_iff] at ht
        rcases ht with ⟨mid, hmid, ht⟩
        have hstep := R.step_rank s mid hterm
          (by simpa [PMF.mem_support_iff] using hmid)
        have hmidRank : R.rank mid ≤ n := by
          have hsucc : R.rank mid + 1 ≤ n + 1 := by
            simpa [hstep] using hn
          exact Nat.succ_le_succ_iff.mp hsucc
        exact ih mid t hmidRank ht

/-- Main closure theorem: after enough stopped-process fuel, observing the
final state has the continuation-value distribution of the initial state. -/
theorem map_observe_run_eq_value
    (R : ValueProcess S Ω) (n : Nat) (s : S)
    (hn : R.rank s ≤ n) :
    PMF.map R.observe (R.run n s) = R.value s := by
  rw [← PMF.bind_pure_comp]
  rw [bind_congr_on_support
    (R.run n s) (PMF.pure ∘ R.observe) R.value]
  · exact R.run_bind_value n s
  · intro t ht
    have hterm := R.support_terminal_of_rank_le n s t hn ht
    rw [R.terminal_value t hterm]
    rfl

end ValueProcess
end OutcomeClosure
end Math
