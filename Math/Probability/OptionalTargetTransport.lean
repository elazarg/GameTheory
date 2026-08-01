/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.FiniteControlledStoppingEnvelope
import Math.Probability.SublinearLedger

/-!
# Optional target transport under unilateral control

This file is the kernel of a composition engine.  It supplies two
independent, deliberately elementary pieces.

## Part 1: vector-valued optional target transport

A `ControlledTransport` records a finite state space, a history type with a
one-step extension, a causal stopping predicate and, for one designated
deviating coordinate, a set of allowed replacement transition laws.  A
*unilateral control* picks, at every history, either the prescribed law or an
allowed deviation.  All values are evaluated at the history stopped either by
the causal predicate or by a finite horizon, so every stopping time occurring
below is bounded.

Three statements are proved, in the history-potential form and then in the
state-vector form:

* exact transport - a coordinatewise harmonic vector value is delivered
  *in expectation* at the stopped history;
* a unilateral cap - a coordinate superharmonic under the prescribed law and
  under every allowed deviation cannot be increased by any unilateral
  control;
* approximate versions with a nonnegative per-step error, whose penalty is
  the expected accumulated error `E[∑_{t < τ} e t]`.

Every conclusion is **signed and one-sided**.  The approximate transport is
recorded as two separate signed inequalities rather than one absolute-value
bound, and no statement is branchwise: the point of the theorem is exactly
that expected target delivery does *not* require pathwise preservation of
the target.  `TwoBranchProbe` below documents this with an explicit chain
whose value is harmonic at the root while the two positive-probability
successors carry different values.

A minimality fact worth recording, and proved here as
`harmonic_two_state_constant_or_absorbing`: no two-state example can exhibit
the phenomenon.  On a two-point state space, harmonicity of `V` at a state
forces either `V` constant or an absorbing transition there, so `V` is
preserved pathwise.  The probe therefore uses a root plus a two-point branch,
the smallest possible witness.

## Part 2: occupation concentration

If a nonnegative residual `slack t` is at least the margin `δ` whenever the
process occupies a region at time `t`, then the expected occupation count
before `T` is at most `(∑_{t < T} E[slack t]) / δ`.  A sublinear cumulative
slack budget therefore forces sublinear expected occupation.  A moving-margin
version replaces `δ` by `δ t`.  No adaptedness or Markov property is used:
the estimate is pure linearity plus a pointwise comparison, which is why it
is stated once here instead of being re-derived at each use site.
-/

set_option autoImplicit false

noncomputable section

namespace Math
namespace Probability

open Filter
open Math.ProbabilityMassFunction

/-! ## Part 1: optional target transport -/

/-- Data for a time-indexed process under unilateral control.

`extend` appends a sampled state to the finite history and `current` reads
the last state, so `History` may encode the entire past.  `stop` is the
causal stopping rule: it is decided by the history observed so far.
`prescribed` is the equilibrium transition law and `allowed` is the set of
replacement laws available to the single designated deviating coordinate. -/
structure ControlledTransport (State History : Type*) where
  /-- Append a sampled successor state to a finite history. -/
  extend : History → State → History
  /-- The current state of a finite history. -/
  current : History → State
  /-- Extending a history by a state makes that state current. -/
  current_extend : ∀ history next, current (extend history next) = next
  /-- Causal stopping rule, decided by the history observed so far. -/
  stop : History → Prop
  /-- The prescribed transition law at a history. -/
  prescribed : History → PMF State
  /-- Replacement laws available to the designated deviating coordinate. -/
  allowed : History → PMF State → Prop

namespace ControlledTransport

variable {S H : Type*} (M : ControlledTransport S H)

/-- A unilateral control: at every history the realized transition law is
either the prescribed one or an allowed deviation of the designated
coordinate. -/
def IsUnilateral (K : H → PMF S) : Prop :=
  ∀ history, K history = M.prescribed history ∨ M.allowed history (K history)

theorem isUnilateral_prescribed : M.IsUnilateral M.prescribed :=
  fun _ => Or.inl rfl

open Classical in
/-- Expected value of `payoff` read at the stopped history: the process is
run under the control `K` and stopped at the first history satisfying
`M.stop`, or at the horizon, whichever comes first.  This is the bounded
stopping time `τ ∧ horizon`. -/
def stoppedExpect (K : H → PMF S) (payoff : H → ℝ) : ℕ → H → ℝ
  | 0, history => payoff history
  | horizon + 1, history =>
      if M.stop history then payoff history
      else
        expect (K history) fun next =>
          stoppedExpect K payoff horizon (M.extend history next)

open Classical in
/-- Expected accumulated per-step error `E[∑_{t < τ} error (H t)]` along the
same bounded stopping time. -/
def stoppedErrorExpect (K : H → PMF S) (error : H → ℝ) : ℕ → H → ℝ
  | 0, _ => 0
  | horizon + 1, history =>
      if M.stop history then 0
      else
        error history +
          expect (K history) fun next =>
            stoppedErrorExpect K error horizon (M.extend history next)

@[simp] theorem stoppedExpect_zero
    (K : H → PMF S) (payoff : H → ℝ) (history : H) :
    M.stoppedExpect K payoff 0 history = payoff history := rfl

@[simp] theorem stoppedErrorExpect_zero
    (K : H → PMF S) (error : H → ℝ) (history : H) :
    M.stoppedErrorExpect K error 0 history = 0 := rfl

theorem stoppedExpect_of_stop
    (K : H → PMF S) (payoff : H → ℝ) (horizon : ℕ) (history : H)
    (stopped : M.stop history) :
    M.stoppedExpect K payoff horizon history = payoff history := by
  cases horizon with
  | zero => rfl
  | succ horizon => simp [stoppedExpect, stopped]

theorem stoppedErrorExpect_of_stop
    (K : H → PMF S) (error : H → ℝ) (horizon : ℕ) (history : H)
    (stopped : M.stop history) :
    M.stoppedErrorExpect K error horizon history = 0 := by
  cases horizon with
  | zero => rfl
  | succ horizon => simp [stoppedErrorExpect, stopped]

theorem stoppedExpect_succ_of_not_stop
    (K : H → PMF S) (payoff : H → ℝ) (horizon : ℕ) (history : H)
    (running : ¬ M.stop history) :
    M.stoppedExpect K payoff (horizon + 1) history =
      expect (K history) fun next =>
        M.stoppedExpect K payoff horizon (M.extend history next) := by
  simp [stoppedExpect, running]

theorem stoppedErrorExpect_succ_of_not_stop
    (K : H → PMF S) (error : H → ℝ) (horizon : ℕ) (history : H)
    (running : ¬ M.stop history) :
    M.stoppedErrorExpect K error (horizon + 1) history =
      error history +
        expect (K history) fun next =>
          M.stoppedErrorExpect K error horizon (M.extend history next) := by
  simp [stoppedErrorExpect, running]

theorem stoppedErrorExpect_nonneg
    (K : H → PMF S) {error : H → ℝ}
    (error_nonneg : ∀ history, 0 ≤ error history) :
    ∀ (horizon : ℕ) (history : H),
      0 ≤ M.stoppedErrorExpect K error horizon history := by
  intro horizon
  induction horizon with
  | zero => intro history; simp
  | succ horizon ih =>
      intro history
      by_cases stopped : M.stop history
      · rw [M.stoppedErrorExpect_of_stop K error _ history stopped]
      · rw [M.stoppedErrorExpect_succ_of_not_stop K error horizon history
          stopped]
        exact add_nonneg (error_nonneg history)
          (expect_nonneg _ _ fun next => ih (M.extend history next))

/-- A zero per-step error accumulates to zero. -/
@[simp] theorem stoppedErrorExpect_const_zero
    (K : H → PMF S) :
    ∀ (horizon : ℕ) (history : H),
      M.stoppedErrorExpect K (fun _ => 0) horizon history = 0 := by
  intro horizon
  induction horizon with
  | zero => intro history; rfl
  | succ horizon ih =>
      intro history
      by_cases stopped : M.stop history
      · rw [M.stoppedErrorExpect_of_stop K _ _ history stopped]
      · rw [M.stoppedErrorExpect_succ_of_not_stop K _ horizon history stopped]
        have laws :
            (fun next =>
              M.stoppedErrorExpect K (fun _ => (0 : ℝ)) horizon
                (M.extend history next)) = fun _ : S => (0 : ℝ) := by
          funext next
          exact ih (M.extend history next)
        rw [laws, expect_const, add_zero]

/-! ### Approximate one-sided transport (history-potential form) -/

/-- Approximately superharmonic values cannot gain more than the expected
accumulated per-step error.  The bound is one-sided and signed. -/
theorem stoppedExpect_le_of_superharmonic_of_error [Finite S]
    (K : H → PMF S) (value error : H → ℝ)
    (step : ∀ history, ¬ M.stop history →
      expect (K history) (fun next => value (M.extend history next)) ≤
        value history + error history) :
    ∀ (horizon : ℕ) (history : H),
      M.stoppedExpect K value horizon history ≤
        value history + M.stoppedErrorExpect K error horizon history := by
  intro horizon
  induction horizon with
  | zero => intro history; simp
  | succ horizon ih =>
      intro history
      by_cases stopped : M.stop history
      · rw [M.stoppedExpect_of_stop K value _ history stopped,
          M.stoppedErrorExpect_of_stop K error _ history stopped]
        simp
      · rw [M.stoppedExpect_succ_of_not_stop K value horizon history stopped,
          M.stoppedErrorExpect_succ_of_not_stop K error horizon history
            stopped]
        calc
          expect (K history)
              (fun next =>
                M.stoppedExpect K value horizon (M.extend history next)) ≤
            expect (K history)
              (fun next =>
                value (M.extend history next) +
                  M.stoppedErrorExpect K error horizon
                    (M.extend history next)) := by
              refine expect_mono _ _ _ fun next => ?_
              exact ih (M.extend history next)
          _ =
              expect (K history)
                  (fun next => value (M.extend history next)) +
                expect (K history)
                  (fun next =>
                    M.stoppedErrorExpect K error horizon
                      (M.extend history next)) :=
            expect_add _ _ _
          _ ≤
              (value history + error history) +
                expect (K history)
                  (fun next =>
                    M.stoppedErrorExpect K error horizon
                      (M.extend history next)) := by
            linarith [step history stopped]
          _ =
              value history +
                (error history +
                  expect (K history)
                    (fun next =>
                      M.stoppedErrorExpect K error horizon
                        (M.extend history next))) := by ring

/-- Approximately subharmonic values cannot lose more than the expected
accumulated per-step error.  This is the mirror one-sided statement; the two
together replace an absolute-value bound. -/
theorem le_stoppedExpect_of_subharmonic_of_error [Finite S]
    (K : H → PMF S) (value error : H → ℝ)
    (step : ∀ history, ¬ M.stop history →
      value history ≤
        expect (K history) (fun next => value (M.extend history next)) +
          error history) :
    ∀ (horizon : ℕ) (history : H),
      value history ≤
        M.stoppedExpect K value horizon history +
          M.stoppedErrorExpect K error horizon history := by
  intro horizon
  induction horizon with
  | zero => intro history; simp
  | succ horizon ih =>
      intro history
      by_cases stopped : M.stop history
      · rw [M.stoppedExpect_of_stop K value _ history stopped,
          M.stoppedErrorExpect_of_stop K error _ history stopped]
        simp
      · rw [M.stoppedExpect_succ_of_not_stop K value horizon history stopped,
          M.stoppedErrorExpect_succ_of_not_stop K error horizon history
            stopped]
        calc
          value history ≤
              expect (K history)
                  (fun next => value (M.extend history next)) +
                error history :=
            step history stopped
          _ ≤
              (expect (K history)
                  (fun next =>
                    M.stoppedExpect K value horizon (M.extend history next)) +
                expect (K history)
                  (fun next =>
                    M.stoppedErrorExpect K error horizon
                      (M.extend history next))) +
                error history := by
              have inner :
                  expect (K history)
                      (fun next => value (M.extend history next)) ≤
                    expect (K history)
                        (fun next =>
                          M.stoppedExpect K value horizon
                            (M.extend history next)) +
                      expect (K history)
                        (fun next =>
                          M.stoppedErrorExpect K error horizon
                            (M.extend history next)) := by
                rw [← expect_add]
                refine expect_mono _ _ _ fun next => ?_
                exact ih (M.extend history next)
              linarith
          _ =
              expect (K history)
                  (fun next =>
                    M.stoppedExpect K value horizon (M.extend history next)) +
                (error history +
                  expect (K history)
                    (fun next =>
                      M.stoppedErrorExpect K error horizon
                        (M.extend history next))) := by ring

/-- Exact one-sided transport: a superharmonic value cannot be increased. -/
theorem stoppedExpect_le_of_superharmonic [Finite S]
    (K : H → PMF S) (value : H → ℝ)
    (step : ∀ history, ¬ M.stop history →
      expect (K history) (fun next => value (M.extend history next)) ≤
        value history) :
    ∀ (horizon : ℕ) (history : H),
      M.stoppedExpect K value horizon history ≤ value history := by
  intro horizon history
  have bound :=
    M.stoppedExpect_le_of_superharmonic_of_error K value (fun _ => 0)
      (by
        intro current running
        simpa using step current running)
      horizon history
  simpa using bound

/-- Exact transport: a harmonic value is delivered exactly in expectation at
the bounded stopping time.  Nothing is claimed pathwise. -/
theorem stoppedExpect_eq_of_harmonic [Finite S]
    (K : H → PMF S) (value : H → ℝ)
    (step : ∀ history, ¬ M.stop history →
      expect (K history) (fun next => value (M.extend history next)) =
        value history) :
    ∀ (horizon : ℕ) (history : H),
      M.stoppedExpect K value horizon history = value history := by
  intro horizon
  induction horizon with
  | zero => intro history; rfl
  | succ horizon ih =>
      intro history
      by_cases stopped : M.stop history
      · exact M.stoppedExpect_of_stop K value _ history stopped
      · rw [M.stoppedExpect_succ_of_not_stop K value horizon history stopped]
        have laws :
            (fun next =>
              M.stoppedExpect K value horizon (M.extend history next)) =
              fun next => value (M.extend history next) := by
          funext next
          exact ih (M.extend history next)
        rw [laws]
        exact step history stopped

/-! ### State-valued targets -/

variable {ι : Type*}

/-- Exact prescribed transport for one scalar state target. -/
theorem stoppedExpect_current_eq_of_harmonic [Finite S]
    (value : S → ℝ)
    (harmonic : ∀ history, ¬ M.stop history →
      expect (M.prescribed history) value = value (M.current history))
    (horizon : ℕ) (history : H) :
    M.stoppedExpect M.prescribed (fun past => value (M.current past))
        horizon history =
      value (M.current history) := by
  refine M.stoppedExpect_eq_of_harmonic M.prescribed _ ?_ horizon history
  intro current running
  simpa [M.current_extend] using harmonic current running

/-- **Prescribed transport.**  A coordinatewise harmonic state vector is
delivered exactly, as a whole vector, in expectation at the bounded stopping
time.  No pathwise preservation of the target is asserted or needed. -/
theorem stoppedExpect_vector_eq_of_harmonic [Finite S]
    (V : S → ι → ℝ)
    (harmonic : ∀ history, ¬ M.stop history → ∀ index,
      expect (M.prescribed history) (fun next => V next index) =
        V (M.current history) index)
    (horizon : ℕ) (history : H) :
    (fun index =>
        M.stoppedExpect M.prescribed
          (fun past => V (M.current past) index) horizon history) =
      V (M.current history) := by
  funext index
  exact M.stoppedExpect_current_eq_of_harmonic (fun state => V state index)
    (fun current running => harmonic current running index) horizon history

/-- Approximate prescribed transport, upper half.  Signed and one-sided. -/
theorem stoppedExpect_current_le_of_approx_harmonic [Finite S]
    (value : S → ℝ) (error : H → ℝ)
    (upper : ∀ history, ¬ M.stop history →
      expect (M.prescribed history) value ≤
        value (M.current history) + error history)
    (horizon : ℕ) (history : H) :
    M.stoppedExpect M.prescribed (fun past => value (M.current past))
        horizon history ≤
      value (M.current history) +
        M.stoppedErrorExpect M.prescribed error horizon history := by
  refine M.stoppedExpect_le_of_superharmonic_of_error M.prescribed _ error ?_
    horizon history
  intro current running
  simpa [M.current_extend] using upper current running

/-- Approximate prescribed transport, lower half.  Signed and one-sided. -/
theorem le_stoppedExpect_current_of_approx_harmonic [Finite S]
    (value : S → ℝ) (error : H → ℝ)
    (lower : ∀ history, ¬ M.stop history →
      value (M.current history) ≤
        expect (M.prescribed history) value + error history)
    (horizon : ℕ) (history : H) :
    value (M.current history) ≤
      M.stoppedExpect M.prescribed (fun past => value (M.current past))
          horizon history +
        M.stoppedErrorExpect M.prescribed error horizon history := by
  refine M.le_stoppedExpect_of_subharmonic_of_error M.prescribed
    (fun past => value (M.current past)) error ?_ horizon history
  intro current running
  simpa [M.current_extend] using lower current running

/-! ### The unilateral cap -/

/-- **Unilateral cap.**  If a scalar state target is superharmonic under the
prescribed law and under every allowed deviation of the designated
coordinate, then no unilateral control can raise its stopped expectation
above its initial value.  The conclusion is one-sided. -/
theorem stoppedExpect_current_le_of_unilateral [Finite S]
    (value : S → ℝ)
    (prescribed_super : ∀ history, ¬ M.stop history →
      expect (M.prescribed history) value ≤ value (M.current history))
    (allowed_super : ∀ history law, ¬ M.stop history →
      M.allowed history law → expect law value ≤ value (M.current history))
    (K : H → PMF S) (unilateral : M.IsUnilateral K)
    (horizon : ℕ) (history : H) :
    M.stoppedExpect K (fun past => value (M.current past)) horizon history ≤
      value (M.current history) := by
  refine M.stoppedExpect_le_of_superharmonic K _ ?_ horizon history
  intro current running
  have base : expect (K current) value ≤ value (M.current current) := by
    rcases unilateral current with selected | deviated
    · rw [selected]
      exact prescribed_super current running
    · exact allowed_super current (K current) running deviated
  simpa [M.current_extend] using base

/-- Approximate unilateral cap: the same one-sided conclusion up to the
expected accumulated per-step error. -/
theorem stoppedExpect_current_le_of_unilateral_of_error [Finite S]
    (value : S → ℝ) (error : H → ℝ)
    (prescribed_super : ∀ history, ¬ M.stop history →
      expect (M.prescribed history) value ≤
        value (M.current history) + error history)
    (allowed_super : ∀ history law, ¬ M.stop history →
      M.allowed history law →
        expect law value ≤ value (M.current history) + error history)
    (K : H → PMF S) (unilateral : M.IsUnilateral K)
    (horizon : ℕ) (history : H) :
    M.stoppedExpect K (fun past => value (M.current past)) horizon history ≤
      value (M.current history) +
        M.stoppedErrorExpect K error horizon history := by
  refine M.stoppedExpect_le_of_superharmonic_of_error K _ error ?_
    horizon history
  intro current running
  have base :
      expect (K current) value ≤ value (M.current current) + error current := by
    rcases unilateral current with selected | deviated
    · rw [selected]
      exact prescribed_super current running
    · exact allowed_super current (K current) running deviated
  simpa [M.current_extend] using base

/-- **Vector form of the unilateral cap.**  Only the designated coordinate is
capped; the other coordinates carry no claim, which is exactly the asymmetry
a unilateral deviation argument needs. -/
theorem stoppedExpect_vector_coord_le_of_unilateral [Finite S]
    (V : S → ι → ℝ) (index : ι)
    (prescribed_super : ∀ history, ¬ M.stop history →
      expect (M.prescribed history) (fun next => V next index) ≤
        V (M.current history) index)
    (allowed_super : ∀ history law, ¬ M.stop history →
      M.allowed history law →
        expect law (fun next => V next index) ≤ V (M.current history) index)
    (K : H → PMF S) (unilateral : M.IsUnilateral K)
    (horizon : ℕ) (history : H) :
    M.stoppedExpect K (fun past => V (M.current past) index) horizon
        history ≤
      V (M.current history) index :=
  M.stoppedExpect_current_le_of_unilateral (fun state => V state index)
    prescribed_super allowed_super K unilateral horizon history

end ControlledTransport

/-! ### Falsifier probes

Both probes live on the smallest state space that can carry the phenomenon:
a root together with a two-point branch. -/

/-- Two states are not enough.  If a value is harmonic at one of two states
then either the value is constant or the transition there is absorbing, so in
both cases the target is preserved pathwise.  This is why the probe below
needs a root together with a two-point branch: three states is the minimum. -/
theorem harmonic_two_state_constant_or_absorbing
    (law : PMF Bool) (value : Bool → ℝ) (state : Bool)
    (harmonic : expect law value = value state) :
    value true = value false ∨ law (!state) = 0 := by
  have total : (law true).toReal + (law false).toReal = 1 := by
    have unit := expect_const law (1 : ℝ)
    rw [expect_eq_sum, Fintype.sum_bool] at unit
    simpa using unit
  have expand :
      (law true).toReal * value true + (law false).toReal * value false =
        value state := by
    rw [← harmonic, expect_eq_sum, Fintype.sum_bool]
  have mass_zero : ∀ side : Bool, (law side).toReal = 0 → law side = 0 := by
    intro side vanishes
    rcases (ENNReal.toReal_eq_zero_iff (law side)).mp vanishes with zero | top
    · exact zero
    · exact absurd top (PMF.apply_ne_top law side)
  cases state with
  | false =>
      have substituted : (law false).toReal = 1 - (law true).toReal := by
        linarith
      rw [substituted] at expand
      have key : (law true).toReal * (value true - value false) = 0 := by
        linear_combination expand
      rcases mul_eq_zero.mp key with vanishes | equal
      · exact Or.inr (mass_zero true vanishes)
      · exact Or.inl (by linarith)
  | true =>
      have substituted : (law true).toReal = 1 - (law false).toReal := by
        linarith
      rw [substituted] at expand
      have key : (law false).toReal * (value false - value true) = 0 := by
        linear_combination expand
      rcases mul_eq_zero.mp key with vanishes | equal
      · exact Or.inr (mass_zero false vanishes)
      · exact Or.inl (by linarith)

namespace TwoBranchProbe

/-- Root (`none`) plus a two-point branch. -/
abbrev Probe := Option Bool

/-- Target value: `0` at the root, `±1` on the two leaves. -/
def value : Probe → ℝ
  | none => 0
  | some true => 1
  | some false => -1

/-- Weights of the fair branch out of the root. -/
def branchWeights : Probe → ENNReal
  | none => 0
  | some _ => 2⁻¹

theorem branchWeights_sum : ∑ state : Probe, branchWeights state = 1 := by
  rw [Fintype.sum_option]
  simp only [branchWeights, Fintype.sum_bool, zero_add]
  exact ENNReal.inv_two_add_inv_two

/-- The prescribed kernel: a fair branch out of the root, absorbing at each
leaf. -/
def kernel : Probe → PMF Probe
  | none => PMF.ofFintype branchWeights branchWeights_sum
  | some leaf => PMF.pure (some leaf)

/-- The probe transport: histories are states, the process stops as soon as
it leaves the root, and the single allowed deviation drives the process to
the low leaf. -/
def model : ControlledTransport Probe Probe where
  extend := fun _ next => next
  current := id
  current_extend := fun _ _ => rfl
  stop := fun state => state ≠ none
  prescribed := kernel
  allowed := fun _ law => law = PMF.pure (some false)

@[simp] theorem model_stop (state : Probe) :
    model.stop state ↔ state ≠ none := Iff.rfl

@[simp] theorem model_current (state : Probe) :
    model.current state = state := rfl

@[simp] theorem model_extend (state next : Probe) :
    model.extend state next = next := rfl

@[simp] theorem model_prescribed (state : Probe) :
    model.prescribed state = kernel state := rfl

@[simp] theorem model_allowed (state : Probe) (law : PMF Probe) :
    model.allowed state law ↔ law = PMF.pure (some false) := Iff.rfl

/-- The target is harmonic at the root. -/
theorem harmonic_root : expect (kernel none) value = value none := by
  rw [expect_eq_sum, Fintype.sum_option]
  simp only [kernel, PMF.ofFintype_apply, branchWeights, Fintype.sum_bool,
    value]
  norm_num

/-- The high leaf really is reached with positive probability. -/
theorem branch_ne_zero : kernel none (some true) ≠ 0 := by
  change PMF.ofFintype branchWeights branchWeights_sum (some true) ≠ 0
  rw [PMF.ofFintype_apply]
  simp [branchWeights]

/-- **Falsifier probe 1.**  Expected target delivery holds at the bounded
stopping time, yet the target is *not* preserved pathwise: the high leaf is
reached with positive probability and carries a different value. -/
theorem expectedDelivery_without_pathwise_preservation :
    model.stoppedExpect model.prescribed
        (fun past => value (model.current past)) 1 none =
      value (model.current none) ∧
    kernel none (some true) ≠ 0 ∧
    value (some true) ≠ value (model.current none) := by
  refine ⟨?_, branch_ne_zero, ?_⟩
  · refine model.stoppedExpect_current_eq_of_harmonic value ?_ 1 none
    intro history running
    have root : history = none := by
      by_contra leaf
      exact running leaf
    subst root
    simpa using harmonic_root
  · simp [value]

/-- The deviating control: leave the root towards the low leaf. -/
def deviation : Probe → PMF Probe :=
  fun state => if state = none then PMF.pure (some false) else kernel state

theorem deviation_isUnilateral : model.IsUnilateral deviation := by
  intro state
  by_cases root : state = none
  · exact Or.inr (by simp [deviation, root])
  · exact Or.inl (by simp [deviation, root])

theorem prescribed_superharmonic (history : Probe)
    (running : ¬ model.stop history) :
    expect (model.prescribed history) value ≤ value (model.current history) := by
  have root : history = none := by
    by_contra leaf
    exact running leaf
  subst root
  simpa using le_of_eq harmonic_root

theorem allowed_superharmonic (history : Probe) (law : PMF Probe)
    (_running : ¬ model.stop history) (deviated : model.allowed history law) :
    expect law value ≤ value (model.current history) := by
  have root : history = none := by
    by_contra leaf
    exact _running leaf
  subst root
  rw [show law = PMF.pure (some false) from deviated]
  simp [value]

/-- **Falsifier probe 2.**  The cap is genuinely one-sided: under the allowed
deviation the deviator strictly loses. -/
theorem unilateralCap_strict :
    model.stoppedExpect deviation
        (fun past => value (model.current past)) 1 none <
      value (model.current none) := by
  have step :=
    model.stoppedExpect_succ_of_not_stop deviation
      (fun past => value (model.current past)) 0 none (by simp)
  rw [step]
  simp [deviation, value]

/-- The cap of course still holds at the deviating control. -/
theorem unilateralCap_holds (horizon : ℕ) :
    model.stoppedExpect deviation
        (fun past => value (model.current past)) horizon none ≤
      value (model.current none) :=
  model.stoppedExpect_current_le_of_unilateral value
    prescribed_superharmonic allowed_superharmonic deviation
    deviation_isUnilateral horizon none

end TwoBranchProbe

/-! ### Bridge to the finite controlled stopping envelope

The rank-indexed potentials of `FiniteControlledStoppingEnvelope` are exactly
the harmonic and superharmonic inputs required above.  Instantiating the
transport theorems at that model shows the two files compose without any new
process definition: the envelope's `Node` doubles as both the state and the
history, its `terminal` predicate is the causal stopping rule, and its mixed
unilateral replacements are the allowed deviations. -/

namespace FiniteControlledStoppingModel

variable {Player Node : Type} {Action : Player → Type}
  [Finite Node] [∀ who, Fintype (Action who)] [∀ who, Nonempty (Action who)]

/-- The finite ranked stopping model read as a controlled transport whose
histories are its nodes. -/
def toControlledTransport
    (model : FiniteControlledStoppingModel Player Node Action)
    (who : Player) :
    ControlledTransport Node Node where
  extend := fun _ next => next
  current := id
  current_extend := fun _ _ => rfl
  stop := model.terminal
  prescribed := model.prescribedKernel
  allowed := fun node law =>
    ∃ mixed : PMF (Action who),
      law = mixed.bind (model.controlledKernel node who)

omit [Finite Node] [∀ who, Fintype (Action who)]
    [∀ who, Nonempty (Action who)] in
@[simp] theorem toControlledTransport_extend
    (model : FiniteControlledStoppingModel Player Node Action)
    (who : Player) (node next : Node) :
    (model.toControlledTransport who).extend node next = next := rfl

omit [Finite Node] [∀ who, Fintype (Action who)]
    [∀ who, Nonempty (Action who)] in
@[simp] theorem toControlledTransport_prescribed
    (model : FiniteControlledStoppingModel Player Node Action)
    (who : Player) (node : Node) :
    (model.toControlledTransport who).prescribed node =
      model.prescribedKernel node := rfl

omit [Finite Node] [∀ who, Fintype (Action who)]
    [∀ who, Nonempty (Action who)] in
@[simp] theorem toControlledTransport_stop
    (model : FiniteControlledStoppingModel Player Node Action)
    (who : Player) (node : Node) :
    (model.toControlledTransport who).stop node ↔ model.terminal node :=
  Iff.rfl

omit [∀ who, Fintype (Action who)] [∀ who, Nonempty (Action who)] in
/-- The prescribed rank-indexed potential is transported exactly to the
terminal obstacle in expectation. -/
theorem stoppedExpect_prescribedPotential
    (model : FiniteControlledStoppingModel Player Node Action)
    (who : Player) (horizon : ℕ) (node : Node) :
    (model.toControlledTransport who).stoppedExpect model.prescribedKernel
        (model.prescribedPotential who) horizon node =
      model.prescribedPotential who node := by
  refine ControlledTransport.stoppedExpect_eq_of_harmonic _ _ _ ?_ horizon node
  intro current running
  exact model.prescribedPotential_harmonic who current running

/-- Every unilateral control is capped by the worst-case envelope potential
at the bounded stopping time. -/
theorem stoppedExpect_worstCasePotential_le
    (model : FiniteControlledStoppingModel Player Node Action)
    (who : Player) (K : Node → PMF Node)
    (unilateral : (model.toControlledTransport who).IsUnilateral K)
    (horizon : ℕ) (node : Node) :
    (model.toControlledTransport who).stoppedExpect K
        (model.worstCasePotential who) horizon node ≤
      model.worstCasePotential who node := by
  refine ControlledTransport.stoppedExpect_le_of_superharmonic _ _ _ ?_
    horizon node
  intro current running
  simp only [toControlledTransport_extend]
  rcases unilateral current with selected | ⟨mixed, mixed_eq⟩
  · rw [selected, toControlledTransport_prescribed,
      model.prescribed_eq_mix current who]
    exact model.worstCasePotential_mixed_superharmonic who current running _
  · rw [mixed_eq]
    exact model.worstCasePotential_mixed_superharmonic who current running mixed

end FiniteControlledStoppingModel

/-! ## Part 2: occupation concentration -/

section Occupation

variable {Ω : Type*}

open Classical in
/-- Indicator of the region at one step. -/
def regionIndicator (region : ℕ → Ω → Prop) (step : ℕ) (state : Ω) : ℝ :=
  if region step state then 1 else 0

theorem regionIndicator_nonneg
    (region : ℕ → Ω → Prop) (step : ℕ) (state : Ω) :
    0 ≤ regionIndicator region step state := by
  unfold regionIndicator
  split <;> norm_num

/-- The comparison that drives every occupation bound: on the region the
residual pays the margin, off the region the indicator vanishes. -/
theorem margin_mul_regionIndicator_le
    (region : ℕ → Ω → Prop) (step : ℕ) (state : Ω)
    {margin residual : ℝ}
    (residual_nonneg : 0 ≤ residual)
    (margin_le : region step state → margin ≤ residual) :
    margin * regionIndicator region step state ≤ residual := by
  unfold regionIndicator
  split
  · rename_i occupied
    simpa using margin_le occupied
  · simpa using residual_nonneg

/-- Weighted count of the steps before the horizon at which the region is
occupied. -/
def weightedRegionOccupation
    (region : ℕ → Ω → Prop) (weight : ℕ → ℝ) : ℕ → Ω → ℝ
  | 0, _ => 0
  | horizon + 1, state =>
      weightedRegionOccupation region weight horizon state +
        weight horizon * regionIndicator region horizon state

/-- Plain occupation count of the region before the horizon. -/
def regionOccupation (region : ℕ → Ω → Prop) : ℕ → Ω → ℝ :=
  weightedRegionOccupation region fun _ => 1

@[simp] theorem weightedRegionOccupation_zero
    (region : ℕ → Ω → Prop) (weight : ℕ → ℝ) (state : Ω) :
    weightedRegionOccupation region weight 0 state = 0 := rfl

@[simp] theorem weightedRegionOccupation_succ
    (region : ℕ → Ω → Prop) (weight : ℕ → ℝ) (horizon : ℕ) (state : Ω) :
    weightedRegionOccupation region weight (horizon + 1) state =
      weightedRegionOccupation region weight horizon state +
        weight horizon * regionIndicator region horizon state := rfl

@[simp] theorem regionOccupation_zero
    (region : ℕ → Ω → Prop) (state : Ω) :
    regionOccupation region 0 state = 0 := rfl

@[simp] theorem regionOccupation_succ
    (region : ℕ → Ω → Prop) (horizon : ℕ) (state : Ω) :
    regionOccupation region (horizon + 1) state =
      regionOccupation region horizon state +
        regionIndicator region horizon state := by
  simp [regionOccupation]

theorem regionOccupation_nonneg
    (region : ℕ → Ω → Prop) (horizon : ℕ) (state : Ω) :
    0 ≤ regionOccupation region horizon state := by
  induction horizon with
  | zero => simp
  | succ horizon ih =>
      rw [regionOccupation_succ]
      exact add_nonneg ih (regionIndicator_nonneg region horizon state)

theorem regionOccupation_eq_sum
    (region : ℕ → Ω → Prop) (horizon : ℕ) (state : Ω) :
    regionOccupation region horizon state =
      ∑ step ∈ Finset.range horizon, regionIndicator region step state := by
  induction horizon with
  | zero => simp
  | succ horizon ih =>
      rw [regionOccupation_succ, Finset.sum_range_succ, ih]

theorem weightedRegionOccupation_const
    (region : ℕ → Ω → Prop) (constant : ℝ) (horizon : ℕ) (state : Ω) :
    weightedRegionOccupation region (fun _ => constant) horizon state =
      constant * regionOccupation region horizon state := by
  induction horizon with
  | zero => simp
  | succ horizon ih =>
      rw [weightedRegionOccupation_succ, regionOccupation_succ, ih]
      ring

/-- **Moving-margin occupation bound.**  Each occupied step is charged its
own margin against the residual at that step.  Only a pointwise comparison
and linearity of expectation are used: no adaptedness, no Markov property. -/
theorem expect_weightedRegionOccupation_le_sum_expect [Finite Ω]
    (law : PMF Ω) (region : ℕ → Ω → Prop) (slack : ℕ → Ω → ℝ)
    (margin : ℕ → ℝ)
    (slack_nonneg : ∀ step state, 0 ≤ slack step state)
    (margin_le : ∀ step state, region step state → margin step ≤ slack step state)
    (horizon : ℕ) :
    expect law (weightedRegionOccupation region margin horizon) ≤
      ∑ step ∈ Finset.range horizon, expect law (slack step) := by
  induction horizon with
  | zero =>
      have empty : weightedRegionOccupation region margin 0 =
          fun _ : Ω => (0 : ℝ) := rfl
      simp [empty]
  | succ horizon ih =>
      rw [Finset.sum_range_succ]
      have unfold :
          weightedRegionOccupation region margin (horizon + 1) =
            fun state =>
              weightedRegionOccupation region margin horizon state +
                margin horizon * regionIndicator region horizon state := rfl
      have split :
          expect law (weightedRegionOccupation region margin (horizon + 1)) =
            expect law (weightedRegionOccupation region margin horizon) +
              expect law (fun state =>
                margin horizon * regionIndicator region horizon state) := by
        rw [unfold, expect_add]
      rw [split]
      refine add_le_add ih ?_
      refine expect_mono _ _ _ fun state => ?_
      exact margin_mul_regionIndicator_le region horizon state
        (slack_nonneg horizon state) (margin_le horizon state)

/-- Constant-margin form: `δ · E[occupation] ≤ ∑ E[slack]`. -/
theorem margin_mul_expect_regionOccupation_le [Finite Ω]
    (law : PMF Ω) (region : ℕ → Ω → Prop) (slack : ℕ → Ω → ℝ) {margin : ℝ}
    (slack_nonneg : ∀ step state, 0 ≤ slack step state)
    (margin_le : ∀ step state, region step state → margin ≤ slack step state)
    (horizon : ℕ) :
    margin * expect law (regionOccupation region horizon) ≤
      ∑ step ∈ Finset.range horizon, expect law (slack step) := by
  have weighted :=
    expect_weightedRegionOccupation_le_sum_expect law region slack
      (fun _ => margin) slack_nonneg (fun step state => margin_le step state)
      horizon
  have rewrite :
      weightedRegionOccupation region (fun _ => margin) horizon =
        fun state => margin * regionOccupation region horizon state := by
    funext state
    exact weightedRegionOccupation_const region margin horizon state
  rw [rewrite, expect_const_mul] at weighted
  exact weighted

/-- **The generic error bound.**  A positive margin on a region converts a
cumulative slack budget into an occupation bound. -/
theorem expect_regionOccupation_le_div [Finite Ω]
    (law : PMF Ω) (region : ℕ → Ω → Prop) (slack : ℕ → Ω → ℝ) {margin : ℝ}
    (margin_pos : 0 < margin)
    (slack_nonneg : ∀ step state, 0 ≤ slack step state)
    (margin_le : ∀ step state, region step state → margin ≤ slack step state)
    (horizon : ℕ) :
    expect law (regionOccupation region horizon) ≤
      (∑ step ∈ Finset.range horizon, expect law (slack step)) / margin := by
  rw [le_div_iff₀ margin_pos, mul_comm]
  exact margin_mul_expect_regionOccupation_le law region slack slack_nonneg
    margin_le horizon

/-- Budgeted form: `∑_{t < T} E[slack t] ≤ B T` gives `E[occupation T] ≤ B T / δ`. -/
theorem expect_regionOccupation_le_budget_div [Finite Ω]
    (law : PMF Ω) (region : ℕ → Ω → Prop) (slack : ℕ → Ω → ℝ) {margin : ℝ}
    (budget : ℕ → ℝ)
    (margin_pos : 0 < margin)
    (slack_nonneg : ∀ step state, 0 ≤ slack step state)
    (margin_le : ∀ step state, region step state → margin ≤ slack step state)
    (budgeted : ∀ horizon : ℕ,
      ∑ step ∈ Finset.range horizon, expect law (slack step) ≤ budget horizon)
    (horizon : ℕ) :
    expect law (regionOccupation region horizon) ≤ budget horizon / margin := by
  refine le_trans
    (expect_regionOccupation_le_div law region slack margin_pos slack_nonneg
      margin_le horizon) ?_
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (budgeted horizon)
    (inv_nonneg.mpr margin_pos.le)

/-- Moving-margin divided form: each step contributes `E[slack t] / δ t`. -/
theorem expect_regionOccupation_le_sum_div [Finite Ω]
    (law : PMF Ω) (region : ℕ → Ω → Prop) (slack : ℕ → Ω → ℝ)
    (margin : ℕ → ℝ)
    (margin_pos : ∀ step, 0 < margin step)
    (slack_nonneg : ∀ step state, 0 ≤ slack step state)
    (margin_le : ∀ step state, region step state → margin step ≤ slack step state)
    (horizon : ℕ) :
    expect law (regionOccupation region horizon) ≤
      ∑ step ∈ Finset.range horizon, expect law (slack step) / margin step := by
  induction horizon with
  | zero =>
      have empty : regionOccupation region 0 = fun _ : Ω => (0 : ℝ) := rfl
      simp [empty]
  | succ horizon ih =>
      rw [Finset.sum_range_succ]
      have unfold :
          regionOccupation region (horizon + 1) =
            fun state =>
              regionOccupation region horizon state +
                regionIndicator region horizon state := by
        funext state
        exact regionOccupation_succ region horizon state
      have split :
          expect law (regionOccupation region (horizon + 1)) =
            expect law (regionOccupation region horizon) +
              expect law (regionIndicator region horizon) := by
        rw [unfold, expect_add]
      rw [split]
      refine add_le_add ih ?_
      rw [le_div_iff₀ (margin_pos horizon), mul_comm, ← expect_const_mul]
      refine expect_mono _ _ _ fun state => ?_
      exact margin_mul_regionIndicator_le region horizon state
        (slack_nonneg horizon state) (margin_le horizon state)

/-- **Sublinear occupation.**  A sublinear cumulative slack budget forces
sublinear expected occupation of the margin region. -/
theorem isAsymptoticallySublinear_expect_regionOccupation [Finite Ω]
    (law : PMF Ω) (region : ℕ → Ω → Prop) (slack : ℕ → Ω → ℝ) {margin : ℝ}
    (budget : ℕ → ℝ)
    (margin_pos : 0 < margin)
    (slack_nonneg : ∀ step state, 0 ≤ slack step state)
    (margin_le : ∀ step state, region step state → margin ≤ slack step state)
    (budgeted : ∀ horizon : ℕ,
      ∑ step ∈ Finset.range horizon, expect law (slack step) ≤ budget horizon)
    (sublinear : IsAsymptoticallySublinear budget) :
    IsAsymptoticallySublinear
      (fun horizon => expect law (regionOccupation region horizon)) := by
  rw [isAsymptoticallySublinear_iff_tendsto]
  have scaled : IsAsymptoticallySublinear (fun horizon => margin⁻¹ * budget horizon) :=
    sublinear.const_mul margin⁻¹
  have limit := isAsymptoticallySublinear_iff_tendsto.mp scaled
  refine squeeze_zero (fun horizon => ?_) (fun horizon => ?_) limit
  · exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg horizon))
      (expect_nonneg _ _ fun state =>
        regionOccupation_nonneg region horizon state)
  · refine mul_le_mul_of_nonneg_left ?_
      (inv_nonneg.mpr (Nat.cast_nonneg horizon))
    have bound :=
      expect_regionOccupation_le_budget_div law region slack budget margin_pos
        slack_nonneg margin_le budgeted horizon
    rwa [div_eq_inv_mul] at bound

end Occupation

end Probability
end Math
