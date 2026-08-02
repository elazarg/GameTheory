/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability
import Math.Probability.SublinearLedger
import Mathlib.Data.ZMod.Basic

/-!
# The switching-coboundary calculus for predictable potentials

A potential account for a *time-varying* environment must let the potential
move with the environment.  This file is the single integration-by-parts layer
for that situation: a predictable potential path `H : ℕ → S → ℝ` is paired with
per-stage kernels `Q t` and per-stage costs `f t`, and the one-step **slack**

```
switchedLocalSlack (Q t) (f t) (H t) (H (t + 1)) s
  = f t s + (Q t H (t + 1)) s - H t s
```

is the exact coboundary defect.  Summing the slack telescopes: the potential
path contributes only its two endpoints, and everything else is a *charge*.

The design is deliberately **mode/phase-lifted** rather than state-only.  Two
independent sources say a state-only potential is not enough: the answered
research question `questions/Question89-ControllerCapsUnderSwitchedHarmlessEnvironments.md`
(its Part A switching identity and its Part C.3 phase-augmented biases), and
experiment `E03` of `ephemeral/experiments/` (path-complete accounts are
coboundaries on lifted `(mode, state)` graphs).  The falsifier probes at the end
of this file check both obstructions inside Lean.

## Layers

1. `stageSlack` and `sum_expect_stageSlack_eq` — the exact telescoping identity
   along a marginal law path, together with its one-sided forms.
2. `controlledKernel` / `controlledCost` — the control layer: a pointwise
   `(state, action)` inequality survives every randomized state-feedback policy,
   which is how the "supremum over policies" strength is obtained.
3. Switching charges in three payment modes, each a separate theorem:
   * `sum_expect_scheduledCost_le_switchingBill` — span-normalized pairwise
     oscillation bills, the `C (1 + J)` shape of Question 89 (15);
   * `sum_expect_scheduledCost_le_directedCharges` — the transition-aware
     directed cost `Γᵢⱼ` of Question 89 (11)-(12), with
     `directedCharge_le_oscillationCharge` proving `Γᵢⱼ ≤ Δᵢⱼ` (13);
   * `sum_expect_cost_le_resetBudget` — total-variation / reset budgets.
4. `sum_expect_phaseCost_le` — the phase-lifted exactness layer for a periodic
   mode word, Question 89 (34)-(39): per-phase slack `≤ g` gives the
   uniform-in-shifts windowed bound `g * N + 2 * bound`.
5. Falsifier probes `AlternatingHarvest` (Question 89 (16)-(17)) and
   `PhaseHarvest` (Question 89 (40)-(42)).

Every cap here is conditioned on `IsMarginalLawPath`, which
`isMarginalLawPath_marginalLawPath` shows is always satisfiable, so none of the
statements is vacuous; the two probes additionally exhibit explicit witnesses.

## What is *not* formalized

Only the sufficiency half of Question 89 (39) is proved.  The converse
`g(w) = max over the phase occupation polytope` of Question 89 (38) is a finite
average-reward LP duality statement on the phase-augmented chain; the repo has
no average-reward LP duality (`Math.LinearAlgebra.FourierMotzkin` is raw
elimination, not a Farkas certificate for occupation measures), so that
direction is left open.  Likewise Question 89 (7), the Farkas equivalence
between per-mode harmlessness and nonemptiness of the bias polyhedron, is
assumed rather than derived: `IsModeBias` is taken as the primitive input.

## Relation to existing in-tree accounts

This layer is designed to *subsume* — but does not modify — the following
existing instances, each of which is a special case of one row above:

* `Math.Probability.AdaptiveTransitionAccount`: its fixed-potential identity
  `selectedTransitionCenteredScore_add_drift_eq_accountIncrement` is the
  constant-potential case `H t = H`, and its exceptional-transition machinery
  (`exceptionalTransitionCost_isAsymptoticallySublinear`) is a reset-budget
  charge supported on a sublinearly used index set.
* `Math.Probability.SupportedMovingKernelEpochAccount`: its epoch-selected
  potentials (`expected_epochCost_le_supportedBill_of_expectedDrift`) are the
  piecewise-constant predictable potential path `H t = potential (epoch t)`,
  whose charge is exactly the epoch-boundary oscillation bill.
* `GameTheory.Concepts.Stochastic.FinkLimit`'s time-dependent state-potential
  telescopes are the uncontrolled (`A = Unit`) special case of
  `sum_expect_stageSlack_eq`.

Actually rewriting those three files on top of this one is future work; nothing
here depends on them and nothing there is changed.
-/

set_option autoImplicit false

noncomputable section

namespace Math
namespace Probability

/-! ## Finite extrema

Small named wrappers around `Finset.sup'` / `Finset.inf'`.  They are what makes
"span-normalized bias" and "oscillation charge" statable without carrying a
nonemptiness proof through every lemma. -/

section Extrema

variable {X : Type*} [Fintype X] [Nonempty X]

/-- The maximum of a real function on a nonempty finite type. -/
def finiteMax (g : X → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty g

/-- The minimum of a real function on a nonempty finite type. -/
def finiteMin (g : X → ℝ) : ℝ := Finset.univ.inf' Finset.univ_nonempty g

/-- The span (oscillation) of a real function on a nonempty finite type. -/
def finiteSpan (g : X → ℝ) : ℝ := finiteMax g - finiteMin g

/-- The supremum norm of a real function on a nonempty finite type. -/
def finiteSupNorm (g : X → ℝ) : ℝ := finiteMax fun x => |g x|

theorem le_finiteMax (g : X → ℝ) (x : X) : g x ≤ finiteMax g :=
  Finset.le_sup' g (Finset.mem_univ x)

theorem finiteMin_le (g : X → ℝ) (x : X) : finiteMin g ≤ g x :=
  Finset.inf'_le g (Finset.mem_univ x)

theorem finiteMax_le {g : X → ℝ} {bound : ℝ} (le_bound : ∀ x, g x ≤ bound) :
    finiteMax g ≤ bound :=
  Finset.sup'_le _ g fun x _ => le_bound x

theorem le_finiteMin {g : X → ℝ} {bound : ℝ} (bound_le : ∀ x, bound ≤ g x) :
    bound ≤ finiteMin g :=
  Finset.le_inf' _ g fun x _ => bound_le x

theorem finiteMin_le_finiteMax (g : X → ℝ) : finiteMin g ≤ finiteMax g :=
  (finiteMin_le g (Classical.arbitrary X)).trans (le_finiteMax g (Classical.arbitrary X))

theorem finiteSpan_nonneg (g : X → ℝ) : 0 ≤ finiteSpan g :=
  sub_nonneg.mpr (finiteMin_le_finiteMax g)

@[simp]
theorem finiteMax_const (c : ℝ) : finiteMax (fun _ : X => c) = c :=
  le_antisymm (finiteMax_le fun _ => le_rfl)
    (le_finiteMax (fun _ : X => c) (Classical.arbitrary X))

@[simp]
theorem finiteMin_const (c : ℝ) : finiteMin (fun _ : X => c) = c :=
  le_antisymm (finiteMin_le (fun _ : X => c) (Classical.arbitrary X)) (le_finiteMin fun _ => le_rfl)

theorem finiteMax_le_finiteSupNorm (g : X → ℝ) : finiteMax g ≤ finiteSupNorm g :=
  finiteMax_le fun x => (le_abs_self (g x)).trans (le_finiteMax (fun y => |g y|) x)

theorem expect_le_finiteMax (law : PMF X) (g : X → ℝ) : expect law g ≤ finiteMax g := by
  calc
    expect law g ≤ expect law (fun _ => finiteMax g) := expect_mono law g _ (le_finiteMax g)
    _ = finiteMax g := expect_const _ _

theorem finiteMin_le_expect (law : PMF X) (g : X → ℝ) : finiteMin g ≤ expect law g := by
  calc
    finiteMin g = expect law (fun _ => finiteMin g) := (expect_const _ _).symm
    _ ≤ expect law g := expect_mono law _ g (finiteMin_le g)

end Extrema

/-! ## The predictable coboundary and its exact telescope -/

section Core

variable {S : Type*}

/-- The one-step coboundary defect of a *predictable* potential pair: the cost
paid now, plus the expected value of the *next* stage's potential, minus the
current stage's potential.  This is the object Question 89 (34) bounds by a
per-stage charge `αₜ`. -/
def switchedLocalSlack (kernel : S → PMF S) (cost current next : S → ℝ) (state : S) : ℝ :=
  cost state + expect (kernel state) next - current state

/-- The stage-`stage` slack of a predictable potential path. -/
def stageSlack (kernel : ℕ → S → PMF S) (cost potential : ℕ → S → ℝ) (stage : ℕ) : S → ℝ :=
  switchedLocalSlack (kernel stage) (cost stage) (potential stage) (potential (stage + 1))

/-- `law` is the marginal law path of the per-stage kernels `kernel`. -/
def IsMarginalLawPath (law : ℕ → PMF S) (kernel : ℕ → S → PMF S) : Prop :=
  ∀ stage, law (stage + 1) = (law stage).bind (kernel stage)

/-- The marginal law path generated by an initial law and per-stage kernels. -/
def marginalLawPath (initial : PMF S) (kernel : ℕ → S → PMF S) : ℕ → PMF S
  | 0 => initial
  | stage + 1 => (marginalLawPath initial kernel stage).bind (kernel stage)

/-- The `IsMarginalLawPath` hypothesis used everywhere below is always
satisfiable: every initial law generates one.  This is what keeps the caps of
this file from being vacuous. -/
theorem isMarginalLawPath_marginalLawPath (initial : PMF S) (kernel : ℕ → S → PMF S) :
    IsMarginalLawPath (marginalLawPath initial kernel) kernel :=
  fun _ => rfl

/-- One stage of the integration by parts: the expected slack is the expected
cost plus the increment of the expected potential.  This is the whole content of
the calculus; everything below is bookkeeping. -/
theorem expect_stageSlack_eq [Finite S]
    (law : ℕ → PMF S) (kernel : ℕ → S → PMF S) (cost potential : ℕ → S → ℝ)
    (path : IsMarginalLawPath law kernel) (stage : ℕ) :
    expect (law stage) (stageSlack kernel cost potential stage) =
      expect (law stage) (cost stage) +
        (expect (law (stage + 1)) (potential (stage + 1)) -
          expect (law stage) (potential stage)) := by
  have successor :
      expect (law stage) (fun state => expect (kernel stage state) (potential (stage + 1))) =
        expect (law (stage + 1)) (potential (stage + 1)) := by
    rw [path stage, expect_bind]
  have unfolded :
      stageSlack kernel cost potential stage =
        fun state =>
          (cost stage state + expect (kernel stage state) (potential (stage + 1))) -
            potential stage state := rfl
  rw [unfolded,
    expect_sub (law stage)
      (fun state => cost stage state + expect (kernel stage state) (potential (stage + 1)))
      (potential stage),
    expect_add (law stage) (cost stage)
      (fun state => expect (kernel stage state) (potential (stage + 1))),
    successor]
  ring

/-- **Exact switching identity.**  Over any window `[start, start + horizon)`,
the accumulated expected slack equals the accumulated expected cost plus the
boundary motion of the expected potential.  Question 89 (8) and (35) are the
two one-sided readings of this equation. -/
theorem sum_expect_stageSlack_eq [Finite S]
    (law : ℕ → PMF S) (kernel : ℕ → S → PMF S) (cost potential : ℕ → S → ℝ)
    (path : IsMarginalLawPath law kernel) (start horizon : ℕ) :
    (∑ i ∈ Finset.range horizon,
        expect (law (start + i)) (stageSlack kernel cost potential (start + i))) =
      (∑ i ∈ Finset.range horizon, expect (law (start + i)) (cost (start + i))) +
        (expect (law (start + horizon)) (potential (start + horizon)) -
          expect (law start) (potential start)) := by
  induction horizon with
  | zero => simp
  | succ horizon inductionHypothesis =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, inductionHypothesis,
        expect_stageSlack_eq law kernel cost potential path (start + horizon),
        show start + horizon + 1 = start + (horizon + 1) by omega]
      ring

/-- The same identity solved for the accumulated cost: cost equals slack plus
the *reversed* boundary motion of the potential. -/
theorem sum_expect_cost_eq_sum_expect_stageSlack_add_boundary [Finite S]
    (law : ℕ → PMF S) (kernel : ℕ → S → PMF S) (cost potential : ℕ → S → ℝ)
    (path : IsMarginalLawPath law kernel) (start horizon : ℕ) :
    (∑ i ∈ Finset.range horizon, expect (law (start + i)) (cost (start + i))) =
      (∑ i ∈ Finset.range horizon,
          expect (law (start + i)) (stageSlack kernel cost potential (start + i))) +
        (expect (law start) (potential start) -
          expect (law (start + horizon)) (potential (start + horizon))) := by
  have identity := sum_expect_stageSlack_eq law kernel cost potential path start horizon
  linarith

/-- **One-sided switching bound.**  A per-stage charge dominating the slack
pointwise gives the accumulated cost bound of Question 89 (35). -/
theorem sum_expect_cost_le_of_stageSlack_le [Finite S]
    (law : ℕ → PMF S) (kernel : ℕ → S → PMF S) (cost potential : ℕ → S → ℝ)
    (path : IsMarginalLawPath law kernel) (charge : ℕ → ℝ) (start horizon : ℕ)
    (slack_le : ∀ i, i < horizon → ∀ state,
      stageSlack kernel cost potential (start + i) state ≤ charge (start + i)) :
    (∑ i ∈ Finset.range horizon, expect (law (start + i)) (cost (start + i))) ≤
      (∑ i ∈ Finset.range horizon, charge (start + i)) +
        (expect (law start) (potential start) -
          expect (law (start + horizon)) (potential (start + horizon))) := by
  have identity :=
    sum_expect_cost_eq_sum_expect_stageSlack_add_boundary law kernel cost potential path
      start horizon
  have slack_sum :
      (∑ i ∈ Finset.range horizon,
          expect (law (start + i)) (stageSlack kernel cost potential (start + i))) ≤
        ∑ i ∈ Finset.range horizon, charge (start + i) := by
    refine Finset.sum_le_sum fun i memberOfRange => ?_
    calc
      expect (law (start + i)) (stageSlack kernel cost potential (start + i)) ≤
          expect (law (start + i)) (fun _ => charge (start + i)) :=
        expect_mono _ _ _ (slack_le i (Finset.mem_range.mp memberOfRange))
      _ = charge (start + i) := expect_const _ _
  linarith

/-- The boundary term of the one-sided bound, replaced by the deterministic span
of the two endpoint potentials. -/
theorem sum_expect_cost_le_of_stageSlack_le_span [Fintype S] [Nonempty S]
    (law : ℕ → PMF S) (kernel : ℕ → S → PMF S) (cost potential : ℕ → S → ℝ)
    (path : IsMarginalLawPath law kernel) (charge : ℕ → ℝ) (start horizon : ℕ)
    (slack_le : ∀ i, i < horizon → ∀ state,
      stageSlack kernel cost potential (start + i) state ≤ charge (start + i)) :
    (∑ i ∈ Finset.range horizon, expect (law (start + i)) (cost (start + i))) ≤
      (∑ i ∈ Finset.range horizon, charge (start + i)) +
        (finiteMax (potential start) - finiteMin (potential (start + horizon))) := by
  have raw :=
    sum_expect_cost_le_of_stageSlack_le law kernel cost potential path charge start horizon
      slack_le
  have upper : expect (law start) (potential start) ≤ finiteMax (potential start) :=
    expect_le_finiteMax _ _
  have lower :
      finiteMin (potential (start + horizon)) ≤
        expect (law (start + horizon)) (potential (start + horizon)) :=
    finiteMin_le_expect _ _
  linarith

end Core

/-! ## The control layer

A controller picks actions; the environment supplies the kernels.  The point of
this section is that a pointwise inequality quantified over `(state, action)`
is inherited by *every* randomized state-feedback policy, so the resulting caps
hold uniformly over policies. -/

section Control

variable {S A : Type*}

/-- The one-step kernel induced by a randomized state-feedback policy. -/
def controlledKernel (kernel : ℕ → S → A → PMF S) (policy : ℕ → S → PMF A) :
    ℕ → S → PMF S :=
  fun stage state => (policy stage state).bind (kernel stage state)

/-- The one-step expected cost induced by a randomized state-feedback policy. -/
def controlledCost (reward : ℕ → S → A → ℝ) (policy : ℕ → S → PMF A) : ℕ → S → ℝ :=
  fun stage state => expect (policy stage state) (reward stage state)

/-- A pointwise `(state, action)` slack bound survives every policy. -/
theorem stageSlack_controlled_le [Finite S] [Finite A]
    (kernel : ℕ → S → A → PMF S) (reward : ℕ → S → A → ℝ) (policy : ℕ → S → PMF A)
    (potential : ℕ → S → ℝ) (charge : ℝ) (stage : ℕ)
    (pointwise : ∀ state action,
      reward stage state action + expect (kernel stage state action) (potential (stage + 1)) -
        potential stage state ≤ charge)
    (state : S) :
    stageSlack (controlledKernel kernel policy) (controlledCost reward policy) potential stage
        state ≤ charge := by
  simp only [stageSlack, switchedLocalSlack, controlledKernel, controlledCost]
  rw [expect_bind,
    ← expect_add (policy stage state) (reward stage state)
      (fun action => expect (kernel stage state action) (potential (stage + 1)))]
  have key :
      expect (policy stage state)
          (fun action =>
            reward stage state action + expect (kernel stage state action) (potential (stage + 1)))
        ≤ charge + potential stage state := by
    calc
      expect (policy stage state)
            (fun action =>
              reward stage state action +
                expect (kernel stage state action) (potential (stage + 1))) ≤
          expect (policy stage state) (fun _ => charge + potential stage state) := by
        refine expect_mono _ _ _ fun action => ?_
        have step := pointwise state action
        linarith
      _ = charge + potential stage state := expect_const _ _
  linarith

end Control

/-! ## Switching charges

A schedule `κ : ℕ → K` selects a mode at each stage.  The mode-lifted potential
path is `H t = h (κ t)`.  Three separate payment modes are proved below. -/

section Switching

variable {S A K : Type*} [Fintype S] [Nonempty S] [Fintype A] [Nonempty A]

/-- Question 89 (5)/(6): `h mode` is a bias (relative value function) for
`mode`, i.e. it lies in the mode's bias polyhedron `ℋ_mode`. -/
def IsModeBias (kernel : K → S → A → PMF S) (reward : K → S → A → ℝ) (bias : K → S → ℝ)
    (mode : K) : Prop :=
  ∀ state action,
    reward mode state action + expect (kernel mode state action) (bias mode) - bias mode state ≤ 0

/-- Question 89 (10): the pairwise oscillation charge `Δᵢⱼ = maxₓ (hⱼ x - hᵢ x)`. -/
def oscillationCharge (bias : K → S → ℝ) (source target : K) : ℝ :=
  finiteMax fun state => bias target state - bias source state

/-- Question 89 (11): the transition-aware directed charge
`Γᵢⱼ = max_{s,a} [fᵢ + Qᵢ hⱼ - hᵢ]`. -/
def directedCharge (kernel : K → S → A → PMF S) (reward : K → S → A → ℝ) (bias : K → S → ℝ)
    (source target : K) : ℝ :=
  finiteMax fun pair : S × A =>
    reward source pair.1 pair.2 + expect (kernel source pair.1 pair.2) (bias target) -
      bias source pair.1

theorem le_directedCharge (kernel : K → S → A → PMF S) (reward : K → S → A → ℝ)
    (bias : K → S → ℝ) (source target : K) (state : S) (action : A) :
    reward source state action + expect (kernel source state action) (bias target) -
        bias source state ≤ directedCharge kernel reward bias source target :=
  le_finiteMax
    (fun pair : S × A =>
      reward source pair.1 pair.2 + expect (kernel source pair.1 pair.2) (bias target) -
        bias source pair.1)
    (state, action)

/-- Question 89 (13): the directed charge is sharper than the oscillation
charge.  This is where the bias inequality for the *source* mode is spent. -/
theorem directedCharge_le_oscillationCharge [Finite S]
    (kernel : K → S → A → PMF S) (reward : K → S → A → ℝ) (bias : K → S → ℝ)
    (source target : K) (source_bias : IsModeBias kernel reward bias source) :
    directedCharge kernel reward bias source target ≤ oscillationCharge bias source target := by
  refine finiteMax_le ?_
  rintro ⟨state, action⟩
  have transported :
      expect (kernel source state action) (bias target) -
          expect (kernel source state action) (bias source) ≤
        oscillationCharge bias source target := by
    rw [← expect_sub]
    calc
      expect (kernel source state action)
            (fun successor => bias target successor - bias source successor) ≤
          expect (kernel source state action) (fun _ => oscillationCharge bias source target) :=
        expect_mono _ _ _ fun successor =>
          le_finiteMax (fun state => bias target state - bias source state) successor
      _ = oscillationCharge bias source target := expect_const _ _
  have base := source_bias state action
  simp only
  linarith

/-- A mode never charges itself: `Γᵢᵢ ≤ 0`. -/
theorem directedCharge_self_nonpos (kernel : K → S → A → PMF S) (reward : K → S → A → ℝ)
    (bias : K → S → ℝ) (mode : K) (mode_bias : IsModeBias kernel reward bias mode) :
    directedCharge kernel reward bias mode mode ≤ 0 := by
  refine finiteMax_le ?_
  rintro ⟨state, action⟩
  exact mode_bias state action

@[simp]
theorem oscillationCharge_self (bias : K → S → ℝ) (mode : K) :
    oscillationCharge bias mode mode = 0 := by
  simp [oscillationCharge]

/-- Every oscillation charge of a nonnegative, `bound`-dominated bias family is
at most `bound`.  This is the span normalization of Question 89 (14). -/
theorem oscillationCharge_le_of_normalized (bias : K → S → ℝ) (bound : ℝ)
    (nonneg : ∀ mode state, 0 ≤ bias mode state)
    (le_bound : ∀ mode state, bias mode state ≤ bound) (source target : K) :
    oscillationCharge bias source target ≤ bound := by
  refine finiteMax_le fun state => ?_
  have lower := nonneg source state
  have upper := le_bound target state
  linarith

/-! ### Span normalization -/

/-- The bias family shifted so that every mode's minimum is `0`.  Adding a
constant to a bias does not change its bias inequality. -/
def normalizedBias (bias : K → S → ℝ) (mode : K) (state : S) : ℝ :=
  bias mode state - finiteMin (bias mode)

omit [Fintype A] [Nonempty A] in
theorem isModeBias_normalizedBias [Finite S]
    (kernel : K → S → A → PMF S) (reward : K → S → A → ℝ) (bias : K → S → ℝ) (mode : K)
    (mode_bias : IsModeBias kernel reward bias mode) :
    IsModeBias kernel reward (normalizedBias bias) mode := by
  intro state action
  have shifted :
      expect (kernel mode state action) (normalizedBias bias mode) =
        expect (kernel mode state action) (bias mode) - finiteMin (bias mode) := by
    have unfolded :
        normalizedBias bias mode =
          fun successor => bias mode successor - finiteMin (bias mode) := rfl
    rw [unfolded, expect_sub, expect_const]
  have base := mode_bias state action
  simp only [normalizedBias, shifted]
  linarith

theorem normalizedBias_nonneg (bias : K → S → ℝ) (mode : K) (state : S) :
    0 ≤ normalizedBias bias mode state :=
  sub_nonneg.mpr (finiteMin_le _ _)

theorem normalizedBias_le_finiteSpan (bias : K → S → ℝ) (mode : K) (state : S) :
    normalizedBias bias mode state ≤ finiteSpan (bias mode) :=
  sub_le_sub_right (le_finiteMax _ _) _

/-- Question 89 (14): the uniform span constant `C = maxₖ span hₖ`. -/
def uniformBiasSpan [Fintype K] [Nonempty K] (bias : K → S → ℝ) : ℝ :=
  finiteMax fun mode => finiteSpan (bias mode)

theorem normalizedBias_le_uniformBiasSpan [Fintype K] [Nonempty K]
    (bias : K → S → ℝ) (mode : K) (state : S) :
    normalizedBias bias mode state ≤ uniformBiasSpan bias :=
  (normalizedBias_le_finiteSpan bias mode state).trans
    (le_finiteMax (fun other => finiteSpan (bias other)) mode)

theorem uniformBiasSpan_nonneg [Fintype K] [Nonempty K] (bias : K → S → ℝ) :
    0 ≤ uniformBiasSpan bias :=
  (finiteSpan_nonneg (bias (Classical.arbitrary K))).trans
    (le_finiteMax (fun other => finiteSpan (bias other)) (Classical.arbitrary K))

/-! ### Scheduled systems and the mode-lifted potential -/

/-- The per-stage kernel family selected by a mode schedule. -/
def scheduledKernel (kernel : K → S → A → PMF S) (schedule : ℕ → K) : ℕ → S → A → PMF S :=
  fun stage => kernel (schedule stage)

/-- The per-stage reward family selected by a mode schedule. -/
def scheduledReward (reward : K → S → A → ℝ) (schedule : ℕ → K) : ℕ → S → A → ℝ :=
  fun stage => reward (schedule stage)

/-- The mode-lifted predictable potential path `H t = h (κ t)`. -/
def modeLiftedPotential (bias : K → S → ℝ) (schedule : ℕ → K) : ℕ → S → ℝ :=
  fun stage => bias (schedule stage)

/-- The mode-lifted potential pays exactly the directed charge of the transition
it performs. -/
theorem stageSlack_modeLifted_le_directedCharge [Finite A]
    (kernel : K → S → A → PMF S) (reward : K → S → A → ℝ) (bias : K → S → ℝ)
    (schedule : ℕ → K) (policy : ℕ → S → PMF A) (stage : ℕ) (state : S) :
    stageSlack (controlledKernel (scheduledKernel kernel schedule) policy)
        (controlledCost (scheduledReward reward schedule) policy)
        (modeLiftedPotential bias schedule) stage state ≤
      directedCharge kernel reward bias (schedule stage) (schedule (stage + 1)) := by
  refine stageSlack_controlled_le _ _ _ _ _ _ ?_ _
  intro source action
  exact le_directedCharge kernel reward bias (schedule stage) (schedule (stage + 1)) source action

/-- **Payment mode (b): transition-aware directed costs.**  Question 89 (12). -/
theorem sum_expect_scheduledCost_le_directedCharges [Finite A]
    (kernel : K → S → A → PMF S) (reward : K → S → A → ℝ) (bias : K → S → ℝ)
    (schedule : ℕ → K) (policy : ℕ → S → PMF A) (law : ℕ → PMF S)
    (path : IsMarginalLawPath law (controlledKernel (scheduledKernel kernel schedule) policy))
    (start horizon : ℕ) :
    (∑ i ∈ Finset.range horizon,
        expect (law (start + i))
          (controlledCost (scheduledReward reward schedule) policy (start + i))) ≤
      (∑ i ∈ Finset.range horizon,
          directedCharge kernel reward bias (schedule (start + i)) (schedule (start + i + 1))) +
        (finiteMax (bias (schedule start)) - finiteMin (bias (schedule (start + horizon)))) :=
  sum_expect_cost_le_of_stageSlack_le_span law _ _ (modeLiftedPotential bias schedule) path
    (fun stage => directedCharge kernel reward bias (schedule stage) (schedule (stage + 1)))
    start horizon
    (fun i _ state =>
      stageSlack_modeLifted_le_directedCharge kernel reward bias schedule policy (start + i) state)

/-! ### Payment mode (a): span-normalized oscillation bills

To avoid charging a switch at the right endpoint of a window, the potential path
is the mode-lifted potential of the schedule *frozen* after the window's last
stage.  The frozen schedule is used only for the potential; the kernels and
rewards keep the true schedule. -/

/-- The schedule frozen after stage `last`. -/
def frozenSchedule (schedule : ℕ → K) (last stage : ℕ) : K := schedule (min stage last)

/-- `bound` is charged exactly at the stages where the frozen schedule changes. -/
def frozenSwitchCharge [DecidableEq K] (bound : ℝ) (schedule : ℕ → K) (last stage : ℕ) : ℝ :=
  if frozenSchedule schedule last (stage + 1) ≠ frozenSchedule schedule last stage then bound
  else 0

/-- Question 89's `J_{s,N}`: the number of mode changes strictly inside the
window `[start, start + steps]`, which has length `steps + 1`. -/
def windowSwitchCount [DecidableEq K] (schedule : ℕ → K) (start steps : ℕ) : ℕ :=
  ((Finset.range steps).filter fun i => schedule (start + i + 1) ≠ schedule (start + i)).card

theorem sum_frozenSwitchCharge [DecidableEq K] (bound : ℝ) (schedule : ℕ → K)
    (start steps : ℕ) :
    (∑ i ∈ Finset.range (steps + 1),
        frozenSwitchCharge bound schedule (start + steps) (start + i)) =
      bound * windowSwitchCount schedule start steps := by
  rw [Finset.sum_range_succ]
  have last_zero :
      frozenSwitchCharge bound schedule (start + steps) (start + steps) = 0 := by
    simp only [frozenSwitchCharge, frozenSchedule,
      show min (start + steps + 1) (start + steps) = start + steps by omega,
      show min (start + steps) (start + steps) = start + steps by omega]
    simp
  rw [last_zero, add_zero]
  have inner :
      ∀ i ∈ Finset.range steps,
        frozenSwitchCharge bound schedule (start + steps) (start + i) =
          if schedule (start + i + 1) ≠ schedule (start + i) then bound else 0 := by
    intro i memberOfRange
    have index_lt : i < steps := Finset.mem_range.mp memberOfRange
    simp only [frozenSwitchCharge, frozenSchedule,
      show min (start + i + 1) (start + steps) = start + i + 1 by omega,
      show min (start + i) (start + steps) = start + i by omega]
  rw [Finset.sum_congr rfl inner, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    windowSwitchCount, mul_comm]

omit [Fintype S] [Fintype A] in
/-- Every stage of the window pays at most its frozen switch charge. -/
theorem stageSlack_frozen_le [Finite S] [Finite A] [DecidableEq K]
    (kernel : K → S → A → PMF S) (reward : K → S → A → ℝ) (bias : K → S → ℝ)
    (schedule : ℕ → K) (policy : ℕ → S → PMF A) (bound : ℝ)
    (all_bias : ∀ mode, IsModeBias kernel reward bias mode)
    (nonneg : ∀ mode state, 0 ≤ bias mode state)
    (le_bound : ∀ mode state, bias mode state ≤ bound)
    (last stage : ℕ) (stage_le : stage ≤ last) (state : S) :
    stageSlack (controlledKernel (scheduledKernel kernel schedule) policy)
        (controlledCost (scheduledReward reward schedule) policy)
        (modeLiftedPotential bias (frozenSchedule schedule last)) stage state ≤
      frozenSwitchCharge bound schedule last stage := by
  letI : Fintype S := Fintype.ofFinite S
  letI : Fintype A := Fintype.ofFinite A
  have current : min stage last = stage := min_eq_left stage_le
  have charge_eq :
      frozenSwitchCharge bound schedule last stage =
        if schedule (min (stage + 1) last) ≠ schedule stage then bound else 0 := by
    simp only [frozenSwitchCharge, frozenSchedule, current]
  have charge_bound :
      directedCharge kernel reward bias (schedule stage) (schedule (min (stage + 1) last)) ≤
        frozenSwitchCharge bound schedule last stage := by
    rw [charge_eq]
    by_cases changed : schedule (min (stage + 1) last) ≠ schedule stage
    · rw [if_pos changed]
      refine le_trans (directedCharge_le_oscillationCharge kernel reward bias _ _
        (all_bias (schedule stage))) ?_
      exact oscillationCharge_le_of_normalized bias bound nonneg le_bound _ _
    · rw [not_not] at changed
      rw [if_neg (by simp [changed]), changed]
      exact directedCharge_self_nonpos kernel reward bias (schedule stage)
        (all_bias (schedule stage))
  have pointwise :
      ∀ source action,
        scheduledReward reward schedule stage source action +
            expect (scheduledKernel kernel schedule stage source action)
              (modeLiftedPotential bias (frozenSchedule schedule last) (stage + 1)) -
            modeLiftedPotential bias (frozenSchedule schedule last) stage source ≤
          frozenSwitchCharge bound schedule last stage := by
    intro source action
    have raw :=
      le_directedCharge kernel reward bias (schedule stage) (schedule (min (stage + 1) last))
        source action
    simp only [scheduledReward, scheduledKernel, modeLiftedPotential, frozenSchedule, current]
    linarith
  exact stageSlack_controlled_le _ _ _ _ _ _ pointwise _

omit [Fintype S] [Fintype A] in
/-- **Payment mode (a): the `C (1 + J)` switching bill.**  Question 89 (15),
verbatim: with a nonnegative bias family dominated by `bound`, the expected
reward over any window of length `steps + 1` is at most
`bound * (1 + #switches strictly inside the window)`, uniformly in the shift,
the horizon and the policy. -/
theorem sum_expect_scheduledCost_le_switchingBill [Finite S] [Finite A] [DecidableEq K]
    (kernel : K → S → A → PMF S) (reward : K → S → A → ℝ) (bias : K → S → ℝ)
    (schedule : ℕ → K) (policy : ℕ → S → PMF A) (law : ℕ → PMF S) (bound : ℝ)
    (path : IsMarginalLawPath law (controlledKernel (scheduledKernel kernel schedule) policy))
    (all_bias : ∀ mode, IsModeBias kernel reward bias mode)
    (nonneg : ∀ mode state, 0 ≤ bias mode state)
    (le_bound : ∀ mode state, bias mode state ≤ bound)
    (start steps : ℕ) :
    (∑ i ∈ Finset.range (steps + 1),
        expect (law (start + i))
          (controlledCost (scheduledReward reward schedule) policy (start + i))) ≤
      bound * (1 + windowSwitchCount schedule start steps) := by
  letI : Fintype S := Fintype.ofFinite S
  have windowed :=
    sum_expect_cost_le_of_stageSlack_le law
      (controlledKernel (scheduledKernel kernel schedule) policy)
      (controlledCost (scheduledReward reward schedule) policy)
      (modeLiftedPotential bias (frozenSchedule schedule (start + steps))) path
      (frozenSwitchCharge bound schedule (start + steps)) start (steps + 1)
      (fun i index_lt state =>
        stageSlack_frozen_le kernel reward bias schedule policy bound all_bias nonneg le_bound
          (start + steps) (start + i) (by omega) state)
  rw [sum_frozenSwitchCharge] at windowed
  have potential_head :
      modeLiftedPotential bias (frozenSchedule schedule (start + steps)) start =
        bias (schedule start) := by
    simp only [modeLiftedPotential, frozenSchedule, show min start (start + steps) = start by omega]
  have potential_tail :
      modeLiftedPotential bias (frozenSchedule schedule (start + steps)) (start + (steps + 1)) =
        bias (schedule (start + steps)) := by
    simp only [modeLiftedPotential, frozenSchedule,
      show min (start + (steps + 1)) (start + steps) = start + steps by omega]
  rw [potential_head, potential_tail] at windowed
  have head : expect (law start) (bias (schedule start)) ≤ bound :=
    (expect_le_finiteMax _ _).trans (finiteMax_le fun state => le_bound _ state)
  have tail :
      (0 : ℝ) ≤ expect (law (start + (steps + 1))) (bias (schedule (start + steps))) :=
    (le_finiteMin fun state => nonneg _ state).trans (finiteMin_le_expect _ _)
  have expanded : bound * (1 + (windowSwitchCount schedule start steps : ℝ)) =
      bound * windowSwitchCount schedule start steps + bound := by ring
  rw [expanded]
  linarith

/-- The `o(N)`-switch regime of Question 89 Part B: if the number of switches in
a growing window is sublinear, the whole switching bill is sublinear in the
sense of `Math.Probability.IsAsymptoticallySublinear`. -/
theorem isAsymptoticallySublinear_switchingBill [DecidableEq K]
    (schedule : ℕ → K) (bound : ℝ) (start : ℕ)
    (sparse : IsAsymptoticallySublinear
      fun steps => (windowSwitchCount schedule start steps : ℝ)) :
    IsAsymptoticallySublinear
      fun steps => bound * (1 + (windowSwitchCount schedule start steps : ℝ)) := by
  have expanded :
      (fun steps => bound * (1 + (windowSwitchCount schedule start steps : ℝ))) =
        fun steps => bound + bound * (windowSwitchCount schedule start steps : ℝ) := by
    funext steps
    ring
  rw [expanded]
  exact IsAsymptoticallySublinear.add (IsAsymptoticallySublinear.const bound)
    (IsAsymptoticallySublinear.const_mul sparse bound)

omit [Fintype A] [Nonempty A] in
/-- If a *single* state potential is a bias for every mode — Question 89 (5) —
then no switch is ever charged and the cap is the span of that potential,
uniformly in the schedule, the shift, the horizon and the policy. -/
theorem sum_expect_scheduledCost_le_span_of_commonBias [Finite A]
    (kernel : K → S → A → PMF S) (reward : K → S → A → ℝ) (common : S → ℝ)
    (schedule : ℕ → K) (policy : ℕ → S → PMF A) (law : ℕ → PMF S)
    (path : IsMarginalLawPath law (controlledKernel (scheduledKernel kernel schedule) policy))
    (common_bias : ∀ mode, IsModeBias kernel reward (fun _ => common) mode)
    (start horizon : ℕ) :
    (∑ i ∈ Finset.range horizon,
        expect (law (start + i))
          (controlledCost (scheduledReward reward schedule) policy (start + i))) ≤
      finiteSpan common := by
  have windowed :=
    sum_expect_cost_le_of_stageSlack_le_span law
      (controlledKernel (scheduledKernel kernel schedule) policy)
      (controlledCost (scheduledReward reward schedule) policy)
      (fun _ => common) path (fun _ => 0) start horizon
      (fun i _ state => by
        refine stageSlack_controlled_le _ _ _ _ _ _ ?_ _
        intro source action
        exact common_bias (schedule (start + i)) source action)
  simpa [finiteSpan] using windowed

end Switching

/-! ### Payment mode (c): total-variation / reset budgets

If every stage's potential is a bias for *its own* stage, the only charge left
is the motion of the potential path itself. -/

section ResetBudget

variable {S A : Type*} [Fintype S] [Nonempty S] [Fintype A] [Nonempty A]

/-- The accumulated reset (total-variation) budget of a potential path. -/
def potentialResetBudget (potential : ℕ → S → ℝ) (start horizon : ℕ) : ℝ :=
  ∑ i ∈ Finset.range horizon,
    finiteSupNorm fun state => potential (start + i + 1) state - potential (start + i) state

omit [Fintype A] [Nonempty A] in
theorem stageSlack_le_potentialMotion [Finite A]
    (kernel : ℕ → S → A → PMF S) (reward : ℕ → S → A → ℝ) (policy : ℕ → S → PMF A)
    (potential : ℕ → S → ℝ) (stage : ℕ)
    (stage_bias : ∀ state action,
      reward stage state action + expect (kernel stage state action) (potential stage) -
        potential stage state ≤ 0)
    (state : S) :
    stageSlack (controlledKernel kernel policy) (controlledCost reward policy) potential stage
        state ≤
      finiteSupNorm fun successor => potential (stage + 1) successor - potential stage successor :=
  by
  refine stageSlack_controlled_le _ _ _ _ _ _ ?_ _
  intro source action
  have transported :
      expect (kernel stage source action) (potential (stage + 1)) -
          expect (kernel stage source action) (potential stage) ≤
        finiteSupNorm fun successor =>
          potential (stage + 1) successor - potential stage successor := by
    rw [← expect_sub]
    calc
      expect (kernel stage source action)
            (fun successor => potential (stage + 1) successor - potential stage successor) ≤
          expect (kernel stage source action)
            (fun _ =>
              finiteSupNorm fun successor =>
                potential (stage + 1) successor - potential stage successor) := by
        refine expect_mono _ _ _ fun successor => ?_
        exact le_trans (le_abs_self _)
          (le_finiteMax
            (fun other => |potential (stage + 1) other - potential stage other|) successor)
      _ = _ := expect_const _ _
  have base := stage_bias source action
  linarith

omit [Fintype A] [Nonempty A] in
/-- **Payment mode (c).**  A stagewise-bias potential path costs only its own
total variation plus the endpoint span. -/
theorem sum_expect_cost_le_resetBudget [Finite A]
    (kernel : ℕ → S → A → PMF S) (reward : ℕ → S → A → ℝ) (policy : ℕ → S → PMF A)
    (potential : ℕ → S → ℝ) (law : ℕ → PMF S)
    (path : IsMarginalLawPath law (controlledKernel kernel policy))
    (stage_bias : ∀ stage state action,
      reward stage state action + expect (kernel stage state action) (potential stage) -
        potential stage state ≤ 0)
    (start horizon : ℕ) :
    (∑ i ∈ Finset.range horizon,
        expect (law (start + i)) (controlledCost reward policy (start + i))) ≤
      potentialResetBudget potential start horizon +
        (finiteMax (potential start) - finiteMin (potential (start + horizon))) :=
  sum_expect_cost_le_of_stageSlack_le_span law (controlledKernel kernel policy)
    (controlledCost reward policy) potential path
    (fun stage => finiteSupNorm fun state => potential (stage + 1) state - potential stage state)
    start horizon
    (fun i _ state =>
      stageSlack_le_potentialMotion kernel reward policy potential (start + i)
        (stage_bias (start + i)) state)

omit [Fintype A] [Nonempty A] in
/-- A bounded reset budget gives a horizon-free cap: bounded total charge. -/
theorem sum_expect_cost_le_of_bounded_resetBudget [Finite A]
    (kernel : ℕ → S → A → PMF S) (reward : ℕ → S → A → ℝ) (policy : ℕ → S → PMF A)
    (potential : ℕ → S → ℝ) (law : ℕ → PMF S) (budget potentialBound : ℝ) (start horizon : ℕ)
    (path : IsMarginalLawPath law (controlledKernel kernel policy))
    (stage_bias : ∀ stage state action,
      reward stage state action + expect (kernel stage state action) (potential stage) -
        potential stage state ≤ 0)
    (budget_le : ∀ n, potentialResetBudget potential start n ≤ budget)
    (potential_le : ∀ stage state, |potential stage state| ≤ potentialBound) :
    (∑ i ∈ Finset.range horizon,
        expect (law (start + i)) (controlledCost reward policy (start + i))) ≤
      budget + 2 * potentialBound := by
  have windowed :=
    sum_expect_cost_le_resetBudget kernel reward policy potential law path stage_bias start horizon
  have head : finiteMax (potential start) ≤ potentialBound :=
    finiteMax_le fun state => (le_abs_self _).trans (potential_le start state)
  have tail : -potentialBound ≤ finiteMin (potential (start + horizon)) :=
    le_finiteMin fun state => neg_le_of_abs_le (potential_le (start + horizon) state)
  have budgeted := budget_le horizon
  linarith

end ResetBudget

/-! ## The phase-lifted exactness layer

For a periodic mode word the *exact* schedule-adapted invariant is indexed by
the phase, not by the mode: Question 89 (37)-(39).  The same mode occurring at
two phases may be reachable at different states with different accumulated
credit, so per-mode biases are strictly conservative (see `PhaseHarvest`). -/

section Phase

variable {S A K : Type*} [Fintype S] [Nonempty S] [Fintype A] [Nonempty A] {P : ℕ}

/-- The schedule generated by a period-`P` mode word. -/
def phaseSchedule (word : ZMod P → K) : ℕ → K := fun stage => word (stage : ZMod P)

/-- The phase-augmented predictable potential path induced by a cyclic family
`H₀, …, H_{P-1}` with `H_P = H₀`. -/
def phasePotential (phaseBias : ZMod P → S → ℝ) : ℕ → S → ℝ :=
  fun stage => phaseBias (stage : ZMod P)

/-- Question 89 (37): the phase-augmented bias inequalities with slack `g`.
The cyclic closure `H_P = H₀` is automatic because the index is `ZMod P`. -/
def HasPhaseSlack (kernel : K → S → A → PMF S) (reward : K → S → A → ℝ)
    (word : ZMod P → K) (phaseBias : ZMod P → S → ℝ) (g : ℝ) : Prop :=
  ∀ phase state action,
    reward (word phase) state action +
        expect (kernel (word phase) state action) (phaseBias (phase + 1)) -
      phaseBias phase state ≤ g

omit [Fintype S] [Nonempty S] [Fintype A] [Nonempty A] in
theorem stageSlack_phase_le [Finite S] [Finite A]
    (kernel : K → S → A → PMF S) (reward : K → S → A → ℝ) (word : ZMod P → K)
    (phaseBias : ZMod P → S → ℝ) (g : ℝ) (policy : ℕ → S → PMF A)
    (slack : HasPhaseSlack kernel reward word phaseBias g) (stage : ℕ) (state : S) :
    stageSlack (controlledKernel (scheduledKernel kernel (phaseSchedule word)) policy)
        (controlledCost (scheduledReward reward (phaseSchedule word)) policy)
        (phasePotential phaseBias) stage state ≤ g := by
  refine stageSlack_controlled_le _ _ _ _ _ _ ?_ _
  intro source action
  have successor : ((stage + 1 : ℕ) : ZMod P) = ((stage : ZMod P) + 1) := by push_cast; ring
  simp only [scheduledReward, scheduledKernel, phaseSchedule, phasePotential, successor]
  exact slack (stage : ZMod P) source action

omit [Fintype S] [Nonempty S] [Fintype A] [Nonempty A] in
/-- **Phase-lifted uniform windowed bound.**  Question 89 (39), sufficiency
direction: per-phase slack `≤ g` together with `|H| ≤ bound` gives
`sup over shifts of E Σ ≤ g * N + 2 * bound`, with the additive constant
explicit and independent of the shift, the horizon and the policy. -/
theorem sum_expect_phaseCost_le [Finite S] [Finite A]
    (kernel : K → S → A → PMF S) (reward : K → S → A → ℝ) (word : ZMod P → K)
    (phaseBias : ZMod P → S → ℝ) (g bound : ℝ) (policy : ℕ → S → PMF A) (law : ℕ → PMF S)
    (path : IsMarginalLawPath law
      (controlledKernel (scheduledKernel kernel (phaseSchedule word)) policy))
    (slack : HasPhaseSlack kernel reward word phaseBias g)
    (bounded : ∀ phase state, |phaseBias phase state| ≤ bound)
    (start horizon : ℕ) :
    (∑ i ∈ Finset.range horizon,
        expect (law (start + i))
          (controlledCost (scheduledReward reward (phaseSchedule word)) policy (start + i))) ≤
      g * horizon + 2 * bound := by
  have windowed :=
    sum_expect_cost_le_of_stageSlack_le law
      (controlledKernel (scheduledKernel kernel (phaseSchedule word)) policy)
      (controlledCost (scheduledReward reward (phaseSchedule word)) policy)
      (phasePotential phaseBias) path (fun _ => g) start horizon
      (fun i _ state =>
        stageSlack_phase_le kernel reward word phaseBias g policy slack (start + i) state)
  have charge_sum : (∑ _i ∈ Finset.range horizon, g) = g * horizon := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
  have head : |expect (law start) (phasePotential phaseBias start)| ≤ bound :=
    abs_expect_le_of_abs_le _ _ fun state => bounded _ state
  have tail :
      |expect (law (start + horizon)) (phasePotential phaseBias (start + horizon))| ≤ bound :=
    abs_expect_le_of_abs_le _ _ fun state => bounded _ state
  have head_le := (le_abs_self _).trans head
  have tail_le := (neg_le_of_abs_le tail)
  rw [charge_sum] at windowed
  linarith

end Phase

/-! ## Falsifier probe 1: the alternating harvest

Question 89 (16)-(17).  Two uncontrolled two-state modes, each harmless on its
own invariant measure, which nevertheless earn one unit at *every* stage under
the alternating schedule.  This checks that

* the switch term of the account is genuinely unavoidable — there is no common
  state-only bias (`no_common_bias`), so `sum_expect_scheduledCost_le_span_of_commonBias`
  cannot apply; and
* the coefficient `C (1 + J)` of `sum_expect_scheduledCost_le_switchingBill` is
  attained with equality (`attains_switchingBill`). -/

namespace AlternatingHarvest

/-- Mode `true` is Question 89's mode 1 (everything moves to state `true`);
mode `false` is its mode 2 (everything moves to state `false`). -/
def modeNext (mode : Bool) (_state : Bool) : Bool := mode

/-- Both modes are deterministic and uncontrolled: the action type is `Unit`. -/
def kernel (mode state : Bool) (_action : Unit) : PMF Bool := PMF.pure (modeNext mode state)

/-- Question 89 (16): each mode pays one unit exactly at the state the other
mode drives towards. -/
def reward (mode state : Bool) (_action : Unit) : ℝ := if mode = state then 0 else 1

/-- The per-mode biases `h₁ = (1, 0)`, `h₂ = (0, 1)` of Question 89's Part A.4
witness, already span-normalized. -/
def bias (mode state : Bool) : ℝ := if mode = state then 0 else 1

theorem isModeBias_bias (mode : Bool) : IsModeBias kernel reward bias mode := by
  intro state action
  cases mode <;> cases state <;> simp [kernel, reward, bias, modeNext]

theorem bias_nonneg (mode state : Bool) : 0 ≤ bias mode state := by
  unfold bias
  split_ifs <;> norm_num

theorem bias_le_one (mode state : Bool) : bias mode state ≤ 1 := by
  unfold bias
  split_ifs <;> norm_num

/-- **No common bias.**  Question 89 (16) has no single state potential valid
for both modes, so the switch charge cannot be removed. -/
theorem no_common_bias :
    ¬ ∃ common : Bool → ℝ, ∀ mode, IsModeBias kernel reward (fun _ => common) mode := by
  rintro ⟨common, common_bias⟩
  have first := common_bias true false ()
  have second := common_bias false true ()
  simp only [kernel, reward, modeNext, expect_pure] at first second
  norm_num at first second
  linarith

/-- The alternating schedule: mode 1 at even stages, mode 2 at odd stages. -/
def schedule (stage : ℕ) : Bool := stage % 2 == 0

/-- The realized state of the alternating run started at state `false`. -/
def runState (stage : ℕ) : Bool := stage % 2 == 1

/-- The unique (single-action) policy. -/
def policy : ℕ → Bool → PMF Unit := fun _ _ => PMF.pure ()

/-- The alternating run's law: a point mass at each stage. -/
def law (stage : ℕ) : PMF Bool := PMF.pure (runState stage)

theorem runState_succ (stage : ℕ) : runState (stage + 1) = schedule stage := by
  unfold runState schedule
  rcases Nat.mod_two_eq_zero_or_one stage with parity | parity
  · rw [show (stage + 1) % 2 = 1 by omega, parity]
    decide
  · rw [show (stage + 1) % 2 = 0 by omega, parity]
    decide

theorem runState_ne_schedule (stage : ℕ) : schedule stage ≠ runState stage := by
  unfold runState schedule
  rcases Nat.mod_two_eq_zero_or_one stage with parity | parity
  · rw [parity]
    decide
  · rw [parity]
    decide

theorem schedule_ne_succ (stage : ℕ) : schedule (stage + 1) ≠ schedule stage := by
  unfold schedule
  rcases Nat.mod_two_eq_zero_or_one stage with parity | parity
  · rw [show (stage + 1) % 2 = 1 by omega, parity]
    decide
  · rw [show (stage + 1) % 2 = 0 by omega, parity]
    decide

theorem isMarginalLawPath :
    IsMarginalLawPath law (controlledKernel (scheduledKernel kernel schedule) policy) := by
  intro stage
  simp only [law, controlledKernel, scheduledKernel, policy, kernel, modeNext, PMF.pure_bind]
  rw [runState_succ]

/-- Every stage of the alternating run pays exactly one unit. -/
theorem expect_cost (stage : ℕ) :
    expect (law stage) (controlledCost (scheduledReward reward schedule) policy stage) = 1 := by
  simp only [law, controlledCost, scheduledReward, policy, expect_pure, reward]
  rw [if_neg (runState_ne_schedule stage)]

theorem sum_expect_cost (start horizon : ℕ) :
    (∑ i ∈ Finset.range horizon,
        expect (law (start + i))
          (controlledCost (scheduledReward reward schedule) policy (start + i))) = horizon := by
  simp [expect_cost]

theorem windowSwitchCount_eq (start steps : ℕ) :
    windowSwitchCount schedule start steps = steps := by
  unfold windowSwitchCount
  rw [Finset.filter_true_of_mem, Finset.card_range]
  intro i _
  exact schedule_ne_succ (start + i)

theorem uniformBiasSpan_eq : uniformBiasSpan bias = 1 := by
  have span_eq : ∀ mode : Bool, finiteSpan (bias mode) = 1 := by
    intro mode
    have upper : finiteMax (bias mode) = 1 := by
      refine le_antisymm (finiteMax_le fun state => bias_le_one mode state) ?_
      refine le_trans ?_ (le_finiteMax (bias mode) (!mode))
      cases mode <;> norm_num [bias]
    have lower : finiteMin (bias mode) = 0 := by
      refine le_antisymm ?_ (le_finiteMin fun state => bias_nonneg mode state)
      refine le_trans (finiteMin_le (bias mode) mode) ?_
      simp [bias]
    rw [finiteSpan, upper, lower, sub_zero]
  unfold uniformBiasSpan
  simp [span_eq]

/-- **Question 89 (17): the switching bill is attained.**  Over the window
`[start, start + steps]` the alternating harvest earns exactly
`C * (1 + J)` with `C = 1` the uniform bias span and `J = steps` the internal
switch count, matching `sum_expect_scheduledCost_le_switchingBill` with
equality. -/
theorem attains_switchingBill (start steps : ℕ) :
    (∑ i ∈ Finset.range (steps + 1),
        expect (law (start + i))
          (controlledCost (scheduledReward reward schedule) policy (start + i))) =
      uniformBiasSpan bias * (1 + windowSwitchCount schedule start steps) := by
  rw [sum_expect_cost, uniformBiasSpan_eq, windowSwitchCount_eq]
  push_cast
  ring

/-- The general switching bill really does apply to this witness, so the
equality above is an attainment statement and not a vacuity. -/
theorem switchingBill_applies (start steps : ℕ) :
    (∑ i ∈ Finset.range (steps + 1),
        expect (law (start + i))
          (controlledCost (scheduledReward reward schedule) policy (start + i))) ≤
      1 * (1 + windowSwitchCount schedule start steps) :=
  sum_expect_scheduledCost_le_switchingBill kernel reward bias schedule policy law 1
    isMarginalLawPath isModeBias_bias bias_nonneg bias_le_one start steps

end AlternatingHarvest

/-! ## Falsifier probe 2: phase-dependent potentials strictly beat mode-indexed
oscillation accounting

Question 89 (40)-(42).  The `(u, v, v)` schedule admits phase potentials with
per-phase slack `g = 0`, hence a horizon-free cap; but every pair of per-mode
biases pays at least one unit of oscillation per `u ↔ v` cycle, i.e. at least
`1 / 3` per stage. -/

namespace PhaseHarvest

/-- Question 89 (40).  Mode `false` is `u` (always resets to state `false`);
mode `true` is `v` (the two-cycle). -/
def modeNext (mode state : Bool) : Bool := if mode then !state else false

def kernel (mode state : Bool) (_action : Unit) : PMF Bool := PMF.pure (modeNext mode state)

/-- Question 89 (40): `f_u = (-1, 0)` and `f_v = (1, -1)`. -/
def reward (mode state : Bool) (_action : Unit) : ℝ :=
  if mode then (if state then -1 else 1) else (if state then 0 else -1)

/-- Question 89 (41): the period-three word `(u, v, v)`. -/
def word (phase : ZMod 3) : Bool := decide (phase ≠ 0)

/-- Question 89 (42): the phase potentials `H₀ = (0, 0)`, `H₁ = (0, 0)`,
`H₂ = (1, -1)`. -/
def phaseBias (phase : ZMod 3) (state : Bool) : ℝ :=
  if phase = 2 then (if state then -1 else 1) else 0

@[simp] theorem word_zero : word 0 = false := by decide
@[simp] theorem word_one : word 1 = true := by decide
@[simp] theorem word_two : word 2 = true := by decide

@[simp] theorem phaseBias_zero (state : Bool) : phaseBias 0 state = 0 := by
  rw [phaseBias, if_neg (by decide)]

@[simp] theorem phaseBias_one (state : Bool) : phaseBias 1 state = 0 := by
  rw [phaseBias, if_neg (by decide)]

@[simp] theorem phaseBias_two (state : Bool) :
    phaseBias 2 state = if state then -1 else 1 := by
  rw [phaseBias, if_pos rfl]

@[simp] theorem phaseBias_three (state : Bool) : phaseBias 3 state = 0 := by
  rw [phaseBias, if_neg (by decide)]

/-- **Question 89 (42) verified.**  The three phase potentials satisfy the
per-phase bias inequalities with slack `g = 0`. -/
theorem hasPhaseSlack : HasPhaseSlack kernel reward word phaseBias 0 := by
  intro phase state action
  have trichotomy : phase = 0 ∨ phase = 1 ∨ phase = 2 := by revert phase; decide
  rcases trichotomy with rfl | rfl | rfl <;> cases state <;>
    norm_num [kernel, reward, modeNext, show (1 : ZMod 3) + 1 = 2 by decide,
      show (2 : ZMod 3) + 1 = 0 by decide, show (3 : ZMod 3) = 0 by decide]

theorem abs_phaseBias_le_one (phase : ZMod 3) (state : Bool) : |phaseBias phase state| ≤ 1 := by
  unfold phaseBias
  split_ifs <;> norm_num

/-- **The `(u, v, v)` schedule has a horizon-free cap.**  For every policy,
every shift and every horizon the expected reward is at most `2`. -/
theorem sum_expect_cost_le_two
    (policy : ℕ → Bool → PMF Unit) (law : ℕ → PMF Bool)
    (path : IsMarginalLawPath law
      (controlledKernel (scheduledKernel kernel (phaseSchedule word)) policy))
    (start horizon : ℕ) :
    (∑ i ∈ Finset.range horizon,
        expect (law (start + i))
          (controlledCost (scheduledReward reward (phaseSchedule word)) policy (start + i))) ≤
      2 := by
  have windowed :=
    sum_expect_phaseCost_le kernel reward word phaseBias 0 1 policy law path hasPhaseSlack
      abs_phaseBias_le_one start horizon
  simpa using windowed

/-- **Mode-indexed oscillation billing is strictly weaker.**  Question 89 C.3:
whatever per-mode biases are chosen, the two oscillation bills of a `u → v → u`
cycle already sum to at least one, i.e. at least `1 / 3` per stage of the
period-three word — even though `sum_expect_cost_le_two` caps the same schedule
by an absolute constant. -/
theorem one_le_oscillationCharge_cycle (bias : Bool → Bool → ℝ)
    (bias_u : IsModeBias kernel reward bias false)
    (bias_v : IsModeBias kernel reward bias true) :
    1 ≤ oscillationCharge bias false true + oscillationCharge bias true false := by
  have from_u := bias_u true ()
  have from_v := bias_v false ()
  simp only [kernel, reward, modeNext, expect_pure] at from_u from_v
  norm_num at from_u from_v
  have first : bias true false - bias false false ≤ oscillationCharge bias false true :=
    le_finiteMax (fun state => bias true state - bias false state) false
  have second : bias false true - bias true true ≤ oscillationCharge bias true false :=
    le_finiteMax (fun state => bias false state - bias true state) true
  linarith

/-- The cap of `sum_expect_cost_le_two` is not vacuous: the canonical law path
of any policy satisfies its hypothesis. -/
theorem sum_expect_canonicalCost_le_two
    (policy : ℕ → Bool → PMF Unit) (initial : PMF Bool) (start horizon : ℕ) :
    (∑ i ∈ Finset.range horizon,
        expect
          (marginalLawPath initial
            (controlledKernel (scheduledKernel kernel (phaseSchedule word)) policy) (start + i))
          (controlledCost (scheduledReward reward (phaseSchedule word)) policy (start + i))) ≤
      2 :=
  sum_expect_cost_le_two policy _ (isMarginalLawPath_marginalLawPath _ _) start horizon

/-- An explicit pair of per-mode biases: `h_u ≡ 0` and `h_v = (1, 0)`.  Both
modes are therefore harmless, so `one_le_oscillationCharge_cycle` is not
vacuous. -/
def modeBias (mode state : Bool) : ℝ := if mode then (if state then 0 else 1) else 0

theorem isModeBias_modeBias (mode : Bool) : IsModeBias kernel reward modeBias mode := by
  intro state action
  cases mode <;> cases state <;> norm_num [kernel, reward, modeNext, modeBias]

theorem oscillationCharge_modeBias_le_one :
    oscillationCharge modeBias false true + oscillationCharge modeBias true false ≤ 1 := by
  have first : oscillationCharge modeBias false true ≤ 1 := by
    refine finiteMax_le fun state => ?_
    cases state <;> norm_num [modeBias]
  have second : oscillationCharge modeBias true false ≤ 0 := by
    refine finiteMax_le fun state => ?_
    cases state <;> norm_num [modeBias]
  linarith

/-- The lower bound of `one_le_oscillationCharge_cycle` is attained: the best
per-mode oscillation account for the `(u, v, v)` word really does pay exactly
one unit per period, i.e. `1 / 3` per stage, against a phase account whose total
bill over every horizon is at most `2`. -/
theorem oscillationCharge_modeBias_eq_one :
    oscillationCharge modeBias false true + oscillationCharge modeBias true false = 1 :=
  le_antisymm oscillationCharge_modeBias_le_one
    (one_le_oscillationCharge_cycle modeBias (isModeBias_modeBias false)
      (isModeBias_modeBias true))

end PhaseHarvest

end Probability
end Math
