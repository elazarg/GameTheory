/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.AdaptiveCertificate

/-!
# The Stationary Average-Optimality (Guarantee) Certificate

A **stationary, undiscounted** sufficient condition for
`StochasticGame.IsOneSidedGuaranteeCertificate` — a player securing a value
against *every* opponent completion — built directly from the undiscounted
average-reward Bellman (LP-dual) optimality inequalities for a fixed
stationary policy, with **no discount factor and no `1/λ` anywhere**.

## Why this file exists

The discounted route to a uniform value guarantee converts a discounted
Bellman certificate to an average-payoff guarantee via a `β / (1 − β)`
rescaling that diverges as the discount `λ := 1 − β → 0`: a proved wall (see
`ephemeral/UniformEquilibriumInsights.md` §8). The escape is to certify the
average payoff *directly*, with a **bounded, state-dependent benchmark `ρ`**
(the "gain") and a **bounded bias `u`** satisfying the classical undiscounted
average-reward optimality inequalities for a stationary policy — exactly the
shape `TransitionIndependentCertificate.lean`'s Poisson-equation certificate
uses for the *no-control* case (`Math.MeanErgodic.exists_harmonic_add_poisson`,
an exact identity there because the opponent has no real choice). Here the
policy must be **robust against every opponent action**, so the identity used
there weakens to a pair of *inequalities* holding against every opponent
action — this is precisely **Vrieze's primal LP for undiscounted stochastic
games**: the gain variable `ρ` satisfies a one-step transition inequality
against every action, and the bias variable `u` satisfies the
payoff-plus-continuation inequality against every action. This file is the
Lean object that LP's feasible solutions are certificates *for*; solving that
LP (e.g. via the single-controller/no-control special cases already in this
repository) is the natural continuation, not attempted here.

## The two drift inequalities

For a stationary (behavior-independent-of-time, state-dependent) mixed action
`mwho : G.State → PMF (G.Act who)`, a bounded gain `ρ : G.State → ℝ` and a
bounded bias `u : G.State → ℝ` witness a **guarantee of `vwho` from below**
when, for *every* state `s` and *every* joint opponent action `b` (`who`'s own
coordinate of `b` is irrelevant — it gets overridden by the actual mixed draw
from `mwho s`):

* **gain drift** (`ρ` subharmonic): `ρ s ≤ E[ρ (S') | s, mwho s, b]`
* **bias drift**: `ρ s + u s ≤ E[g_who (s, A) + u (S') | s, mwho s, b]`

where `A := Function.update b who a` for `a` drawn from `mwho s`, and `S'` is
the resulting next state. Both are **inequalities**, deliberately not the
equalities of a genuinely harmonic/Poisson potential: an equality can only be
maintained *on the equilibrium path* (or for a *fixed*, uncontrolled chain, as
in `TransitionIndependentCertificate.lean`); against an adversarially chosen
opponent action `b` there is in general no equality available, only that
neither drift term can be negative. This is exactly enough: telescoping the
bias drift and using the gain drift's submartingale consequence
(`E[ρ (S_t)]` nondecreasing in `t`, hence `≥ ρ s₀` at every `t`) gives

  `E[∑_{t < N} g_who] ≥ N · ρ s₀ − 2 ‖u‖_∞`,

hence `finiteAveragePayoff ≥ ρ s₀ − 2 ‖u‖_∞ / N`, uniformly in the horizon and
against *every* opponent completion — the `IsOneSidedGuaranteeCertificateAt`
shape, with the `2 ‖u‖_∞ / N` boundary term vanishing as `N → ∞`. **No
discount, no `1/λ`, appears anywhere in this telescope.**

(The dual **capping-from-above** certificate — used to bound a minimizer's
own payoff, or equivalently a maximizer's deviation gain against a fixed
opponent policy — is obtained by reversing both inequalities, `ρ`
*super*harmonic and `ρ s + u s ≥ E[g + u (S')]`; it is not built as a separate
object here because `IsOneSidedGuaranteeCertificate` already gets both
directions for free: applying `IsStationaryAverageGuaranteeCertificate` to
*each* player of a zero-sum game and composing with
`isUniformEquilibriumPayoff_of_isZeroSumBoolGame_of_oneSidedGuarantees`
turns each player's own *lower* guarantee into the *other* player's deviation
cap, matching the zero-sum wrapper's own design.)

**Reward-shift invariance.** The certificate is stated purely in terms of the
two *drift* inequalities (differences of expectations, never a raw scaled
quantity such as `(1 − λ)/λ · v`): shifting every stage payoff by a constant
`c` shifts `ρ` (and the guaranteed value) by `c` but leaves both drift
inequalities unchanged, since the added constant cancels inside
`E[· (S')] − ·(s)`. This is what keeps the certificate genuinely
discount-free and rules out the divergent `1/λ` rescaling that blocks the
discounted route.

## Main definitions

* `StochasticGame.stationaryFrom` — the time-independent behavior strategy
  induced by a state-dependent mixed action
* `StochasticGame.IsStationaryAverageGuaranteeCertificate` — the certificate:
  a stationary mixed action together with a subharmonic gain `ρ` and a bias
  `u` satisfying the two drift inequalities against every opponent action

## Main results

* `StochasticGame.isOneSidedGuaranteeCertificate_of_isStationaryAverageGuaranteeCertificate`
  — the certificate implies `IsOneSidedGuaranteeCertificate`, via the bounded
  undiscounted telescope described above
* `StochasticGame.IsAbsorbingEverywhere` /
  `StochasticGame.isStationaryAverageGuaranteeCertificate_of_isAbsorbingEverywhere`
  — the validating instance: a game absorbing at *every* state (so the drift
  inequalities are trivial, `ρ` and `u ≡ 0` exact) reproves the one-sided
  guarantee at every state's stage-game *security* (maximin) level — genuinely
  adversary-robust, unlike the repository's existing absorbing-state examples
  which only certify Nash play
* `StochasticGame.isUniformEquilibriumPayoff_of_isZeroSumBoolGame_of_stationaryAverageGuarantees`
  — the zero-sum assembly: two stationary average-guarantee certificates (one
  per player) give a full `IsUniformEquilibriumPayoff`, via the existing
  zero-sum wrapper

## Status / next step

Steps 1–2 (the certificate and its bounded-telescope reduction to
`IsOneSidedGuaranteeCertificate`) are complete and sorry-free. Step 3 is
validated on the absorbing-everywhere instance. The natural continuation —
*solving* Vrieze's primal LP for a genuine single-controller stochastic game
(not merely a disjoint union of one-shot games) to produce a
non-trivially-moving instance of this certificate — is intentionally left as
future work; it needs LP/optimality machinery this file does not build.

This file is deliberately **not** wired into `GameTheory.lean` (the project
aggregator): it is a standalone verification object, importable directly.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability Math.PMFProduct

variable {ι : Type}

-- ============================================================================
-- A Fubini fact: swapping the order of two finite expectations
-- ============================================================================

/-- Two finite expectations commute: `expect p (fun a => expect q (F a))` is
symmetric in the order of integration. Used to swap the roles of `who`'s own
randomized action and the opponent's action inside a joint expectation. -/
private theorem expect_expect_comm {Ω₁ Ω₂ : Type*} [Finite Ω₁] [Finite Ω₂]
    (p : PMF Ω₁) (q : PMF Ω₂) (F : Ω₁ → Ω₂ → ℝ) :
    expect p (fun a => expect q (fun b => F a b)) =
      expect q (fun b => expect p (fun a => F a b)) := by
  letI : Fintype Ω₁ := Fintype.ofFinite Ω₁
  letI : Fintype Ω₂ := Fintype.ofFinite Ω₂
  simp_rw [expect_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

-- ============================================================================
-- Stationary strategies
-- ============================================================================

/-- The time-independent behavior strategy that plays the state-dependent
mixed action `mwho` at every history, regardless of calendar time or the
rest of the history: `stationaryFrom who mwho t h := mwho h.2`. -/
def stationaryFrom (G : StochasticGame ι) [Fintype ι] (who : ι)
    (mwho : G.State → PMF (G.Act who)) : G.BehaviorStrategy who :=
  fun _ h => mwho h.2

-- ============================================================================
-- The certificate
-- ============================================================================

/-- **Stationary average-optimality (guarantee) certificate.** Player `who`
has a stationary mixed action `mwho`, a bounded gain `ρ : G.State → ℝ` with
`vwho ≤ ρ s₀`, and a bounded bias `u : G.State → ℝ`, such that against
*every* state `s` and *every* joint opponent action `b` (`b`'s `who`
coordinate is irrelevant, since it is overridden by `mwho s`'s own draw):

* **gain drift** (`ρ` subharmonic under `mwho`, for every opponent choice):
  `ρ s ≤ E_{a ~ mwho s}[ E[ρ (S') | s, Function.update b who a] ]`
* **bias drift**: `ρ s + u s ≤
  E_{a ~ mwho s}[ g_who (s, Function.update b who a) +
    E[u (S') | s, Function.update b who a] ]`

These are the undiscounted average-reward (LP-dual) optimality inequalities
for the stationary policy `mwho`, required to hold against *every* possible
opponent behavior (not merely a fixed chain), and are what
`isOneSidedGuaranteeCertificate_of_isStationaryAverageGuaranteeCertificate`
consumes to certify `who` securing `vwho` via a bounded, discount-free
telescope. Both `ρ` and `u` are automatically bounded (`G.State` is finite);
that boundedness is exactly what makes the telescope's boundary loss vanish
as the horizon grows. -/
def IsStationaryAverageGuaranteeCertificate (G : StochasticGame ι) [Fintype ι]
    [DecidableEq ι] [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State) (who : ι) (vwho : ℝ) : Prop :=
  ∃ (mwho : G.State → PMF (G.Act who)) (ρ u : G.State → ℝ),
    vwho ≤ ρ s₀ ∧
    (∀ (s : G.State) (b : G.JointAct),
      ρ s ≤ expect (mwho s) (fun a =>
        expect (G.transition s (Function.update b who a)) ρ)) ∧
    (∀ (s : G.State) (b : G.JointAct),
      ρ s + u s ≤ expect (mwho s) (fun a =>
        G.stagePayoff s (Function.update b who a) who +
          expect (G.transition s (Function.update b who a)) u))

-- ============================================================================
-- Verification: the certificate implies a one-sided guarantee
-- ============================================================================

/-- **Decomposition of the joint action distribution under a stationary
update.** Under `Function.update opp who (G.stationaryFrom who mwho)` at
history `h`, the joint action distribution factors as: draw `who`'s own
action `a` from `mwho h.2`, and independently draw the *opponents'* proposed
joint action `b` from the product of their own (possibly history-dependent)
strategies at `h`, then combine as `Function.update b who a`. This is the
"Fubini" identity for `pmfPi` under a coordinate update
(`Math.PMFProduct.pmfPi_update_bind` / `pmfPi_bind_update_pure`), specialized
to `stageActionDist`. -/
private theorem expect_stageActionDist_update_stationaryFrom
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [∀ i, Finite (G.Act i)]
    (opp : G.BehaviorProfile) (who : ι) (mwho : G.State → PMF (G.Act who))
    {t : ℕ} (h : G.Hist t) (F : G.JointAct → ℝ) :
    expect (G.stageActionDist
        (Function.update opp who (G.stationaryFrom who mwho)) h) F =
      expect (mwho h.2) (fun a =>
        expect (pmfPi (fun i => opp i t h))
          (fun b => F (Function.update b who a))) := by
  have hπh : G.stageActionDist
      (Function.update opp who (G.stationaryFrom who mwho)) h =
      pmfPi (Function.update (fun i => opp i t h) who (mwho h.2)) := by
    unfold stageActionDist
    congr 1
    funext j
    by_cases hj : j = who
    · subst hj; simp [stationaryFrom]
    · simp [Function.update_of_ne hj]
  rw [hπh, pmfPi_update_bind, expect_bind]
  refine congrArg (expect (mwho h.2)) (funext fun a => ?_)
  rw [← pmfPi_bind_update_pure (fun i => opp i t h) who a, expect_bind]
  simp

/-- **The stationary average-optimality certificate implies a one-sided
guarantee.** The bounded, discount-free telescope: the gain drift makes
`E[ρ (S_t)]` a nondecreasing sequence starting at `ρ s₀`, and the bias drift
telescopes against the bounded bias `u`, giving
`finiteAveragePayoff ≥ ρ s₀ − 2 ‖u‖_∞ / T` uniformly against every opponent
completion. No discount factor and no `1/λ` term appears. -/
theorem isOneSidedGuaranteeCertificate_of_isStationaryAverageGuaranteeCertificate
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] (s₀ : G.State) (who : ι) (vwho : ℝ)
    (hcert : G.IsStationaryAverageGuaranteeCertificate s₀ who vwho) :
    G.IsOneSidedGuaranteeCertificate s₀ who vwho := by
  classical
  letI : Fintype G.State := Fintype.ofFinite G.State
  obtain ⟨mwho, ρ, u, hρ0, hgain, hstep⟩ := hcert
  set C : ℝ := ∑ s : G.State, |u s| with hCdef
  have hCbound : ∀ s : G.State, |u s| ≤ C := fun s =>
    Finset.single_le_sum (fun x _ => abs_nonneg (u x)) (Finset.mem_univ s)
  intro δ hδ
  obtain ⟨T₁, hT₁⟩ := exists_nat_gt (2 * C / δ)
  refine ⟨G.stationaryFrom who mwho, max 2 (T₁ + 1), le_max_left _ _,
    fun opp T hT => ?_⟩
  set π : G.BehaviorProfile :=
    Function.update opp who (G.stationaryFrom who mwho) with hπ
  set φᵤ : G.HistoryPotential := fun _ h => u h.2 with hφᵤ
  -- Decomposition of the joint action distribution under `π`, at every history.
  have hdecomp : ∀ {t : ℕ} (h : G.Hist t) (F : G.JointAct → ℝ),
      expect (G.stageActionDist π h) F =
        expect (mwho h.2) (fun a =>
          expect (pmfPi (fun i => opp i t h))
            (fun b => F (Function.update b who a))) := by
    intro t h F
    rw [hπ]
    exact G.expect_stageActionDist_update_stationaryFrom opp who mwho h F
  -- Pointwise gain-drift step, at every history.
  have hgainStep : ∀ (t : ℕ) (h : G.Hist t),
      ρ h.2 ≤ G.historyContinuationEU π (fun _ h' => ρ h'.2) h := by
    intro t h
    have hunfold : G.historyContinuationEU π (fun _ h' => ρ h'.2) h =
        expect (G.stageActionDist π h) (fun a => expect (G.transition h.2 a) ρ) := rfl
    rw [hunfold, hdecomp h (fun a' => expect (G.transition h.2 a') ρ), expect_expect_comm]
    calc ρ h.2 = expect (pmfPi (fun i => opp i t h)) (fun _ => ρ h.2) :=
          (expect_const _ _).symm
      _ ≤ expect (pmfPi (fun i => opp i t h)) (fun b => expect (mwho h.2) (fun a =>
            expect (G.transition h.2 (Function.update b who a)) ρ)) :=
          expect_mono _ _ _ (fun b => hgain h.2 b)
  -- The gain's expectation is a nondecreasing sequence, starting at `ρ s₀`.
  have hgainLB : ∀ t : ℕ, ρ s₀ ≤ expect (G.histDist π s₀ t) (fun h => ρ h.2) := by
    intro t
    induction t with
    | zero => simp [emptyHist]
    | succ t ih =>
      have hsucc : expect (G.histDist π s₀ (t + 1)) (fun h => ρ h.2) =
          expect (G.histDist π s₀ t)
            (fun h => G.historyContinuationEU π (fun _ h' => ρ h'.2) h) :=
        G.expectedHistoryValue_succ π s₀ (fun _ h => ρ h.2) t
      rw [hsucc]
      calc ρ s₀ ≤ expect (G.histDist π s₀ t) (fun h => ρ h.2) := ih
        _ ≤ expect (G.histDist π s₀ t)
              (fun h => G.historyContinuationEU π (fun _ h' => ρ h'.2) h) :=
            expect_mono _ _ _ (fun h => hgainStep t h)
  -- Pointwise bias-drift step, at every history.
  have hpointwise : ∀ (t : ℕ) (h : G.Hist t),
      ρ h.2 + u h.2 ≤ G.stageEUAt π h who + G.historyContinuationEU π φᵤ h := by
    intro t h
    have hcomb : G.stageEUAt π h who + G.historyContinuationEU π φᵤ h =
        expect (G.stageActionDist π h)
          (fun a => G.stagePayoff h.2 a who + expect (G.transition h.2 a) u) := by
      have h1 : G.stageEUAt π h who =
          expect (G.stageActionDist π h) (fun a => G.stagePayoff h.2 a who) := rfl
      have h2 : G.historyContinuationEU π φᵤ h =
          expect (G.stageActionDist π h) (fun a => expect (G.transition h.2 a) u) := rfl
      rw [h1, h2, expect_add]
    rw [hcomb, hdecomp h (fun a =>
        G.stagePayoff h.2 a who + expect (G.transition h.2 a) u), expect_expect_comm]
    calc ρ h.2 + u h.2 =
        expect (pmfPi (fun i => opp i t h)) (fun _ => ρ h.2 + u h.2) :=
          (expect_const _ _).symm
      _ ≤ expect (pmfPi (fun i => opp i t h)) (fun b => expect (mwho h.2) (fun a =>
            G.stagePayoff h.2 (Function.update b who a) who +
              expect (G.transition h.2 (Function.update b who a)) u)) :=
          expect_mono _ _ _ (fun b => hstep h.2 b)
  -- Expectation-level Bellman inequality with `e ≡ 0`, combining the two drifts.
  have hbellman : ∀ t : ℕ, ρ s₀ + G.expectedHistoryValue π s₀ φᵤ t ≤
      G.expectedStagePayoff π s₀ t who + G.expectedHistoryValue π s₀ φᵤ (t + 1) := by
    intro t
    have hLHS : G.expectedHistoryValue π s₀ φᵤ t =
        expect (G.histDist π s₀ t) (fun h => u h.2) := rfl
    have hsucc : G.expectedHistoryValue π s₀ φᵤ (t + 1) =
        expect (G.histDist π s₀ t) (fun h => G.historyContinuationEU π φᵤ h) :=
      G.expectedHistoryValue_succ π s₀ φᵤ t
    have hstage : G.expectedStagePayoff π s₀ t who =
        expect (G.histDist π s₀ t) (fun h => G.stageEUAt π h who) := rfl
    rw [hLHS, hsucc, hstage]
    have hgt := hgainLB t
    have hmono := expect_mono (G.histDist π s₀ t)
      (fun h => ρ h.2 + u h.2)
      (fun h => G.stageEUAt π h who + G.historyContinuationEU π φᵤ h)
      (fun h => hpointwise t h)
    rw [expect_add (G.histDist π s₀ t) (fun h => ρ h.2) (fun h => u h.2)] at hmono
    rw [← expect_add]
    linarith [hgt, hmono]
  have hbound : ∀ t (h : G.Hist t), |φᵤ t h| ≤ C := fun t h => hCbound h.2
  have hT0 : 0 < T := by
    have h1 : T₁ + 1 ≤ T := le_trans (le_max_right _ _) hT
    omega
  have hres := G.finiteAveragePayoff_ge_of_expectedHistoryValue_bellman_le_of_bound
    π s₀ who φᵤ (fun _ => (0 : ℝ)) (v := ρ s₀) (C := C) hbound
    (fun t => by have := hbellman t; linarith) hT0
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_zero] at hres
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT0
  have hT1 : T₁ + 1 ≤ T := le_trans (le_max_right _ _) hT
  have hT1real : (T₁ : ℝ) < (T : ℝ) := by
    have : T₁ < T := by omega
    exact_mod_cast this
  have hdiv : 2 * C / (T : ℝ) ≤ δ := by
    rw [div_le_iff₀ hTreal]
    have h2 : 2 * C < (T : ℝ) * δ := by
      rw [div_lt_iff₀ hδ] at hT₁
      calc 2 * C < (T₁ : ℝ) * δ := hT₁
        _ ≤ (T : ℝ) * δ := mul_le_mul_of_nonneg_right hT1real.le hδ.le
    linarith
  linarith [hres, hdiv, hρ0]

-- ============================================================================
-- Validating instance: games absorbing at every state
-- ============================================================================

/-- A stochastic game is **absorbing everywhere** when every state is
absorbing (`StochasticGame.IsAbsorbingState`): no transition, from any state,
ever depends on the joint action played. Such a game is a disjoint union of
one-shot stage games — play never actually moves — which is exactly what
makes both drift inequalities trivial (equalities) for *any* choice of
benchmark `ρ`, at *every* state, not merely the initial one. -/
def IsAbsorbingEverywhere (G : StochasticGame ι) : Prop :=
  ∀ s : G.State, G.IsAbsorbingState s

/-- **The stationary average-optimality certificate holds at every state of a
game absorbing everywhere, with `u ≡ 0` and `ρ` the per-state stage-game
*security* (maximin) value.** Unlike the repository's existing absorbing-state
worked examples (`isAdaptiveEquilibriumCertificate_of_isAbsorbingState`,
built from a *Nash* equilibrium of the stage game — sufficient there only
because the certificate need only survive a *fixed* opponent profile, not an
adversarial completion), the one-sided-guarantee certificate genuinely needs
`who`'s stationary action to be robust against *every* possible opponent
action, i.e. a security (maximin) strategy of the stage game at `s`, not
merely a best response to one particular opponent profile. Built directly
(via `Finset.exists_max_image` on the finite type `G.Act who`) rather than
through `GameTheory.Concepts.ZeroSum.SecurityStrategy`'s `KernelGame`
machinery: that machinery states its guarantee for an *arbitrary* ambient
`[DecidableEq ι]`, resolved once inside that file (to a classical instance,
via its `open Classical in` decorations) and hence not syntactically equal
to *this* file's own `[DecidableEq ι]` parameter at the term level, even
though the two are propositionally interchangeable — the direct construction
sidesteps that entirely by staying inside a single elaboration context. -/
theorem isStationaryAverageGuaranteeCertificate_of_isAbsorbingEverywhere
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)]
    (hAbs : G.IsAbsorbingEverywhere) (s₀ : G.State) (who : ι) :
    ∃ v : ℝ, G.IsStationaryAverageGuaranteeCertificate s₀ who v := by
  classical
  letI : Fintype (G.Act who) := Fintype.ofFinite (G.Act who)
  letI : Fintype G.JointAct := Fintype.ofFinite G.JointAct
  have hneJ : (Finset.univ : Finset G.JointAct).Nonempty :=
    ⟨Classical.arbitrary G.JointAct, Finset.mem_univ _⟩
  have hneA : (Finset.univ : Finset (G.Act who)).Nonempty :=
    ⟨Classical.arbitrary (G.Act who), Finset.mem_univ _⟩
  -- `f s a` is the worst-case (over every opponent joint action `b`) stage
  -- payoff to `who` at state `s` when `who` plays the pure action `a`.
  set f : G.State → G.Act who → ℝ := fun s a =>
    Finset.inf' Finset.univ hneJ (fun b => G.stagePayoff s (Function.update b who a) who)
    with hfdef
  have hfle : ∀ (s : G.State) (a : G.Act who) (b : G.JointAct),
      f s a ≤ G.stagePayoff s (Function.update b who a) who :=
    fun s a b => Finset.inf'_le _ (Finset.mem_univ b)
  -- `act s` maximizes `f s ·`: a security (maximin) action at state `s`.
  have hsec : ∀ s : G.State, ∃ a : G.Act who, ∀ a' : G.Act who, f s a' ≤ f s a := by
    intro s
    obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ (f s) hneA
    exact ⟨a, fun a' => ha a' (Finset.mem_univ a')⟩
  choose act _hact using hsec
  refine ⟨f s₀ (act s₀), fun s => PMF.pure (act s), fun s => f s (act s), fun _ => 0,
    le_refl _, ?_, ?_⟩
  · intro s b
    rw [expect_pure]
    have htr : G.transition s (Function.update b who (act s)) = PMF.pure s := hAbs s _
    rw [htr, expect_pure]
  · intro s b
    rw [expect_pure]
    have htr : G.transition s (Function.update b who (act s)) = PMF.pure s := hAbs s _
    rw [htr, expect_pure]
    dsimp only
    linarith [hfle s (act s) b]

-- ============================================================================
-- The zero-sum assembly step
-- ============================================================================

/-- **Two stationary average-optimality certificates, one per player of a
zero-sum `Bool`-indexed stochastic game, assemble into a full uniform
equilibrium payoff.** Pure composition of
`isOneSidedGuaranteeCertificate_of_isStationaryAverageGuaranteeCertificate`
(applied once per player) with the existing zero-sum wrapper
`isUniformEquilibriumPayoff_of_isZeroSumBoolGame_of_oneSidedGuarantees`: no
new telescoping is needed here. -/
theorem isUniformEquilibriumPayoff_of_isZeroSumBoolGame_of_stationaryAverageGuarantees
    (G : StochasticGame Bool) [Finite G.State] [∀ i, Finite (G.Act i)]
    (hzs : G.IsZeroSumBoolGame) (s₀ : G.State) (v : ℝ)
    (hmax : G.IsStationaryAverageGuaranteeCertificate s₀ false v)
    (hmin : G.IsStationaryAverageGuaranteeCertificate s₀ true (-v)) :
    G.IsUniformEquilibriumPayoff s₀ (fun who => match who with | false => v | true => -v) := by
  classical
  exact G.isUniformEquilibriumPayoff_of_isZeroSumBoolGame_of_oneSidedGuarantees hzs s₀ v
    (G.isOneSidedGuaranteeCertificate_of_isStationaryAverageGuaranteeCertificate s₀ false v hmax)
    (G.isOneSidedGuaranteeCertificate_of_isStationaryAverageGuaranteeCertificate s₀ true (-v) hmin)

end StochasticGame
end GameTheory
