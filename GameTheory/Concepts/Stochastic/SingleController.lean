/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.AverageOptimalityCertificate
import Math.MeanErgodic
import Math.LinearProgramming.StrongDuality
import Math.LinearProgramming.StrongComplementarity

/-!
# Single-Controller Zero-Sum Stochastic Games: the Undiscounted Vrieze Route

The mechanism-1 uniform-value theorem for **single-controller** two-player
zero-sum stochastic games (`StochasticGame Bool`, one designated `controller`
player whose action alone determines the transition kernel), via the
**undiscounted** average-reward LP of Vrieze (*Stochastic Games with Finite
State and Action Spaces*, CWI Tract 33, 1987, Ch. 4) — no discount factor,
no `1/λ` anywhere, matching
`GameTheory.Concepts.Stochastic.AverageOptimalityCertificate`'s certificate
shape almost definitionally.

## Five-step decomposition

1. `isLowerAverageCertificate_of_vriezePrimalFeasible` — a feasible point of
   Vrieze's primal LP (`IsVriezePrimalFeasible`) gives the **noncontroller's**
   `IsStationaryAverageGuaranteeCertificate` directly: the LP's two families
   of inequalities are *literally* the certificate's two drift inequalities
   with `who := !controller`. No duality is used.
2.–3. **THE ISOLATED RESIDUAL.** Extracting the *controller's own* stationary
   strategy and gain from an optimal primal–dual pair. Stated as an explicit,
   undischarged hypothesis (`exists_controllerProjectionWitness_of_vriezePrimalDualOptimal`)
   rather than proved — see "The trap" below.
4. `isUpperAverageCertificate_of_controllerProjectionWitness` — **game
   independent**: given an `IsControllerProjectionWitness` (a controller
   policy `τ` together with a gain `ρ` that is exactly harmonic under the
   `τ`-induced kernel and dominated by that kernel's mean-ergodic projection
   of the worst-case reward), the *exact* (zero-error) Poisson-equation
   mechanism of `Math.MeanErgodic.exists_harmonic_add_poisson` — already used
   by `TransitionIndependentCertificate.lean` for the no-control case —
   produces the **controller's own**
   `IsStationaryAverageGuaranteeCertificate`. This step is entirely mechanical
   once the witness is in hand.
5. `exists_uniformEquilibriumPayoff_of_singleController` — assembles a
   noncontroller certificate (from Step 1) and a controller projection
   witness (whose existence Steps 2–3 leave open) via
   `isUniformEquilibriumPayoff_of_isZeroSumBoolGame_of_stationaryAverageGuarantees`
   into a full `IsUniformEquilibriumPayoff`.

## The trap (why Steps 2–3 are not proved here)

Vrieze's primal LP dualizes to an **occupation measure** `z_s(j)` (dual to
the bias row) and an auxiliary variable `y_s(j)` (dual to the gain row). The
naive idea — normalize `z_s(·)` into a mixed controller action
`τ_s(j) := z_s(j) / Σ_j z_s(j)` — is not total: at a **transient** state of
the chain induced by the extracted policy, an optimal dual point can have
`Σ_j z_s(j) = 0`. Vrieze's fix uses the *second* dual variable `y_s(·)` to
normalize at those states instead, and separately proves that the zero-`z`
states are *exactly* the transient states of the resulting chain. That
transient/recurrent support analysis is genuinely the hard step of the
undiscounted theory and is **not attempted here**; see the TODO on
`exists_controllerProjectionWitness_of_vriezePrimalDualOptimal` for exactly
what is missing and which pieces of the repository's LP-duality inventory
(below) it would draw on.

## LP-duality inventory (`Math/LinearProgramming`, `Math/LinearAlgebra`)

* `Math.LinearProgramming.Basic` — `dot`, `PrimalFeasible`/`DualFeasible`
  (`≤`/`≥`-form), `weak_duality`, primal/dual slack, and complementary
  slackness *from a zero duality gap*
  (`primalSlack_mul_dual_eq_zero_of_gap_zero`, its dual counterpart).
* `Math.LinearProgramming.Standard` — the standard-form pair
  (`MinPrimalFeasible`: `Ax ≥ b`, `x ≥ 0`; `MaxDualFeasible`: `yA ≤ c`,
  `y ≥ 0`), `min_weak_duality`, and the same complementary-slackness pattern.
* `Math.LinearProgramming.Certificates` — Farkas-style infeasibility
  certificates (`not_exists_primalFeasible_iff_exists_dual_certificate`,
  `not_exists_minPrimalFeasible_iff_exists_dual_certificate`), built on
  `Math.LinearAlgebra.Farkas`'s fintype Farkas lemma
  (`Math.LinearAlgebra.farkas_lemma_fintype`), itself built on
  `Math.LinearAlgebra.FourierMotzkin` elimination.
* `Math.LinearProgramming.StrongDuality` — **strong duality**: from an
  optimal primal point, `lp_strong_duality` produces a dual-feasible point of
  *equal* value (`exists_maxDualFeasible_of_minPrimal_lower_bound` is the
  underlying existence lemma, itself Farkas-based).
* `Math.LinearProgramming.StrongComplementarity` — the **Goldman–Tucker**
  strict-complementarity theorem: `exists_strong_complementary_pair` upgrades
  *any* optimal primal–dual pair to one that is *strictly* complementary at
  **every** row and column (`IsStrongComplementaryPair`). This is exactly the
  extra strength Vrieze's transient/recurrent argument needs — a state's
  dual occupation mass is positive *iff* its primal row is not strictly
  slack — but it is stated for the abstract `Row`/`Col` LP encoding, and
  *embedding* Vrieze's single-controller primal (two families of rows
  indexed by `(state, controller-action)`, plus the noncontroller's
  per-state simplex rows) into that encoding is precisely the piece of work
  this file does not do; see the TODO below.
* `Math.Minimax.Loomis` / `MinimaxLoomis` / `ShapleySnow` — LP-flavored
  proofs of the two-player zero-sum *matrix*-game minimax theorem (stage
  games only, no state dynamics); not used here, listed for completeness of
  the inventory.

None of `StrongDuality`/`StrongComplementarity` are invoked by the theorems
below: Step 1 needs no duality, and Step 4 needs only the (already proved)
mean-ergodic Poisson decomposition. They are inventoried because the
residual (Steps 2–3) is exactly the place a full solution would need them.

## Main definitions

* `StochasticGame.IsSingleController` — the controller's action alone
  determines the transition kernel
* `StochasticGame.controllerKernel` — the well-defined state kernel induced
  by a stationary controller strategy, under `IsSingleController`
* `StochasticGame.worstReward` — the per-state worst-case (over every
  opponent action) expected stage reward to the controller under a
  stationary controller strategy
* `StochasticGame.IsVriezePrimalFeasible` — Vrieze's undiscounted primal LP
  feasibility, stated in exactly the shape of
  `IsStationaryAverageGuaranteeCertificate`'s two drift inequalities
* `StochasticGame.IsControllerProjectionWitness` — the bridge object Step 4
  consumes: a controller policy `τ` and gain `ρ`, harmonic under `τ`'s kernel
  and dominated by that kernel's ergodic projection of `worstReward`
* `StochasticGame.IsVriezePrimalOptimal` — primal feasibility *plus*
  optimality of `Σ g_s`, the natural hypothesis the residual is stated under

## Main results

* `StochasticGame.isLowerAverageCertificate_of_vriezePrimalFeasible` (Step 1)
* `StochasticGame.isUpperAverageCertificate_of_controllerProjectionWitness`
  (Step 4)
* `StochasticGame.exists_uniformEquilibriumPayoff_of_singleController`
  (Step 5, conditional on a supplied `IsControllerProjectionWitness`)
* `StochasticGame.exists_controllerProjectionWitness_of_vriezePrimalDualOptimal`
  — **the isolated residual**, Steps 2–3, stated but not proved
* `SingleControllerExample.transientProjectionWitness` — a minimal concrete
  instance: a two-state single-controller game (one transient, one absorbing
  state under the extracted policy) with an explicit
  `IsControllerProjectionWitness`, exercising the non-constant / transient
  branch of Step 4's mechanism

This file is deliberately **not** wired into `GameTheory.lean` (the project
aggregator): it is a standalone verification object, importable directly.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability

-- ============================================================================
-- Single-controller games
-- ============================================================================

/-- **Single controller.** The transition kernel of `G` depends only on the
`controller`'s own action coordinate: replacing the *other* player's action,
with the controller's action held fixed, never changes the distribution over
next states. -/
def IsSingleController (G : StochasticGame Bool) (controller : Bool) : Prop :=
  ∀ (s : G.State) (j : G.Act controller) (b b' : G.JointAct),
    G.transition s (Function.update b controller j) =
      G.transition s (Function.update b' controller j)

variable {G : StochasticGame Bool} [Finite G.State] [∀ i, Finite (G.Act i)]
  [∀ i, Nonempty (G.Act i)]

/-- A canonical joint action, used only to pick out *some* transition query;
under `IsSingleController` the choice is immaterial (`controllerKernel_eq_bind`
below). -/
private def anyJointAct (G : StochasticGame Bool) [∀ i, Nonempty (G.Act i)] :
    G.JointAct :=
  fun i => Classical.arbitrary (G.Act i)

/-- **The controller-only kernel** induced by a stationary controller
strategy `τ`: mix the controller's own action according to `τ s`, and read
off the transition using *any* fixed joint action to complete it (immaterial
by single-controllerness). Well defined without any hypothesis; matching it
to the transition at an *arbitrary* opponent choice needs
`controllerKernel_eq_bind`. -/
def controllerKernel (G : StochasticGame Bool) [∀ i, Nonempty (G.Act i)]
    (controller : Bool) (τ : G.State → PMF (G.Act controller)) :
    G.State → PMF G.State :=
  fun s => (τ s).bind fun j =>
    G.transition s (Function.update (anyJointAct G) controller j)

omit [Finite G.State] [∀ i, Finite (G.Act i)] in
/-- Under `IsSingleController`, `controllerKernel` agrees with binding `τ`
against the transition completed by *any* joint action `b`, not just the
canonical one baked into the definition. -/
theorem controllerKernel_eq_bind {controller : Bool}
    (hSC : G.IsSingleController controller) (τ : G.State → PMF (G.Act controller))
    (s : G.State) (b : G.JointAct) :
    G.controllerKernel controller τ s =
      (τ s).bind fun j => G.transition s (Function.update b controller j) := by
  unfold controllerKernel
  congr 1
  funext j
  exact hSC s j (anyJointAct G) b

/-- A (noncanonical) `Fintype` instance on `G.State` from the ambient
`Finite` hypothesis, registered globally so it is found consistently by
every later typeclass search (`Math.MeanErgodic`'s finite-Markov API is
stated for `[Fintype S]`, not merely `[Finite S]`). -/
instance instFintypeState {G : StochasticGame Bool} [Finite G.State] :
    Fintype G.State :=
  Fintype.ofFinite G.State

/-- A (noncanonical) `Fintype` instance on `G.JointAct` from the ambient
`Finite` hypotheses, registered globally (rather than as a local `letI`
inside a single definition) so that every later `unfold`/typeclass search
resolves the *same* instance consistently. -/
instance instFintypeJointAct {G : StochasticGame Bool} [∀ i, Finite (G.Act i)] :
    Fintype G.JointAct :=
  Fintype.ofFinite G.JointAct

/-- **Worst-case controller reward.** The per-state expected stage payoff to
`controller` under the stationary strategy `τ`, minimized over every possible
opponent joint action (mixed opponent play only lowers this further by
linearity of expectation, so quantifying over *pure* opponent actions here
already captures the guarantee against every mixed opponent strategy — the
same convention `IsStationaryAverageGuaranteeCertificate` uses). -/
def worstReward (G : StochasticGame Bool) [Finite G.State] [∀ i, Finite (G.Act i)]
    [∀ i, Nonempty (G.Act i)] (controller : Bool)
    (τ : G.State → PMF (G.Act controller)) (s : G.State) : ℝ :=
  Finset.inf' (Finset.univ : Finset G.JointAct) ⟨anyJointAct G, Finset.mem_univ _⟩
    fun b : G.JointAct =>
      expect (τ s) fun j => G.stagePayoff s (Function.update b controller j) controller

/-- `worstReward` is a genuine lower bound on the expected stage payoff to
`controller`, at every state and against every opponent joint action. -/
theorem worstReward_le {controller : Bool} (τ : G.State → PMF (G.Act controller))
    (s : G.State) (b : G.JointAct) :
    G.worstReward controller τ s ≤
      expect (τ s) fun j => G.stagePayoff s (Function.update b controller j) controller := by
  unfold worstReward
  exact Finset.inf'_le _ (Finset.mem_univ b)

/-- `worstReward` is the *greatest* such lower bound: any `d` dominated by the
expected stage payoff against *every* opponent joint action is `≤ worstReward`. -/
theorem le_worstReward {controller : Bool} (τ : G.State → PMF (G.Act controller))
    (s : G.State) (d : ℝ)
    (h : ∀ b : G.JointAct,
      d ≤ expect (τ s) fun j => G.stagePayoff s (Function.update b controller j) controller) :
    d ≤ G.worstReward controller τ s := by
  unfold worstReward
  exact Finset.le_inf' _ _ fun b _ => h b

-- ============================================================================
-- Step 1: Vrieze's primal LP feasibility gives the noncontroller's certificate
-- ============================================================================

/-- **Vrieze's undiscounted primal LP, single-controller case.** A mixed
stationary action `x` for the *noncontroller* (`!controller`), a gain
`g : State → ℝ`, and a bias `v : State → ℝ` satisfy, for every state `s` and
every joint action `b` (only `b controller` — the controller's action —
actually matters, since `b`'s own `!controller` coordinate is overridden by
the draw from `x s`; ranging over the full `JointAct` rather than just
`G.Act controller` is harmless and keeps the statement syntactically
identical to `IsStationaryAverageGuaranteeCertificate`'s two clauses):

* **gain**: `g s ≤ E_{i ~ x s}[ E[g t | transition s (update b !controller i)] ]`
* **bias**: `g s + v s ≤
    E_{i ~ x s}[ stagePayoff s (update b !controller i) !controller +
      E[v t | transition s (update b !controller i)] ]`

which is exactly Vrieze's `g_s ≤ Σ_t p(t|s,j) g_t` and
`g_s + v_s ≤ Σ_i x_s(i) r(s,i,j) + Σ_t p(t|s,j) v_t`, reindexed through
`b controller = j`. -/
def IsVriezePrimalFeasible (G : StochasticGame Bool) [∀ i, Finite (G.Act i)]
    (controller : Bool) (x : G.State → PMF (G.Act (!controller)))
    (g v : G.State → ℝ) : Prop :=
  (∀ (s : G.State) (b : G.JointAct),
    g s ≤ expect (x s) fun i =>
      expect (G.transition s (Function.update b (!controller) i)) g) ∧
  (∀ (s : G.State) (b : G.JointAct),
    g s + v s ≤ expect (x s) fun i =>
      G.stagePayoff s (Function.update b (!controller) i) (!controller) +
        expect (G.transition s (Function.update b (!controller) i)) v)

omit [∀ i, Nonempty (G.Act i)] in
/-- **Step 1.** A Vrieze-primal-feasible point gives the *noncontroller's*
`IsStationaryAverageGuaranteeCertificate` directly, at value `g s₀` — a pure
repackaging of `IsVriezePrimalFeasible`'s two clauses, which are *literally*
`IsStationaryAverageGuaranteeCertificate`'s two drift inequalities for
`who := !controller`, `mwho := x`, `ρ := g`, `u := v`. No duality is used. -/
theorem isLowerAverageCertificate_of_vriezePrimalFeasible
    (controller : Bool) (s₀ : G.State) (x : G.State → PMF (G.Act (!controller)))
    (g v : G.State → ℝ) (hfeas : G.IsVriezePrimalFeasible controller x g v) :
    G.IsStationaryAverageGuaranteeCertificate s₀ (!controller) (g s₀) :=
  ⟨x, g, v, le_refl _, hfeas.1, hfeas.2⟩

-- ============================================================================
-- The mean-ergodic projection, repackaged from `Math.MeanErgodic`
-- ============================================================================

/-- **The mean-ergodic (ergodic-projection) component** of an observable `f`
under a finite-state Markov kernel `κ`: the harmonic part `o` of the
Poisson decomposition `f = o + (κ-step u − u)`
(`Math.MeanErgodic.exists_harmonic_add_poisson`), picked once via choice.
Unique by `Math.MeanErgodic.harmonic_eq_of_add_poisson_eq`, so *any* valid
harmonic-plus-Poisson decomposition of `f` identifies this function. -/
def ergodicProjection {S : Type*} [Fintype S] (κ : S → PMF S) (f : S → ℝ) : S → ℝ :=
  (Math.MeanErgodic.exists_harmonic_add_poisson κ f).choose

/-- The Poisson potential paired with `ergodicProjection` by the same choice,
so that `eq_ergodicProjection_add_poisson` below holds. -/
def ergodicPoissonPotential {S : Type*} [Fintype S] (κ : S → PMF S) (f : S → ℝ) :
    S → ℝ :=
  (Math.MeanErgodic.exists_harmonic_add_poisson κ f).choose_spec.choose

theorem ergodicProjection_harmonic {S : Type*} [Fintype S] (κ : S → PMF S)
    (f : S → ℝ) (s : S) : expect (κ s) (ergodicProjection κ f) = ergodicProjection κ f s :=
  (Math.MeanErgodic.exists_harmonic_add_poisson κ f).choose_spec.choose_spec.1 s

theorem eq_ergodicProjection_add_poisson {S : Type*} [Fintype S] (κ : S → PMF S)
    (f : S → ℝ) (s : S) :
    f s = ergodicProjection κ f s +
      (expect (κ s) (ergodicPoissonPotential κ f) - ergodicPoissonPotential κ f s) :=
  (Math.MeanErgodic.exists_harmonic_add_poisson κ f).choose_spec.choose_spec.2.1 s

-- ============================================================================
-- Step 4: the controller projection witness ⟹ the controller's own certificate
-- ============================================================================

/-- **Controller projection witness.** A stationary controller strategy `τ`
together with a candidate gain `ρ` such that:

* `harmonic` — `ρ` is *exactly* harmonic under `τ`'s controller-only kernel
  (`controllerKernel controller τ`); and
* `le_ergodicProjectionWorstReward` — `ρ` is dominated, pointwise, by that
  kernel's mean-ergodic projection of the worst-case controller reward
  `worstReward controller τ`.

This is exactly the data an optimal primal–dual pair of Vrieze's LP would
supply for the controller's side (`τ` from the normalized dual occupation
measure; `ρ` the shared optimal gain) — see the module docstring for what
extracting it needs and why it is not attempted here
(`exists_controllerProjectionWitness_of_vriezePrimalDualOptimal`). Given the
witness, `isUpperAverageCertificate_of_controllerProjectionWitness` produces
the controller's own `IsStationaryAverageGuaranteeCertificate` by a purely
mechanical Poisson-equation computation. -/
structure IsControllerProjectionWitness (G : StochasticGame Bool) [Finite G.State]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)] (controller : Bool)
    (τ : G.State → PMF (G.Act controller)) (ρ : G.State → ℝ) : Prop where
  harmonic : ∀ s, expect (G.controllerKernel controller τ s) ρ = ρ s
  le_ergodicProjectionWorstReward :
    ∀ s, ρ s ≤ ergodicProjection (G.controllerKernel controller τ)
      (G.worstReward controller τ) s

/-- **Step 4** (game independent, mechanical Poisson step). A controller
projection witness `(τ, ρ)` gives the *controller's own*
`IsStationaryAverageGuaranteeCertificate` at value `ρ s₀`, with bias
`u := -(ergodicPoissonPotential κ f)` where `κ` is `τ`'s controller-only
kernel and `f := worstReward controller τ`.

The gain drift is an *exact* equality (`ρ` is genuinely harmonic under `κ`,
and `κ` does not depend on the opponent's action at all, by
single-controllerness). The bias drift uses the Poisson identity
`f s + (κ-step u) s = ergodicProjection κ f s + u s` (from the defining
decomposition of `f`, with `u`'s sign chosen exactly to make this hold),
combined with `le_ergodicProjectionWorstReward` and `worstReward_le` (the
worst-case reward is a genuine lower bound on the actual expected stage
payoff against every opponent action). -/
theorem isUpperAverageCertificate_of_controllerProjectionWitness
    {controller : Bool} (hSC : G.IsSingleController controller)
    (τ : G.State → PMF (G.Act controller)) (ρ : G.State → ℝ)
    (hw : G.IsControllerProjectionWitness controller τ ρ) (s₀ : G.State) :
    G.IsStationaryAverageGuaranteeCertificate s₀ controller (ρ s₀) := by
  classical
  set κ : G.State → PMF G.State := G.controllerKernel controller τ with hκdef
  set f : G.State → ℝ := G.worstReward controller τ with hfdef
  set o : G.State → ℝ := ergodicProjection κ f with hodef
  set w : G.State → ℝ := ergodicPoissonPotential κ f with hwdef
  set u : G.State → ℝ := fun s => -(w s) with hudef
  -- The Poisson identity: `f s + (κ-step u) s = o s + u s`.
  have hkey : ∀ s, f s + expect (κ s) u = o s + u s := by
    intro s
    have hdecomp := eq_ergodicProjection_add_poisson κ f s
    have hneg : expect (κ s) u = -(expect (κ s) w) := by
      have := expect_const_mul (κ s) (-1 : ℝ) w
      simpa [hudef, neg_one_mul] using this
    rw [hneg]
    simp only [hudef, hodef, hwdef] at hdecomp ⊢
    linarith [hdecomp]
  refine ⟨τ, ρ, u, le_refl _, ?_, ?_⟩
  · -- gain: equality via harmonicity, at every `b` (κ does not depend on it)
    intro s b
    have hbind : expect (τ s) (fun a => expect (G.transition s (Function.update b controller a)) ρ)
        = expect (κ s) ρ := by
      rw [hκdef, G.controllerKernel_eq_bind hSC τ s b, expect_bind]
    rw [hbind, hw.harmonic s]
  · -- bias: the Poisson identity, `le_ergodicProjectionWorstReward`, and
    -- `worstReward_le`
    intro s b
    have hbind : expect (τ s) (fun a =>
        G.stagePayoff s (Function.update b controller a) controller +
          expect (G.transition s (Function.update b controller a)) u) =
        expect (τ s) (fun a => G.stagePayoff s (Function.update b controller a) controller) +
          expect (κ s) u := by
      rw [expect_add, hκdef, G.controllerKernel_eq_bind hSC τ s b, expect_bind]
    rw [hbind]
    have hwr : f s ≤ expect (τ s) fun a =>
        G.stagePayoff s (Function.update b controller a) controller :=
      G.worstReward_le τ s b
    have hle : ρ s ≤ o s := hw.le_ergodicProjectionWorstReward s
    linarith [hkey s, hwr, hle]

-- ============================================================================
-- Step 5: assembling the uniform equilibrium payoff
-- ============================================================================

/-- **Step 5.** Assemble a noncontroller certificate (Step 1's output, from a
Vrieze-primal-feasible point at value `V := g s₀`) and a controller
certificate (Step 4's output, from a projection witness with `ρ s₀ = -V`)
into a full `IsUniformEquilibriumPayoff`, via
`isUniformEquilibriumPayoff_of_isZeroSumBoolGame_of_stationaryAverageGuarantees`.
Conditional on the projection witness `hw` — the residual left open by
Steps 2–3. -/
theorem exists_uniformEquilibriumPayoff_of_singleController
    (hzs : G.IsZeroSumBoolGame) {controller : Bool}
    (hSC : G.IsSingleController controller) (s₀ : G.State) (V : ℝ)
    (x : G.State → PMF (G.Act (!controller))) (g v : G.State → ℝ)
    (hfeas : G.IsVriezePrimalFeasible controller x g v) (hgval : g s₀ = V)
    (τ : G.State → PMF (G.Act controller)) (ρ : G.State → ℝ)
    (hw : G.IsControllerProjectionWitness controller τ ρ) (hρval : ρ s₀ = -V) :
    ∃ payoff : Payoff Bool, G.IsUniformEquilibriumPayoff s₀ payoff := by
  have hnc := G.isLowerAverageCertificate_of_vriezePrimalFeasible controller s₀ x g v hfeas
  have hc := G.isUpperAverageCertificate_of_controllerProjectionWitness hSC τ ρ hw s₀
  rw [hgval] at hnc
  rw [hρval] at hc
  cases controller with
  | false =>
    -- controller = false, noncontroller = !false = true
    refine ⟨_, G.isUniformEquilibriumPayoff_of_isZeroSumBoolGame_of_stationaryAverageGuarantees
      hzs s₀ (-V) hc ?_⟩
    simpa using hnc
  | true =>
    -- controller = true, noncontroller = !true = false
    exact ⟨_, G.isUniformEquilibriumPayoff_of_isZeroSumBoolGame_of_stationaryAverageGuarantees
      hzs s₀ V hnc hc⟩

-- ============================================================================
-- The isolated residual: Steps 2–3
-- ============================================================================

/-- **Vrieze primal optimality.** A `IsVriezePrimalFeasible` point that
additionally maximizes the LP objective `Σ_s g_s` over every feasible point
— exactly the hypothesis under which Vrieze's theorem identifies `g` with
the game's value function and extracts the controller's own optimal
stationary policy from the *dual* optimal point of the same LP. -/
structure IsVriezePrimalOptimal (G : StochasticGame Bool) [Finite G.State]
    [∀ i, Finite (G.Act i)] (controller : Bool) (x : G.State → PMF (G.Act (!controller)))
    (g v : G.State → ℝ) : Prop where
  feasible : G.IsVriezePrimalFeasible controller x g v
  optimal : ∀ (x' : G.State → PMF (G.Act (!controller))) (g' v' : G.State → ℝ),
    G.IsVriezePrimalFeasible controller x' g' v' →
    letI : Fintype G.State := Fintype.ofFinite G.State
    ∑ s, g' s ≤ ∑ s, g s

/-- **THE ISOLATED RESIDUAL** (Vrieze's Steps 2–3), stated but **not
proved**. From a primal-optimal Vrieze point `(x, g, v)`, extracting a
controller stationary strategy `τ` and a gain `ρ = -g` satisfying
`IsControllerProjectionWitness` requires:

1. Dualizing `IsVriezePrimalOptimal` — encoding its two families of rows
   (indexed by `(state, controller-action)`, one per gain inequality and one
   per bias inequality) plus the noncontroller's per-state simplex equality
   rows into `Math.LinearProgramming.Standard`'s abstract `Row`/`Col` form,
   then invoking `Math.LinearProgramming.StrongDuality.lp_strong_duality`
   for *existence* of a dual-optimal point `(z, y)` (`z` dual to the bias
   rows — Vrieze's occupation measure; `y` dual to the gain rows).
2. Strengthening to a *strictly* complementary optimal pair via
   `Math.LinearProgramming.StrongComplementarity.exists_strong_complementary_pair`
   (Goldman–Tucker), so that a state's total dual mass
   `Σ_j z_s(j)` is positive *iff* its primal bias row is not strictly slack.
3. **The trap.** Proving that the states with `Σ_j z_s(j) = 0` are *exactly*
   the states that are transient under the kernel induced by the extracted
   policy — this needs a formal notion of transience/recurrence for
   `controllerKernel`'s induced chain (not yet formalized anywhere in this
   repository) and Vrieze's specific argument connecting it to strict
   primal/dual complementarity.
4. At the zero-`z` (transient) states, normalizing `τ_s` from `y_s(·)`
   instead of `z_s(·)`, and checking the resulting `τ` and `ρ := -g` satisfy
   both fields of `IsControllerProjectionWitness` — `harmonic` needs the
   *dual gain-row feasibility* of `y` to force `ρ`'s exact harmonicity under
   `controllerKernel controller τ`; `le_ergodicProjectionWorstReward` needs
   the *dual bias-row feasibility* of `z` together with complementary
   slackness against the primal bias rows.

None of this is attempted: the theorem below takes the entire conclusion as
an explicit hypothesis `hextract` (the honest name for "Steps 2–3, assumed")
and returns it unchanged. Discharging `hextract` — replacing it with an
actual construction of `(τ, ρ)` from `hopt`, following the four points above
— is the required continuation of this file. -/
theorem exists_controllerProjectionWitness_of_vriezePrimalDualOptimal
    {controller : Bool} {x : G.State → PMF (G.Act (!controller))} {g v : G.State → ℝ}
    (_hopt : G.IsVriezePrimalOptimal controller x g v)
    (hextract : ∃ (τ : G.State → PMF (G.Act controller)) (ρ : G.State → ℝ),
      G.IsControllerProjectionWitness controller τ ρ ∧ ρ = fun s => -(g s)) :
    ∃ (τ : G.State → PMF (G.Act controller)) (ρ : G.State → ℝ),
      G.IsControllerProjectionWitness controller τ ρ ∧ ρ = fun s => -(g s) :=
  hextract

/-- The full undiscounted single-controller uniform-value theorem,
**conditional** on the residual `hextract`
(`exists_controllerProjectionWitness_of_vriezePrimalDualOptimal`'s
hypothesis): once `hextract` is discharged for an actual single-controller
game, this corollary needs no further work to deliver
`IsUniformEquilibriumPayoff`. -/
theorem exists_uniformEquilibriumPayoff_of_singleController_of_vriezePrimalOptimal
    (hzs : G.IsZeroSumBoolGame) {controller : Bool}
    (hSC : G.IsSingleController controller) (s₀ : G.State)
    {x : G.State → PMF (G.Act (!controller))} {g v : G.State → ℝ}
    (hopt : G.IsVriezePrimalOptimal controller x g v)
    (hextract : ∃ (τ : G.State → PMF (G.Act controller)) (ρ : G.State → ℝ),
      G.IsControllerProjectionWitness controller τ ρ ∧ ρ = fun s => -(g s)) :
    ∃ payoff : Payoff Bool, G.IsUniformEquilibriumPayoff s₀ payoff := by
  obtain ⟨τ, ρ, hw, hρeq⟩ :=
    G.exists_controllerProjectionWitness_of_vriezePrimalDualOptimal hopt hextract
  refine G.exists_uniformEquilibriumPayoff_of_singleController hzs hSC s₀ (g s₀) x g v
    hopt.feasible rfl τ ρ hw ?_
  rw [hρeq]

end StochasticGame
end GameTheory

-- ============================================================================
-- Minimal validation: a concrete single-controller instance with a
-- transient state
-- ============================================================================

/-!
### A concrete two-state single-controller instance

`State := Bool` with `false` (`A`) **transient** and `true` (`B`)
**absorbing** under the (only available) controller policy: the controller
has a single action (`Unit`), so the transition `A ↦ B`, `B ↦ B` is forced
regardless of play, and is trivially single-controller. The noncontroller
has two actions (`Bool`) affecting the stage payoff at the transient state
`A` only (`0` or `1`), with a fixed payoff `5` at the absorbing state `B`.

This exercises the genuinely **non-constant** branch of Step 4: the
worst-case reward `f` is `0` at the transient state `A` and `5` at the
absorbing state `B`, so its mean-ergodic projection is the *constant* `5`
(the chain's unique recurrent value) — strictly different from `f` at the
transient state `A`, showing the projection is doing real work, not merely
reproducing `f` itself (which the `IsAbsorbingEverywhere` validation in
`AverageOptimalityCertificate.lean` cannot exercise, since there every state
is already absorbing). -/

namespace SingleControllerExample

open GameTheory Math.Probability

/-- Player `false` is the controller (a single, inert action); player `true`
is the noncontroller (two actions, affecting the payoff at the transient
state only). -/
def Act : Bool → Type
  | false => Unit
  | true => Bool

instance : ∀ i, Fintype (Act i)
  | false => inferInstanceAs (Fintype Unit)
  | true => inferInstanceAs (Fintype Bool)

instance : ∀ i, Nonempty (Act i)
  | false => inferInstanceAs (Nonempty Unit)
  | true => inferInstanceAs (Nonempty Bool)

/-- Both states transition to `true` (`B`) for sure, regardless of the joint
action: `false` (`A`) is transient, `true` (`B`) is absorbing. -/
def transition : Bool → (∀ i, Act i) → PMF Bool := fun _ _ => PMF.pure true

/-- The controller's (`false`'s) stage payoff: `5` at the absorbing state
`B`; at the transient state `A`, `1` if the noncontroller plays `true`, `0`
otherwise. -/
def payoffFalse (s : Bool) (a : ∀ i, Act i) : ℝ :=
  if s then 5 else (cond (a true) 1 0)

/-- Zero-sum stage payoff. -/
def payoff (s : Bool) (a : ∀ i, Act i) (who : Bool) : ℝ :=
  if who then -(payoffFalse s a) else payoffFalse s a

/-- The two-state single-controller validating instance. -/
def game : StochasticGame Bool where
  State := Bool
  Act := Act
  stagePayoff := payoff
  transition := transition
  discount := 0
  discount_nonneg := le_refl 0
  discount_lt_one := by norm_num

instance : Finite game.State := inferInstanceAs (Finite Bool)

instance : ∀ i, Finite (game.Act i) := fun i => inferInstanceAs (Finite (Act i))

instance : ∀ i, Nonempty (game.Act i) := fun i => inferInstanceAs (Nonempty (Act i))

theorem game_isZeroSumBoolGame : game.IsZeroSumBoolGame := fun s a => by
  simp [game, payoff]

theorem game_isSingleController : game.IsSingleController false :=
  fun _ _ _ _ => rfl

/-- The (only) controller stationary strategy: the single available action. -/
def τ : Bool → PMF (game.Act false) := fun _ => PMF.pure ()

/-- `false` (`A`) is genuinely transient, `true` (`B`) genuinely absorbing,
under `τ`'s induced kernel. -/
theorem controllerKernel_τ_eq :
    game.controllerKernel false τ = fun _ => PMF.pure true := by
  funext s
  unfold StochasticGame.controllerKernel τ
  simp [game, transition]

/-- Any joint action, used to complete transition/payoff queries whose
value does not depend on the choice. -/
def someJointAct (j : Bool) : (i : Bool) → Act i
  | false => ()
  | true => j

theorem worstReward_τ_false : game.worstReward false τ false = 0 := by
  have hle : game.worstReward false τ false ≤
      expect (τ false) fun j =>
        game.stagePayoff false (Function.update (someJointAct false) false j) false :=
    game.worstReward_le τ false (someJointAct false)
  have hval0 : (expect (τ false) fun j =>
      game.stagePayoff false (Function.update (someJointAct false) false j) false) = 0 := by
    simp [τ, game, payoff, payoffFalse, someJointAct, Function.update]
  have hge : (0 : ℝ) ≤ game.worstReward false τ false := by
    apply game.le_worstReward
    intro b
    rcases hb : b true with _ | _ <;>
      simp [τ, game, payoff, payoffFalse, Function.update, hb]
  linarith [hle, hval0, hge]

theorem worstReward_τ_true : game.worstReward false τ true = 5 := by
  have hle : game.worstReward false τ true ≤
      expect (τ true) fun j =>
        game.stagePayoff true (Function.update (someJointAct false) false j) false :=
    game.worstReward_le τ true (someJointAct false)
  have hval : (expect (τ true) fun j =>
      game.stagePayoff true (Function.update (someJointAct false) false j) false) = 5 := by
    simp [τ, game, payoff, payoffFalse]
  have hge : (5 : ℝ) ≤ game.worstReward false τ true := by
    apply game.le_worstReward
    intro b
    simp [τ, game, payoff, payoffFalse]
  linarith [hle, hval, hge]

/-- Generic (state-type-agnostic, hence friction-free) computation of the
mean-ergodic projection for a two-state, transient-into-absorbing `Bool`
kernel: proved entirely over `Bool` so that no `game.State`-vs-`Bool`
defeq-unfolding issue can arise inside `rw`; `ergodicProjection_worstReward_τ`
below applies it to `game`'s (definitionally `Bool`) state type at a single
top-level function application, where full elaboration-time defeq suffices. -/
private theorem ergodicProjection_pure_true_kernel (κ : Bool → PMF Bool) (f : Bool → ℝ)
    (hκ : ∀ s, κ s = PMF.pure true) (hfA : f false = 0) (hfB : f true = 5) :
    StochasticGame.ergodicProjection κ f = fun _ => (5 : ℝ) := by
  classical
  set o2 : Bool → ℝ := fun _ => (5 : ℝ) with ho2
  set u2 : Bool → ℝ := fun s => cond s 0 5 with hu2
  have ho2harm : ∀ s, expect (κ s) o2 = o2 s := by
    intro s; rw [hκ s, Math.Probability.expect_pure, ho2]
  have hdecomp2 : ∀ s, f s = o2 s + (expect (κ s) u2 - u2 s) := by
    intro s
    rw [hκ s, Math.Probability.expect_pure]
    rcases s with _ | _
    · rw [hfA, ho2, hu2]; norm_num
    · rw [hfB, ho2, hu2]; norm_num
  have huniq := Math.MeanErgodic.harmonic_eq_of_add_poisson_eq κ f
    (StochasticGame.ergodicProjection κ f) (StochasticGame.ergodicPoissonPotential κ f)
    o2 u2
    (StochasticGame.ergodicProjection_harmonic κ f)
    (StochasticGame.eq_ergodicProjection_add_poisson κ f) ho2harm hdecomp2
  rw [huniq, ho2]

/-- The constant `5` is a valid harmonic-plus-Poisson decomposition of the
worst-case reward under `τ`'s (transient-at-`A`, absorbing-at-`B`) kernel. -/
theorem ergodicProjection_worstReward_τ :
    StochasticGame.ergodicProjection (game.controllerKernel false τ)
        (game.worstReward false τ) = fun _ => (5 : ℝ) :=
  ergodicProjection_pure_true_kernel (game.controllerKernel false τ) (game.worstReward false τ)
    (fun s => congrFun controllerKernel_τ_eq s) worstReward_τ_false worstReward_τ_true

/-- **The minimal validating instance**: the constant gain `ρ ≡ 5` and the
(only) controller strategy `τ` form an `IsControllerProjectionWitness` for
`game`, whose induced chain has a genuinely transient state (`false`/`A`). -/
theorem transientProjectionWitness :
    game.IsControllerProjectionWitness false τ (fun _ => (5 : ℝ)) where
  harmonic := by
    intro s
    rw [controllerKernel_τ_eq]
    simp
  le_ergodicProjectionWorstReward := by
    intro s
    rw [ergodicProjection_worstReward_τ]

end SingleControllerExample
