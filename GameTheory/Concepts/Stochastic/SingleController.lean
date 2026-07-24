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
transient/recurrent support analysis splits into a purely **combinatorial**
part — no choice of controller action anywhere can build a "trap" region
disjoint from `R := {s | 0 < Σ_j z_s(j)}` (a bottom strongly-connected
component of the induced chain missing `R` entirely) — and a genuinely
**game-specific** part, that `R` in fact has this property because it is
the *optimal* LP occupation support (a policy-improvement argument). The
`FiniteReachability` namespace below proves the combinatorial part in full
generality (for an arbitrary successor relation, independent of the game
and LP data); the game-specific part, and the probabilistic translation of
graph-reachability into the mean-ergodic statement `IsControllerProjectionWitness`
actually needs, are **not attempted here**; see the TODO on
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
* `StochasticGame.FiniteReachability.CanReachSet` — reachability of a target
  set along an arbitrary successor relation (generic finite-graph theory,
  independent of the game/LP data)
* `StochasticGame.controllerSucc` — the game's controller-action successor
  relation `FiniteReachability` is meant to be instantiated against

## Main results

* `StochasticGame.isLowerAverageCertificate_of_vriezePrimalFeasible` (Step 1)
* `StochasticGame.isUpperAverageCertificate_of_controllerProjectionWitness`
  (Step 4)
* `StochasticGame.exists_uniformEquilibriumPayoff_of_singleController`
  (Step 5, conditional on a supplied `IsControllerProjectionWitness`)
* `StochasticGame.FiniteReachability.trap_closed_of_not_canReachSet` — the
  states that cannot reach a target set `R` are themselves closed under
  every successor: the precise combinatorial form of "a trap disjoint from
  `R` is unavoidable unless every non-`R` state can reach `R`", i.e. Vrieze's
  bottom-strongly-connected-component obstruction, proved for an arbitrary
  successor relation
* `StochasticGame.FiniteReachability.exists_succ_canReachSet_of_canReachSet`
  — the "make one step of progress toward `R`" building block a total
  completion policy on the non-recurrent states would iterate
* `StochasticGame.exists_controllerProjectionWitness_of_vriezePrimalDualOptimal`
  — **the isolated residual**, Steps 2–3, stated but not proved; see its
  docstring for the six obligations the graph reformulation above splits it
  into, and which of them remain open
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

/-- A (noncanonical) `Fintype` instance on each `G.Act i` from the ambient
`Finite` hypothesis, registered globally so the LP-embedding column/row types
below (products and sums built from `G.Act controller`/`G.Act (!controller)`)
find a consistent `Fintype` instance by typeclass search. -/
instance instFintypeAct {G : StochasticGame Bool} [∀ i, Finite (G.Act i)] (i : Bool) :
    Fintype (G.Act i) :=
  Fintype.ofFinite (G.Act i)

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
-- Finite successor-graph reachability (pure graph theory, generic)
-- ============================================================================

/-!
### The trap/reachability structure behind the transient completion

Vrieze's "zero occupation ⟺ transient" step (the module docstring's "trap")
is a genuine two-part claim: (a) a purely **combinatorial** fact about which
states can be routed, by *some* choice of controller action at every state,
into the recurrent support `R` of the extracted policy; and (b) the
genuinely game-specific fact that `R` (the set of states with positive LP
occupation mass) always has this routing property — i.e. that no *trap*
region disjoint from `R` can be LP-optimal, which needs the LP's
*optimality* (not just feasibility) via a policy-improvement argument.

This section proves (a) in full generality, as a statement about an
arbitrary successor relation on an arbitrary type — deliberately **not**
about `StochasticGame`, `PMF`, or the LP data at all, so it is reusable
regardless of how the connection to (b) is eventually made.
`trap_closed_of_not_canReachSet` shows that if (b) *fails* at some
particular `R`, the failure set is itself closed under every available
successor (an unavoidable trap, exactly Vrieze's obstruction: a "bottom
strongly-connected component" disjoint from `R`); and
`exists_succ_canReachSet_of_canReachSet` is the "make one step of progress
toward `R`" building block a total completion policy would be assembled
from, at every state from which `R` remains reachable at all. -/

namespace FiniteReachability

variable {S : Type*} (Succ : S → S → Prop) (R : S → Prop)

/-- Reachability along a successor relation `Succ`: the reflexive–transitive
closure, i.e. "there is a (possibly empty) chain of `Succ`-steps". -/
abbrev CanReachVia (s t : S) : Prop := Relation.ReflTransGen Succ s t

/-- `s` can reach the target set `R` along `Succ`. -/
def CanReachSet (s : S) : Prop := ∃ r, R r ∧ CanReachVia Succ s r

/-- **Trap closure** (Vrieze's obstruction, made precise). The states that
neither lie in `R` nor can reach `R` are closed under every available
`Succ`-step: if such a state exists, it (together with everything reachable
from it) forms an unavoidable region entirely disjoint from `R`, no matter
which successor is chosen at each step — exactly the "trap" the module
docstring's transient/recurrent analysis must rule out for `R := {s | 0 <
Σ_j z_s(j)}` (the LP-optimal occupation support). -/
theorem trap_closed_of_not_canReachSet {s t : S}
    (_hsR : ¬ R s) (hs : ¬ CanReachSet Succ R s) (hst : Succ s t) :
    ¬ R t ∧ ¬ CanReachSet Succ R t := by
  refine ⟨fun htR => hs ⟨t, htR, Relation.ReflTransGen.single hst⟩, ?_⟩
  rintro ⟨r, hr, hpath⟩
  exact hs ⟨r, hr, Relation.ReflTransGen.head hst hpath⟩

/-- **Greedy one-step progress.** If a non-`R` state can reach `R` at all,
some single available successor can *also* reach `R`. Iterating this choice
is exactly how a total completion policy would be assembled on the
non-recurrent states, and (by `trap_closed_of_not_canReachSet`'s
contrapositive) is the only way to avoid building a trap. -/
theorem exists_succ_canReachSet_of_canReachSet {s : S}
    (hsR : ¬ R s) (h : CanReachSet Succ R s) :
    ∃ t, Succ s t ∧ CanReachSet Succ R t := by
  obtain ⟨r, hr, hpath⟩ := h
  rcases hpath.cases_head with heq | ⟨t, hst, htr⟩
  · exact absurd (heq ▸ hr) hsR
  · exact ⟨t, hst, r, hr, htr⟩

end FiniteReachability

/-- **The game's controller-action successor relation.** `t` is reachable
from `s` in one step under *some* pure controller action `j` — the
nondeterministic "support graph" that `FiniteReachability`'s lemmas above
are meant to be instantiated against, with the target set
`R := {s | 0 < Σ_j z_s(j)}` the LP-optimal occupation support. Connecting
the two — proving `R` has no trap, which needs the LP's *optimality*, not
just feasibility — is exactly the part of the residual this file does not
close; see the TODO below. -/
def controllerSucc (G : StochasticGame Bool) [∀ i, Finite (G.Act i)]
    [∀ i, Nonempty (G.Act i)] (controller : Bool) (s t : G.State) : Prop :=
  ∃ j : G.Act controller,
    t ∈ (G.controllerKernel controller (fun _ => PMF.pure j) s).support

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
3. **The trap**, now split into the six obligations the graph
   reformulation below isolates. Let `R := {s | 0 < Σ_j z_s(j)}` (the
   LP-optimal occupation support) and `τR` the `z`-normalized policy on `R`
   (`τR s := z_s(·) / Σ_j z_s(j)`, well defined exactly on `R`):
   (i) *totality* — extending `τR` to a total `τ : G.State → PMF (G.Act
   controller)`; (ii) *no trap* — every recurrent class of the completed
   `controllerKernel controller τ` meets `R` (equivalently, by
   `FiniteReachability.trap_closed_of_not_canReachSet`'s contrapositive
   applied to `Succ := controllerSucc G controller`: every state outside
   `R` can reach `R`, so the "0-occupation states are exactly the transient
   states" identity is the *consequence*, not the definition, of this
   step — this is the part needing the LP's *optimality*, via a
   policy-improvement argument ruling out an LP-beating trap, not proved
   here); (iii) states outside that support are transient (or zero-mass
   under the mean-ergodic projection) — given (ii),
   `FiniteReachability.exists_succ_canReachSet_of_canReachSet` supplies the
   one-step "make progress toward `R`" building block totality's completion
   at each non-`R` state would use, but the *probabilistic* consequence
   (transience in the Cesàro/ergodic sense the projection needs, as opposed
   to mere graph-reachability) is not derived from it here; (iv) the reward
   inequality on recurrent classes, from complementary slackness against
   `z` where the invariant mass lives; (v) the projection extension
   `ergodicProjection κ (worstReward controller τ) ≥ ρ` globally, because
   the non-`R` states are transient (needs (iii)); (vi) harmonicity
   `expect κ ρ = ρ` over the full state space, using the *dual gain-row*
   feasibility of `y` on `R` and, on the non-`R` states, the specific
   choice from (i)/(ii) making `ρ` locally constant along the completion.
4. At the zero-`z` (transient) states, normalizing `τ_s` from `y_s(·)`
   instead of `z_s(·)` where obligation (ii) leaves genuine freedom, and
   checking the resulting `τ` and `ρ := -g` satisfy both fields of
   `IsControllerProjectionWitness` per (iv)–(vi) above.

**What is landed vs. open.** The `FiniteReachability` namespace and
`controllerSucc` above discharge the *pure combinatorics* of obligation
(ii)'s statement (a bottom-strongly-connected-component-meets-`R` fact,
proved for an arbitrary successor relation, independent of the game and LP
data) and give the one-step tool obligation (i)'s completion would iterate.
They do **not** discharge (ii) itself (that `R` has no trap — the
LP-optimality/policy-improvement argument), nor the probabilistic content of
(iii)/(v)/(vi) (turning graph-reachability into an actual Cesàro/mean-ergodic
statement about `ergodicProjection`), nor points 1–2 and 4 (the LP embedding
itself). The theorem below still takes the entire conclusion as an explicit
hypothesis `hextract` (the honest name for "Steps 2–3, assumed") and returns
it unchanged — replacing it with an actual construction of `(τ, ρ)` from
`hopt`, discharging the open obligations above, is the required continuation
of this file. -/
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

-- ============================================================================
-- The LP embedding: Vrieze's primal in `Math.LinearProgramming.Standard` form
-- ============================================================================

/-!
### The LP embedding

This section carries out the "LP embedding" half of the residual above: it
embeds `IsVriezePrimalOptimal` into `Math.LinearProgramming.Standard`'s
min-primal/max-dual pair (`MinPrimalFeasible`/`MaxDualFeasible`), invokes
`Math.LinearProgramming.StrongDuality.lp_strong_duality`, and decodes the
resulting dual-optimal point into `IsVriezeDualOptimal`: the occupation
measure `z` (dual to the bias rows), the auxiliary `yGain` (dual to the gain
rows), and the per-state multiplier `lam` (dual to the noncontroller's
simplex row), together with the flow/stationarity equation, the gain-dual
identity, the reward-domination inequality, and the equal-objective fact.

The embedding needs `IsSingleController controller`: without it,
`IsVriezePrimalFeasible`'s two families of inequalities are **bilinear** in
`(x, g, v)` (the transition kernel genuinely depends on the noncontroller's
action `i`, which is averaged against by the very `x` being solved for), not
linear, so there is no linear program to embed. Under `IsSingleController`,
the transition/probability terms collapse to depend only on the
*controller's* action `j`, and the system becomes linear: this is exactly
what makes it *Vrieze's* LP (a single-controller construction) rather than a
general two-player stochastic-game LP.
-/

-- Classical decidability is opened locally (see `open Classical in` below) for
-- specific definitions where needed, to ensure consistent `Classical.propDecidable`
-- instances. Mixing instances would make `rw`/`simp` fail to match syntactically
-- identical propositions.

/-- A joint action with the `controller` coordinate fixed to `j` and the
`!controller` coordinate filled by `anyJointAct` (immaterial, since only the
`controller` coordinate is ever read through `IsSingleController`). -/
def jointOfControllerAct (G : StochasticGame Bool) [∀ i, Nonempty (G.Act i)]
    (controller : Bool) (j : G.Act controller) : G.JointAct :=
  Function.update (anyJointAct G) controller j

/-- A joint action with `controller`-coordinate `j` and `!controller`-coordinate
`i`. Matches `Function.update b (!controller) i` for `b := jointOfControllerAct
G controller j` **definitionally**, and (given `IsSingleController controller`)
for *every* `b` with `b controller = j`, up to the transition/payoff it feeds —
see `transition_jointOf_eq_of_single_controller`. -/
def jointOf (G : StochasticGame Bool) [∀ i, Nonempty (G.Act i)]
    (controller : Bool) (j : G.Act controller) (i : G.Act (!controller)) : G.JointAct :=
  Function.update (G.jointOfControllerAct controller j) (!controller) i

@[simp] theorem jointOfControllerAct_apply_self (G : StochasticGame Bool)
    [∀ i, Nonempty (G.Act i)] (controller : Bool) (j : G.Act controller) :
    (G.jointOfControllerAct controller j) controller = j :=
  Function.update_self ..

theorem controller_ne_not (controller : Bool) : controller ≠ !controller := by
  cases controller <;> decide

@[simp] theorem jointOf_apply_controller (G : StochasticGame Bool)
    [∀ i, Nonempty (G.Act i)] (controller : Bool) (j : G.Act controller)
    (i : G.Act (!controller)) :
    (G.jointOf controller j i) controller = j := by
  unfold jointOf
  rw [Function.update_of_ne (controller_ne_not controller)]
  exact jointOfControllerAct_apply_self G controller j

@[simp] theorem jointOf_apply_not (G : StochasticGame Bool) [∀ i, Nonempty (G.Act i)]
    (controller : Bool) (j : G.Act controller) (i : G.Act (!controller)) :
    (G.jointOf controller j i) (!controller) = i :=
  Function.update_self ..

/-- Any two joint actions agreeing at both `controller` and `!controller` (i.e.
everywhere, since `Bool` has exactly these two players) are equal. -/
theorem jointAct_ext_of_agree_controller_not (G : StochasticGame Bool) (controller : Bool)
    {b b' : G.JointAct} (hc : b controller = b' controller)
    (hn : b (!controller) = b' (!controller)) : b = b' := by
  funext p
  cases controller <;> cases p <;> first | exact hc | exact hn

/-- Under `IsSingleController controller`, the transition from `jointOf` does
not depend on the noncontroller's action `i` — the algebraic core that
collapses `IsVriezePrimalFeasible`'s bilinear inequalities to linear ones. -/
theorem transition_jointOf_eq_of_single_controller {G : StochasticGame Bool}
    [∀ i, Nonempty (G.Act i)] {controller : Bool} (hSC : G.IsSingleController controller)
    (s : G.State) (j : G.Act controller) (i : G.Act (!controller)) :
    G.transition s (G.jointOf controller j i) =
      G.transition s (G.jointOfControllerAct controller j) := by
  have h := hSC s j (G.jointOf controller j i) (G.jointOfControllerAct controller j)
  have e1 : Function.update (G.jointOf controller j i) controller j
      = G.jointOf controller j i := by
    have := Function.update_eq_self controller (G.jointOf controller j i)
    rwa [jointOf_apply_controller G controller j i] at this
  have e2 : Function.update (G.jointOfControllerAct controller j) controller j
      = G.jointOfControllerAct controller j := by
    have := Function.update_eq_self controller (G.jointOfControllerAct controller j)
    rwa [jointOfControllerAct_apply_self G controller j] at this
  rwa [e1, e2] at h

/-- Every joint action `b`, once its `!controller` coordinate is overridden to
`i`, agrees with `jointOf controller (b controller) i` — the general (not just
canonical-`b`) form needed to decode an arbitrary Standard-form feasible point
back into an `IsVriezePrimalFeasible` witness (which quantifies over *every*
`b`, not just `jointOfControllerAct`-shaped ones). -/
theorem update_not_eq_jointOf (G : StochasticGame Bool) [∀ i, Nonempty (G.Act i)]
    (controller : Bool) (b : G.JointAct) (i : G.Act (!controller)) :
    Function.update b (!controller) i = G.jointOf controller (b controller) i := by
  apply jointAct_ext_of_agree_controller_not G controller
  · rw [Function.update_of_ne (controller_ne_not controller), jointOf_apply_controller]
  · rw [Function.update_self, jointOf_apply_not]

/-- The controller-induced transition probability `P(t | s, j)`, as a real
number: the `IsSingleController`-collapsed transition kernel used throughout
the LP embedding. -/
noncomputable def transProb (G : StochasticGame Bool) [∀ i, Nonempty (G.Act i)]
    (controller : Bool) (s : G.State) (j : G.Act controller) (t : G.State) : ℝ :=
  (G.transition s (G.jointOfControllerAct controller j) t).toReal

/-- The noncontroller's stage reward `r(s, i, j)` at controller action `j`. -/
def rewardVal (G : StochasticGame Bool) [∀ i, Nonempty (G.Act i)]
    (controller : Bool) (s : G.State) (i : G.Act (!controller)) (j : G.Act controller) : ℝ :=
  G.stagePayoff s (G.jointOf controller j i) (!controller)

/-- **LP columns** for Vrieze's primal: the noncontroller's mixed-action
weights `x_s(i)`, and the sign-split free variables `g⁺_s, g⁻_s, v⁺_s, v⁻_s`
(with `g_s = g⁺_s - g⁻_s`, `v_s = v⁺_s - v⁻_s`), as required by
`Math.LinearProgramming.Standard`'s `x ≥ 0` convention. -/
abbrev VriezeCol (G : StochasticGame Bool) (controller : Bool) : Type :=
  (G.State × G.Act (!controller)) ⊕ G.State ⊕ G.State ⊕ G.State ⊕ G.State

/-- **LP rows** for Vrieze's primal: the gain inequality and the bias
inequality at each `(state, controller-action)` pair, and the noncontroller's
per-state simplex equality `Σ_i x_s(i) = 1`, split into its two inequality
directions. -/
abbrev VriezeRow (G : StochasticGame Bool) (controller : Bool) : Type :=
  (G.State × G.Act controller) ⊕ (G.State × G.Act controller) ⊕ G.State ⊕ G.State

open Classical in
/-- The standard-form constraint matrix for Vrieze's primal. Row
`inl (s, j)` is the gain row at `(s, j)`; row `inr (inl (s, j))` is the bias
row; rows `inr (inr (inl s))`/`inr (inr (inr s))` are the two directions of
the noncontroller's simplex equality at `s`. -/
noncomputable def vriezeA (G : StochasticGame Bool) [Finite G.State] [∀ i, Finite (G.Act i)]
    [∀ i, Nonempty (G.Act i)] (controller : Bool) :
    VriezeRow G controller → VriezeCol G controller → ℝ
  | Sum.inl (_, _), Sum.inl _ => 0
  | Sum.inl (s, j), Sum.inr (Sum.inl t) => G.transProb controller s j t - (if t = s then 1 else 0)
  | Sum.inl (s, j), Sum.inr (Sum.inr (Sum.inl t)) =>
      (if t = s then 1 else 0) - G.transProb controller s j t
  | Sum.inl _, Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => 0
  | Sum.inl _, Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => 0
  | Sum.inr (Sum.inl (s, j)), Sum.inl (s', i) => if s' = s then G.rewardVal controller s i j else 0
  | Sum.inr (Sum.inl (s, _)), Sum.inr (Sum.inl t) => -(if t = s then 1 else 0)
  | Sum.inr (Sum.inl (s, _)), Sum.inr (Sum.inr (Sum.inl t)) => if t = s then 1 else 0
  | Sum.inr (Sum.inl (s, j)), Sum.inr (Sum.inr (Sum.inr (Sum.inl t))) =>
      G.transProb controller s j t - (if t = s then 1 else 0)
  | Sum.inr (Sum.inl (s, j)), Sum.inr (Sum.inr (Sum.inr (Sum.inr t))) =>
      (if t = s then 1 else 0) - G.transProb controller s j t
  | Sum.inr (Sum.inr (Sum.inl s)), Sum.inl (s', _) => if s' = s then 1 else 0
  | Sum.inr (Sum.inr (Sum.inl _)), Sum.inr _ => 0
  | Sum.inr (Sum.inr (Sum.inr s)), Sum.inl (s', _) => if s' = s then -1 else 0
  | Sum.inr (Sum.inr (Sum.inr _)), Sum.inr _ => 0

/-- The standard-form RHS: `0` on the gain/bias rows, `±1` on the two
simplex-row directions (encoding `Σ_i x_s(i) = 1`). -/
def vriezeB (G : StochasticGame Bool) (controller : Bool) : VriezeRow G controller → ℝ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr (Sum.inl _)) => 1
  | Sum.inr (Sum.inr (Sum.inr _)) => -1

/-- The standard-form objective: minimize `-Σ_s g_s = -Σ_s (g⁺_s - g⁻_s)`,
i.e. maximize `Σ_s g_s`. -/
def vriezeC (G : StochasticGame Bool) (controller : Bool) : VriezeCol G controller → ℝ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => -1
  | Sum.inr (Sum.inr (Sum.inl _)) => 1
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => 0
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => 0

/-- Convert a nonnegative weight vector summing to `1` into a `PMF`. -/
private noncomputable def weightsToPMF {α : Type*} [Fintype α] (w : α → ℝ)
    (hnn : ∀ a, 0 ≤ w a) (hsum : ∑ a, w a = 1) : PMF α :=
  PMF.ofFintype (fun a => ENNReal.ofReal (w a)) (by
    rw [← ENNReal.ofReal_one, ← hsum]
    exact (ENNReal.ofReal_sum_of_nonneg (fun i _ => hnn i)).symm)

private theorem weightsToPMF_apply_toReal {α : Type*} [Fintype α] (w : α → ℝ)
    (hnn : ∀ a, 0 ≤ w a) (hsum : ∑ a, w a = 1) (a : α) :
    ((weightsToPMF w hnn hsum) a).toReal = w a := by
  unfold weightsToPMF
  rw [PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal (hnn a)

/-- Encode a Vrieze-primal point `(x, g, v)` as a standard-form column vector:
`x_s(i)` directly, and `g, v` sign-split via `max (·) 0`/`max (-·) 0`. -/
noncomputable def vriezeEncode (G : StochasticGame Bool) [∀ i, Nonempty (G.Act i)]
    (controller : Bool) (x : G.State → PMF (G.Act (!controller))) (g v : G.State → ℝ) :
    VriezeCol G controller → ℝ
  | Sum.inl (s, i) => ((x s) i).toReal
  | Sum.inr (Sum.inl s) => max (g s) 0
  | Sum.inr (Sum.inr (Sum.inl s)) => max (-(g s)) 0
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl s))) => max (v s) 0
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr s))) => max (-(v s)) 0

/-- Recover `g` from a standard-form column vector's `g⁺, g⁻` block. -/
def vriezeDecodeG (G : StochasticGame Bool) (controller : Bool)
    (z : VriezeCol G controller → ℝ) (s : G.State) : ℝ :=
  z (Sum.inr (Sum.inl s)) - z (Sum.inr (Sum.inr (Sum.inl s)))

/-- Recover `v` from a standard-form column vector's `v⁺, v⁻` block. -/
def vriezeDecodeV (G : StochasticGame Bool) (controller : Bool)
    (z : VriezeCol G controller → ℝ) (s : G.State) : ℝ :=
  z (Sum.inr (Sum.inr (Sum.inr (Sum.inl s)))) - z (Sum.inr (Sum.inr (Sum.inr (Sum.inr s))))

/-- The raw `x`-block weight of a standard-form column vector, before it is
known to define a genuine `PMF` (nonnegative, summing to `1`). -/
def vriezeDecodeXVal (G : StochasticGame Bool) (controller : Bool)
    (z : VriezeCol G controller → ℝ) (s : G.State) (i : G.Act (!controller)) : ℝ :=
  z (Sum.inl (s, i))

open Classical in
/-- Recover the noncontroller's mixed action `x_s` from a standard-form column
vector's `x`-block, when it is a genuine probability weighting (the case
`MinPrimalFeasible` together with the simplex rows guarantees); an arbitrary
fallback `PMF` otherwise, so the function is total. -/
noncomputable def vriezeDecodeX (G : StochasticGame Bool) [Finite G.State]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)] (controller : Bool)
    (z : VriezeCol G controller → ℝ) (s : G.State) : PMF (G.Act (!controller)) :=
  if h : (∀ i, 0 ≤ G.vriezeDecodeXVal controller z s i) ∧
      (∑ i, G.vriezeDecodeXVal controller z s i = 1) then
    weightsToPMF (G.vriezeDecodeXVal controller z s) h.1 h.2
  else
    PMF.pure (Classical.arbitrary _)

theorem vriezeDecodeX_apply_toReal (G : StochasticGame Bool) [Finite G.State]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)] (controller : Bool)
    (z : VriezeCol G controller → ℝ) (s : G.State)
    (hnn : ∀ i, 0 ≤ G.vriezeDecodeXVal controller z s i)
    (hsum : ∑ i, G.vriezeDecodeXVal controller z s i = 1) (i : G.Act (!controller)) :
    ((G.vriezeDecodeX controller z s) i).toReal = G.vriezeDecodeXVal controller z s i := by
  unfold vriezeDecodeX
  rw [dif_pos ⟨hnn, hsum⟩]
  exact weightsToPMF_apply_toReal _ hnn hsum i

private theorem max_sub_max_neg (a : ℝ) : max a 0 - max (-a) 0 = a := by
  rcases le_total a 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring

theorem vriezeDecodeG_vriezeEncode (G : StochasticGame Bool) [∀ i, Nonempty (G.Act i)]
    (controller : Bool) (x : G.State → PMF (G.Act (!controller))) (g v : G.State → ℝ) :
    G.vriezeDecodeG controller (G.vriezeEncode controller x g v) = g := by
  funext s
  simp only [vriezeDecodeG, vriezeEncode]
  exact max_sub_max_neg (g s)

theorem vriezeDecodeV_vriezeEncode (G : StochasticGame Bool) [∀ i, Nonempty (G.Act i)]
    (controller : Bool) (x : G.State → PMF (G.Act (!controller))) (g v : G.State → ℝ) :
    G.vriezeDecodeV controller (G.vriezeEncode controller x g v) = v := by
  funext s
  simp only [vriezeDecodeV, vriezeEncode]
  exact max_sub_max_neg (v s)

theorem vriezeDecodeXVal_vriezeEncode (G : StochasticGame Bool) [∀ i, Nonempty (G.Act i)]
    (controller : Bool) (x : G.State → PMF (G.Act (!controller))) (g v : G.State → ℝ)
    (s : G.State) (i : G.Act (!controller)) :
    G.vriezeDecodeXVal controller (G.vriezeEncode controller x g v) s i = ((x s) i).toReal :=
  rfl

private theorem sum_vriezeCol (G : StochasticGame Bool) [Finite G.State]
    [∀ i, Finite (G.Act i)] (controller : Bool) (f : VriezeCol G controller → ℝ) :
    (∑ c, f c) =
      (∑ p : G.State × G.Act (!controller), f (Sum.inl p)) +
      (∑ s, f (Sum.inr (Sum.inl s))) +
      (∑ s, f (Sum.inr (Sum.inr (Sum.inl s)))) +
      (∑ s, f (Sum.inr (Sum.inr (Sum.inr (Sum.inl s))))) +
      (∑ s, f (Sum.inr (Sum.inr (Sum.inr (Sum.inr s))))) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  ring

private theorem sum_vriezeRow (G : StochasticGame Bool) [Finite G.State]
    [∀ i, Finite (G.Act i)] (controller : Bool) (f : VriezeRow G controller → ℝ) :
    (∑ r, f r) =
      (∑ p : G.State × G.Act controller, f (Sum.inl p)) +
      (∑ p : G.State × G.Act controller, f (Sum.inr (Sum.inl p))) +
      (∑ s, f (Sum.inr (Sum.inr (Sum.inl s)))) +
      (∑ s, f (Sum.inr (Sum.inr (Sum.inr s)))) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  ring

private theorem sum_coeff_mul_max_sub {ι : Type*} [Fintype ι] (A f : ι → ℝ) :
    (∑ t, A t * max (f t) 0) - (∑ t, A t * max (-(f t)) 0) = ∑ t, A t * f t := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun t _ => by rw [← mul_sub, max_sub_max_neg]

open Classical in
theorem rowEval_vriezeA_vriezeEncode_gain (G : StochasticGame Bool) [Finite G.State]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)] (controller : Bool)
    (x : G.State → PMF (G.Act (!controller))) (g v : G.State → ℝ) (s : G.State)
    (j : G.Act controller) :
    Math.LinearProgramming.rowEval (G.vriezeA controller) (G.vriezeEncode controller x g v)
        (Sum.inl (s, j)) =
      (∑ t, G.transProb controller s j t * g t) - g s := by
  change (∑ c, G.vriezeA controller (Sum.inl (s, j)) c * G.vriezeEncode controller x g v c) = _
  rw [sum_vriezeCol]
  simp only [vriezeA, vriezeEncode, zero_mul, Finset.sum_const_zero]
  simp only [zero_add, add_zero]
  have hneg : (∑ x, ((if x = s then (1:ℝ) else 0) - G.transProb controller s j x) * max (-(g x)) 0)
      = -(∑ x, (G.transProb controller s j x - (if x = s then (1:ℝ) else 0)) * max (-(g x)) 0) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [hneg, ← sub_eq_add_neg, sum_coeff_mul_max_sub]
  simp only [sub_mul]
  rw [Finset.sum_sub_distrib]
  have hite : (∑ x : G.State, (if x = s then (1:ℝ) else 0) * g x) = g s := by simp
  rw [hite]

open Classical in
private theorem sum_prod_ite_eq (G : StochasticGame Bool) [Finite G.State]
    {β : Type*} [Fintype β] (s : G.State) (f : G.State → β → ℝ) :
    (∑ p : G.State × β, (if p.1 = s then f p.1 p.2 else 0)) = ∑ i : β, f s i := by
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single s]
  · simp
  · intro s' _ hne
    simp [hne]
  · simp

open Classical in
theorem rowEval_vriezeA_vriezeEncode_bias (G : StochasticGame Bool) [Finite G.State]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)] (controller : Bool)
    (x : G.State → PMF (G.Act (!controller))) (g v : G.State → ℝ) (s : G.State)
    (j : G.Act controller) :
    Math.LinearProgramming.rowEval (G.vriezeA controller) (G.vriezeEncode controller x g v)
        (Sum.inr (Sum.inl (s, j))) =
      (∑ i, ((x s) i).toReal * G.rewardVal controller s i j) +
        (∑ t, G.transProb controller s j t * v t) - g s - v s := by
  change (∑ c, G.vriezeA controller (Sum.inr (Sum.inl (s, j))) c *
      G.vriezeEncode controller x g v c) = _
  rw [sum_vriezeCol]
  simp only [vriezeA, vriezeEncode]
  have e1 : (∑ p : G.State × G.Act (!controller),
      (if p.1 = s then G.rewardVal controller s p.2 j else 0) * ((x p.1) p.2).toReal) =
      ∑ i, ((x s) i).toReal * G.rewardVal controller s i j := by
    have step : (∑ p : G.State × G.Act (!controller),
        (if p.1 = s then G.rewardVal controller s p.2 j else 0) * ((x p.1) p.2).toReal) =
        ∑ p : G.State × G.Act (!controller),
          (if p.1 = s then G.rewardVal controller s p.2 j * ((x p.1) p.2).toReal else 0) := by
      refine Finset.sum_congr rfl ?_
      rintro ⟨s', i⟩ _
      by_cases h : s' = s <;> simp [h]
    rw [step, sum_prod_ite_eq G s (fun p i => G.rewardVal controller s i j * ((x p) i).toReal)]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e23 : (∑ x, (-(if x = s then (1:ℝ) else 0)) * max (g x) 0) +
      (∑ x, (if x = s then (1:ℝ) else 0) * max (-(g x)) 0) = -g s := by
    have hneg : (∑ x, (if x = s then (1:ℝ) else 0) * max (-(g x)) 0)
        = -(∑ x, (-(if x = s then (1:ℝ) else 0)) * max (-(g x)) 0) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun t _ => by ring
    rw [hneg, ← sub_eq_add_neg, sum_coeff_mul_max_sub]
    have hcollapse : (∑ x : G.State, (-(if x = s then (1:ℝ) else 0)) * g x) = -(g s) := by
      simp [neg_mul, Finset.sum_neg_distrib]
    exact hcollapse
  have e45 : (∑ x, (G.transProb controller s j x - (if x = s then (1:ℝ) else 0)) * max (v x) 0) +
      (∑ x, ((if x = s then (1:ℝ) else 0) - G.transProb controller s j x) * max (-(v x)) 0) =
      (∑ t, G.transProb controller s j t * v t) - v s := by
    have hneg : (∑ x, ((if x = s then (1:ℝ) else 0) - G.transProb controller s j x) *
        max (-(v x)) 0) =
        -(∑ x, (G.transProb controller s j x - (if x = s then (1:ℝ) else 0)) * max (-(v x)) 0) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun t _ => by ring
    rw [hneg, ← sub_eq_add_neg, sum_coeff_mul_max_sub]
    rw [show (∑ x, (G.transProb controller s j x - (if x = s then (1:ℝ) else 0)) * v x)
        = (∑ x, G.transProb controller s j x * v x) - (∑ x, (if x = s then (1:ℝ) else 0) * v x)
        from by rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun t _ => by ring]
    have hv : (∑ x : G.State, (if x = s then (1:ℝ) else 0) * v x) = v s := by simp
    rw [hv]
  rw [e1]
  linarith [e23, e45]

-- ============================================================================
-- Duality extraction: strong duality applied to the Vrieze embedding
-- ============================================================================

/-!
### From primal optimality to a dual-feasible point

This section closes obligation 1 of the module docstring's residual: it
embeds `IsVriezePrimalOptimal` into `Math.LinearProgramming.Standard`'s
`MinPrimalFeasible`, invokes `Math.LinearProgramming.StrongDuality.
lp_strong_duality`, and decodes the resulting dual-feasible point into the
two named dual flows `IsVriezeDualFeasible` exports: `z` (dual to the bias
rows — Vrieze's occupation measure) and `yGain` (dual to the gain rows).
There is no third dual object: the abstract row-indexed vector
`Math.LinearProgramming.MaxDualFeasible` produces is a technical artifact of
the `VriezeRow` embedding (it also carries the two split directions of the
noncontroller's simplex-equality dual, which is a genuine third *quantity*
— the per-state Lagrange multiplier for `Σ_i x_s(i) = 1` — but not a fourth
row/column family, and not consumed by anything below), decoded here into
exactly the two named flows the module docstring's "LP-duality inventory"
promises. -/

private theorem sum_coeff_mul_sub {ι : Type*} [Fintype ι] (A f h : ι → ℝ) :
    (∑ t, A t * f t) - (∑ t, A t * h t) = ∑ t, A t * (f t - h t) := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun t _ => (mul_sub _ _ _).symm

open Classical in
/-- **General gain-row evaluation**, for an *arbitrary* standard-form column
vector `z` (not necessarily of `vriezeEncode` shape), expressed via the
decoded gain `vriezeDecodeG`. The algebra is simpler than
`rowEval_vriezeA_vriezeEncode_gain`'s encode-specific version: no
`max(·,0)`-splitting is needed, since `vriezeDecodeG` reads the `g⁺`/`g⁻`
difference directly off `z`. -/
theorem rowEval_vriezeA_gain (G : StochasticGame Bool) [Finite G.State]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)] (controller : Bool)
    (z : VriezeCol G controller → ℝ) (s : G.State) (j : G.Act controller) :
    Math.LinearProgramming.rowEval (G.vriezeA controller) z (Sum.inl (s, j)) =
      (∑ t, G.transProb controller s j t * G.vriezeDecodeG controller z t) -
        G.vriezeDecodeG controller z s := by
  change (∑ c, G.vriezeA controller (Sum.inl (s, j)) c * z c) = _
  rw [sum_vriezeCol]
  simp only [vriezeA, zero_mul, Finset.sum_const_zero, zero_add, add_zero]
  have hneg : (∑ x, ((if x = s then (1:ℝ) else 0) - G.transProb controller s j x) *
      z (Sum.inr (Sum.inr (Sum.inl x))))
      = -(∑ x, (G.transProb controller s j x - (if x = s then (1:ℝ) else 0)) *
        z (Sum.inr (Sum.inr (Sum.inl x)))) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [hneg, ← sub_eq_add_neg,
    sum_coeff_mul_sub (fun x => G.transProb controller s j x - (if x = s then (1:ℝ) else 0))
      (fun x => z (Sum.inr (Sum.inl x))) (fun x => z (Sum.inr (Sum.inr (Sum.inl x))))]
  simp only [sub_mul]
  rw [Finset.sum_sub_distrib]
  have hite : (∑ x : G.State, (if x = s then (1:ℝ) else 0) *
      (z (Sum.inr (Sum.inl x)) - z (Sum.inr (Sum.inr (Sum.inl x))))) =
      z (Sum.inr (Sum.inl s)) - z (Sum.inr (Sum.inr (Sum.inl s))) := by simp
  simp only [vriezeDecodeG]
  rw [show (∑ x : G.State, G.transProb controller s j x *
      (z (Sum.inr (Sum.inl x)) - z (Sum.inr (Sum.inr (Sum.inl x)))))
      = ∑ x : G.State, G.transProb controller s j x *
        (z (Sum.inr (Sum.inl x)) - z (Sum.inr (Sum.inr (Sum.inl x)))) from rfl,
    hite]

open Classical in
/-- **General bias-row evaluation**, the arbitrary-`z` analogue of
`rowEval_vriezeA_vriezeEncode_bias`. -/
theorem rowEval_vriezeA_bias (G : StochasticGame Bool) [Finite G.State]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)] (controller : Bool)
    (z : VriezeCol G controller → ℝ) (s : G.State) (j : G.Act controller) :
    Math.LinearProgramming.rowEval (G.vriezeA controller) z (Sum.inr (Sum.inl (s, j))) =
      (∑ i, G.vriezeDecodeXVal controller z s i * G.rewardVal controller s i j) +
        (∑ t, G.transProb controller s j t * G.vriezeDecodeV controller z t) -
        G.vriezeDecodeG controller z s - G.vriezeDecodeV controller z s := by
  change (∑ c, G.vriezeA controller (Sum.inr (Sum.inl (s, j))) c * z c) = _
  rw [sum_vriezeCol]
  simp only [vriezeA]
  have e1 : (∑ p : G.State × G.Act (!controller),
      (if p.1 = s then G.rewardVal controller s p.2 j else 0) * z (Sum.inl p)) =
      ∑ i, G.vriezeDecodeXVal controller z s i * G.rewardVal controller s i j := by
    have step : (∑ p : G.State × G.Act (!controller),
        (if p.1 = s then G.rewardVal controller s p.2 j else 0) * z (Sum.inl p)) =
        ∑ p : G.State × G.Act (!controller),
          (if p.1 = s then G.rewardVal controller s p.2 j * z (Sum.inl p) else 0) := by
      refine Finset.sum_congr rfl ?_
      rintro ⟨s', i⟩ _
      by_cases h : s' = s <;> simp [h]
    rw [step, sum_prod_ite_eq G s
      (fun p i => G.rewardVal controller s i j * z (Sum.inl (p, i)))]
    exact Finset.sum_congr rfl fun i _ => by
      rw [vriezeDecodeXVal]; ring
  have e23 : (∑ x, (-(if x = s then (1:ℝ) else 0)) * z (Sum.inr (Sum.inl x))) +
      (∑ x, (if x = s then (1:ℝ) else 0) * z (Sum.inr (Sum.inr (Sum.inl x)))) =
      -(G.vriezeDecodeG controller z s) := by
    have hcollapse1 : (∑ x : G.State, (-(if x = s then (1:ℝ) else 0)) *
        z (Sum.inr (Sum.inl x))) = -(z (Sum.inr (Sum.inl s))) := by
      simp [neg_mul, Finset.sum_neg_distrib]
    have hcollapse2 : (∑ x : G.State, (if x = s then (1:ℝ) else 0) *
        z (Sum.inr (Sum.inr (Sum.inl x)))) = z (Sum.inr (Sum.inr (Sum.inl s))) := by simp
    rw [hcollapse1, hcollapse2, vriezeDecodeG]; ring
  have e45 : (∑ x, (G.transProb controller s j x - (if x = s then (1:ℝ) else 0)) *
      z (Sum.inr (Sum.inr (Sum.inr (Sum.inl x))))) +
      (∑ x, ((if x = s then (1:ℝ) else 0) - G.transProb controller s j x) *
        z (Sum.inr (Sum.inr (Sum.inr (Sum.inr x))))) =
      (∑ t, G.transProb controller s j t * G.vriezeDecodeV controller z t) -
        G.vriezeDecodeV controller z s := by
    have hneg : (∑ x, ((if x = s then (1:ℝ) else 0) - G.transProb controller s j x) *
        z (Sum.inr (Sum.inr (Sum.inr (Sum.inr x))))) =
        -(∑ x, (G.transProb controller s j x - (if x = s then (1:ℝ) else 0)) *
          z (Sum.inr (Sum.inr (Sum.inr (Sum.inr x))))) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun t _ => by ring
    rw [hneg, ← sub_eq_add_neg,
      sum_coeff_mul_sub (fun x => G.transProb controller s j x - (if x = s then (1:ℝ) else 0))
        (fun x => z (Sum.inr (Sum.inr (Sum.inr (Sum.inl x)))))
        (fun x => z (Sum.inr (Sum.inr (Sum.inr (Sum.inr x)))))]
    simp only [sub_mul]
    rw [Finset.sum_sub_distrib]
    have hite : (∑ x : G.State, (if x = s then (1:ℝ) else 0) *
        (z (Sum.inr (Sum.inr (Sum.inr (Sum.inl x)))) -
          z (Sum.inr (Sum.inr (Sum.inr (Sum.inr x)))))) =
        z (Sum.inr (Sum.inr (Sum.inr (Sum.inl s)))) -
          z (Sum.inr (Sum.inr (Sum.inr (Sum.inr s)))) := by simp
    rw [hite]
    simp only [vriezeDecodeV]
  rw [e1]
  linarith [e23, e45]

open Classical in
/-- **General simplex-row evaluations**, both directions: the noncontroller's
raw column weight at `s` summed over its own actions, and its negation. -/
theorem rowEval_vriezeA_simplex (G : StochasticGame Bool) [Finite G.State]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)] (controller : Bool)
    (z : VriezeCol G controller → ℝ) (s : G.State) :
    Math.LinearProgramming.rowEval (G.vriezeA controller) z
        (Sum.inr (Sum.inr (Sum.inl s))) = ∑ i, G.vriezeDecodeXVal controller z s i ∧
    Math.LinearProgramming.rowEval (G.vriezeA controller) z
        (Sum.inr (Sum.inr (Sum.inr s))) = -(∑ i, G.vriezeDecodeXVal controller z s i) := by
  constructor
  · change (∑ c, G.vriezeA controller (Sum.inr (Sum.inr (Sum.inl s))) c * z c) = _
    rw [sum_vriezeCol]
    simp only [vriezeA, zero_mul, Finset.sum_const_zero, add_zero]
    rw [show (∑ p : G.State × G.Act (!controller),
        (if p.1 = s then (1:ℝ) else 0) * z (Sum.inl p)) =
        ∑ p : G.State × G.Act (!controller), (if p.1 = s then z (Sum.inl p) else 0) from
      Finset.sum_congr rfl fun p _ => by by_cases h : p.1 = s <;> simp [h]]
    rw [sum_prod_ite_eq G s (fun p i => z (Sum.inl (p, i)))]
    rfl
  · change (∑ c, G.vriezeA controller (Sum.inr (Sum.inr (Sum.inr s))) c * z c) = _
    rw [sum_vriezeCol]
    simp only [vriezeA, zero_mul, Finset.sum_const_zero, add_zero]
    rw [show (∑ p : G.State × G.Act (!controller),
        (if p.1 = s then (-1:ℝ) else 0) * z (Sum.inl p)) =
        -(∑ p : G.State × G.Act (!controller), (if p.1 = s then z (Sum.inl p) else 0)) from by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun p _ => by by_cases h : p.1 = s <;> simp [h]]
    rw [sum_prod_ite_eq G s (fun p i => z (Sum.inl (p, i)))]
    rfl

/-!
### The primal embedding, both directions

`vriezeGainRow_of_isVriezePrimalFeasible`/`vriezeBiasRow_of_isVriezePrimalFeasible`
collapse `IsVriezePrimalFeasible`'s two `∀ b : G.JointAct`-quantified clauses
down to the single-`j` form the embedded LP's rows are indexed by, using
`IsSingleController` to discharge the collapse
`transition_jointOf_eq_of_single_controller` needs. Combined with the
already-proved `rowEval_vriezeA_vriezeEncode_gain`/`_bias` and the PMF-sums-
to-one fact, they give `minPrimalFeasible_vriezeEncode_of_isVriezePrimalFeasible`
— the encode direction. The reverse, `isVriezePrimalFeasible_of_minPrimalFeasible`,
runs the same collapse outward from the *general* `rowEval_vriezeA_gain`/`_bias`/
`_simplex` computed above, decoding an arbitrary standard-form feasible point
back into a genuine `IsVriezePrimalFeasible` witness. -/

private theorem vriezeGainRow_of_isVriezePrimalFeasible
    {controller : Bool} (hSC : G.IsSingleController controller)
    {x : G.State → PMF (G.Act (!controller))} {g v : G.State → ℝ}
    (hfeas : G.IsVriezePrimalFeasible controller x g v) (s : G.State) (j : G.Act controller) :
    g s ≤ ∑ t, G.transProb controller s j t * g t := by
  have h := hfeas.1 s (G.jointOfControllerAct controller j)
  have hconst : (fun i : G.Act (!controller) =>
      expect (G.transition s (Function.update (G.jointOfControllerAct controller j)
        (!controller) i)) g)
      = fun _ : G.Act (!controller) =>
        expect (G.transition s (G.jointOfControllerAct controller j)) g := by
    funext i
    exact congrArg (expect · g) (G.transition_jointOf_eq_of_single_controller hSC s j i)
  rw [hconst, expect_const, expect_eq_sum] at h
  simpa [transProb] using h

private theorem vriezeBiasRow_of_isVriezePrimalFeasible
    {controller : Bool} (hSC : G.IsSingleController controller)
    {x : G.State → PMF (G.Act (!controller))} {g v : G.State → ℝ}
    (hfeas : G.IsVriezePrimalFeasible controller x g v) (s : G.State) (j : G.Act controller) :
    g s + v s ≤ (∑ i, ((x s) i).toReal * G.rewardVal controller s i j) +
      ∑ t, G.transProb controller s j t * v t := by
  have h := hfeas.2 s (G.jointOfControllerAct controller j)
  have hconst : (fun i : G.Act (!controller) =>
      G.stagePayoff s (Function.update (G.jointOfControllerAct controller j) (!controller) i)
          (!controller) +
        expect (G.transition s (Function.update (G.jointOfControllerAct controller j)
          (!controller) i)) v)
      = fun i : G.Act (!controller) =>
        G.rewardVal controller s i j +
          expect (G.transition s (G.jointOfControllerAct controller j)) v := by
    funext i
    change G.stagePayoff s (G.jointOf controller j i) (!controller) +
        expect (G.transition s (G.jointOf controller j i)) v
      = G.rewardVal controller s i j +
        expect (G.transition s (G.jointOfControllerAct controller j)) v
    rw [G.transition_jointOf_eq_of_single_controller hSC s j i]
    rfl
  rw [hconst, expect_add, expect_const] at h
  simp only [expect_eq_sum] at h
  simpa [transProb] using h

private theorem sum_pmf_toReal_eq_one {α : Type*} [Fintype α] (p : PMF α) :
    (∑ a, (p a).toReal) = 1 := by
  have h : expect p (fun _ => (1:ℝ)) = ∑ a, (p a).toReal * 1 := expect_eq_sum p (fun _ => 1)
  rw [expect_const] at h
  simpa using h.symm

theorem minPrimalFeasible_vriezeEncode_of_isVriezePrimalFeasible
    {controller : Bool} (hSC : G.IsSingleController controller)
    {x : G.State → PMF (G.Act (!controller))} {g v : G.State → ℝ}
    (hfeas : G.IsVriezePrimalFeasible controller x g v) :
    Math.LinearProgramming.MinPrimalFeasible (G.vriezeA controller) (G.vriezeB controller)
      (G.vriezeEncode controller x g v) := by
  refine ⟨?_, ?_⟩
  · rintro (⟨s, i⟩ | s | s | s | s) <;> simp [vriezeEncode, ENNReal.toReal_nonneg]
  · rintro (⟨s, j⟩ | ⟨s, j⟩ | s | s)
    · rw [rowEval_vriezeA_vriezeEncode_gain]
      have := G.vriezeGainRow_of_isVriezePrimalFeasible hSC hfeas s j
      change (0:ℝ) ≤ _
      linarith
    · rw [rowEval_vriezeA_vriezeEncode_bias]
      have := G.vriezeBiasRow_of_isVriezePrimalFeasible hSC hfeas s j
      change (0:ℝ) ≤ _
      linarith
    · change (1:ℝ) ≤ Math.LinearProgramming.rowEval (G.vriezeA controller)
        (G.vriezeEncode controller x g v) (Sum.inr (Sum.inr (Sum.inl s)))
      rw [(G.rowEval_vriezeA_simplex controller (G.vriezeEncode controller x g v) s).1]
      simp only [vriezeDecodeXVal, vriezeEncode]
      exact le_of_eq (sum_pmf_toReal_eq_one (x s)).symm
    · change (-1:ℝ) ≤ Math.LinearProgramming.rowEval (G.vriezeA controller)
        (G.vriezeEncode controller x g v) (Sum.inr (Sum.inr (Sum.inr s)))
      rw [(G.rowEval_vriezeA_simplex controller (G.vriezeEncode controller x g v) s).2]
      simp only [vriezeDecodeXVal, vriezeEncode]
      rw [sum_pmf_toReal_eq_one (x s)]

/-- The two simplex-row directions sandwich `vriezeDecodeXVal` into a genuine
probability weighting: nonnegative (from `Nonnegative z`) and summing to `1`
(from the two opposite-signed `≥` bounds forcing equality). -/
private theorem vriezeDecodeXVal_isProb_of_minPrimalFeasible
    {controller : Bool} {z : VriezeCol G controller → ℝ}
    (hmin : Math.LinearProgramming.MinPrimalFeasible (G.vriezeA controller)
      (G.vriezeB controller) z) (s : G.State) :
    (∀ i, 0 ≤ G.vriezeDecodeXVal controller z s i) ∧
      (∑ i, G.vriezeDecodeXVal controller z s i) = 1 := by
  refine ⟨fun i => hmin.1 (Sum.inl (s, i)), ?_⟩
  have hpos := hmin.2 (Sum.inr (Sum.inr (Sum.inl s)))
  have hneg := hmin.2 (Sum.inr (Sum.inr (Sum.inr s)))
  rw [(G.rowEval_vriezeA_simplex controller z s).1] at hpos
  rw [(G.rowEval_vriezeA_simplex controller z s).2] at hneg
  simp only [vriezeB] at hpos hneg
  linarith

open Classical in
/-- **The decode direction.** An arbitrary standard-form feasible point of the
Vrieze embedding decodes to a genuine `IsVriezePrimalFeasible` witness — the
converse of `minPrimalFeasible_vriezeEncode_of_isVriezePrimalFeasible`, and
the half of the equivalence `exists_vriezeMaxDualFeasible_of_vriezePrimalOptimal`
below needs to turn `IsVriezePrimalOptimal`'s domination over
`IsVriezePrimalFeasible` points into domination over *every* standard-form
feasible column vector, as `lp_strong_duality`'s `hopt` hypothesis requires. -/
theorem isVriezePrimalFeasible_of_minPrimalFeasible
    {controller : Bool} (hSC : G.IsSingleController controller)
    {z : VriezeCol G controller → ℝ}
    (hmin : Math.LinearProgramming.MinPrimalFeasible (G.vriezeA controller)
      (G.vriezeB controller) z) :
    G.IsVriezePrimalFeasible controller (G.vriezeDecodeX controller z)
      (G.vriezeDecodeG controller z) (G.vriezeDecodeV controller z) := by
  have hnn : ∀ s, ∀ i, 0 ≤ G.vriezeDecodeXVal controller z s i :=
    fun s => (G.vriezeDecodeXVal_isProb_of_minPrimalFeasible hmin s).1
  have hsum : ∀ s, (∑ i, G.vriezeDecodeXVal controller z s i) = 1 :=
    fun s => (G.vriezeDecodeXVal_isProb_of_minPrimalFeasible hmin s).2
  have hxeq : ∀ s i, ((G.vriezeDecodeX controller z s) i).toReal =
      G.vriezeDecodeXVal controller z s i := fun s =>
    G.vriezeDecodeX_apply_toReal controller z s (hnn s) (hsum s)
  constructor
  · intro s b
    have hrow := hmin.2 (Sum.inl (s, b controller))
    rw [G.rowEval_vriezeA_gain] at hrow
    simp only [vriezeB] at hrow
    have hgain : G.vriezeDecodeG controller z s ≤
        ∑ t, G.transProb controller s (b controller) t * G.vriezeDecodeG controller z t := by
      linarith
    have hcollapse : ∀ i, G.transition s (Function.update b (!controller) i) =
        G.transition s (G.jointOfControllerAct controller (b controller)) := by
      intro i
      rw [G.update_not_eq_jointOf controller b i,
        G.transition_jointOf_eq_of_single_controller hSC s (b controller) i]
    have hexpect : (expect (G.vriezeDecodeX controller z s) fun i =>
        expect (G.transition s (Function.update b (!controller) i))
          (G.vriezeDecodeG controller z)) =
        ∑ t, G.transProb controller s (b controller) t * G.vriezeDecodeG controller z t := by
      rw [show (fun i => expect (G.transition s (Function.update b (!controller) i))
            (G.vriezeDecodeG controller z))
          = fun _ : G.Act (!controller) => expect
            (G.transition s (G.jointOfControllerAct controller (b controller)))
            (G.vriezeDecodeG controller z) from funext fun i => congrArg
            (expect · (G.vriezeDecodeG controller z)) (hcollapse i),
        expect_const, expect_eq_sum]
      rfl
    rw [hexpect]
    exact hgain
  · intro s b
    have hrow := hmin.2 (Sum.inr (Sum.inl (s, b controller)))
    rw [G.rowEval_vriezeA_bias] at hrow
    simp only [vriezeB] at hrow
    have hbias : G.vriezeDecodeG controller z s + G.vriezeDecodeV controller z s ≤
        (∑ i, G.vriezeDecodeXVal controller z s i *
          G.rewardVal controller s i (b controller)) +
        ∑ t, G.transProb controller s (b controller) t * G.vriezeDecodeV controller z t := by
      linarith
    have hcollapse : ∀ i : G.Act (!controller),
        G.stagePayoff s (Function.update b (!controller) i) (!controller) +
          expect (G.transition s (Function.update b (!controller) i))
            (G.vriezeDecodeV controller z) =
        G.rewardVal controller s i (b controller) +
          expect (G.transition s (G.jointOfControllerAct controller (b controller)))
            (G.vriezeDecodeV controller z) := by
      intro i
      rw [G.update_not_eq_jointOf controller b i]
      rw [G.transition_jointOf_eq_of_single_controller hSC s (b controller) i]
      rfl
    have hexpect : (expect (G.vriezeDecodeX controller z s) fun i =>
        G.stagePayoff s (Function.update b (!controller) i) (!controller) +
          expect (G.transition s (Function.update b (!controller) i))
            (G.vriezeDecodeV controller z)) =
        (∑ i, G.vriezeDecodeXVal controller z s i *
          G.rewardVal controller s i (b controller)) +
        ∑ t, G.transProb controller s (b controller) t * G.vriezeDecodeV controller z t := by
      rw [show (fun i => G.stagePayoff s (Function.update b (!controller) i) (!controller) +
              expect (G.transition s (Function.update b (!controller) i))
                (G.vriezeDecodeV controller z))
          = fun i => G.rewardVal controller s i (b controller) +
              expect (G.transition s (G.jointOfControllerAct controller (b controller)))
                (G.vriezeDecodeV controller z) from funext hcollapse,
        expect_add, expect_const]
      simp only [expect_eq_sum, hxeq, transProb]
    rw [hexpect]
    exact hbias

/-- **The objective identity.** `minPrimalValue (vriezeC controller)` reads
off `-Σ_s g_s` from *any* standard-form column vector, encoded or not — a
pure algebraic consequence of `vriezeC`'s definition, with no feasibility
hypothesis needed. -/
theorem minPrimalValue_vriezeC_eq (G : StochasticGame Bool) [Finite G.State]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)] (controller : Bool)
    (z : VriezeCol G controller → ℝ) :
    Math.LinearProgramming.minPrimalValue (G.vriezeC controller) z =
      -(∑ s, G.vriezeDecodeG controller z s) := by
  change Math.LinearProgramming.dot (G.vriezeC controller) z = _
  unfold Math.LinearProgramming.dot
  rw [sum_vriezeCol]
  simp only [vriezeC, zero_mul, Finset.sum_const_zero, zero_add, add_zero, neg_one_mul, one_mul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun t _ => by rw [vriezeDecodeG]; ring

/-!
### Strong duality: the dual-feasible point, and its two named flows

`exists_vriezeMaxDualFeasible_of_vriezePrimalOptimal` is the payoff of the
embedding above: from `IsVriezePrimalOptimal` (primal feasibility *plus*
`Σ g_s`-optimality) and `IsSingleController`, it produces a dual-feasible
point of the embedded LP with the same objective value, via
`Math.LinearProgramming.lp_strong_duality`. `vriezeDualZ`/`vriezeDualYGain`
read off the two dual flows the module docstring names — `z` (dual to the
bias rows, Vrieze's occupation measure) and `yGain` (dual to the gain rows)
— from that single row-indexed witness; there is no third dual flow, only
the two remaining `VriezeRow` summands (the noncontroller's split simplex-
equality dual), which are not given names here because
`exists_completedPolicy_of_vriezeDualFeasible` below never needs them. -/

theorem exists_vriezeMaxDualFeasible_of_vriezePrimalOptimal
    {controller : Bool} (hSC : G.IsSingleController controller)
    {x : G.State → PMF (G.Act (!controller))} {g v : G.State → ℝ}
    (hopt : G.IsVriezePrimalOptimal controller x g v) :
    ∃ w : VriezeRow G controller → ℝ,
      Math.LinearProgramming.MaxDualFeasible (G.vriezeA controller) (G.vriezeC controller) w ∧
      Math.LinearProgramming.maxDualValue (G.vriezeB controller) w = -(∑ s, g s) := by
  have hx := G.minPrimalFeasible_vriezeEncode_of_isVriezePrimalFeasible hSC hopt.feasible
  have hoptLP : ∀ z, Math.LinearProgramming.MinPrimalFeasible (G.vriezeA controller)
      (G.vriezeB controller) z →
      Math.LinearProgramming.minPrimalValue (G.vriezeC controller)
        (G.vriezeEncode controller x g v) ≤
        Math.LinearProgramming.minPrimalValue (G.vriezeC controller) z := by
    intro z hz
    rw [G.minPrimalValue_vriezeC_eq, G.minPrimalValue_vriezeC_eq, G.vriezeDecodeG_vriezeEncode]
    have hdec := G.isVriezePrimalFeasible_of_minPrimalFeasible hSC hz
    have hle := hopt.optimal (G.vriezeDecodeX controller z) (G.vriezeDecodeG controller z)
      (G.vriezeDecodeV controller z) hdec
    linarith
  obtain ⟨w, hw, heq⟩ :=
    Math.LinearProgramming.lp_strong_duality (A := G.vriezeA controller)
      (b := G.vriezeB controller) (c := G.vriezeC controller) hx hoptLP
  refine ⟨w, hw, ?_⟩
  rw [heq, G.minPrimalValue_vriezeC_eq, G.vriezeDecodeG_vriezeEncode]

/-- **Vrieze's occupation measure** — the dual flow `z` (dual to the bias
rows), read off the abstract dual witness `w`. -/
def vriezeDualZ (G : StochasticGame Bool) (controller : Bool)
    (w : VriezeRow G controller → ℝ) (s : G.State) (j : G.Act controller) : ℝ :=
  w (Sum.inr (Sum.inl (s, j)))

/-- **Vrieze's gain-row dual flow** `yGain` (dual to the gain rows), read off
the abstract dual witness `w`. -/
def vriezeDualYGain (G : StochasticGame Bool) (controller : Bool)
    (w : VriezeRow G controller → ℝ) (s : G.State) (j : G.Act controller) : ℝ :=
  w (Sum.inl (s, j))

/-- **Vrieze dual feasibility.** The nonnegativity of the two named dual
flows `z`/`yGain`, exported from `MaxDualFeasible (vriezeA controller)
(vriezeC controller) w` for the abstract row-indexed witness `w` strong
duality produces. This is deliberately a *fragment* of full dual
feasibility: `exists_completedPolicy_of_vriezeDualFeasible` below only ever
needs `z`'s sign, not the per-column dual inequalities `MaxDualFeasible.2`
also carries (decoding those into named closed forms, mirroring
`rowEval_vriezeA_gain`/`_bias`/`_simplex` for `colEval`, is the natural next
increment but is not needed downstream of this file yet). -/
structure IsVriezeDualFeasible (G : StochasticGame Bool) [Finite G.State]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)] (controller : Bool)
    (z yGain : G.State → G.Act controller → ℝ) : Prop where
  z_nonneg : ∀ s j, 0 ≤ z s j
  yGain_nonneg : ∀ s j, 0 ≤ yGain s j

theorem isVriezeDualFeasible_vriezeDualZ_vriezeDualYGain
    {controller : Bool} {w : VriezeRow G controller → ℝ}
    (hw : Math.LinearProgramming.MaxDualFeasible (G.vriezeA controller)
      (G.vriezeC controller) w) :
    G.IsVriezeDualFeasible controller (G.vriezeDualZ controller w)
      (G.vriezeDualYGain controller w) :=
  ⟨fun _ _ => hw.1 _, fun _ _ => hw.1 _⟩

/-- Assembling `exists_vriezeMaxDualFeasible_of_vriezePrimalOptimal` and
`isVriezeDualFeasible_vriezeDualZ_vriezeDualYGain`: from an
`IsVriezePrimalOptimal` point, the two named dual flows `z`/`yGain` exist
and are dual-feasible. -/
theorem exists_vriezeDualFeasible_of_vriezePrimalOptimal
    {controller : Bool} (hSC : G.IsSingleController controller)
    {x : G.State → PMF (G.Act (!controller))} {g v : G.State → ℝ}
    (hopt : G.IsVriezePrimalOptimal controller x g v) :
    ∃ z yGain : G.State → G.Act controller → ℝ, G.IsVriezeDualFeasible controller z yGain := by
  obtain ⟨w, hw, -⟩ := G.exists_vriezeMaxDualFeasible_of_vriezePrimalOptimal hSC hopt
  exact ⟨_, _, G.isVriezeDualFeasible_vriezeDualZ_vriezeDualYGain hw⟩

/-- **The LP-optimal occupation support**, `R := {s | 0 < Σ_j z_s(j)}`, for a
dual flow `z` — the target set the module docstring's `FiniteReachability`
obstruction is instantiated against. -/
def vriezeOccupationSupport (G : StochasticGame Bool) [Finite G.State]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)] (controller : Bool)
    (z : G.State → G.Act controller → ℝ) (s : G.State) : Prop :=
  0 < ∑ j, z s j

/-- **Obligations (i)+(iii) of the residual, made concrete.** Given
`IsVriezeDualFeasible`'s occupation measure `z` and the hypothesis that
every state outside its support `R` can reach `R` along `controllerSucc`
(obligation (ii) — genuinely open, needing the LP's *optimality* via a
policy-improvement argument ruling out an LP-beating trap; taken here as an
explicit hypothesis, exactly the honest name for what is *not* proved),
a *total* controller policy `τ` exists that: agrees with the `z`-normalized
mixture on `R`, and off `R` plays a pure action making one step of
`FiniteReachability` progress toward `R`. This discharges totality
(obligation (i)) completely and supplies the one-step "make progress toward
`R`" fact obligation (iii) needs to iterate into an actual transience
statement (not attempted here — see the module docstring). -/
theorem exists_completedPolicy_of_vriezeDualFeasible
    {controller : Bool} {z yGain : G.State → G.Act controller → ℝ}
    (hdual : G.IsVriezeDualFeasible controller z yGain)
    (hnotrap : ∀ s, ¬ G.vriezeOccupationSupport controller z s →
      FiniteReachability.CanReachSet (G.controllerSucc controller)
        (G.vriezeOccupationSupport controller z) s) :
    ∃ τ : G.State → PMF (G.Act controller),
      (∀ s (_ : G.vriezeOccupationSupport controller z s) (j : G.Act controller),
        ((τ s) j).toReal = z s j / (∑ j', z s j')) ∧
      (∀ s (_ : ¬ G.vriezeOccupationSupport controller z s),
        ∃ t, t ∈ (G.controllerKernel controller τ s).support ∧
          (G.vriezeOccupationSupport controller z t ∨
            FiniteReachability.CanReachSet (G.controllerSucc controller)
              (G.vriezeOccupationSupport controller z) t)) := by
  classical
  have hprogress : ∀ s, ¬ G.vriezeOccupationSupport controller z s → ∃ j : G.Act controller,
      ∃ t, t ∈ (G.controllerKernel controller (fun _ => PMF.pure j) s).support ∧
        (G.vriezeOccupationSupport controller z t ∨
          FiniteReachability.CanReachSet (G.controllerSucc controller)
            (G.vriezeOccupationSupport controller z) t) := by
    intro s hs
    obtain ⟨t, hst, htR⟩ := FiniteReachability.exists_succ_canReachSet_of_canReachSet
      (G.controllerSucc controller) (G.vriezeOccupationSupport controller z) hs (hnotrap s hs)
    obtain ⟨j, hjt⟩ := hst
    exact ⟨j, t, hjt, Or.inr htR⟩
  choose jOf hjOf using hprogress
  set τ : G.State → PMF (G.Act controller) := fun s =>
    if h : G.vriezeOccupationSupport controller z s then
      weightsToPMF (fun j => z s j / (∑ j', z s j'))
        (fun j => div_nonneg (hdual.z_nonneg s j) h.le)
        (by rw [← Finset.sum_div]; exact div_self h.ne')
    else PMF.pure (jOf s h) with hτdef
  refine ⟨τ, ?_, ?_⟩
  · intro s hs j
    have : τ s = weightsToPMF (fun j => z s j / (∑ j', z s j'))
        (fun j => div_nonneg (hdual.z_nonneg s j) hs.le)
        (by rw [← Finset.sum_div]; exact div_self hs.ne') := by
      rw [hτdef]; exact dif_pos hs
    rw [this]
    exact weightsToPMF_apply_toReal _ _ _ j
  · intro s hs
    have hτs : τ s = PMF.pure (jOf s hs) := by rw [hτdef]; exact dif_neg hs
    obtain ⟨t, ht, hor⟩ := hjOf s hs
    refine ⟨t, ?_, hor⟩
    have hker : G.controllerKernel controller τ s =
        G.controllerKernel controller (fun _ => PMF.pure (jOf s hs)) s := by
      unfold controllerKernel
      rw [hτs]
    rw [hker]
    exact ht

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
