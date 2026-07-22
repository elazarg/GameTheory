/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.Intrinsic.Strategies
import GameTheory.Core.KernelGame

/-!
# Compilation of Intrinsic Games to KernelGame

Every game representation in this project compiles to the core
`KernelGame` abstraction. For expected-utility W-games, the compilation is
straightforward under solvability:

- **Players** are the expected-utility W-game's player set `P`
- **Strategies** for player `p` are pure strategies over `p`'s agents
- **Outcomes** are configurations (nature + decisions)
- **Kernel** averages the deterministic solution map over the prior on Ω
-/

namespace Intrinsic

open GameTheory Math.Probability
open Math.PMFProduct Math.ProbabilityMassFunction

-- ============================================================================
-- Lifting player strategies to a full profile
-- ============================================================================

/-- Lift a player-indexed strategy assignment to a full agent profile.
    Each agent `a` gets the strategy assigned by `owner a`'s player strategy. -/
noncomputable def liftProfile (G : WGame)
    (strats : ∀ p : G.P, PlayerStrategySpace G p) : PureProfile G.toWModel :=
  fun a => strats (G.owner a) ⟨a, by simp [WGame.agents]⟩

-- ============================================================================
-- Mixed outcome laws
-- ============================================================================

open Classical in
/-- Opponent mixed profiles for a fixed player `p`. -/
def OpponentMixedProfile (G : WGame) (p : G.P) : Type :=
  ∀ q : { q : G.P // q ≠ p }, MixedStrategy G q

open Classical in
/-- Assemble a full mixed profile from player `p`'s mixed strategy and an
    opponent profile. -/
noncomputable def assembleMixedProfile (G : WGame) (p : G.P)
    (μp : MixedStrategy G p) (μminus : OpponentMixedProfile G p) :
    MixedProfile G := by
  intro q
  by_cases h : q = p
  · subst h
    exact μp
  · exact μminus ⟨q, h⟩

open Classical in
/-- Equation (22), pointwise in nature: sample a pure-strategy profile from the
    mixed profile and push it through the closed-loop solution map. -/
noncomputable def mixedOutcomeAt (G : WGame) (hsolv : Solvable G.toWModel)
    (μ : MixedProfile G) (ω : G.Ω) : PMF (∀ a : G.A, G.U a) :=
  (mixedJoint G μ).map
    (fun strats => solutionMap G.toWModel hsolv (liftProfile G strats) ω)

open Classical in
/-- The full outcome law induced by a mixed profile. -/
noncomputable def mixedOutcomeLaw (G : WGame) (hsolv : Solvable G.toWModel)
    (μ : MixedProfile G) : OutcomeLaw G.toWModel :=
  fun ω => mixedOutcomeAt G hsolv μ ω

/-- For a proposed decision profile `u`, player `p`'s pure strategy is
    consistent with `u` at nature state `ω` when every agent owned by `p`
    chooses the corresponding coordinate of `u` at configuration `(ω, u)`. -/
def playerSolutionEvent (G : WGame) (p : G.P) (ω : G.Ω)
    (u : ∀ a : G.A, G.U a) (strat : PlayerStrategySpace G p) : Prop :=
  ∀ (a : G.A) (ha : G.owner a = p),
    u a = (strat ⟨a, by simp [WGame.agents, ha]⟩).act ⟨ω, u⟩

/-- A full pure-strategy profile is consistent with `u` iff every player's
    strategy is consistent with `u`. -/
def profileSolutionEvent (G : WGame) (ω : G.Ω)
    (u : ∀ a : G.A, G.U a)
    (strats : ∀ p : G.P, PlayerStrategySpace G p) : Prop :=
  ∀ p : G.P, playerSolutionEvent G p ω u (strats p)

/-- The solution map equals `u` exactly when the player-indexed pure profile is
    consistent with `u` for every player. -/
theorem solutionMap_eq_iff_profileSolutionEvent (G : WGame)
    (hsolv : Solvable G.toWModel)
    (strats : ∀ p : G.P, PlayerStrategySpace G p)
    (ω : G.Ω) (u : ∀ a : G.A, G.U a) :
    solutionMap G.toWModel hsolv (liftProfile G strats) ω = u ↔
      profileSolutionEvent G ω u strats := by
  constructor
  · intro hsol p a ha
    have hfp := solutionMap_spec G.toWModel hsolv (liftProfile G strats) ω a
    rw [hsol] at hfp
    cases ha
    simpa [playerSolutionEvent, liftProfile, WGame.agents] using hfp
  · intro hevent
    symm
    apply solutionMap_unique G.toWModel hsolv (liftProfile G strats) ω u
    intro a
    simpa [liftProfile, WGame.agents] using hevent (G.owner a) a rfl

open Classical in
/-- Point-mass expansion for `mixedOutcomeAt`: the probability of a decision
    profile `u` is the product, over players, of the masses of their
    consistency events. -/
theorem mixedOutcomeAt_apply_eq_prod (G : WGame)
    (hsolv : Solvable G.toWModel) (μ : MixedProfile G)
    (ω : G.Ω) (u : ∀ a : G.A, G.U a) :
    mixedOutcomeAt G hsolv μ ω u =
      ∏ p : G.P, pmfMass (μ := μ p) (playerSolutionEvent G p ω u) := by
  rw [mixedOutcomeAt]
  change pushforward (mixedJoint G μ)
      (fun strats => solutionMap G.toWModel hsolv (liftProfile G strats) ω) u =
    ∏ p : G.P, pmfMass (μ := μ p) (playerSolutionEvent G p ω u)
  rw [pushforward_apply_eq_pmfMass]
  rw [show pmfMass (μ := mixedJoint G μ)
      (fun strats =>
        solutionMap G.toWModel hsolv (liftProfile G strats) ω = u) =
      pmfMass (μ := mixedJoint G μ) (profileSolutionEvent G ω u) from by
        apply congrArg
        funext strats
        exact propext (solutionMap_eq_iff_profileSolutionEvent G hsolv strats ω u)]
  exact
    pmfMass_pmfPi_forall (A := fun p : G.P => PlayerStrategySpace G p)
      (σ := μ) (E := fun p strat => playerSolutionEvent G p ω u strat)

/-- Player-level event-mass equivalence. This is the exact local condition
    needed to replace player `p`'s mixed strategy by a product-mixed strategy
    in the full outcome law. -/
def PlayerEventMassEquivalent (G : WGame) (p : G.P)
    (μp : MixedStrategy G p) (πp : ProductMixedStrategy G p) : Prop :=
  ∀ (ω : G.Ω) (u : ∀ a : G.A, G.U a),
    pmfMass (μ := μp) (playerSolutionEvent G p ω u) =
      pmfMass (μ := productMixedAsMixed G p πp) (playerSolutionEvent G p ω u)

/-- The product-mixed mass of a player's consistency event factors across that
    player's agents. -/
theorem productMixed_playerSolutionEvent_mass_eq_prod (G : WGame)
    (p : G.P) (πp : ProductMixedStrategy G p)
    (ω : G.Ω) (u : ∀ a : G.A, G.U a) :
    pmfMass (μ := productMixedAsMixed G p πp) (playerSolutionEvent G p ω u) =
      ∏ a : G.agents p,
        pmfMass (μ := πp a) (fun s => u a = s.act ⟨ω, u⟩) := by
  classical
  have hevent :
      playerSolutionEvent G p ω u =
        (fun strat : PlayerStrategySpace G p =>
          ∀ a : G.agents p, u a = (strat a).act ⟨ω, u⟩) := by
    funext strat
    apply propext
    constructor
    · intro h a
      exact h (a : G.A) ((Finset.mem_filter.mp a.property).2)
    · intro h a ha
      exact h ⟨a, by simp [WGame.agents, ha]⟩
  rw [productMixedAsMixed, hevent]
  exact
    pmfMass_pmfPi_forall
      (A := fun a : G.agents p => PureStrategy G.toWModel a)
      (σ := πp)
      (E := fun a s => u a = s.act ⟨ω, u⟩)

/-- Outcome-law equivalence for a candidate product-mixed strategy of player
    `p`: for every opponent mixed profile and state of nature, the full
    decision-profile distribution is unchanged. -/
def KuhnOutcomeEquivalent (G : WGame) (hsolv : Solvable G.toWModel)
    (p : G.P) (μp : MixedStrategy G p) (πp : ProductMixedStrategy G p) : Prop :=
  ∀ (μminus : OpponentMixedProfile G p) (ω : G.Ω),
    mixedOutcomeAt G hsolv (assembleMixedProfile G p μp μminus) ω =
      mixedOutcomeAt G hsolv
        (assembleMixedProfile G p (productMixedAsMixed G p πp) μminus) ω

/-- If a candidate product-mixed strategy matches player `p`'s consistency
    event masses, then replacing `p`'s mixed strategy preserves the full
    outcome distribution against every opponent profile. -/
theorem kuhn_equivalence_of_player_event_mass (G : WGame)
    (hsolv : Solvable G.toWModel) (p : G.P)
    (μp : MixedStrategy G p) (πp : ProductMixedStrategy G p)
    (heq : PlayerEventMassEquivalent G p μp πp) :
    KuhnOutcomeEquivalent G hsolv p μp πp := by
  classical
  intro μminus ω
  ext u
  rw [mixedOutcomeAt_apply_eq_prod G hsolv, mixedOutcomeAt_apply_eq_prod G hsolv]
  apply Finset.prod_congr rfl
  intro q hq
  by_cases hqp : q = p
  · subst hqp
    simpa [assembleMixedProfile, PlayerEventMassEquivalent] using heq ω u
  · simp [assembleMixedProfile, hqp]

-- ============================================================================
-- EUWGame → KernelGame
-- ============================================================================

/-- Compile a solvable expected-utility W-game to a `KernelGame`.

    - Players are `G.P`
    - Strategy for player `p` is the pure `PlayerStrategySpace G.toWGame p`
    - Outcomes are full configurations `H = Ω × ∏ₐ Uₐ`
    - Utility is defined on configurations
    - The kernel averages the solution map over the prior on Ω

    Mixed and behavioral semantics are expressed separately by
    `mixedOutcomeLaw` and the equivalence predicates above; this constructor
    does not transport those strategy carriers into the compiled
    `KernelGame`. -/
noncomputable def EUWGame.toKernelGame (G : EUWGame) (hsolv : Solvable G.toWModel) :
    KernelGame G.P where
  Strategy := fun p => PlayerStrategySpace G.toWGame p
  Outcome := G.toWModel.H
  utility := fun h p => G.utility p h
  outcomeKernel := fun strats =>
    G.prior.bind (fun ω =>
      PMF.pure ⟨ω, solutionMap G.toWModel hsolv (liftProfile G.toWGame strats) ω⟩)

end Intrinsic
