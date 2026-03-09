import GameTheory.Languages.Intrinsic.Strategies
import GameTheory.Core.KernelGame

/-!
# Compilation of W-Games to KernelGame

Every game representation in this project compiles to the core
`KernelGame` abstraction. For W-games (the intrinsic form), the
compilation is straightforward under solvability:

- **Players** are the W-game's player set `P`
- **Strategies** for player `p` are pure strategies over `p`'s agents
- **Outcomes** are configurations (nature + decisions)
- **Kernel** averages the deterministic solution map over the prior on Ω
-/

namespace Intrinsic

open GameTheory Math.Probability

-- ============================================================================
-- Lifting player strategies to a full profile
-- ============================================================================

/-- Lift a player-indexed strategy assignment to a full agent profile.
    Each agent `a` gets the strategy assigned by `owner a`'s player strategy. -/
noncomputable def liftProfile (G : WGame)
    (strats : ∀ p : G.P, PlayerStrategySpace G p) : PureProfile G.toWModel :=
  fun a => strats (G.owner a) ⟨a, by simp [WGame.agents]⟩

-- ============================================================================
-- WGame → KernelGame
-- ============================================================================

/-- Compile a solvable W-game to a `KernelGame`.

    - Players are `G.P`
    - Strategy for player `p` is `PlayerStrategySpace G p`
    - Outcomes are full configurations `H = Ω × ∏ₐ Uₐ`
    - Utility is defined on configurations
    - The kernel averages the solution map over the prior on Ω -/
noncomputable def WGame.toKernelGame (G : WGame) (hsolv : Solvable G.toWModel) :
    KernelGame G.P where
  Strategy := fun p => PlayerStrategySpace G p
  Outcome := G.toWModel.H
  utility := fun h p => G.utility p h
  outcomeKernel := fun strats =>
    G.prior.bind (fun ω =>
      PMF.pure ⟨ω, solutionMap G.toWModel hsolv (liftProfile G strats) ω⟩)

end Intrinsic
