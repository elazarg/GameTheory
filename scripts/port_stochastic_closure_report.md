source_repo: D:\workspace\GameTheory
source_commit: cdaa59153efc1fe809e45356d6abf9d6b0e05557
verified_source_head: 62d09e3a0f318d38a9071a8877293c153ec950c0
target_repo: D:\workspace\games\GameTheory
roots: 23
closure_modules: 85
copied_modules: 44
existing_boundary_modules: 41
missing_source_modules: 0
unresolved_source_imports: 0
unresolved_target_imports: 0

Copied modules:
- GameTheory.Concepts.Stochastic
- GameTheory.Concepts.Stochastic.Classes.Absorbing
- GameTheory.Concepts.Stochastic.Classes.TransitionIndependent
- GameTheory.Concepts.Stochastic.Core.Basic
- GameTheory.Concepts.Stochastic.Core.Probability.InfinitePlayMeasure
- GameTheory.Concepts.Stochastic.Core.StageGame
- GameTheory.Concepts.Stochastic.Equilibrium.Asymptotic
- GameTheory.Concepts.Stochastic.Equilibrium.Asymptotic.LiminfAverageBridge
- GameTheory.Concepts.Stochastic.Equilibrium.Discounted
- GameTheory.Concepts.Stochastic.Equilibrium.Discounted.Fink
- GameTheory.Concepts.Stochastic.Equilibrium.Uniform
- GameTheory.Concepts.Stochastic.Equilibrium.Uniform.AsymptoticPayoffEquivalence
- GameTheory.Concepts.Stochastic.Equilibrium.Uniform.ExpectedPotentialShaping
- GameTheory.Concepts.Stochastic.Equilibrium.Uniform.PayoffExistenceClosure
- GameTheory.Concepts.Stochastic.Models.Quitting.Asymptotic
- GameTheory.Concepts.Stochastic.Models.Quitting.Game
- GameTheory.Concepts.Stochastic.Models.Quitting.PunishmentLevel
- GameTheory.Concepts.Stochastic.Models.Quitting.RootContinuation
- GameTheory.Concepts.Stochastic.Models.Quitting.RootPerturbation
- GameTheory.Concepts.Stochastic.Models.Quitting.SimpleBranches
- GameTheory.Concepts.Stochastic.Models.Quitting.UniformPayoffExistenceClosure
- GameTheory.Concepts.Stochastic.Strategy.Controller.MemoryController
- GameTheory.Concepts.Stochastic.Strategy.Potential.Adaptive
- GameTheory.Concepts.Stochastic.Transform.ActionLegality.BehaviorTransfer
- GameTheory.Concepts.Stochastic.Transform.ActionLegality.Disintegration
- GameTheory.Concepts.Stochastic.Transform.ActionLegality.MarkovConverse
- GameTheory.Concepts.Stochastic.Transform.ActionLegality.Normalization
- GameTheory.Concepts.Stochastic.Transform.ActionLegality.NormalizedHistory
- GameTheory.Concepts.Stochastic.Transform.Payoff.AffinePayoff
- GameTheory.Concepts.Stochastic.Transform.Repeated.RealizedActionRepeatedAdapter
- GameTheory.Concepts.Stochastic.Welfare.Feasible
- GameTheory.Concepts.Stochastic.Welfare.PunishmentLevel
- GameTheory.Concepts.Stochastic.ZeroSum.Basic
- GameTheory.Concepts.Stochastic.ZeroSum.DiscountedShapleyAlgebraic
- GameTheory.Concepts.Stochastic.ZeroSum.ValueAPI
- Math.CofiniteIdeal
- Math.MeanErgodic
- Math.Minimax.DiscountedShapleySystem
- Math.Minimax.ShapleySnow
- Math.MultivariateElimination
- Math.PMFProduct.Bool
- Math.PMFProduct.CoalitionMass
- Math.PMFProduct.TotalVariation
- Math.ShapleyOperator

Existing same-path boundary modules (not copied):
- GameTheory.Basic
- GameTheory.Concepts.Equilibrium.ApproximateNash
- GameTheory.Concepts.Equilibrium.GameFormSolutionConcepts
- GameTheory.Concepts.Equilibrium.SolutionConcepts
- GameTheory.Concepts.Equilibrium.StrictNashProperties
- GameTheory.Concepts.Existence.NashExistenceMixed
- GameTheory.Concepts.Existence.ProductSimplexBrouwer
- GameTheory.Concepts.Foundations.Convergence
- GameTheory.Concepts.Foundations.Deviation
- GameTheory.Concepts.Mixed.MixedExtension
- GameTheory.Concepts.Repeated.Basic
- GameTheory.Concepts.Repeated.Monitoring
- GameTheory.Concepts.Repeated.MonitoringInstances
- GameTheory.Concepts.Repeated.Uniform
- GameTheory.Concepts.Transport.Deviation
- GameTheory.Concepts.Welfare.FolkTheorem.Feasible
- GameTheory.Concepts.ZeroSum.SecurityStrategy
- GameTheory.Core.Coalition
- GameTheory.Core.GameForm
- GameTheory.Core.KernelGame
- GameTheory.Languages.MultiRound.StochasticGame
- Math.Coupling
- Math.List
- Math.Minimax.Loomis
- Math.Minimax.MinimaxLoomis
- Math.OptimizationLocalGlobal
- Math.PMFIter
- Math.PMFProduct
- Math.PMFProduct.Basic
- Math.PMFProduct.Bind
- Math.PMFProduct.Conditioning
- Math.PMFProduct.Independence
- Math.PMFProduct.Update
- Math.Probability
- Math.ProbabilityMassFunction
- Math.ProbabilityMassFunction.Simplex
- Math.ProbabilityMassFunction.TotalVariation
- Math.Reindex
- Math.RelationalKernel
- Math.Simplex
- Math.SimplexApproximation

Missing source modules:

Unresolved local imports in source:

Integration follow-up:

- Preserved target boundary modules received only the declarations required by
  the copied closure:
  - `Math.Minimax.MinimaxLoomis`: matrix-value nonexpansiveness and zero lemmas.
  - `Math.Probability`: `tsum_expect_comm`.
  - `Math.ProbabilityMassFunction`: subsingleton purity and support expectation
    bound.
  - `Math.ProbabilityMassFunction.Simplex`: the simplex weighted-sum bridge.
  - `Math.ProbabilityMassFunction.TotalVariation`: `pmfTV_pure_true`.
- `GameTheory.lean` imports `GameTheory.Concepts.Stochastic`.
- `lake build +GameTheory.Concepts.Stochastic` passed on the target's existing
  Lean 4.32.0 toolchain (3627 jobs).
- The 44 copied Lean files were verified against source HEAD `62d09e3a`; the
  only target-side normalization removes one extra blank line at EOF. No
  generic Stochastic or dependency module changed after the copy commit.
- The placeholder scan and its four unit tests passed.
- The 52 untracked `Math/GateG*.lean` files were removed before the port; no
  matching path or status entry remains.
