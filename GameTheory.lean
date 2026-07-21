-- Unified architecture (semantics-first)
import GameTheory.Languages
import GameTheory.Theorems

-- Probability and core
import Math.Probability
import Math.RelationalKernel
import GameTheory.Core.KernelGame
import GameTheory.Core.GameForm
import GameTheory.Core.Coalition
import GameTheory.Core.Subsidy

-- Solution concepts and properties
import GameTheory.Concepts.Equilibrium.GameFormSolutionConcepts
import GameTheory.Concepts.Equilibrium.SolutionConcepts
import GameTheory.Concepts.Foundations.Convergence
import GameTheory.Concepts.Mixed.SequentialAssessment
import GameTheory.Concepts.Foundations.GameMorphism
import GameTheory.Concepts.Foundations.InertExtension
import GameTheory.Concepts.Communication.Babbling

-- Equilibrium transport
import GameTheory.Concepts.Transport.Deviation
import GameTheory.Concepts.Transport.Pref
import GameTheory.Concepts.Transport.View
import GameTheory.Concepts.Transport.Simulation
import GameTheory.Concepts.Transport.Approximate
import GameTheory.Concepts.Transport.Distinguishing
import GameTheory.Concepts.Transport.Transfer
import GameTheory.Concepts.Transport.Order
import GameTheory.Concepts.Transport.Characterize
import GameTheory.Concepts.Transport.Corners
import GameTheory.Concepts.Transport.Oblivious
import GameTheory.Concepts.Transport.Separations
import GameTheory.Concepts.Foundations.Deviation
import GameTheory.Concepts.Foundations.BestResponse
import GameTheory.Concepts.Foundations.PrefPreorderProperties
import GameTheory.Concepts.Foundations.EUProperties
import GameTheory.Concepts.Foundations.OfEUProperties
import GameTheory.Concepts.Foundations.VNM
import GameTheory.Core.GameIsomorphism
import GameTheory.Core.GameSimulation
import GameTheory.Concepts.Foundations.UtilityInvariance
import GameTheory.Concepts.Foundations.StrategicEquivalence

-- Rationalizability
import GameTheory.Concepts.Dominance.Rationalizability

-- Dominance
import GameTheory.Concepts.Dominance.StrictDominance
import GameTheory.Concepts.Dominance.DominanceRelations
import GameTheory.Concepts.Dominance.Undominated
import GameTheory.Concepts.Dominance.DominanceSolvable
import GameTheory.Concepts.Dominance.DominanceNash
import GameTheory.Concepts.Dominance.DominanceSolvability

-- Nash equilibrium
import GameTheory.Concepts.Equilibrium.StrictNashProperties
import GameTheory.Concepts.Equilibrium.SecureEquilibrium
import GameTheory.Concepts.Equilibrium.ApproximateNash
import GameTheory.Concepts.Mixed.MixedExtension
import GameTheory.Concepts.Mixed.MixedDominance
import GameTheory.Concepts.Mixed.MixedImprovement
import GameTheory.Concepts.Mixed.BinaryMixed
import GameTheory.Concepts.Mixed.TremblingHand
import GameTheory.Concepts.Existence.NashExistence
import GameTheory.Concepts.Existence.ProductSimplexBrouwer
import GameTheory.Concepts.Existence.NashExistenceMixed
import GameTheory.Concepts.Mixed.MixedSupport
import GameTheory.Concepts.Foundations.BestResponseDynamics
import GameTheory.Concepts.Equilibrium.NashProperties
import GameTheory.Concepts.Equilibrium.StrongNash
import GameTheory.Concepts.Equilibrium.FlowInvariance

-- Game properties and welfare
import GameTheory.Concepts.Foundations.GameProperties
import GameTheory.Concepts.Equilibrium.NashPareto
import GameTheory.Concepts.Welfare.WelfareTheorems
import GameTheory.Concepts.Welfare.PriceOfAnarchy
import GameTheory.Concepts.Welfare.Smoothness
import GameTheory.Concepts.Welfare.IndividualRationality
import GameTheory.Concepts.ZeroSum.SecurityStrategy
import GameTheory.Concepts.ZeroSum.CoalitionSecurity
import GameTheory.Concepts.Welfare.FolkTheorem

-- Repeated games
import GameTheory.Concepts.Repeated.Basic
import GameTheory.Concepts.Repeated.Discounted
import GameTheory.Concepts.Repeated.Monitoring
import GameTheory.Concepts.Repeated.Uniform
import GameTheory.Concepts.Repeated.MonitoringInstances
import GameTheory.Concepts.Repeated.MonitoringDiscounted
import GameTheory.Concepts.Repeated.MonitoringDecomposition
import GameTheory.Concepts.Repeated.MonitoringSelfGeneration

-- Correlated equilibrium
import GameTheory.Concepts.Correlation.CorrelatedEqProperties
import GameTheory.Concepts.Correlation.Regret
import GameTheory.Concepts.Correlation.ApproximateCorrelatedEq
import GameTheory.Concepts.Correlation.CorrelatedNashMixed
import GameTheory.Concepts.Correlation.CorrelationSaturation
import GameTheory.Concepts.Correlation.GameMorphism
import GameTheory.Concepts.Equilibrium.NashCorrelatedEq
import GameTheory.Concepts.Correlation.CorrelationRegimes
import GameTheory.Concepts.Correlation.ValueOfCorrelation
import GameTheory.Concepts.Correlation.SignalTiming
import GameTheory.Concepts.Communication.CheapTalkPublicRandomness

-- Learning dynamics
import Math.OnlineLearning
import GameTheory.Concepts.Learning.NoRegretToCCE
import GameTheory.Concepts.Learning.SelfPlay
import GameTheory.Concepts.Learning.MWSelfPlay
import GameTheory.Concepts.Learning.FictitiousPlay
import GameTheory.Concepts.Learning.FictitiousPlayPotential
import GameTheory.Concepts.Learning.Approachability
import GameTheory.Concepts.Learning.ApproachabilityRegret

-- Zero-sum and constant-sum
import GameTheory.Concepts.ZeroSum.ZeroSum
import GameTheory.Concepts.ZeroSum.ConstantSum
import GameTheory.Concepts.ZeroSum.ZeroSumNash
import GameTheory.Concepts.ZeroSum.ConstantSumNash
import GameTheory.Concepts.ZeroSum.ConstantSumCorrelated
import GameTheory.Concepts.ZeroSum.ConstantSumCounterexamples
import GameTheory.Concepts.Communication.CheapTalkPublicRandomnessConstantSum

-- Flow decomposition
import GameTheory.Concepts.Potential.Flow
import GameTheory.Concepts.Potential.Harmonic
import GameTheory.Concepts.Potential.Decomposition
import GameTheory.Concepts.Equilibrium.FlowDecomposition

-- Potential games
import GameTheory.Concepts.Potential.PotentialGame
import GameTheory.Concepts.Potential.PotentialFIP
import GameTheory.Concepts.Potential.PotentialWellFounded
import GameTheory.Concepts.Potential.PotentialTeam
import GameTheory.Concepts.Potential.MixedPotential

-- Team games and symmetric games
import GameTheory.Concepts.Classes.TeamGame
import GameTheory.Concepts.Classes.SymmetricGame
import GameTheory.Concepts.Classes.EvolutionaryStability

-- Minimax
import GameTheory.Concepts.ZeroSum.Minimax
import GameTheory.Concepts.ZeroSum.MatrixGame
import GameTheory.Concepts.ZeroSum.MatrixGame.Geometry
import GameTheory.Concepts.ZeroSum.MatrixGame.StrongComplementarity

-- Mechanism design
import GameTheory.Mechanism.Bayesian
import GameTheory.Mechanism.Contracts.Basic

-- Social choice and information
import GameTheory.Mechanism.SocialChoice
import GameTheory.Mechanism.FairDivision

-- Voting and fluid democracy
import GameTheory.Voting.Delegation
import GameTheory.Voting.LiquidDemocracy
import GameTheory.Voting.DelegationGame
import GameTheory.Voting.Majority
import GameTheory.Voting.Median
import GameTheory.Voting.Power

import GameTheory.Concepts.Knowledge.CommonKnowledge
import GameTheory.Concepts.Knowledge.ApproximateCommonKnowledge

-- Congestion games
import GameTheory.Congestion.Basic
import GameTheory.Congestion.Rosenthal
import GameTheory.Congestion.AffinePoA

-- Auctions, mechanism design, and contests
import GameTheory.Auctions.Basic
import GameTheory.Auctions.Combinatorial
import GameTheory.Auctions.Vickrey
import GameTheory.Auctions.ReserveVickrey
import GameTheory.Auctions.FirstPrice
import GameTheory.Auctions.VCG
import GameTheory.Auctions.AllPay
import GameTheory.Auctions.Knapsack

-- Cooperative game theory and non-strategic-form game models
import GameTheory.Cooperative

/-!
# GameTheory

This library formalizes **non-cooperative game theory** as its main
content. The load-bearing abstraction is `KernelGame` (player strategies
+ outcome kernel + utility); the `Languages/` layer compiles various
syntactic game descriptions (NFG, EFG, MAID, FOSG, MultiRound, …) into
`KernelGame`; `Concepts/`, `Theorems/`, `Auctions/`, and `Mechanism/`
are all built over `KernelGame`-derived structures. Strategies, best
responses, Nash equilibrium, and the rest are strategy-centric notions
that presuppose the non-cooperative formalism.

`GameTheory.Cooperative` is a **separate, parallel branch** for the
cooperative-game-theory tradition (TU coalitional games and the Shapley
value, axiomatic bargaining, two-sided matching markets). These
formalisms do *not* go through `KernelGame`: their primitives are
coalition value functions, feasible payoff sets, or preference rankings
rather than per-player strategies. Apart from sharing the player-index
type `ι` and the real line `ℝ`, the cooperative branch and the
non-cooperative core share no load-bearing abstractions — they live in
the same library only for packaging convenience.
-/
