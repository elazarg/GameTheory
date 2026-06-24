-- Unified architecture (semantics-first)
import GameTheory.Languages
import GameTheory.Theorems

-- Probability and core
import Math.Probability
import GameTheory.Core.KernelGame
import GameTheory.Core.GameForm

-- Solution concepts and properties
import GameTheory.Concepts.Equilibrium.GameFormSolutionConcepts
import GameTheory.Concepts.Equilibrium.SolutionConcepts
import GameTheory.Concepts.Foundations.Convergence
import GameTheory.Concepts.Mixed.SequentialAssessment
import GameTheory.Concepts.Foundations.GameMorphism
import GameTheory.Concepts.Foundations.InertExtension
import GameTheory.Concepts.Communication.Babbling
import GameTheory.Concepts.Foundations.DeviationSimulation
import GameTheory.Concepts.Foundations.Deviation
import GameTheory.Concepts.Foundations.BestResponse
import GameTheory.Concepts.Foundations.PrefPreorderProperties
import GameTheory.Concepts.Foundations.EUProperties
import GameTheory.Concepts.Foundations.OfEUProperties
import GameTheory.Core.GameIsomorphism
import GameTheory.Core.GameSimulation
import GameTheory.Concepts.Foundations.UtilityInvariance

-- Rationalizability
import GameTheory.Concepts.Dominance.Rationalizability

-- Dominance
import GameTheory.Concepts.Dominance.StrictDominance
import GameTheory.Concepts.Dominance.DominanceRelations
import GameTheory.Concepts.Dominance.DominanceSolvable
import GameTheory.Concepts.Dominance.DominanceNash
import GameTheory.Concepts.Dominance.DominanceSolvability

-- Nash equilibrium
import GameTheory.Concepts.Equilibrium.StrictNashProperties
import GameTheory.Concepts.Equilibrium.ApproximateNash
import GameTheory.Concepts.Mixed.MixedExtension
import GameTheory.Concepts.Mixed.BinaryMixed
import GameTheory.Concepts.Mixed.TremblingHand
import GameTheory.Concepts.Existence.NashExistence
import GameTheory.Concepts.Existence.ProductSimplexBrouwer
import GameTheory.Concepts.Existence.NashExistenceMixed
import GameTheory.Concepts.Mixed.MixedSupport
import GameTheory.Concepts.Foundations.BestResponseDynamics
import GameTheory.Concepts.Equilibrium.NashProperties
import GameTheory.Concepts.Equilibrium.StrongNash

-- Game properties and welfare
import GameTheory.Concepts.Foundations.GameProperties
import GameTheory.Concepts.Equilibrium.NashPareto
import GameTheory.Concepts.Welfare.WelfareTheorems
import GameTheory.Concepts.Welfare.PriceOfAnarchy
import GameTheory.Concepts.Welfare.IndividualRationality
import GameTheory.Concepts.ZeroSum.SecurityStrategy
import GameTheory.Concepts.Welfare.FolkTheorem

-- Correlated equilibrium
import GameTheory.Concepts.Correlation.CorrelatedEqProperties
import GameTheory.Concepts.Correlation.Regret
import GameTheory.Concepts.Correlation.CorrelatedNashMixed
import GameTheory.Concepts.Equilibrium.NashCorrelatedEq
import GameTheory.Concepts.Correlation.CorrelationRegimes
import GameTheory.Concepts.Correlation.ValueOfCorrelation
import GameTheory.Concepts.Communication.CheapTalkPublicRandomness

-- Zero-sum and constant-sum
import GameTheory.Concepts.ZeroSum.ZeroSum
import GameTheory.Concepts.ZeroSum.ConstantSum
import GameTheory.Concepts.ZeroSum.ZeroSumNash
import GameTheory.Concepts.ZeroSum.ConstantSumNash
import GameTheory.Concepts.ZeroSum.ConstantSumCorrelated
import GameTheory.Concepts.ZeroSum.ConstantSumCounterexamples
import GameTheory.Concepts.Communication.CheapTalkPublicRandomnessConstantSum

-- Potential games
import GameTheory.Concepts.Potential.PotentialGame
import GameTheory.Concepts.Potential.PotentialFIP
import GameTheory.Concepts.Potential.PotentialWellFounded
import GameTheory.Concepts.Potential.PotentialTeam

-- Team games and symmetric games
import GameTheory.Concepts.Classes.TeamGame
import GameTheory.Concepts.Classes.SymmetricGame
import GameTheory.Concepts.Classes.EvolutionaryStability

-- Minimax
import GameTheory.Concepts.ZeroSum.Minimax

-- Mechanism design
import GameTheory.Mechanism.BayesianGame
import GameTheory.Mechanism.InformationDesign
import GameTheory.Mechanism.BayesCorrelatedEq
import GameTheory.Mechanism.MechanismDesign
import GameTheory.Mechanism.RevelationPrinciple
import GameTheory.Mechanism.Contracts.Basic

-- Social choice and information
import GameTheory.Mechanism.SocialChoice
import GameTheory.Concepts.Knowledge.CommonKnowledge
import GameTheory.Concepts.Knowledge.ApproximateCommonKnowledge

-- Auctions, mechanism design, and contests
import GameTheory.Auctions.Basic
import GameTheory.Auctions.Vickrey
import GameTheory.Auctions.FirstPrice
import GameTheory.Auctions.VCG
import GameTheory.Auctions.AllPay

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
