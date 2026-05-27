-- Unified architecture (semantics-first)
import GameTheory.Languages
import GameTheory.Theorems

-- Probability and core
import Math.Probability
import GameTheory.Core.KernelGame
import GameTheory.Core.GameForm

-- Solution concepts and properties
import GameTheory.Concepts.GameForm
import GameTheory.Concepts.SolutionConcepts
import GameTheory.Concepts.Convergence
import GameTheory.Concepts.SequentialAssessment
import GameTheory.Concepts.GameMorphism
import GameTheory.Concepts.InertExtension
import GameTheory.Concepts.Babbling
import GameTheory.Concepts.DeviationSimulation
import GameTheory.Concepts.Deviation
import GameTheory.Concepts.BestResponse
import GameTheory.Concepts.PrefPreorderProperties
import GameTheory.Concepts.EUProperties
import GameTheory.Concepts.OfEUProperties
import GameTheory.Core.GameIsomorphism
import GameTheory.Core.GameSimulation
import GameTheory.Concepts.UtilityInvariance

-- Rationalizability
import GameTheory.Concepts.Rationalizability

-- Dominance
import GameTheory.Concepts.StrictDominance
import GameTheory.Concepts.DominanceRelations
import GameTheory.Concepts.DominanceSolvable
import GameTheory.Concepts.DominanceNash
import GameTheory.Concepts.DominanceSolvability

-- Nash equilibrium
import GameTheory.Concepts.StrictNashProperties
import GameTheory.Concepts.ApproximateNash
import GameTheory.Concepts.MixedExtension
import GameTheory.Concepts.TremblingHand
import GameTheory.Theorems.NashExistence
import GameTheory.Concepts.ProductSimplexBrouwer
import GameTheory.Theorems.NashExistenceMixed
import GameTheory.Concepts.MixedSupport
import GameTheory.Concepts.BestResponseDynamics
import GameTheory.Concepts.NashProperties
import GameTheory.Concepts.StrongNash

-- Game properties and welfare
import GameTheory.Concepts.GameProperties
import GameTheory.Concepts.NashPareto
import GameTheory.Concepts.WelfareTheorems
import GameTheory.Concepts.PriceOfAnarchy
import GameTheory.Concepts.IndividualRationality
import GameTheory.Concepts.SecurityStrategy
import GameTheory.Concepts.FolkTheorem

-- Correlated equilibrium
import GameTheory.Concepts.CorrelatedEqProperties
import GameTheory.Concepts.Regret
import GameTheory.Concepts.CorrelatedNashMixed
import GameTheory.Concepts.NashCorrelatedEq

-- Zero-sum and constant-sum
import GameTheory.Concepts.ZeroSum
import GameTheory.Concepts.ConstantSum
import GameTheory.Concepts.ZeroSumNash
import GameTheory.Concepts.ConstantSumNash

-- Potential games
import GameTheory.Concepts.PotentialGame
import GameTheory.Concepts.PotentialFIP
import GameTheory.Concepts.PotentialWellFounded
import GameTheory.Concepts.PotentialTeam

-- Team games and symmetric games
import GameTheory.Concepts.TeamGame
import GameTheory.Concepts.SymmetricGame
import GameTheory.Concepts.EvolutionaryStability

-- Minimax
import GameTheory.Concepts.Minimax

-- Mechanism design
import GameTheory.Mechanism.BayesianGame
import GameTheory.Mechanism.MechanismDesign
import GameTheory.Mechanism.RevelationPrinciple

-- Social choice and information
import GameTheory.Mechanism.SocialChoice
import GameTheory.Concepts.CommonKnowledge

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
