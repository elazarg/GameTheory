-- Unified architecture (semantics-first)
import GameTheory.Model
import GameTheory.Compilers
import GameTheory.Bridges
import GameTheory.Theorems

-- Probability and core
import Math.Probability
import GameTheory.Core.KernelGame

-- Game form (protocol layer without utility)
import GameTheory.Core.GameForm
import GameTheory.Languages.Sequential.Syntax
import GameTheory.Languages.Sequential.SOS
import GameTheory.Languages.Sequential.Compile
import GameTheory.Languages.Sequential.Theorems

-- Solution concepts and properties
import GameTheory.Concepts.SolutionConcepts
import GameTheory.Concepts.SemanticSolutionConcepts
import GameTheory.Concepts.Deviation
import GameTheory.Concepts.BestResponse
import GameTheory.Concepts.BestResponseExistence
import GameTheory.Concepts.PrefPreorderProperties
import GameTheory.Concepts.EUProperties
import GameTheory.Concepts.OfEUProperties
import GameTheory.Core.GameIsomorphism
import GameTheory.Core.GameSimulation
import GameTheory.Core.UtilityInvariance
import GameTheory.Core.GameMorphism

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
import GameTheory.Concepts.NashExistence
import GameTheory.Concepts.ProductSimplexBrouwer
import GameTheory.Concepts.NashExistenceMixed
import GameTheory.Concepts.MixedSupport
import GameTheory.Concepts.BestResponseDynamics
import GameTheory.Concepts.NashProperties

-- Game properties and welfare
import GameTheory.Core.GameProperties
import GameTheory.Concepts.ParetoOptimal
import GameTheory.Concepts.NashPareto
import GameTheory.Concepts.WelfareTheorems
import GameTheory.Concepts.PriceOfAnarchy
import GameTheory.Concepts.IndividualRationality
import GameTheory.Concepts.SecurityStrategy

-- Correlated equilibrium
import GameTheory.Concepts.CorrelatedEqProperties
import GameTheory.Concepts.Regret
import GameTheory.Concepts.CorrelatedNashMixed
import GameTheory.Concepts.NashCorrelatedEq

-- Zero-sum and constant-sum
import GameTheory.NFG.ZeroSum
import GameTheory.NFG.ZeroSumNash
import GameTheory.NFG.ConstantSum
import GameTheory.NFG.ConstantSumNash
import GameTheory.NFG.Minimax
import GameTheory.NFG.MinimaxTheorem
import GameTheory.NFG.TwoPlayerGame

-- Symmetric games
import GameTheory.NFG.SymmetricGame

-- Potential games, team games, congestion games
import GameTheory.NFG.CongestionGame
import GameTheory.NFG.PotentialGame
import GameTheory.NFG.PotentialFIP
import GameTheory.NFG.PotentialWellFounded
import GameTheory.NFG.TeamGame
import GameTheory.NFG.TeamGameNash
import GameTheory.NFG.PotentialTeam

-- Extensive-form games
import GameTheory.EFG.Basic
import GameTheory.EFG.Kuhn
import GameTheory.EFG.Zermelo
import GameTheory.EFG.OneShotDeviation
import GameTheory.EFG.Refinements

-- Normal-form games
import GameTheory.NFG.Basic

-- Multi-agent influence diagrams
import GameTheory.Languages.MAID.Syntax
import GameTheory.Languages.MAID.SOS
import GameTheory.Languages.MAID.Compile
import GameTheory.Languages.MAID.Theorems

-- Coalitional, bargaining, and matching games
import GameTheory.NFG.CoalitionalGame
import GameTheory.NFG.Bargaining
import GameTheory.NFG.Matching

-- Repeated and stochastic games
import GameTheory.Languages.Sequential.RepeatedGame
import GameTheory.Languages.Sequential.StochasticGame

-- Bayesian games and mechanism design
import GameTheory.Mechanism.BayesianGame
import GameTheory.Mechanism.MechanismDesign
import GameTheory.Mechanism.RevelationPrinciple

-- Social choice and information
import GameTheory.Mechanism.SocialChoice
import GameTheory.Concepts.CommonKnowledge

-- Evolutionary game theory
import GameTheory.NFG.EvolutionaryStability

-- Auctions, mechanism design, and contests
import GameTheory.Auctions.Basic
import GameTheory.Auctions.Vickrey
import GameTheory.Auctions.FirstPrice
import GameTheory.Auctions.VCG
import GameTheory.Auctions.AllPay

-- Stackelberg games
import GameTheory.NFG.Stackelberg

-- Public goods
import GameTheory.NFG.PublicGoods

-- Examples
import GameTheory.NFG.Examples
import GameTheory.EFG.Examples
import GameTheory.Languages.MAID.Tests

