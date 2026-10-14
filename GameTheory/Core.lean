module

/-
# `GameTheory.Core`

The stable foundation and static theory: signatures and profiles, game forms,
preferences and utility evaluation, local deviation schemes, the single
equilibrium predicate, Bayesian forms and interim optimality, response
concepts, potentials, welfare smoothness, mixed and zero-sum games, social
choice, and foundational coalitional games.

Not every concept here is forced through `GameForm`: a coalitional game has no
strategies or outcome law and is deliberately a parallel primitive. Core
imports no protocol, language front-end, executable frontend, project Analysis,
or external fixed-point dependency. Mathlib's canonical probability operations
bring their own analytic prerequisites; game-theoretic existence results live
above Core.

Uniform utility-transfer certificates and their mixture bridge are stable
opt-in leaves: `Core.UtilitySimulation` and `Core.MixtureUtilitySimulation`.
The direct profile-local transfer theorems are included here.
-/

public import GameTheory.Core.PseudoNashCoalition
public import GameTheory.Core.PseudoNashTolerance
public import GameTheory.Core.Signature
public import GameTheory.Core.Form
public import GameTheory.Core.Bayesian
public import GameTheory.Core.BayesianEquilibrium
public import GameTheory.Core.BayesCorrelated
public import GameTheory.Core.Rank
public import GameTheory.Core.Preference
public import GameTheory.Core.VNM
public import GameTheory.Core.Deviation
public import GameTheory.Core.Equilibrium
public import GameTheory.Core.CheapTalk
public import GameTheory.Core.CheapTalkRandomization
public import GameTheory.Core.Utility
public import GameTheory.Core.Welfare
public import GameTheory.Core.Learning
public import GameTheory.Core.FictitiousPlay
public import GameTheory.Core.RobustWelfare
public import GameTheory.Core.Response
public import GameTheory.Core.CorrelatedDominance
public import GameTheory.Core.Rationalizability
public import GameTheory.Core.UtilityInvariance
public import GameTheory.Core.Approximate
public import GameTheory.Core.CoalitionEquilibrium
public import GameTheory.Core.UtilityTransfer
public import GameTheory.Core.MixtureSimulationComposition
public import GameTheory.Core.Potential
public import GameTheory.Core.Mixed
public import GameTheory.Core.MixedSimulation
public import GameTheory.Core.TremblingHand
public import GameTheory.Core.MixedImprovement
public import GameTheory.Core.MixedPotential
public import GameTheory.Core.FictitiousPlayPotential
public import GameTheory.Core.BinaryMixed
public import GameTheory.Core.BinaryCorrelated
public import GameTheory.Core.Transform
public import GameTheory.Core.ZeroSum
public import GameTheory.Core.MatrixGame
public import GameTheory.Core.SocialChoice
public import GameTheory.Core.May
public import GameTheory.Core.Arrow
public import GameTheory.Core.GibbardSatterthwaite
public import GameTheory.Core.Coalitional
public import GameTheory.Core.Shapley
public import GameTheory.Core.PseudoNash

@[expose] public section
