/-
# `GameTheory.Core`

The stable foundation and static theory: signatures and profiles, game forms,
preferences and utility evaluation, local deviation schemes, the single
equilibrium predicate, finite Bayesian forms and interim optimality, response
concepts, potentials, mixed and zero-sum games, social choice, and foundational
coalitional games.

Not every concept here is forced through `GameForm`: a coalitional game has no
strategies or outcome law and is deliberately a parallel primitive. Core
imports no protocol, language front-end, executable frontend, or fixed-point
and topology dependencies. Analytic existence results live above it, so reading
a definition never costs the machinery a later theorem happens to need.
-/

import GameTheory.Core.Signature
import GameTheory.Core.Form
import GameTheory.Core.Bayesian
import GameTheory.Core.BayesianEquilibrium
import GameTheory.Core.BayesCorrelated
import GameTheory.Core.Rank
import GameTheory.Core.Preference
import GameTheory.Core.Deviation
import GameTheory.Core.Equilibrium
import GameTheory.Core.CheapTalk
import GameTheory.Core.CheapTalkRandomization
import GameTheory.Core.Utility
import GameTheory.Core.Learning
import GameTheory.Core.Response
import GameTheory.Core.Potential
import GameTheory.Core.Mixed
import GameTheory.Core.Transform
import GameTheory.Core.ZeroSum
import GameTheory.Core.SocialChoice
import GameTheory.Core.Arrow
import GameTheory.Core.Coalitional
import GameTheory.Core.Shapley
