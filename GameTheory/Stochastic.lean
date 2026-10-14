module

/-
# `GameTheory.Stochastic`

Opt-in ordinary-PMF stochastic games, ordinary public policies over their
perfect-monitoring Protocol bridge, chronological finite-horizon laws,
one-step returns, bounded behavioral/mixed Kuhn correspondence, a law over total pure
policies with exact finite-prefix and discounted consequences, the reverse
conditional reading of arbitrary independent pure-policy measures,
restart/continuation calculus, average payoff, and uniform solution concepts.
The root carries no infinite-path outcome law or general existence claim.
-/

public import GameTheory.Stochastic.Basic
public import GameTheory.Stochastic.OneStep
public import GameTheory.Stochastic.ZeroSum
public import GameTheory.Stochastic.PerfectMonitoring
public import GameTheory.Stochastic.FiniteHorizon
public import GameTheory.Stochastic.PublicPolicy
public import GameTheory.Stochastic.Uniform
public import GameTheory.Stochastic.History
public import GameTheory.Stochastic.Kuhn

@[expose] public section
