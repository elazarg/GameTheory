module

/-
# `GameTheory.Repeated`

Stable public-action repeated-game theory. `Basic` owns finite public histories,
history-dependent strategies, deterministic stage paths, and finite averages.
The monitoring leaves add finite public-signal kernels, deviation-signal rank,
continuation values, canonical perfect-public equilibrium, the bounded
one-shot-deviation principle, and APS self-generation. `Discounted` adds
deterministic-path values as real series and applies the ordinary static Nash
predicate. `Periodic` supplies finite-cycle limits and `Trigger` turns public
first deviations into permanent punishments.

Deterministic public-action prefixes compile to Protocol in `Repeated.Protocol`.
Public-signal monitoring keeps the standard native `SignalHistory` recursion
used by continuation and PPE theory; the separate finite multi-round language
is the Protocol-backed constructor when an execution/information model is
needed. Stochastic laws over entire infinite paths are deliberately absent.
-/

public import GameTheory.Repeated.Basic
public import GameTheory.Repeated.Monitoring
public import GameTheory.Repeated.MonitoringContinuation
public import GameTheory.Repeated.MonitoringRank
public import GameTheory.Repeated.MonitoringPayoff
public import GameTheory.Repeated.MonitoringDiscounted
public import GameTheory.Repeated.MonitoringOneShot
public import GameTheory.Repeated.MonitoringDecomposition
public import GameTheory.Repeated.MonitoringSelfGeneration
public import GameTheory.Repeated.Discounted
public import GameTheory.Repeated.Uniform
public import GameTheory.Repeated.Periodic
public import GameTheory.Repeated.Trigger
public import GameTheory.Repeated.Protocol

@[expose] public section

namespace GameTheory.Repeated

end GameTheory.Repeated
