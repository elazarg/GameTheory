/-
# `GameTheory.Repeated`

Stable public-action repeated-game theory. `Basic` owns finite public histories,
history-dependent strategies, deterministic stage paths, and finite averages.
The monitoring leaves add finite public-signal kernels, continuation values,
canonical perfect-public equilibrium, and the bounded one-shot-deviation
principle. `Discounted` adds deterministic-path values as real series and
applies the ordinary static Nash predicate. `Periodic` supplies finite-cycle
limits and `Trigger` turns public first deviations into permanent punishments.

Finite-prefix execution and information compilation is layered over Protocol;
stochastic laws over entire infinite paths are deliberately absent.
-/

import GameTheory.Repeated.Basic
import GameTheory.Repeated.Monitoring
import GameTheory.Repeated.MonitoringContinuation
import GameTheory.Repeated.MonitoringPayoff
import GameTheory.Repeated.MonitoringDiscounted
import GameTheory.Repeated.MonitoringOneShot
import GameTheory.Repeated.Discounted
import GameTheory.Repeated.Periodic
import GameTheory.Repeated.Trigger
import GameTheory.Repeated.Protocol

namespace GameTheory.Repeated

end GameTheory.Repeated
