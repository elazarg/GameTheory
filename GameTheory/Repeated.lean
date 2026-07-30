/-
# `GameTheory.Repeated`

Stable public-action repeated-game theory. `Basic` owns finite public histories,
history-dependent strategies, deterministic stage paths, and finite averages.
`Monitoring` adds finite public-signal kernels and their prefix laws.
`Discounted` adds normalized infinite-horizon values as real series and applies
the ordinary static Nash predicate. `Periodic` supplies finite-cycle limits and
`Trigger` turns public first deviations into permanent punishments.

Finite-prefix execution and information compilation is layered over Protocol;
stochastic laws over entire infinite paths are deliberately absent.
-/

import GameTheory.Repeated.Basic
import GameTheory.Repeated.Monitoring
import GameTheory.Repeated.Discounted
import GameTheory.Repeated.Periodic
import GameTheory.Repeated.Trigger
import GameTheory.Repeated.Protocol

namespace GameTheory.Repeated

end GameTheory.Repeated
