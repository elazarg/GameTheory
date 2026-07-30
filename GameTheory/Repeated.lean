/-
# `GameTheory.Repeated`

Stable public-action repeated-game theory. `Basic` owns finite public histories,
history-dependent strategies, deterministic stage paths, and finite averages.
`Discounted` adds normalized infinite-horizon values as real series and applies
the ordinary static Nash predicate.

Finite-prefix execution and information compilation is layered over Protocol;
stochastic laws over entire infinite paths are deliberately absent.
-/

import GameTheory.Repeated.Basic
import GameTheory.Repeated.Discounted
import GameTheory.Repeated.Protocol

namespace GameTheory.Repeated

end GameTheory.Repeated
