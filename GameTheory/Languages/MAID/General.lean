/-
# General typed MAIDs

Public entry point for finite, acyclic, heterogeneously typed multi-agent
influence diagrams.

`Basic` defines order-free syntax, site-local policies, simultaneous-frontier
evaluation, and finite completion. `ToEFG` compiles an explicit topological
order to the shared EFG and information layers. `Order` and
`FrontierEquivalence` prove that the compiled behavioral assignment law is
independent of that order and exactly equals native frontier evaluation.
`Strategic` proves the source-owner profile and Nash-equilibrium transfer.
`ObservationPruning` restricts site-local information domains while retaining
source-owner deviations and exact native/compiled laws.

The concrete three-node architecture witness remains available explicitly at
`GameTheory.Experimental.PostArchitecture.MAIDThreeNodeWitness`. This module
is the validated general surface.
-/

import GameTheory.Languages.MAID.ObservationPruning

namespace GameTheory.Languages.MAID

end GameTheory.Languages.MAID
