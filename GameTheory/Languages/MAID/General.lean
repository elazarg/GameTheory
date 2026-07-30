/-
# General typed MAIDs

Public entry point for finite, acyclic, heterogeneously typed multi-agent
influence diagrams.

`Basic` defines order-free syntax, site-local policies, simultaneous-frontier
evaluation, and finite completion. `ToEFG` compiles an explicit topological
order to the shared EFG and information layers. `Order` and
`FrontierEquivalence` prove that the compiled behavioral assignment law is
independent of that order and exactly equals native frontier evaluation.

The earlier `GameTheory.Languages.MAID` module remains the concrete three-node
architecture witness. This module is the validated general surface.
-/

import GameTheory.Languages.MAID.FrontierEquivalence

namespace GameTheory.Languages.MAID

end GameTheory.Languages.MAID
