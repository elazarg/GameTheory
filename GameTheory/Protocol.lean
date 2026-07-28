/-
# `GameTheory.Protocol`

The sequential layer: how a game is *played*, as opposed to what its outcome
law is.

An `ExecutionProtocol` carries states, legality, chance, and a run law over
finite-support distributions; `Trace` records histories as data, which is what
makes uniqueness of history a real property rather than a vacuous one.
`Information` keeps a policy's domain to what its owner can see, by typing
rather than by a side condition. `Backward` supplies the well-founded
recursion and proves it computes the same value as the fuelled runner.
`Strategic` compiles a protocol into a static `GameForm`, which is where this
layer meets `GameTheory.Core`.

`Tree` is the derived finite-first presentation. It is faithful only where no
two players move at once, so it is a convenience for single-mover games rather
than an alternative semantics.
-/

import GameTheory.Protocol.Execution
import GameTheory.Protocol.Tree
import GameTheory.Protocol.Extraction
import GameTheory.Protocol.Backward
import GameTheory.Protocol.Information
import GameTheory.Protocol.Assessment
import GameTheory.Protocol.Strategic
