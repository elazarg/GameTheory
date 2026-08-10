/-
# GameTheory

Public root of the greenfield GameTheory library.

`GameTheory.Core` is the stable foundation and static theory;
`GameTheory.Protocol` is the sequential layer and its compilation into the
core; `GameTheory.Epistemic` is the finite partition and knowledge branch;
`GameTheory.Evolutionary` is the static ESS/NSS branch; `GameTheory.Finite` is
the executable rational frontend and its correctness layer.

Several roots are deliberately opt-in. `GameTheory.Analysis` carries audited
fixed-point and topology dependencies; `GameTheory.Cooperative`,
`GameTheory.Congestion`, `GameTheory.Mechanism`, `GameTheory.Repeated`, and
`GameTheory.Stochastic` expose domain families; and the encodings under
`GameTheory.Languages` demonstrate that native shapes reach the shared layers
without dummy data. Each language records its own scope limits, and none yet
covers its source formalism in full. `GameTheory.Experimental` contains
recorded architecture evidence, not public library surface.
-/

import GameTheory.Core
import GameTheory.Protocol
import GameTheory.Epistemic
import GameTheory.Evolutionary
import GameTheory.Finite.Algorithm
import GameTheory.Finite.Correctness

namespace GameTheory

end GameTheory
