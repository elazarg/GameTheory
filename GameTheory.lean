/-
# GameTheory

Public root of the greenfield GameTheory library.

`GameTheory.Core` is the static semantic core; `GameTheory.Protocol` is the
sequential layer and its compilation into the core; `GameTheory.Finite` is the
executable rational frontend and its correctness layer.

Two trees are deliberately not re-exported. Architecture experiments under
`GameTheory.Experimental` are recorded evidence, not library. The encodings
under `GameTheory.Languages` are demonstrations that a native shape reaches the
shared layers without dummy data; each records its own scope limits, and none
of them yet covers its source formalism in full.
-/

import GameTheory.Core
import GameTheory.Protocol
import GameTheory.Finite.Algorithm
import GameTheory.Finite.Correctness

namespace GameTheory

end GameTheory
