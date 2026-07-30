/-
# GameTheory

Public root of the greenfield GameTheory library.

`GameTheory.Core` is the stable foundation and static theory;
`GameTheory.Protocol` is the sequential layer and its compilation into the
core; `GameTheory.Epistemic` is the finite partition and knowledge branch;
`GameTheory.Finite` is the executable rational frontend and its correctness
layer.

Several roots are deliberately not re-exported. `GameTheory.Analysis` is
stable but opt-in because importing its fixed-point and topology dependencies
is an audited architectural choice. Architecture experiments under
`GameTheory.Experimental` are recorded evidence, not library. The encodings
under `GameTheory.Languages` demonstrate that native shapes reach the shared
layers without dummy data; each records its own scope limits, and none yet
covers its source formalism in full.
-/

import GameTheory.Core
import GameTheory.Protocol
import GameTheory.Epistemic
import GameTheory.Finite.Algorithm
import GameTheory.Finite.Correctness

namespace GameTheory

end GameTheory
