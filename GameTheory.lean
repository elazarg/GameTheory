/-
# GameTheory

Public root of the greenfield GameTheory library.

`GameTheory.Core` is the static semantic core; `GameTheory.Finite` is the
executable rational frontend and its correctness layer. Architecture
experiments under `GameTheory.Experimental` are deliberately not re-exported.
-/

import GameTheory.Core
import GameTheory.Finite.Algorithm
import GameTheory.Finite.Correctness

namespace GameTheory

end GameTheory
