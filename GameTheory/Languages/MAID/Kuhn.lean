import GameTheory.Languages.MAID.CompileObs
import GameTheory.Theorems.Kuhn

/-!
# GameTheory.Languages.MAID.Kuhn

Kuhn reduction lemmas for compiled MAIDs.

The M→B direction requires linearized compilation (one node per step) to satisfy
`StepSupportFactorization`, since the simultaneous frontier compilation has
multiple players acting at once. This is planned but not yet implemented.

## Planned results

- B→M via `ObsModelCore` with `compileObsCoreModelPR` (under `NoNontrivialInfoStateRepeat`)
- M→B via linearized `ObsModelCore` (one node per step, under `PerfectRecall`)
-/

namespace GameTheory.Languages.MAID

open _root_.MAID
open GameTheory.Theorems

variable {Player : Type} [DecidableEq Player] [Fintype Player] {n : Nat}

end GameTheory.Languages.MAID
