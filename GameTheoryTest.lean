import GameTheory.Concepts.Learning.Tests
import GameTheory.Languages.EFG.Tests
import GameTheory.Languages.Expressiveness.Tests
import GameTheory.Languages.FOSG.Tests
import GameTheory.Languages.Intrinsic.Tests
import GameTheory.Languages.MAID.Tests
import GameTheory.Languages.MultiRound.Tests

/-!
# GameTheoryTest

Aggregates all compilation-test modules. This is a **separate Lake target**
from `GameTheory`: tests are not part of the public `import GameTheory`
surface, so downstream consumers do not build them transitively.

Reader-facing `Examples` modules stay in the main library; only the
`*.Tests` modules (which exist purely to exercise compilation) live here.
-/
