import GameTheory.Auctions.Tests
import GameTheory.Concepts.Correlation.Tests
import GameTheory.Concepts.Dominance.Tests
import GameTheory.Concepts.Foundations.Tests
import GameTheory.Concepts.Learning.Tests
import GameTheory.Concepts.Mixed.Tests
import GameTheory.Concepts.Repeated.Tests
import GameTheory.Concepts.Transport.Tests
import GameTheory.Concepts.Welfare.Tests
import GameTheory.Concepts.ZeroSum.Tests
import GameTheory.Cooperative.Tests
import GameTheory.Core.Tests
import GameTheory.Languages.EFG.Tests
import GameTheory.Languages.Expressiveness.Tests
import GameTheory.Languages.FOSG.Tests
import GameTheory.Languages.Intrinsic.Tests
import GameTheory.Languages.MAID.Tests
import GameTheory.Languages.MultiRound.Tests
import GameTheory.Languages.NFG.Tests
import GameTheory.Mechanism.Tests
import GameTheory.Theorems.Tests
import GameTheory.Voting.Tests
import Math.Tests
import Semantics.Tests

/-!
# GameTheoryTest

Aggregates all compilation-test modules. This is a **separate Lake target**
from `GameTheory`: tests are not part of the public `import GameTheory`
surface, so downstream consumers do not build them transitively.

Reader-facing `Examples` modules stay in the main library; only the
`*.Tests` modules (which exist purely to exercise compilation) live here.
-/
