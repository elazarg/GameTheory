import GameTheory.Congestion.Examples
import GameTheory.Languages.NFG.Examples
import GameTheory.Languages.NFG.MatchingPenniesMixed
import GameTheory.Languages.NFG.CheapTalkExamples
import GameTheory.Languages.EFG.Examples
import GameTheory.Languages.FOSG.Examples
import GameTheory.Languages.Bridges.FOSG.Examples
import GameTheory.Languages.MAID.Examples
import GameTheory.Languages.MultiRound.Examples
import GameTheory.Languages.Intrinsic.Examples

/-!
# GameTheoryExamples

Aggregates reader-facing example modules into a **separate Lake target** from
`GameTheory`, so the example games (Prisoner's Dilemma, Matching Pennies,
cheap-talk demonstrations, …) are not built transitively by downstream
consumers of `import GameTheory`.

`MatchingPenniesMixed` and `CheapTalkExamples` are concrete instantiations
that depend on `NFG.Examples`, so they live here too.
-/
