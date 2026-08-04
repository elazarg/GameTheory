# Positive-plateau boundary closure

| Lifecycle | Verdict | Priority | Group decision |
| --- | --- | --- | --- |
| `ACTIVE` | `MIXED` | `P1` | Resolve escaping middle length by tightness, an infinity/stopping-law chart with bounded decoder, or calibrated incompatibility; then decode as repair within the zero-pinned grammar — fixed debt descent is closed ([`AnchoredRepairOrUniformDebtDescent.md`](AnchoredRepairOrUniformDebtDescent.md)). Deprioritized to P1 by `PC-008` pending the free-terminal test. |

| Scientific object | Status |
| --- | --- |
| [Positive debt produces an anchored terminal packet](PositiveDebtProducesAnchoredTerminalPacket.md) | `PROVED` |
| [Finite calibrated blocks have compositional boundary holonomy](FiniteCalibratedBlocksHaveCompositionalBoundaryHolonomy.md) | `PROVED`, production Lean |
| [Realized anchored holonomy should be closed—or fail informatively](RealizedAnchoredHolonomyClosedness.md) | `PARTIAL`, fixed-cutoff closure and unbounded-cost fence proved in Lean |
| [Enriched absorption paths may compactify the escaping middle](EnrichedAbsorptionPathsMayCompactifyTheEscapingMiddle.md) | `OPEN`, leading published infinity-chart candidate |
| [Anchored repair or uniform optimized-debt descent](AnchoredRepairOrUniformDebtDescent.md) | `OPEN`, decisive capstone; descent half closed for the zero-pinned grammar, repair remains open |
| [Narrow repair and closure shortcuts are false](RepairAndClosureShortcutsAreFalse.md) | `PROVED` fences |

Consumers: terminal approximate existence and then terminal-to-uniform payoff
selection. Technical compact dynamics are shared with
[CycleGeometryResolution](../CycleGeometryResolution/README.md). Full
derivations and the complete PB ledger remain in
[BackgroundAndDerivations.md](BackgroundAndDerivations.md).
