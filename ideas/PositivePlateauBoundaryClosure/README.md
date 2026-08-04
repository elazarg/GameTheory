# Positive-plateau boundary closure

| Lifecycle | Verdict | Priority | Group decision |
| --- | --- | --- | --- |
| `ACTIVE` | `MIXED` | `P0` | Resolve escaping middle length by an infinity/stopping-law chart with bounded decoder, or by a calibrated incompatibility family; then decode as repair. **Tightness is no longer a route** — an explicit weight has all mass escaping to a receding terminal row, so no common truncation length exists. Fixed debt descent is likewise closed ([`AnchoredRepairOrUniformDebtDescent.md`](AnchoredRepairOrUniformDebtDescent.md)). Restored to `P0` by `PC-009`, superseding `PC-008`'s demotion; the free-terminal test has since resolved and **splits** — one plateau witness collapses under faithful unpinning, another weight keeps a gap of exactly `1` at every length ([`FaithfulUnpinningLeavesASurvivingGap.md`](FaithfulUnpinningLeavesASurvivingGap.md)). |

| Scientific object | Status |
| --- | --- |
| [Positive debt produces an anchored terminal packet](PositiveDebtProducesAnchoredTerminalPacket.md) | `PROVED` |
| [Finite calibrated blocks have compositional boundary holonomy](FiniteCalibratedBlocksHaveCompositionalBoundaryHolonomy.md) | `PROVED`, production Lean |
| [Realized anchored holonomy should be closed—or fail informatively](RealizedAnchoredHolonomyClosedness.md) | `PARTIAL`, fixed-cutoff closure and unbounded-cost fence proved in Lean |
| [Enriched absorption paths may compactify the escaping middle](EnrichedAbsorptionPathsMayCompactifyTheEscapingMiddle.md) | `OPEN`, leading published infinity-chart candidate |
| [Anchored repair or uniform optimized-debt descent](AnchoredRepairOrUniformDebtDescent.md) | `OPEN`, decisive capstone; descent half closed for the zero-pinned grammar, repair remains open |
| [Narrow repair and closure shortcuts are false](RepairAndClosureShortcutsAreFalse.md) | `PROVED` fences |
| [The completed vector-factor trace carrier is compact and determining](CompletedVectorFactorTraceIsCompactAndDetermining.md) | `OPEN`, `M [reported]` only — unaudited, unformalized |
| [The aggregated carrier conflates origin values](AggregatedCarrierConflatesOriginValues.md) | `OPEN`, `M [reported]` only — fence against a cheaper carrier |
| [The relaxed limit package does not certify small gain](RelaxedLimitPackageDoesNotCertifySmallGain.md) | `OPEN`, `M [reported]` only — closes the limit-object route to `MATH-P0-2` as posed |
| [A gap can survive faithful terminal unpinning](FaithfulUnpinningLeavesASurvivingGap.md) | `MIXED` — unpinning-kills-both-witnesses sub-claim is `M+L`; faithful-formulation content is `M [reported]` only |
| [Anchored shortening has unbounded reachable depth under determined anchors](AnchoredShorteningFailsUnderDeterminedAnchors.md) | `OPEN`, `M [reported]` only — unaudited, unformalized |

Consumers: terminal approximate existence and then terminal-to-uniform payoff
selection. Technical compact dynamics are shared with
[CycleGeometryResolution](../CycleGeometryResolution/README.md). Full
derivations and the complete PB ledger remain in
[BackgroundAndDerivations.md](BackgroundAndDerivations.md).
