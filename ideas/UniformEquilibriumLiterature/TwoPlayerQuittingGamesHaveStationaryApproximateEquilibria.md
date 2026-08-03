# Two-player quitting stationary approximate existence

| Field | Value |
| --- | --- |
| Citation of record | Solan--Vieille, *Quitting Games--An Example* (2002), Section 2.1; citing Flesch--Thuijsman--Vrieze (1996) |
| Source confidence | `PRIMARY_VERIFIED` for the six-scalar proof |
| Mathematical status | `PROVED` |
| Repository status | `ADAPTED` |
| Lean status | `PARTIAL` |
| Objective priority | `P1` |
| Exact scope and quantifiers | Every standard two-player quitting game and every positive error admit a stationary product profile that is terminal approximate Nash against arbitrary behavioral unilateral deviations. |
| Source alignment | Full-rate cap verification and one pair-repair branch are landed; the exhaustive source case split is not. |
| Lean destination | `QuittingTwoPlayerStationaryExistence.lean` |
| Acceptance and consumer | Cover all pure cases, role reversal, both no-pure branches, and Q132's exact-nonattainment regression; feed `QuittingTerminalUniformPayoffSelection`. |
| Discrepancies | Do not strengthen approximate existence to exact behavioral or exact stationary existence. |

The authoritative internal owner is
[`ideas/TwoPlayerBaseCaseExhaustion`](../../ideas/TwoPlayerBaseCaseExhaustion/README.md).
Source-aligned declarations should cite the 2002 Section 2.1 proof and clearly
separate imported source structure from independently proved cap lemmas.
