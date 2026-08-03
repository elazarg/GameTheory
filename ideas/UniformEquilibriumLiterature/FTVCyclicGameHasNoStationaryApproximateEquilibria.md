# FTV cyclic stationary-impossibility fence

| Field | Value |
| --- | --- |
| Citation of record | Flesch--Thuijsman--Vrieze, *Cyclic Markov equilibria in stochastic games*, IJGT 26 (1997) |
| Source confidence | `PRIMARY_VERIFIED` for the construction; exact remaining statement must be rechecked before coding |
| Mathematical status | `PROVED` |
| Repository status | `ADAPTED` |
| Lean status | `PARTIAL` |
| Objective priority | `P1` |
| Exact scope and quantifiers | Concrete three-player cyclic architecture with a uniform equilibrium; the remaining fence excludes sufficiently accurate stationary equilibria at the source's stated scope. |
| Source alignment | Game, architecture, credibility, exact finite-horizon delivery, semantic bridge, and minimality packets are landed; stationary impossibility is absent. |
| Lean destination | `FTVCyclicStationaryImpossibility.lean` |
| Acceptance and consumer | Reuse the landed table and exact cap interface; prove only the source-supported small-error statement and protect it with the cyclic equilibrium positive regression. |
| Discrepancies | Do not say “every epsilon” unless the primary statement has that quantifier; do not re-list landed delivery as missing. |

See [`30-counterexamples.md`](../../docs/uniform-equilibrium/references/30-counterexamples.md)
and the four `FTVCyclic*.lean` modules. Any source-aligned capstone gets a
docstring with the paper attribution and an explicit note that the existing
semantic bridge is an internal formal reconstruction.
