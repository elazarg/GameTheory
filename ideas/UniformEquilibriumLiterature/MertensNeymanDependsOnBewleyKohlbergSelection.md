# Mertens--Neyman and Bewley--Kohlberg closure

| Field | Value |
| --- | --- |
| Citation of record | Bewley--Kohlberg (1976); Mertens--Neyman (1981); Renault's verified modern restatements |
| Source confidence | `PRIMARY_VERIFIED` for the cited statements through the reference audit; full original proofs not all re-read |
| Mathematical status | `PROVED` externally; current internal capstone is conditional |
| Repository status | `ADAPTED` |
| Lean status | `PARTIAL` |
| Objective priority | `P1` |
| Exact scope and quantifiers | Finite two-player zero-sum stochastic games: asymptotic discounted/Shapley structure and existence of the uniform value under the classical theorems. |
| Source alignment | The current Puiseux-selected account strategy is an independent conditional route, not yet the full source-aligned Bewley--Kohlberg plus Mertens--Neyman chain. |
| Lean destination | Continue `DiscountedShapleyAlgebraic.lean`; add `BewleyKohlbergSelection.lean` only when the full source statement and consumers are explicit. |
| Acceptance and consumer | Produce the canonical general Shapley branch including singular roots, then identify its limit and bounded-variation/account hypotheses before claiming the classical theorem. |
| Discrepancies | Do not call a selected Puiseux branch the full Bewley--Kohlberg theorem without bounded variation and limit-identification. |

See [`10-zero-sum-value.md`](../../docs/uniform-equilibrium/references/10-zero-sum-value.md).
Every eventual source-aligned theorem must distinguish which classical input is
formalized and which is independently reproved by the repository's algebraic
selection machinery.
