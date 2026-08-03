# Autonomous correlation exists in finite stochastic games

| Field | Value |
| --- | --- |
| Citation of record | Solan--Vieille, GEB 38(2):362--399 (2002), Theorems 2.3--2.5 |
| Source confidence | `PRIMARY_VERIFIED` |
| Mathematical status | `PROVED` |
| Repository status | `RECORDED` |
| Lean status | `NONE` |
| Objective priority | `P1` |
| Exact scope and quantifiers | Every finite multiplayer stochastic game has a uniform autonomous correlated-equilibrium payoff, with an accuracy-dependent device in general. |
| Source alignment | No formalization yet. Existing public-randomization modules are related but do not implement either device. |
| Lean destination | `AutonomousCorrelation.lean` and `AutonomousCorrelatedExistence.lean` |
| Acceptance and consumer | Preserve private current recommendations, delayed disclosure, and the source deviation quantifiers; consumer is the ordinary-versus-mediated model boundary. |
| Discrepancies | Do not identify the private recommendation/delayed-disclosure device with a public coin. |

The citation-of-record summary is
[`20-nonzero-sum-equilibrium.md`](../../docs/uniform-equilibrium/references/20-nonzero-sum-equilibrium.md).
The important program conclusion is a fence, not a reduction theorem: the
ordinary Nash problem is not known to be equivalent to manufacturing public
correlation. Solan--Vieille's general device uses private contingent
recommendations and delayed public disclosure. No de-correlation compiler has
been proved.

Any source-aligned Lean theorem must name the cited theorem in its docstring
and keep the correlation-device semantics explicit.
