# Renault's precompact non-expansive dynamic-programming criterion

| Field | Value |
| --- | --- |
| Citation of record | Renault, *Uniform value in dynamic programming*, JEMS 13(2):309--330 (2011), Corollary 3.9 |
| Source confidence | `PRIMARY_VERIFIED` against the arXiv version |
| Mathematical status | `PROVED` |
| Repository status | `RECORDED` |
| Lean status | `NONE` |
| Objective priority | `P2` |
| Exact scope and quantifiers | One-player deterministic dynamic programming on a precompact metric state space, uniformly continuous reward, and directed non-expansive transition correspondence; uniform convergence/value at every initial state. |
| Source alignment | No formalization. Compact-dynamics and stochastic-game modules are only potential adapters. |
| Lean destination | `Math/DynamicProgramming/NonexpansiveUniformValue.lean`, followed by a one-player stochastic-game adapter |
| Acceptance and consumer | Recover finite deterministic examples and expose failure of directed non-expansiveness on candidate certificate relations. |
| Discrepancies | The JEMS/arXiv theorem numbering differs; this is not a multiplayer Nash theorem. |

See [`10-zero-sum-value.md`](../../docs/uniform-equilibrium/references/10-zero-sum-value.md).
Its current program value is a lift-or-failure interface: if a proposed compact
certificate dynamic satisfies the directed matching property, Renault supplies
a one-player uniform-value theorem; failure locates the missing strategic
transport. No multiplayer conclusion follows automatically.
