# D-REPEAT public-monitoring equilibrium waist

Pinned source: `reference/GameTheory-v1/` at
`a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`, principally
`GameTheory/Concepts/Repeated/{Monitoring,MonitoringDiscounted}.lean`.

Status: complete for discounted public continuation values, canonical
perfect-public equilibrium, and the bounded exact one-shot-deviation
principle.  D-REPEAT remains partial for the separate rank,
self-generation, approximate-allowance, and uniform families.

| Pinned family | Disposition | Successor evidence | Design result |
|---|---|---|---|
| finite public histories and continuations | adapt | `Repeated/MonitoringContinuation.lean` | List iteration gives arbitrary typed-history continuations without public transports. |
| one-shot and truncated public deviations | adapt | `Repeated/MonitoringContinuation.lean` | Uses the single canonical `Profile.update`; no direct `Function.update`. |
| monitored stage expected utility and tower law | adapt | `Repeated/MonitoringPayoff.lean` | `FinDist.expect` removes v1's artificial boundedness premise from the finite-support tower law. |
| discounted public and continuation payoffs; Bellman equation | adapt | `Repeated/MonitoringDiscounted.lean` | Stagewise finite expectation followed by an ordinary real series; no infinite realized-path law. |
| discounted public Nash | subsume | `IsDiscountedPublicNash`, `IsεDiscountedPublicNash` | Transparent specializations of canonical `IsNash` with `euPreference` / `euPreferenceWithin`, not bespoke inequalities. |
| PPE at every continuation | adapt | `IsPerfectPublicEquilibrium`, `IsεPerfectPublicEquilibrium` | Quantifies uniformly over every typed finite history, improving v1's root/nonempty workaround and including zero-probability histories. |
| exact one-shot-deviation principle | adapt | `Repeated/MonitoringOneShot.lean` | Finite-truncation induction plus dominated convergence under `0 ≤ discount < 1` and per-player bounded stage payoff. |
| finite noisy regression | strengthen | `Tests/MonitoringEquilibrium.lean` | Two-player coordination, branch-dependent noisy kernels, strict unilateral loss, explicit zero-mass `[true,false]` continuation, actual PPE. |
| approximate accumulated allowances | defer after gate | pinned `MonitoringDiscounted.lean` | Useful breadth, but not required for the exact architecture theorem. |
| garbling, finite-average/uniform, rank, self-generation | defer by dependency | remaining D-REPEAT files | Resume as BFS theorem harvesting against the now-validated monitoring waist. |

Validation is owned by EXP-064 in `docs/ExperimentLog.md`.  The final theorem
and Bellman recursion use only `propext`, `Classical.choice`, and `Quot.sound`.
