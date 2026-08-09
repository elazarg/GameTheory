# S-FOUND: response dynamics and team utility seed

Title: Improving steps and identical-interest expected utility
Family ID: S-FOUND
Pinned roots: `GameTheory/Core/GameProperties.lean`,
`GameTheory/Concepts/Foundations/BestResponseDynamics.lean`, and
`GameTheory/Concepts/Classes/TeamGame.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `a829d9d`
Canonical destination: `GameTheory.Core.Response`; `GameTheory.Core.Utility`; `GameTheory.Core.Welfare`
Domain contract / decision: D4-D5; EXP-052/D24
Owner: Wave 2 / foundations recovery
Status: in progress; 9 bounded declarations reviewed
Last verified: 2026-08-09

This partial ledger claims only declarations directly discharged by the generic
response and utility primitives recovered with the potential-game slice. The
structural `ImprovingDeviation`, approximate-equilibrium dynamics, symmetric
games, and remaining foundation rows stay unreviewed.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or chain | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Concepts/Foundations/BestResponseDynamics.lean` | `ImprovingStep` | def | adapt | `GameTheory.ImprovingStep` | focused Core.Response build | Uses canonical `Profile.update` and expected utility directly. |
| same | `not_isNash_iff_exists_improvingStep` | theorem | adapt | `GameTheory.not_isNash_iff_exists_improvingStep` | focused Core.Response build | Failure of ordinary expected-utility `IsNash` is exactly an outgoing improvement edge. |
| same | `strictNash_deviation_lt` | theorem | subsumed | `GameTheory.IsStrictNash` | focused Core.Response build | The source theorem merely restates the successor definition's elimination rule. |
| `GameTheory/Core/GameProperties.lean` | `IsTeamGame` | def | adapt | `GameTheory.IsTeamGame` | focused Core.Utility build | Identical interests are a property of utility itself, independent of potential and zero-sum consumers. |
| same | `socialWelfare` | def | adapt | `GameTheory.UtilityGame.socialWelfare` | EXP-052/D24; focused Core.Welfare build | Same finite-player sum of canonical expected utilities, now on `UtilityGame` without the obsolete kernel hub. |
| same | `IsIndividuallyRational` | def | adapt | `GameTheory.IsIndividuallyRational` | stochastic hostile reservation fixture | Fixed-profile IR uses canonical expected utility and an explicit reservation vector; ex-post mechanism participation and cooperative acceptability remain separate concepts. |
| `GameTheory/Concepts/Classes/TeamGame.lean` | `IsTeamGame.eu_eq` | theorem | subsumed | `GameTheory.IsTeamGame.expectedUtility_eq` | focused Core.Utility build | The successor proves equality for every finite outcome law, hence in particular every played profile law. |
| same | `IsTeamGame.eu_eq_update` | theorem | subsumed | `GameTheory.IsTeamGame.expectedUtility_eq` | focused Core.Utility build | The same generic law theorem applies after any canonical profile update. |
| same | `IsTeamGame.nash_deviation_nonimproving` | theorem | adapt | `GameTheory.IsTeamGame.isNash_deviation_nonimproving` | focused Core.Utility build | The named successor transports the canonical Nash inequality from the deviator to any player using team equality before and after the update. |

Disposition count: 6 adapt; 3 subsumed.

Attribution: the pinned dynamics file supplies the outgoing improvement-edge
presentation and its Nash complement; the pinned team file supplies the lift
from identical outcome utilities to equal expected utilities. The successor
generalizes the team result to arbitrary finite laws and keeps the dynamics on
the canonical static game form. EXP-052 recovers the pinned aggregate welfare
operation directly on the canonical utility bundle.

Validation:

```text
lake build GameTheory.Core.Utility GameTheory.Core.Response GameTheory.Core.Welfare
```
