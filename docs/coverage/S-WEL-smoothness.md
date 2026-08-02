# S-WEL: smoothness and robust welfare bounds

Title: Generic smoothness and robust welfare bounds
Family ID: S-WEL
Pinned root: `GameTheory/Concepts/Welfare/Smoothness.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `9e35ab1`
Canonical destination: `GameTheory.Core.Welfare`; `GameTheory.Core.RobustWelfare`
Domain contract / decision: EXP-052/EXP-053/D24; aggregate expected utility is a Core operation
Owner: post-architecture welfare and congestion wave
Status: complete; 4/4 declarations adapted
Last verified: 2026-08-02

The pure smoothness definition and its Nash consequence belong at the lowest
sufficient Core layer: aggregate canonical expected utility and canonical
profile updates.  The robust results use the canonical `FinDist`
expected-social-welfare/CCE bridge: `UtilityGame.expectedSocialWelfare` and
`expectedSocialWelfare_eq_sum` provide the reusable finite-law aggregate, and
the existing epsilon-CCE/CCE predicates provide the equilibrium hypotheses.
EXP-053 validates this route without finite profile or outcome assumptions and
without recreating the predecessor's `PMF` surface.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Concepts/Welfare/Smoothness.lean` | `IsSmooth` | def | adapt | `GameTheory.UtilityGame.IsSmooth` | current `GameTheory/Core/Welfare.lean`; focused welfare build | Same unilateral-deviation inequality over canonical `Profile.update` and expected utility. |
| same | `IsSmooth.nash_bound` | theorem | adapt | `GameTheory.UtilityGame.IsSmooth.nash_bound` | current welfare source; focused welfare build | Same division-free pure Nash welfare inequality. |
| same | `IsSmooth.epsilonCoarseCorrelated_bound` | theorem | adapt | `GameTheory.UtilityGame.IsSmooth.epsilonCoarseCorrelated_bound` | EXP-053; current `GameTheory/Core/RobustWelfare.lean`; focused welfare build | Uses canonical `FinDist` expected social welfare and existing epsilon-CCE; no finite profile or outcome assumptions. |
| same | `IsSmooth.coarseCorrelated_bound` | theorem | adapt | `GameTheory.UtilityGame.IsSmooth.coarseCorrelated_bound` | EXP-053; current robust-welfare source; focused welfare build | Exact robust bound over the same canonical finite-law route and existing CCE. |

Disposition count: 4 adapt.

Attribution: the smoothness inequality and Nash squeeze are recovered from the
pinned file.  The successor adapts them to `UtilityGame`, `Profile.update`, and
the canonical expected-utility API.  The robust results now use that reusable
consumer-facing finite-distribution welfare home rather than retaining `PMF`
or finite-outcome boilerplate.

Validation:

```text
lake build GameTheory.Core.Welfare GameTheory.Core.RobustWelfare
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
git diff --check
```
