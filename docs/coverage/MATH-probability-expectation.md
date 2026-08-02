# MATH: finite-support expectation and finite sums

Title: Finite-support expectation commutes with finite indexed sums
Family ID: MATH
Pinned roots: `Math/Probability.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `fce311c`
Canonical destination: `GameTheory.Probability.FinDist`
Domain contract / decision: D2 and EXP-053; canonical finite-support laws
Owner: robust-welfare consumer
Status: complete; 1/1 declaration reviewed
Last verified: 2026-08-02

This demand-driven row records the general expectation identity needed by the
robust-welfare consumer.  The successor theorem is stronger at the carrier
boundary: `FinDist` supplies finite support directly, so neither a finite
sample-space assumption nor `Fintype.ofFinite` is needed.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `Math/Probability.lean` | `expect_sum_comm` | theorem | adapt | `GameTheory.Probability.FinDist.expect_sum_comm` | EXP-053; focused probability and robust-welfare builds | Same finite-index sum/expectation interchange, generalized from finite `PMF` carriers to arbitrary carriers under canonical finite-support laws. |

Disposition count: 1 adapt.

Attribution: the pinned theorem supplies the finite-sum interchange statement.
The successor proof reuses the canonical support sum and changes only the law
representation and the now-unnecessary carrier assumption.

Validation:

```text
lake build GameTheory.Probability.FinDist GameTheory.Core.RobustWelfare
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
git diff --check
```
