# P-CONG: affine congestion price of anarchy

Title: Affine congestion smoothness and pure price of anarchy
Family ID: P-CONG
Pinned root: `GameTheory/Congestion/AffinePoA.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `9e35ab1`
Canonical destination: `GameTheory.CongestionGame`; `GameTheory.Core.RobustWelfare`
Domain contract / decision: EXP-052/EXP-053/D24; opt-in congestion over canonical Core welfare
Owner: post-architecture welfare and congestion wave
Status: complete; 8/8 declarations adapted
Last verified: 2026-08-02

The affine load calculation and pure `5 / 2` price-of-anarchy consequence are
recovered over the canonical congestion game, profile update, and
`UtilityGame` welfare conventions.  Its robust correlated theorem uses the
same canonical `FinDist` expected-social-welfare/CCE bridge validated by
EXP-053, including a finite-law interpretation of expected social cost.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Congestion/AffinePoA.lean` | `IsAffine` | structure | adapt | `GameTheory.CongestionGame.IsAffine` | current `GameTheory/Congestion/AffinePoA.lean`; focused congestion build | Same nonnegative affine delay certificate. |
| same | `IsAffine.delay_mono` | theorem | adapt | `GameTheory.CongestionGame.IsAffine.delay_mono` | current affine source; focused build | Same monotonicity consequence, with finiteness omitted from the theorem. |
| same | `ck_inequality` | theorem | adapt | `GameTheory.CongestionGame.ck_inequality` | current affine source; focused build | Same integer-load Christodoulou--Koutsoupias inequality. |
| same | `sum_deviation_cost_le` | theorem | adapt | `GameTheory.CongestionGame.sum_deviation_cost_le` | current affine source; focused build | Same cost-form smoothness calculation using canonical unilateral updates. |
| same | `socialWelfare_toKernelGame` | theorem | adapt | `GameTheory.CongestionGame.socialWelfare_toUtilityGame` | current affine source; focused build | Obsolete kernel-game wrapper becomes the canonical utility-game identity. |
| same | `isSmooth_of_isAffine` | theorem | adapt | `GameTheory.CongestionGame.isSmooth_of_isAffine` | current affine source; focused build | Affine costs give `(5 / 3, -1 / 3)` smoothness under negated-cost utility. |
| same | `socialCost_nash_le` | theorem | adapt | `GameTheory.CongestionGame.socialCost_nash_le` | current affine source; focused build | Same pure Nash `5 / 2` social-cost bound. |
| same | `correlated_socialCost_le` | theorem | adapt | `GameTheory.CongestionGame.correlated_socialCost_le` | EXP-053; current `GameTheory/Congestion/AffinePoA.lean`; focused congestion build | Uses canonical finite-support expected social cost and the generic CCE smoothness bound, with no per-strategy finiteness. |

Disposition count: 8 adapt.

Attribution: the pinned source supplies the affine certificate, integral pairing
argument, common-support aggregation, sign translation, and pure price bound.
The successor changes only the obsolete `KernelGame` representation to the
canonical `UtilityGame`.  The correlated bound is now discharged through the
shared finite-law welfare/CCE gate.

Validation:

```text
lake build GameTheory.Core.RobustWelfare GameTheory.Congestion.AffinePoA
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
git diff --check
```
