# P-CONG: affine congestion price of anarchy

Title: Affine congestion smoothness and pure price of anarchy
Family ID: P-CONG
Pinned root: `GameTheory/Congestion/AffinePoA.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `9e35ab1`
Canonical destination: `GameTheory.CongestionGame`; `GameTheory.Core.Welfare`
Domain contract / decision: EXP-052/D24; opt-in congestion over canonical Core welfare
Owner: post-architecture welfare and congestion wave
Status: in progress; 8/8 declarations reviewed, 1 deferred to the finite-law CCE gate
Last verified: 2026-08-02

The affine load calculation and pure `5 / 2` price-of-anarchy consequence are
recovered over the canonical congestion game, profile update, and
`UtilityGame` welfare conventions.  The old robust correlated theorem is not
silently weakened or subsumed: it needs the same named **canonical `FinDist`
expected-social-welfare/CCE gate** as generic smoothness, including a finite
law interpretation of expected social cost.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Congestion/AffinePoA.lean` | `IsAffine` | structure | adapt | `GameTheory.CongestionGame.IsAffine` | current `GameTheory/Congestion/AffinePoA.lean`; focused congestion build | Same nonnegative affine delay certificate. |
| same | `IsAffine.delay_mono` | theorem | adapt | `GameTheory.CongestionGame.IsAffine.delay_mono` | current affine source; focused build | Same monotonicity consequence, with finiteness omitted from the theorem. |
| same | `ck_inequality` | theorem | adapt | `GameTheory.CongestionGame.ck_inequality` | current affine source; focused build | Same integer-load Christodoulou--Koutsoupias inequality. |
| same | `sum_deviation_cost_le` | theorem | adapt | `GameTheory.CongestionGame.sum_deviation_cost_le` | current affine source; focused build | Same cost-form smoothness calculation using canonical unilateral updates. |
| same | `socialWelfare_toKernelGame` | theorem | adapt | `GameTheory.CongestionGame.socialWelfare_toUtilityGame` | current affine source; focused build | Obsolete kernel-game wrapper becomes the canonical utility-game identity. |
| same | `isSmooth_of_isAffine` | theorem | adapt | `GameTheory.CongestionGame.isSmooth_of_isAffine` | current affine source; focused build | Affine costs give `(5 / 3, -1 / 3)` smoothness under negated-cost utility. |
| same | `socialCost_nash_le` | theorem | adapt | `GameTheory.CongestionGame.socialCost_nash_le` | current affine source; focused build | Same pure Nash `5 / 2` social-cost bound. |
| same | `correlated_socialCost_le` | theorem | deferred | canonical `FinDist` expected-social-welfare/CCE gate | source comparison; P-CONG/S-WEL gate | Reopen only after generic robust smoothness supplies the finite-law CCE welfare bound; it is not a pure-Nash corollary. |

Disposition count: 7 adapt, 1 deferred.

Attribution: the pinned source supplies the affine certificate, integral pairing
argument, common-support aggregation, sign translation, and pure price bound.
The successor changes only the obsolete `KernelGame` representation to the
canonical `UtilityGame`.  The correlated bound remains an explicit downstream
obligation of the shared finite-law welfare/CCE gate.

Validation:

```text
lake build GameTheory.Core.Welfare GameTheory.Congestion.AffinePoA
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
git diff --check
```
