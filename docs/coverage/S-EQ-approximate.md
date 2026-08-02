# S-EQ: approximate Nash

Title: Approximate expected-utility Nash
Family ID: S-EQ
Pinned root: `GameTheory/Concepts/Equilibrium/ApproximateNash.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `c3197a2`
Canonical destination: `GameTheory.Core.Approximate`
Domain contract / decision: D4-D5
Owner: post-architecture breadth wave
Status: complete; 7 declarations reviewed
Last verified: 2026-08-02

The legacy `KernelGame` predicates become transparent specializations of the
one canonical `GameForm` equilibrium and response predicates.  The successor
uses `Profile.update` throughout and introduces no capability or transport
surface.

| Pinned path | Declaration | Kind | Disposition | Successor declaration | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Concepts/Equilibrium/ApproximateNash.lean` | `IsεNash` | def | adapt | `GameTheory.IsεNash` | focused Core.Approximate build | Transparent `IsNash` specialization with the slack preference. |
| same | `IsεBestResponse` | def | adapt | `GameTheory.IsεBestResponse` | focused Core.Approximate build | Transparent canonical `IsBestResponse` specialization. |
| same | `IsεNash.of_isNash` | theorem | adapt | `GameTheory.IsεNash.of_isNash` | focused Core.Approximate build | Nonnegative slack absorbs no-profitable-deviation. |
| same | `isNash_iff_isεNash_zero` | theorem | adapt | `GameTheory.isNash_iff_isεNash_zero` | focused Core.Approximate build | Zero slack is ordinary expected-utility Nash. |
| same | `IsεNash.mono` | theorem | adapt | `GameTheory.IsεNash.mono` | focused Core.Approximate build | Monotone in the allowance. |
| same | `isεNash_iff_εBestResponse` | theorem | adapt | `GameTheory.isεNash_iff_εBestResponse` | focused Core.Approximate build | Reuses canonical Nash/best-response characterization. |
| same | `IsStrictNash.isεNash` | theorem | adapt | `GameTheory.IsStrictNash.isεNash` | focused Core.Approximate build | Strict improvement excludes every genuine deviation; equality is handled through `Profile.update_eq_self`. |

Disposition count: 7 adapt.

Attribution: theorem inventory and the expected-utility inequalities are from
the pinned file.  The successor changes only the obsolete `KernelGame` carrier
to the canonical utility-free form plus separate utility evaluation.

Validation:

```text
lake build GameTheory.Core.Approximate
```
