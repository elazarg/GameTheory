# D-REPEAT: deterministic uniform equilibrium

Title: Long-run average payoff and stationary uniform equilibrium
Family ID: D-REPEAT
Pinned roots: `GameTheory/Concepts/Repeated/Basic.lean`; `GameTheory/Concepts/Repeated/Uniform.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `ba1f534`
Canonical destination: `GameTheory.UtilityGame` in `Repeated.Basic` and `Repeated.Uniform`
Domain contract / decision: D5, EXP-064; post-architecture D-REPEAT BFS gate
Owner: Wave 3 / deterministic repeated play
Status: complete; all 8 declarations in the bounded long-run/uniform slice adapted with no deferred rows
Last verified: 2026-08-09

The successor keeps long-run payoff as coordinatewise convergence of finite
averages over the deterministic public-profile path.  Finite-horizon
approximate Nash is not copied as a raw second equilibrium predicate: it is
defined through canonical `IsεNash` on the existing repeated form with a
finite-average utility, and its inequality theorem makes that specialization
transparent.  No probability law over an infinite realized path is added.
The Prisoner's Dilemma fixture proves stationary defection uniform and shows
stationary cooperation fails one-stage approximate Nash at slack one.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Concepts/Repeated/Basic.lean` | `HasLongRunAveragePayoff` | def | adapt | `UtilityGame.HasLongRunAveragePayoff` | focused Repeated build | Coordinatewise convergence of canonical finite averages. |
| same | `hasLongRunAveragePayoff_stationaryRepeatedProfile` | theorem | adapt | same name | focused Repeated build | Stationary finite averages are eventually constant after horizon zero. |
| `GameTheory/Concepts/Repeated/Uniform.lean` | `IsεFiniteRepeatedNash` | def | adapt | `UtilityGame.IsεFiniteRepeatedNash` | canonical-specialization theorem | Defined through `IsεNash`; `isεFiniteRepeatedNash_iff` exposes the source inequality. |
| same | `IsUniformεEquilibrium` | def | adapt | `UtilityGame.IsUniformεEquilibrium` | focused Repeated build | One threshold works for every longer horizon. |
| same | `IsUniformEquilibrium` | def | adapt | `UtilityGame.IsUniformEquilibrium` | focused Repeated build | Requires both a limiting average and every positive tolerance. |
| same | `IsεFiniteRepeatedNash.mono` | theorem | adapt | same name | focused Repeated build | Delegates to canonical `IsεNash.mono`. |
| same | `IsUniformεEquilibrium.mono` | theorem | adapt | same name | focused Repeated build | Reuses the same horizon threshold. |
| same | `stationaryRepeatedProfile_isUniformEquilibrium_of_isNash` | theorem | adapt | same name | focused Repeated build and hostile fixture | Stage Nash bounds every history-dependent repeated deviation stage by stage. |

Attribution: the predecessor supplied the long-run average and uniform
equilibrium theorem family.  The successor preserves the deterministic-path
mathematics while factoring finite-horizon rationality through the canonical
approximate-Nash layer and using `Profile.update` exclusively.

This bounded ledger does not close D-REPEAT.  APS decomposition,
self-generation, public randomization, monitoring rank/incentive theory, and
the broader monitored uniform family remain separate BFS gates.  None requires
an infinite-path probability law merely because this deterministic uniform
slice uses ordinary real-sequence convergence.

The long-run stationary theorem, finite-horizon specialization, stationary
uniform theorem, and both Prisoner's Dilemma fixture theorems depend only on
`propext`, `Classical.choice`, and `Quot.sound`.  Source checks find no raw
`Function.update`, source transport, placeholder, custom axiom, native
evaluation, or build-output command.

Validation:

```text
lake build GameTheory.Repeated.Basic GameTheory.Repeated.Uniform GameTheory.Tests.RepeatedUniform GameTheory.Repeated
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected -SkipReachability
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
lake build
git diff --check
```
