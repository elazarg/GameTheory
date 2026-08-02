# P-CONG: congestion-load calculus and Rosenthal potential

Title: Finite-player congestion games and Rosenthal's exact potential
Family ID: P-CONG
Pinned roots: `GameTheory/Congestion/Basic.lean` and
`GameTheory/Congestion/Rosenthal.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `d9ff55e`
Canonical destination: opt-in `GameTheory.Congestion`, over `GameTheory.Core`
Domain contract / decision: D0, D4-D5, D9, D12; static domain package, never
a parallel game/equilibrium hierarchy
Owner: Wave 2 / potential and congestion
Status: complete; 25/25 declarations reviewed
Last verified: 2026-08-02

The successor deliberately removes the predecessor's stored `[Fintype ι]`.
`CongestionGame` carries only resources, dependent strategy carriers, occupied
resource sets, and delays.  `[Fintype ι]` is requested by load and aggregate
operations, and `[DecidableEq ι]` only by unilateral-update theorems and the
canonical potential/equilibrium consequences.  The deterministic presentation
is one `GameSignature`/`GameForm`/`UtilityGame`, with profiles as outcomes,
`FinDist.pure` as play, and negative cost as utility.

The load-calculus module stops at `GameTheory.Core.Utility`; only the Rosenthal
consumer imports `GameTheory.Core.Potential`.  A negative import probe confirms
that `IsExactPotential` is not reachable from `GameTheory.Congestion.Basic`,
and a second confirms that the main `GameTheory` root does not expose the
opt-in `CongestionGame` API.
The profile-level `Finite`/`Nonempty` hypotheses on the consequences remain
usable from the predecessor's pointwise strategy hypotheses by typeclass
inference, while stating exactly the capability the generic potential theorem
needs.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `Congestion/Basic.lean` | `CongestionGame` | structure | adapt | `GameTheory.CongestionGame` | `lake build GameTheory.Congestion` | Drops stored player finiteness; otherwise same mathematical data. |
| same | `Profile` | abbrev | adapt | `GameTheory.CongestionGame.Profile`; `GameTheory.Profile` | focused build | Pure congestion profiles specialize the canonical profile carrier. |
| same | `congestion` | def | adapt | `GameTheory.CongestionGame.congestion` | focused build | Requires `[Fintype ι]` at operation use. |
| same | `usedResources` | def | adapt | `GameTheory.CongestionGame.usedResources` | focused build | Finite union of the profile's resource sets. |
| same | `mem_usedResources` | theorem | adapt | `GameTheory.CongestionGame.mem_usedResources` | focused build | Same occupied-resource characterization. |
| same | `resources_subset_usedResources` | theorem | adapt | `GameTheory.CongestionGame.resources_subset_usedResources` | focused build | Same support inclusion. |
| same | `congestion_eq_zero_of_not_mem_usedResources` | theorem | adapt | `GameTheory.CongestionGame.congestion_eq_zero_of_not_mem_usedResources` | focused build | Same zero-load support fact. |
| same | `playerCost` | def | adapt | `GameTheory.CongestionGame.playerCost` | focused build | Same cost, with finiteness at use. |
| same | `socialCost` | def | adapt | `GameTheory.CongestionGame.socialCost` | focused build | Same total cost. |
| same | `toKernelGame` | def | adapt | `GameTheory.CongestionGame.toGameForm`; `toUtilityGame` | focused build | Replaced obsolete KernelGame wrapper by canonical deterministic form and utility bundle. |
| same | `eu_toKernelGame` | theorem | adapt | `GameTheory.CongestionGame.expectedUtility_toGameForm` | focused build | Expected utility of pure play is negative player cost. |
| same | `congestionWithout` | def | adapt | `GameTheory.CongestionGame.congestionWithout` | focused build | Same other-player load. |
| same | `congestion_decompose` | theorem | adapt | `GameTheory.CongestionGame.congestion_decompose` | focused build | Same load decomposition. |
| same | `congestionWithout_update` | theorem | adapt | `GameTheory.CongestionGame.congestionWithout_update` | focused build | Uses canonical `Profile.update`, never raw function update. |
| same | `congestion_update` | theorem | adapt | `GameTheory.CongestionGame.congestion_update` | focused build | Canonical unilateral-update load equation. |
| same | `congestion_le_congestionWithout_add_one` | theorem | adapt | `GameTheory.CongestionGame.congestion_le_congestionWithout_add_one` | focused build | Same unit-load bound. |
| same | `congestionWithout_le_congestion` | theorem | adapt | `GameTheory.CongestionGame.congestionWithout_le_congestion` | focused build | Same monotonicity bound. |
| same | `sum_players_sum_resources` | theorem | adapt | `GameTheory.CongestionGame.sum_players_sum_resources` | focused build | Same load aggregation identity. |
| same | `sum_congestion_mul_subset` | theorem | adapt | `GameTheory.CongestionGame.sum_congestion_mul_subset` | focused build | Same support-extension identity. |
| same | `socialCost_eq_sum_load_delay` | theorem | adapt | `GameTheory.CongestionGame.socialCost_eq_sum_load_delay` | focused build | Same social-cost decomposition. |
| `Congestion/Rosenthal.lean` | `potential` | def | adapt | `GameTheory.CongestionGame.potential` | `lake build GameTheory.Congestion` | Cumulative delay over occupied resources. |
| same | `isExactPotential` | theorem | adapt | `GameTheory.CongestionGame.isExactPotential` | focused build | Rosenthal identity over canonical expected utility. |
| same | `nash_exists` | theorem | adapt | `GameTheory.CongestionGame.nash_exists` | focused build | Finite nonempty profile space, not stored finite strategies. |
| same | `no_infinite_improving_path` | theorem | adapt | `GameTheory.CongestionGame.no_infinite_improving_path` | focused build | Uses Core's canonical improving-step relation. |
| same | `weaklyAcyclic` | theorem | adapt | `GameTheory.CongestionGame.weaklyAcyclic` | focused build | Uses Core's canonical weak-acyclicity predicate. |

Disposition count: 25 adapt; 0 subsumed; 0 retired; 0 deferred.

Attribution: the pinned Basic file supplies the finite-load counting and
aggregate-sum proof pattern; pinned Rosenthal supplies the common-support
telescoping proof and its potential-game consequences.  The successor adapts
those arguments to `Profile.update`, `FinDist.pure`, expected utility, and the
single Core potential/improvement/Nash vocabulary.

Validation:

```text
lake build GameTheory.Congestion
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
git diff --check
```

The integrated gate records `TRANSPORT_CONGESTION_SOURCE=0`, no unbucketed
files, and no non-reducible literal carrier constructors.  `#print axioms` for
Rosenthal's identity and Nash existence reports only `propext`,
`Classical.choice`, and `Quot.sound`.
