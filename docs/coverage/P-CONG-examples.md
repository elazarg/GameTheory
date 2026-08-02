# P-CONG: Pigou and Braess routing examples

Title: Canonical Pigou and Braess congestion witnesses
Family ID: P-CONG
Pinned root: `GameTheory/Congestion/Examples.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `9e35ab1`
Canonical destination: `GameTheory.Congestion`; `GameTheory.CongestionGame`
Domain contract / decision: EXP-052/D24; opt-in congestion examples over one Nash surface
Owner: post-architecture welfare and congestion wave
Status: complete; 17 declarations reviewed
Last verified: 2026-08-02

The two finite routing witnesses are recovered exactly as canonical congestion
games.  Their cost calculations, affine certificate, social-optimum witness,
and Nash/non-Nash statements retain the pinned mathematical payload while
changing the obsolete `KernelGame` shell to `GameForm`, expected-utility
preference, and `Profile.update`.  No result here depends on the deferred
finite-law welfare/CCE gate: these are pure-profile examples.
The additional successor theorem `pigou_socialCost_nash_le` names the pinned
file's anonymous application of the generic affine bound, so the concrete
example visibly exercises the D24 bridge.

| Pinned path | Declaration | Kind | Disposition | Successor declaration | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Congestion/Examples.lean` | `congestion_two` | theorem | adapt | `GameTheory.CongestionGame.congestion_two` | focused congestion examples build | Same two-player load decomposition. |
| same | `pigou` | abbrev | adapt | `GameTheory.Congestion.pigou` | focused build | Same two-edge congestion instance. |
| same | `pigou_isAffine` | theorem | adapt | `GameTheory.Congestion.pigou_isAffine` | focused build | Same nonnegative affine certificate. |
| same | `pigou_both_isNash` | theorem | adapt | `GameTheory.Congestion.pigou_both_isNash` | focused build | Same all-variable-edge equilibrium over canonical `IsNash`. |
| same | `pigou_socialCost_both` | theorem | adapt | `GameTheory.Congestion.pigou_socialCost_both` | focused build | Same cost-four calculation. |
| same | `pigou_socialCost_split` | theorem | adapt | `GameTheory.Congestion.pigou_socialCost_split` | focused build | Same cost-three calculation. |
| same | `pigou_split_optimal` | theorem | adapt | `GameTheory.Congestion.pigou_split_optimal` | focused build | Same finite profile enumeration establishing optimality. |
| same | `pigou_poa_witness` | theorem | adapt | `GameTheory.Congestion.pigou_poa_witness` | focused build | Same `4 / 3` lower-bound witness. |
| same | `braessDelay` | abbrev | adapt | `GameTheory.Congestion.braessDelay` | focused build | Same load-dependent and constant delay function. |
| same | `braessRestricted` | abbrev | adapt | `GameTheory.Congestion.braessRestricted` | focused build | Same two-route restricted network. |
| same | `braessAugmented` | abbrev | adapt | `GameTheory.Congestion.braessAugmented` | focused build | Same shortcut-augmented network. |
| same | `braessRestricted_split_isNash` | theorem | adapt | `GameTheory.Congestion.braessRestricted_split_isNash` | focused build | Same restricted-network split equilibrium. |
| same | `braessRestricted_socialCost_split` | theorem | adapt | `GameTheory.Congestion.braessRestricted_socialCost_split` | focused build | Same cost-seven calculation. |
| same | `braessAugmented_both_isNash` | theorem | adapt | `GameTheory.Congestion.braessAugmented_both_isNash` | focused build | Same shortcut equilibrium. |
| same | `braessAugmented_socialCost_both` | theorem | adapt | `GameTheory.Congestion.braessAugmented_socialCost_both` | focused build | Same cost-eight calculation. |
| same | `braessAugmented_split_not_isNash` | theorem | adapt | `GameTheory.Congestion.braessAugmented_split_not_isNash` | focused build | Same strict shortcut-deviation counterexample. |
| same | `braess_socialCost_increases` | theorem | adapt | `GameTheory.Congestion.braess_socialCost_increases` | focused build | Same Braess-paradox strict cost comparison. |

Disposition count: 17 adapt.

Attribution: the pinned file supplies the two-player load identity, both
networks, their literal costs, and all finite enumeration proof patterns.  The
successor translates only the surrounding semantics from `KernelGame` and raw
function update to the canonical deterministic game form and `Profile.update`.

Validation:

```text
lake build GameTheory.Congestion.Examples
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
git diff --check
```
