# M-AUCT: VCG recovery

Title: Vickrey--Clarke--Groves mechanisms
Family ID: M-AUCT
Pinned root: `GameTheory/Auctions/VCG.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `21c49fd`
Canonical destination: `GameTheory.Mechanism.Auction.VCGSetup`
Domain contract / decision: D4-D5; opt-in mature mechanism-design domain
Owner: post-architecture breadth wave
Status: complete; 9 declarations reviewed
Last verified: 2026-08-02

The VCG data is recovered without storing finite enumeration or decidable
equality.  Efficient allocation and report-independent Groves offsets appear
as explicit certificates on the truthfulness theorems that consume them.  The
pinned prior-free informational-game wrapper is adapted to a deterministic
`UtilityGame` for each true-type profile; ex-post equilibrium is ordinary
expected-utility Nash for every such profile, not a second solution concept.

| Pinned path | Declaration | Kind | Disposition | Successor declaration | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Auctions/VCG.lean` | `VCGSetup` | structure | adapt | `GameTheory.Mechanism.Auction.VCGSetup` | focused Mechanism build | Capability-free data; efficiency and offset independence move to theorem premises. |
| same | `vcgPayment` | def | adapt | `VCGSetup.vcgPayment` | focused build | Groves offset less reported welfare of all other players. |
| same | `trueUtility` | def | adapt | `VCGSetup.trueUtility` | focused build | True valuation less Groves payment. |
| same | `trueUtility_eq` | theorem | adapt | `VCGSetup.trueUtility_eq` | focused build | Same welfare-minus-offset decomposition. |
| same | `vcg_truthful` | theorem | adapt | `VCGSetup.vcg_truthful` | focused build | Strengthened to arbitrary fixed opposing reports; uses canonical `Profile.update`. |
| same | `toInformationalGame` | def | adapt | `VCGSetup.toUtilityGame` | focused build | A fixed true-type profile induces the canonical deterministic report game. |
| same | `truthfulStrategy` | def | adapt | `VCGSetup.truthfulStrategy` | focused build | Dependent identity report strategy, without a parallel informational-game carrier. |
| same | `toInformationalGame_play_truthful` | theorem | adapt | `VCGSetup.toUtilityGame_play_truthful` | focused build | Truthful reports produce the point mass at the true-type profile. |
| same | `truthfulStrategy_isExPostEq` | theorem | adapt | `VCGSetup.truthfulStrategy_isExPostNash` | focused build | Ex-post means canonical Nash for every true-type profile. |

Disposition count: 9 adapt.

Attribution: the setup, Groves payment, utility decomposition, efficient-welfare
proof, dependent truthful strategy, and ex-post result are recovered from the
pinned file.  The successor removes the obsolete informational-game equilibrium
surface while retaining its full prior-free mathematical content.  No
combinatorial-auction allocation infrastructure is required: `alloc` remains
an abstract chosen efficient rule, so its tie-breaking semantics are preserved
exactly rather than reconstructed.

Validation:

```text
lake build GameTheory.Mechanism.VCG GameTheory.Mechanism
rg -n "KernelGame|PMF|Function\.update|sorry|admit|axiom|Fintype\.ofFinite|open Classical|GameTheory\.Analysis" GameTheory/Mechanism/VCG.lean
git diff --check
```
