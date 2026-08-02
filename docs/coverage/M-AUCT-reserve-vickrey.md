# M-AUCT: reserve-price Vickrey recovery

Title: Reserve-price Vickrey auction
Family ID: M-AUCT
Pinned root: `GameTheory/Auctions/ReserveVickrey.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `1a1831d`
Canonical destination: `GameTheory.Mechanism.Auction.ReserveVickrey`
Domain contract / decision: D4-D5; opt-in mature mechanism-design domain
Owner: post-architecture breadth wave
Status: complete; 27 declarations reviewed
Last verified: 2026-08-02

The pinned finite single-item reserve Vickrey construction is recovered on the
canonical bid profile, deterministic `UtilityGame`, expected-utility
preference, dominance, and Nash surfaces.  Allocation remains strict-clear:
tied top bids do not allocate.  All finite and equality instances are local to
the operations that require them.

| Pinned path | Declaration | Kind | Disposition | Successor declaration | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Auctions/ReserveVickrey.lean` | `reserveVickreyClearingPrice` | def | adapt | `GameTheory.Mechanism.Auction.ReserveVickrey.reserveVickreyClearingPrice` | focused Mechanism build | Reserve maximum and canonical `maxOtherBid`. |
| same | `reserveVickreyWins` | def | adapt | `reserveVickreyWins` | focused build | Strict threshold, so ties do not clear. |
| same | `reserveVickreyClearingPrice_update_self` | theorem | adapt | `reserveVickreyClearingPrice_update_self` | focused build | Uses `Profile.update`. |
| same | `bid_le_maxOtherBid_of_ne` | theorem | adapt | `bid_le_maxOtherBid_of_ne` | focused build | Finite opposing-bid bound. |
| same | `reserveVickreyWins_unique` | theorem | adapt | `reserveVickreyWins_unique` | focused build | Strict clearing is unique. |
| same | `reserveVickreyAllocation` | def | adapt | `reserveVickreyAllocation` | focused build | `Option` allocation preserves no-sale/tie semantics. |
| same | `allocation_eq_some_iff` | theorem | adapt | `allocation_eq_some_iff` | focused build | Selection iff strict clearing. |
| same | `allocation_eq_none_iff` | theorem | adapt | `allocation_eq_none_iff` | focused build | No selection iff nobody clears. |
| same | `clearingPrice_eq_max_reserve_excluding` | theorem | adapt | `clearingPrice_eq_max_reserve_excluding` | focused build | Definitional threshold law. |
| same | `clearingPrice_lt_bid_of_allocation_eq_some` | theorem | adapt | `clearingPrice_lt_bid_of_allocation_eq_some` | focused build | Winners clear strictly. |
| same | `clearingPrice_le_bid_of_allocation_eq_some` | theorem | adapt | `clearingPrice_le_bid_of_allocation_eq_some` | focused build | Weak consequence of strict clearing. |
| same | `reserveVickreyValue` | def | adapt | `reserveVickreyValue` | focused build | Single-item winner value. |
| same | `reserveVickreyPayment` | def | adapt | `reserveVickreyPayment` | focused build | Only a winner pays their threshold. |
| same | `payment_of_allocation_eq_some` | theorem | adapt | `payment_of_allocation_eq_some` | focused build | Winner payment law. |
| same | `payment_of_allocation_ne_some` | theorem | adapt | `payment_of_allocation_ne_some` | focused build | Nonwinner payment law. |
| same | `payment_le_bid_of_allocation_eq_some` | theorem | adapt | `payment_le_bid_of_allocation_eq_some` | focused build | Winner payment is affordable at their report. |
| same | `reserveVickreyUtility` | def | adapt | `reserveVickreyUtility` | focused build | Quasilinear displayed payoff. |
| same | `utility_winner` | theorem | adapt | `utility_winner` | focused build | Value minus threshold. |
| same | `utility_loser` | theorem | adapt | `utility_loser` | focused build | Nonwinner payoff zero. |
| same | `reserveVickreyUtility_eq_if_wins` | theorem | adapt | `reserveVickreyUtility_eq_if_wins` | focused build | Strict-clear payoff characterization. |
| same | `utility_nonneg` | theorem | adapt | `utility_nonneg` | focused build | Truthful winner/nonwinner nonnegativity. |
| same | `truthful_weakly_dominant` | theorem | adapt | `truthful_weakly_dominant` | focused build | Pointwise truthful payoff comparison. |
| same | `reserveVickreyGame` | def | adapt | `reserveVickreyGame` | focused build | Generic canonical `auctionGame` specialization. |
| same | `reserveVickreyGame_eu` | theorem | adapt | `reserveVickreyGame_expectedUtility` | focused build | Renamed for the canonical expected-utility API. |
| same | `valuation_is_dominant` | theorem | adapt | `valuation_is_dominant` | focused build | Canonical `IsDominant` under `euPreference`. |
| same | `mechanism_isDSIC` | theorem | adapt | `mechanism_isDSIC` | focused build | Pointwise dominance profile. |
| same | `reserveVickrey_truthful_isNash` | theorem | adapt | `reserveVickrey_truthful_isNash` | focused build | Derived by `IsDominantProfile.isNash`. |

Disposition count: 27 adapt.

Attribution: statements and proof structure are recovered from the pinned
reserve-price Vickrey file.  The successor replaces its obsolete `KernelGame`,
raw function update, and raw expected-utility predicates with `UtilityGame`,
`Profile.update`, `euPreference`, `IsDominant`, and `IsNash`.

Validation:

```text
lake build GameTheory.Mechanism.ReserveVickrey GameTheory.Mechanism
rg -n "KernelGame|PMF|Function\.update|sorry|admit|axiom|Fintype\.ofFinite|open Classical" GameTheory/Mechanism/ReserveVickrey.lean
git diff --check
```
