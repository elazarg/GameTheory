# M-AUCT: Basic sealed-bid auction recovery

Title: Basic sealed-bid auction recovery
Family ID: M-AUCT
Pinned roots: `GameTheory/Auctions/Basic.lean`; `GameTheory/Auctions/Vickrey.lean`; `GameTheory/Auctions/FirstPrice.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `f04e404`
Canonical destination: `GameTheory.Mechanism.Auction`, opt-in through `GameTheory.Mechanism`
Domain contract / decision: D4; `Languages.Mechanism` direct-revelation probe
Owner: Post-architecture Wave 2 / mature mechanism-design recovery
Status: complete; 28/28 declarations reviewed
Last verified: 2026-08-02

This package recovers the pinned basic auction mathematics on the canonical
`GameForm`, `UtilityGame`, `Profile.update`, `IsDominant`, and `IsNash`
surfaces.  It deliberately does not re-export from `GameTheory.lean`.

The Vickrey result is a payoff-only strict-winner presentation: a bidder earns
value less the largest other bid exactly when strictly highest, and receives
zero on a tie.  It proves dominance but does not represent allocation, revenue,
or a tie rule.  The first-price result instead faithfully uses an arbitrary
highest-bid maximizer, as did the pinned source, so its no-dominant-bid theorem
also covers a singleton bidder carrier.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Auctions/Basic.lean` | `maxOtherBid` | def | adapt | `GameTheory.Mechanism.Auction.maxOtherBid` | focused `lake build GameTheory.Mechanism.Auction` | Finite maximum excluding the named bidder, formulated on canonical bid profiles. |
| same | `maxOtherBid_update_self` | theorem | adapt | `maxOtherBid_update_self` | focused build | Uses only `Profile.update`; the own bid is absent from the maximum. |
| same | `QuasiLinear` | structure | adapt | `QuasiLinear` | focused build | Structure is carried by `UtilityGame`, not obsolete `KernelGame`. |
| same | `IsExPostIR` | def | adapt | `QuasiLinear.IsExPostIR` | focused build | Same valuation/payment inequality. |
| same | `NoPosTransfers` | def | adapt | `QuasiLinear.NoPositiveTransfers` | focused build | Renamed to state the nonnegative-payment convention explicitly. |
| same | `IsEfficient` | def | adapt | `QuasiLinear.IsEfficient` | focused build | Finite aggregation remains operation-local. |
| same | `StrongBudgetBalanced` | def | adapt | `QuasiLinear.IsStronglyBudgetBalanced` | focused build | Renamed, same total-transfer condition. |
| same | `auctionGame` | def | adapt | `auctionGame` | focused build | Deterministic canonical `UtilityGame` constructor. |
| same | `auctionGame_eu` | theorem | adapt | `auctionGame_expectedUtility` | focused build | Expected utility of the pure play law is valuation less payment. |
| same | `auctionGame_quasiLinear` | def | adapt | `auctionGame_quasiLinear` | focused build | Canonical witness for the generic constructor only. |
| same | `auctionGame_ic_isNash` | theorem | adapt | `auctionGame_ic_isNash`; `IsDominantProfile.isNash` | focused build | The source-shaped pointwise IC premise is packaged through the canonical dominance-to-Nash theorem, not a second EU-specific solution concept. |
| `GameTheory/Auctions/Vickrey.lean` | `vickreyPayoff` | def | adapt | `secondPricePayoff` | focused build | Strict-winner payoff-only specialization, documented above. |
| same | `vickrey_truthful_dominant` | theorem | adapt | `secondPrice_truthful_payoff_ge` | focused build | Exact pointwise finite-bidder truthful-payoff inequality, using canonical profile updates. |
| same | `vickreyGame` | def | adapt | `secondPriceGame` | focused build | Canonical deterministic `UtilityGame`. |
| same | `vickrey_truthful_isDominant` | theorem | adapt | `secondPrice_truthful_isDominant` | focused build | The old raw EU predicate is the canonical `IsDominant` under `euPreference`. |
| same | `vickrey_truthful_isNash` | theorem | adapt | `secondPrice_truthful_isNash` | focused build | Derived by `IsDominantProfile.isNash`. |
| `GameTheory/Auctions/FirstPrice.lean` | `maxBid` | def | adapt | `maxBid` | focused build | Maximum on a nonempty finite canonical bid profile. |
| same | `exists_maxBid` | lemma | adapt | `exists_maxBid` | focused build | Finite supremum attainment. |
| same | `winner` | def | adapt | `winner` | focused build | Arbitrary highest-bid tie breaker, as in the pinned source. |
| same | `bid_winner_eq_maxBid` | lemma | adapt | `bid_winner_eq_maxBid` | focused build | Choice specification. |
| same | `bid_le_bid_winner` | lemma | adapt | `bid_le_bid_winner` | focused build | Supremum bound. |
| same | `eq_winner_of_bid_gt` | lemma | adapt | `eq_winner_of_bid_gt` | focused build | Strict highest bid forces the selected maximizer. |
| same | `firstPricePayoff` | def | adapt | `firstPricePayoff` | focused build | Winner pays own bid; tied winner is selected arbitrarily. |
| same | `firstPricePayoff_winner` | lemma | adapt | `firstPricePayoff_winner` | focused build | ITE winner branch. |
| same | `firstPricePayoff_loser` | lemma | adapt | `firstPricePayoff_loser` | focused build | ITE loser branch. |
| same | `firstPriceGame` | def | adapt | `firstPriceGame` | focused build | Canonical deterministic `UtilityGame`. |
| same | `firstPrice_no_dominant_strategy_ofEU` | theorem | subsumed | `firstPrice_not_isDominant` | focused build | Raw `ofEU` wrapper disappears; its exact inequality is the canonical dominance refutation. |
| same | `firstPrice_no_dominant_strategy` | theorem | adapt | `firstPrice_not_isDominant` | focused build | Every bid is defeated by shading one unit while still strictly winning. |

## Validation

```text
lake build GameTheory.Mechanism.Auction GameTheory.Mechanism
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
rg -n "KernelGame|PMF|Function\.update|sorry|admit|axiom|Fintype\.ofFinite|open Classical" GameTheory/Mechanism.lean GameTheory/Mechanism/Auction.lean
```

The focused build and coverage audit passed.  The forbidden-source scan found
no matches: the auction leaf imports the canonical response core directly,
while the opt-in coordinated root is the only layer that also imports the
direct-revelation mechanism language.  The integrated gate records
`TRANSPORT_MECHANISM_SOURCE=0`; `#print axioms` for generic IC-to-Nash,
second-price dominance/Nash, and first-price non-dominance reports only
`propext`, `Classical.choice`, and `Quot.sound`.
