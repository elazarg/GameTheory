# M-AUCT: all-pay recovery

Title: All-pay auction arithmetic
Family ID: M-AUCT
Pinned root: `GameTheory/Auctions/AllPay.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `8239c18`
Canonical destination: `GameTheory.Mechanism.Auction`
Domain contract / decision: D4-D5; opt-in mature mechanism-design domain
Owner: post-architecture breadth wave
Status: complete; 5 declarations reviewed
Last verified: 2026-08-02

The pinned file is an arithmetic lemma family, not a formal all-pay allocation
or equilibrium model.  Its successor therefore remains a minimal leaf module:
it exposes the exact real inequalities without importing game or equilibrium
definitions.

| Pinned path | Declaration | Kind | Disposition | Successor declaration | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Auctions/AllPay.lean` | `allPay_overbid_unprofitable` | theorem | adapt | `GameTheory.Mechanism.Auction.allPay_overbid_unprofitable` | focused build | Both win and loss expressions are negative after overbidding a nonnegative prize. |
| same | `allPay_winner_profit_of_lt` | theorem | adapt | `GameTheory.Mechanism.Auction.allPay_winner_profit_of_lt` | focused build | Below-value winner payoff is positive. |
| same | `allPay_winner_profit` | theorem | retired | `GameTheory.Mechanism.Auction.allPay_winner_profit_of_lt` | source comparison; focused build | Compatibility wrapper with an unused positive-bid hypothesis; its full mathematical conclusion is the surviving stronger theorem. |
| same | `allPay_rent_dissipation` | theorem | adapt | `GameTheory.Mechanism.Auction.allPay_rent_dissipation` | focused build | Two positive bids reduce the displayed aggregate below the prize. |
| same | `allPay_symmetric_negative` | theorem | adapt | `GameTheory.Mechanism.Auction.allPay_symmetric_negative` | focused build | Above-half symmetric fair-tie payoff is negative. |

Disposition count: 4 adapt; 1 retired.

Attribution: theorem statements and their linear-arithmetic proof shape are
recovered from the pinned all-pay file.  The successor places the isolated
facts below the opt-in mechanism namespace and deliberately does not claim a
formal allocation, tie-breaking, dominance, or equilibrium theorem.

Validation:

```text
lake build GameTheory.Mechanism.AllPay
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
git diff --check
```
