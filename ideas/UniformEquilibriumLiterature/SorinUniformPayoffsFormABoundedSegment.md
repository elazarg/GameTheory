# Sorin's uniform payoff set is a bounded segment

| Field | Value |
| --- | --- |
| Citation of record | Sorin, IJGT 15(2):101--107 (1986), Theorem 2 |
| Source confidence | `PRIMARY_VERIFIED`; secondary numerical cross-check absent |
| Mathematical status | `PROVED` externally |
| Repository / Lean status | `ADAPTED / PARTIAL` |
| Exact scope and quantifiers | In the cited absorbing game, uniform-equilibrium payoffs are exactly `{(a,2(1-a)) : 1/2 <= a <= 2/3}`. |
| Source alignment | The target-free separation/hyperplane direction and discounted-endpoint exclusion are landed; construction of every bounded-segment point is not. |
| Lean destination | `SorinUniformPayoffSegment.lean` for the converse construction, retaining both endpoint bounds |
| Consumer | Regression separating discounted/finite-horizon singleton behavior from the larger uniform payoff set |
| Discrepancies | The bare line `2w1+w2=2` is too large; `(1,0)` and `(0,2)` are not in the source set. |

Do not cite Sorin as a uniform-versus-limiting-average separation: the paper's
`E(infinity)` is the uniform set and does not study a Cesaro equilibrium notion.
