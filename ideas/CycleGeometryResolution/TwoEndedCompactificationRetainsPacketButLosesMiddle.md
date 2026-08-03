# Two-ended compactification retains the packet but loses the middle

| Status | Provenance | Lean | Nonclaim |
| --- | --- | --- | --- |
| `PROVED`, maturity `M+L` for the unscaled core | E50, commit `e2d5170` | `QuittingTwoEndedDynamicDebtCompactification` | no bi-infinite orbit or bridge |

Read selected cutoff-`K` minimizers both forward from their root and backward
from the terminal zero boundary. A common diagonal subsequence yields a forward
exact-D ray and a reverse exact-D ray whose origin is the closed terminal face
`payoff=0`, `debt_i=max(0,r_i({i}))`. Root debt is bounded by preterminal debt,
so the selected positive owner remains positive one reverse step from the
boundary; that exact edge produces a quantitative full-action terminal packet.

For every fixed forward depth `t` and reverse depth `r`, the middle interval
still has length `K-t-r -> infinity`. Common subsequence provenance does not
make the two rays adjacent and does not transport the reverse packet to a close
pair on the forward ray. Infinity is therefore a second chart, not one extra
distance coordinate; the missing object is a compact summary of the escaping
middle.
