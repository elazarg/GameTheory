# The optimized-debt split is exhaustive

| Status | Provenance | Lean | Next use |
| --- | --- | --- | --- |
| `PROVED`, maturity `M+L+A` | Q125--Q131 / proof-mining §§77--79 | `QuittingFiniteNashBellman*`, `QuittingFiniteDynamicDebt*`, positive-tail modules | Feeds the sole positive-plateau branch |

For each finite cutoff, exact zero-boundary Nash--Bellman chains form a compact
set and the aggregate initial dynamic debt attains a minimum `S_K`. Extension
gives `S_{K+1} <= S_K`, so `S_K` has a nonnegative limit `S∞`.

- If `S∞=0`, selected chains compile into terminal approximate equilibria at
  every accuracy and therefore a uniform-equilibrium payoff.
- If `S∞>0`, a fixed owner retains positive exact debt on a projective infinite
  exact-D tail, has a summable opponent-only clock, and is tied by finite-chain
  provenance to a nonvanishing terminal action packet.

This is a genuine exhaustive numerical split; it is not an exhaustive grammar
of the repair in the positive branch. The debt is optimized over the stated
zero-boundary chain class, which can omit a valid stationary repair. Q125 is
the mandatory regression against treating positive `S∞` as nonexistence.
