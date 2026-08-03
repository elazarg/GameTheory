# Orbit sums turn positive weights into invariant positive weights

| Status | Provenance | Evidence | Missing consumer |
| --- | --- | --- | --- |
| finite algebra `PROVED`; cap transport `OPEN`, maturity `X+I` | finite-group experiment | `FiniteGroupInvariantWeights.lean` | game automorphism preserving all-profile cap inequalities |

Summing a strictly positive player-weight vector over a finite group orbit
produces another strictly positive vector fixed by the action. If the game
transports a valid all-profile welfare cap for every translated weight, summing
those inequalities gives the cap for the invariant orbit sum.

Positivity and invariance are automatic; validity of the translated cap is not.
An arbitrary player permutation need not preserve the game, target, profile
class, or Bellman bias. The theorem becomes operational only with an actual
automorphism adapter.
