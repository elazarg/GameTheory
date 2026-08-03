# The full-rate stationary cap is exact

| Status | Provenance | Lean | Scope |
| --- | --- | --- | --- |
| `PROVED`, maturity `M+L+C` | E48, commit `6a64b15` | `QuittingFullRateStationaryVerifier` | every stationary product profile, arbitrary behavioral unilateral deviations |

For each player at any stationary product profile, the exact best-response cap
has two exhaustive regimes. If the opponents' Continue mass is below one, use
the stationary Snell cap; if it equals one, product saturation forces every
opponent to Continue surely and the cap is `max(0,r_i({i}))`, attained by
Never or immediate Quit.

Consequently the profile is terminal `ε`-Nash iff, for every player, this
full-rate cap is at most prescribed terminal payoff plus `ε`. This is an exact
all-behavior equivalence and includes cube faces. It verifies a supplied
profile; it neither constructs stationary hazards nor speaks about
nonstationary equilibrium.
