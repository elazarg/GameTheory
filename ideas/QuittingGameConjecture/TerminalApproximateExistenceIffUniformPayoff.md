# Terminal approximate existence iff a uniform payoff exists

| Status | Provenance | Lean | Consumer |
| --- | --- | --- | --- |
| `PROVED`, maturity `M+L+C` | Solan--Vieille Proposition 2.13 route; internal fixed-payoff selection | `QuittingTerminalUniformization.lean`, `QuittingTerminalUniformPayoffSelection.lean` | Final semantic reduction |

For a finite quitting game, the following are equivalent at the existence
level:

1. for every `ε>0`, some behavioral profile is terminal `ε`-Nash;
2. the game has a uniform-equilibrium payoff.

The forward direction uniformizes a terminal profile over all sufficiently
long horizons and uses compactness to select one target payoff across an
accuracy sequence. The reverse direction is the terminal consequence of the
uniform finite-horizon inequalities. The statement is about existence of a
payoff; profiles may depend on accuracy.

This theorem removes uniformization from the finite-quitting research gap. A
counterexample must exhibit a fixed positive terminal exploitability gap, not
merely slow convergence, nonstationarity, or failure of one certificate
grammar. Do not extrapolate the bridge to arbitrary stochastic games.
