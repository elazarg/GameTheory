# Naive stationary compactification need not attain equilibrium

| Status | Provenance | Lean | Forbidden inference |
| --- | --- | --- | --- |
| `PROVED`, maturity `M` | Q132 two-player table; stopping-law bridge landed | explicit game theorem pending | relaxed zero at a boundary point implies an actual exact equilibrium |

There is a two-player quitting table with stationary profiles `x(a)` whose
maximum terminal regret is `a^2/(a+2) -> 0` as `a -> 0+`, yet no exact
behavioral terminal Nash equilibrium exists. At the limiting actual profile,
the cap switches regime and regret jumps upward.

Thus closing the graph of stationary cap data yields an attained **relaxed**
zero representing an escape sequence, not an equilibrium at its base-profile
projection. A useful scale/direction compactification must preserve which cap
regime and rate direction is approached and must never decode every relaxed
zero as an actual stationary profile.

This fence protects both stationary synthesis and the larger attainable-tail
closedness argument. It does not refute stationary approximate existence.
