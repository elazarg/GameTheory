# Exact behavioral equilibrium need not exist

| Status | Provenance | Formalization | Role |
| --- | --- | --- | --- |
| `PROVED`, maturity `M` | Q132 exact two-player table | explicit packaged game pending; stopping-law semantics landed | regression against strengthening approximate existence |

A finite two-player quitting game can have stationary terminal exploitability
tending to zero while admitting no exact behavioral terminal Nash equilibrium.
The arbitrary behavioral best response is reduced to deterministic quit times
and Never, so the nonexistence is not an artifact of restricting deviations.

Therefore the base theorem must quantify `for every ε>0, exists profile`; it
cannot be strengthened to an exact stationary or exact behavioral equilibrium.
Vanishing hazards and nonattained cap limits are essential, not proof defects.
