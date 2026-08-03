# Compact recurrence does not control a vanishing strategic charge

| Lifecycle | Verdict | Priority | Formalization |
| --- | --- | --- | --- |
| `MINED` | `PROVED` fence | `P1` regression | production Lean for the relative-charge obstruction |

Compactness can make two downstream states close in absolute distance, but a
strategic closing estimate may require the seam to be small relative to a
contraction or absorption charge that is itself vanishing. No such relative
estimate follows from compactness alone.

The production regression takes a compact convergent state sequence
`z_n = 1/(n+1)` and charge `q_n = 1/(n+1)^3`. Every strict return seam from
`a` to `b` is at least `q_a/2`; hence no subsequence yields a seam that is
little-o of the source charge. See
`GameTheory/Concepts/Stochastic/QuittingVanishingChargeRecurrenceNoGo.lean`.

A related elementary rank example shows that pointwise strict decrease can
also fail to give a fixed finite-step decrement near a recurrent boundary.
Therefore an exit branch in the quitting producer needs a compact bad region
separated by a uniform strategic margin—or a separately proved quantitative
decoder—not merely a Lyapunov function which decreases pointwise.
