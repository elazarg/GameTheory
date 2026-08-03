# Separately existing split equilibria do not glue

| Status | Provenance | Formalization | Forbidden inference |
| --- | --- | --- | --- |
| `WRONG` naive claim; counterlogic `M` | coalition-splitting audit | regression documented; no universal game counterexample claimed | exchange `forall player, exists profile` with `exists profile, forall player` |

Uniform equilibria of each singleton-versus-complement split may use different
profiles, clocks, correlations, and continuation targets. Their existence does
not yield one original-game profile satisfying every player's deviation
inequality. A merged coalition may also correlate member actions in a way the
original independent behavior profile cannot reproduce.

The logical quantifier failure refutes naive gluing, not every structured split
theorem. A valid construction needs actual transport/compatibility and a common
positive welfare ceiling, as stated in the companion assembly theorem.
