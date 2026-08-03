# Monotone orbit constraints glue under lattice closure

| Status | Provenance | Evidence | Missing adapter |
| --- | --- | --- | --- |
| abstract lattice result `PROVED`; strategic instance `OPEN`, maturity `X+I` | orbit-gluing experiment | finite group/lattice Lean probe | actual coalition continuation sets with monotone meet/join closure |

For a finite group acting on a lattice of feasible constraints, orbit translates
can be glued by taking the appropriate finite meet or join when feasibility is
monotone and closed under that operation. The result is invariant by
construction.

Strategic certificate sets are often nonconvex and not lattice-closed; taking
a meet/join may erase support, independence, or chronology. This theorem must
not replace the resolved provenance groupoid. Its next discriminant is one
actual coalition-continuation constraint satisfying the hypotheses.
