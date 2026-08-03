# The owner-hazard split exhausts exceptional clock patterns

| Status | Provenance | Lean | Consumer |
| --- | --- | --- | --- |
| `PROVED`, maturity `M+L+A` | Q128 and positive-debt tail calculus | opponent-clock summability and closure modules | fully summable plateau branch |

Positive exact debt for owner `i` makes the additive probability that some
opponent quits summable. Every nonowner hazard is pointwise bounded by this
clock and is therefore summable. Only the owner's own hazard remains to split:

- if it is nonsummable, it lies in every other player's opponent clock; those
  clocks contract, and the exact-path/positive-singleton argument closes by an
  exact terminal equilibrium;
- if it is summable, all individual hazards and hence every opponent clock are
  summable.

No `2^n` lattice of clock patterns remains. The classification does not solve
value compatibility or attainability in the fully summable branch; that is the
relative-boundary problem.
