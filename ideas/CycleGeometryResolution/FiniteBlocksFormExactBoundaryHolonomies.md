# Finite blocks form exact boundary holonomies

| Status | Provenance | Lean | Remaining boundary |
| --- | --- | --- | --- |
| `PROVED`, maturity `M+L` | proof-mining §§79,83; `e1fe7dc` | `QuittingBoundaryHolonomy.lean` | closure/decoding of arbitrary-length realized limits |

An actual finite calibrated block carries both its prescribed affine transfer
and every player's max-affine arbitrary-deviation cap transfer. These summaries
compose exactly in chronological order, retain the finite root word and packet
provenance, and have uniformly bounded scalar coefficients.

Fixed-word acceptance is decidable by two affine inequalities per player. This
supports exact stationary and finite-lasso verification and gives the correct
semigroup for a middle bridge. It does not prove that limits of longer words
are realized, that equal scalar summaries are strategically interchangeable,
or that a fixed point of the coefficient map corresponds to an attainable
tail. Those are explicitly outside the landed theorem.
