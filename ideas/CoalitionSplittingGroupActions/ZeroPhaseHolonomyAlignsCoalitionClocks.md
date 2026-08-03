# Zero phase holonomy aligns coalition clocks

| Status | Provenance | Evidence | Consumer |
| --- | --- | --- | --- |
| `PROVED` on complete overlap graph, maturity `X` | `CoalitionPhaseHolonomy.lean` experiment | exact finite cocycle calculation | potential common-clock adapter |

Additive phase offsets on pairwise coalition overlaps admit one global phase
gauge iff they are antisymmetric and have zero sum around every triangle. This
is the exact cocycle/coboundary criterion on the complete overlap graph.

The theorem aligns already compatible abstract clocks. It does not prove that
split equilibria share overlap histories, that phase shifts preserve strategy
legality, or that the induced welfare/security data transport. Sparse overlap
graphs and actual game phases require separate adapters.
