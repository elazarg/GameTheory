# Contracting graph-directed codes have unique periodic lifts

| Lifecycle | Verdict | Priority | Formalization |
| --- | --- | --- | --- |
| `MINED` | `PROVED` | `P2` geometry/compiler infrastructure | production Lean; density corollary checked experimentally |

In a compact graph-directed pullback system with one common contraction
constant below one, every admissible infinite edge code has a unique compatible
value lift. If the vertex and edge code is periodic, the value lift inherits
that period. Two compatible lifts whose edge codes agree for a finite prefix
are exponentially close at the prefix's start, with an explicit bound by the
contraction power times a finite diameter budget.

Production Lean proves existence/uniqueness and the periodic/common-prefix
claims in `GraphDirectedCompactPullback.lean` and
`GraphDirectedPeriodicLift.lean`. The one-vertex full-shift corollary—repeat a
long prefix to obtain exponentially close periodic lifts—is checked in
`experiments/GraphDirectedFullShiftDensity.lean` but is not yet a production
declaration.

This theorem explains the local symbolic component of the block-pair atlas.
It does **not** prove that a game's strategic predecessor relation is covered
by such a graph, that the coding map is injective, or that every quitting-game
equilibrium is periodic.
