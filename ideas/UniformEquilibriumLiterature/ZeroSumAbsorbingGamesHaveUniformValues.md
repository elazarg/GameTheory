# Finite zero-sum absorbing games have uniform values

| Field | Value |
| --- | --- |
| Citation of record | Kohlberg, *Repeated Games with Absorbing States*, Annals of Statistics 2 (1974), DOI `10.1214/aos/1176342760` |
| Source confidence | `SECONDARY_VERIFIED`; full primary text unread |
| Mathematical status | `PROVED` externally |
| Repository / Lean status | `RECORDED / NONE` for the full live-state theorem |
| Exact scope and quantifiers | Finite-action two-player zero-sum absorbing games have the classical uniform value at the source scope. |
| Adapter | Distinguish a live initial state from the repository modules that only trivialize an already absorbing initial state. |
| Lean destination | `KohlbergAbsorbingUniformValue.lean` after primary proof audit |
| Consumer | Intermediate zero-sum benchmark below Mertens--Neyman |

The symmetry/finite-action hypotheses matter. Compact-action extensions have
different attribution. This result is not already covered by the generic
`Absorbing.lean` interface merely because that file has the same word in its
name.
