# Two-player absorbing games have uniform equilibria

| Field | Value |
| --- | --- |
| Citation of record | Vrieze--Thuijsman, *On equilibria in repeated games with absorbing states* (1989), DOI `10.1007/BF01254293` |
| Source confidence | `SECONDARY_VERIFIED`; full primary text unread |
| Mathematical status | `PROVED` externally |
| Repository / Lean status | `RECORDED / NONE` for the full absorbing theorem |
| Exact scope and quantifiers | Finite two-player non-zero-sum repeated/absorbing games admit uniform approximate equilibria/payoffs at the source's stated notion. |
| Adapter | Must align source absorbing-state, evaluation, and behavior-strategy conventions with repository `Absorbing`/`Uniform`. |
| Lean destination | `TwoPlayerAbsorbingUniformExistence.lean`; no scaffolding before primary-source audit |
| Consumer | Published positive island and base case below Vieille's general theorem |

This is broader than standard quitting games. The currently planned two-player
quitting formalization is not a formalization of this theorem. Exact source
quantifiers and whether the theorem is payoff or profile existence must be
read from the primary paper before coding.
