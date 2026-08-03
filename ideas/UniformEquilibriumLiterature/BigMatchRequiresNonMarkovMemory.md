# The Big Match requires memory beyond Markov play

| Field | Value |
| --- | --- |
| Citation of record | Blackwell--Ferguson (1968); Thuijsman (2003) Markov-insufficiency lemmas; Hansen--Ibsen-Jensen--Neyman (2023) clock-and-bit upper bound |
| Source confidence | `MIXED`: classical/secondary statements verified; exact source matching varies |
| Mathematical status | `PROVED` externally and independently in part |
| Repository / Lean status | `CONSUMED / LANDED` for `BigMatchUniform.lean` and `BigMatchNoMarkov.lean` |
| Exact scope and quantifiers | The finite zero-sum Big Match has uniform value `1/2`; stationary/Markov strategy classes are insufficient in the stated senses, while a clock plus two memory states suffices for epsilon-optimality in the modern result. |
| Source alignment | `BigMatchNoMarkov.lean` independently re-proves the cited Markov-insufficiency content; it is not a line-by-line source formalization. |
| Formalization destination | Record docstring attribution on the independent theorems; the 2023 memory upper bound remains unformalized. |
| Consumer | Permanent falsifier for finite-memory/Markov completeness and calibration of the general conjecture. |

The independent Lean proof and the published result must remain distinct in
attribution. The modern memory upper bound does not imply that the same small
memory works in multiplayer non-zero-sum games.
