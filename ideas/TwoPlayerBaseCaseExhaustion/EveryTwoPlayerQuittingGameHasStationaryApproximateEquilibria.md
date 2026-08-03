# Every two-player quitting game has stationary approximate equilibria

| Status | Attribution | Lean | Consumer |
| --- | --- | --- | --- |
| `PROVED` externally, maturity `M` | Solan--Vieille 2002 §2.1, citing Flesch--Thuijsman--Vrieze 1996 | target `QuittingTwoPlayerStationaryExistence.lean`; partial branches landed | terminal-to-uniform payoff selection |

For every standard two-player quitting reward table and every `ε>0`, some
stationary product profile is terminal `ε`-Nash against arbitrary behavioral
unilateral deviations. The source proof uses all six payoff coordinates. It
first closes any pure stationary Nash case; otherwise, after role exchange, it
derives one sign/order chamber and splits on one comparison. One branch uses a
vanishing owner-solo hazard, the other a vanishing owner hazard against a sure
quitter.

The full-rate stationary cap theorem reduces both branches to explicit scalar
inequalities, and the pair-repair branch is already formalized. Missing Lean
work is the pure-profile exhaustion, role orientation, and complementary
vanishing owner-solo estimate. No player-count induction follows.
