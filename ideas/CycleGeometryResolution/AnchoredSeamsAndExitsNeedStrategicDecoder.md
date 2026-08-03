# Anchored seams and exits need a strategic decoder

| Status | Provenance | Consumer | Exact missing interfaces |
| --- | --- | --- | --- |
| `OPEN`, maturity `I` | E40/E46/E47, CG8 | positive-plateau repair-or-descent | bounded edge cost, anchor transport, cap-valid seam, root-debt exit |

## Decoder input

The decoder receives a path segment cut from one selected exact finite
minimizer—not an arbitrary orbit—together with its date-zero root debt, owner,
complete marked terminal action, transported packet mass, exact-D endpoint
roots, and full playerwise holonomy data. Every abstract relation edge must
carry a finite realization and a game-stage cost. If an infinity/stopping-law
chart is used, a separate theorem must replace it by a uniformly bounded
finite realization before this decoder is invoked.

## Decoder outputs

A close-seam output must give a chronologically legal strategy splice whose
single full-state mismatch controls both prescribed payoff and every unilateral
behavioral cap through the depth-free reinsertion estimate. It must retain the
original terminal packet and deliver an actual terminal approximate Nash
profile.

An exit/dead-end output must give either that repair or new exact Nash--Bellman
roots extending the same selected prefix by uniformly bounded game time. The
resulting aggregate debt is evaluated at the **original entry/root** and must
fall by one cutoff-independent positive constant. A drop in a local potential,
at the exit state, or for a reoptimized unrelated chain does not satisfy the
contract.

Four separate statements are needed:

1. every relation edge decodes to uniformly bounded game stages;
2. the selected segment attaches chronologically to the supplied minimizer;
3. closeness in the **full** resolved state controls every player's prescribed
   payoff and arbitrary-behavior cap while retaining the packet; and
4. failure of buffered continuation creates new exact roots and a fixed root-
   debt decrement, not merely a lower local potential.

Ordinary chain recurrence cannot replace these interfaces: pseudo-orbits may
need many small jumps, and pointwise Lyapunov decrease can vanish near a
positive plateau. `GreedyBufferedExitDecoder.lean` proves the abstract greedy
first-exit/dead-end facts and is at its natural stopping point; it supplies none
of the game-facing inputs or outputs above. This claim is the game-facing half
of the P0 capstone.
