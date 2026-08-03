# Greedy buffered paths return, exit, or die

| Status | Provenance | Formalization | Natural stopping point |
| --- | --- | --- | --- |
| `PROVED`, maturity `M+X` | E46 and Q133 | `experiments/GreedyBufferedExitDecoder.lean` | abstract combinatorics is complete; move to game decoder |

In a finitely covered buffer, the greedy exact path has within the covering
number one of three outcomes:

1. two buffered states share a cell, producing one downstream closing seam;
2. a first exit occurs, with the entire prefix buffered, potential drop above
   the level gap, and no admissible buffered successor at the pre-exit state;
3. without ambient seriality, the path reaches a typed dead end with no
   admissible successor at all.

This is stronger than choosing an arbitrary serial orbit: an exit certifies
failure of restricted seriality rather than a poor successor choice. The
theorem does not say that relation edges cost bounded game time, preserve the
terminal packet/root anchor, or lower optimized debt. More abstract refinement
of the greedy path is not currently valuable; the next work is the strategic
decoder in the companion claim.
