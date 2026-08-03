# Anchored repair or uniform optimized-debt descent

| Status | Provenance | Consumer | Falsifier |
| --- | --- | --- | --- |
| `OPEN`, maturity `I`, P0 capstone | PB8/CG8, E40/E46/E47 | zero-debt branch then terminal-to-uniform selection | positive plateau with neither executable repair nor cutoff-independent descent |

## Input contract

Fix a finite quitting table and a sequence of exact finite Nash--Bellman
minimizers whose optimized root debts converge to a positive limit. The input
must come from that same sequence and retain:

- the original date-zero root and its optimized debt;
- the selected debt owner, complete marked terminal quitter set, and a uniform
  positive transported packet-mass lower bound;
- exact-D entry/exit roots, chronological source data, and all playerwise
  `(A,T,χ,B,P)` holonomy coordinates; and
- either a uniformly bounded realized middle or an infinity/stopping-law state
  with a separately proved uniformly bounded finite decoder.

Arbitrary supplied tails, scalar coefficient limits without provenance, and
length-zero certificates are not admissible inputs.

## Required output

For every sufficiently small seam tolerance, produce constants `L,c>0`
independent of the large cutoff and one of the following alternatives.

**Repair.** Decode at most `L` game stages/blocks, chronologically attached to
the supplied minimizer, into an actual terminal behavior tail. The prescribed
payoff recursion and every player's cap against arbitrary behavioral deviations
must hold up to a modulus tending to zero with the single full-state closing
seam. The original owner/action packet and its positive mass must survive the
attachment. This must feed terminal approximate Nash existence—not merely a
local root or a relaxed continuation value.

**Descent.** Decode an exact zero-boundary extension of at most `L` game stages
from the supplied prefix whose aggregate dynamic debt, evaluated back at the
**original date-zero root**, is at most the selected root debt minus `c`.
Consequently the optimized debt at the enlarged cutoff is lower by `c`; since
`c` is cutoff-independent, this contradicts convergence to a positive
plateau. A dead end is acceptable only if it constructs this extension or an
immediate repair.

E40 makes one accepted seam's scalar error depth-free. E46 gives a greedy
return/exit/dead-end trichotomy, and E47 applies the finite-cover return to an
actual exact-D tail. None preserves the original packet through the middle or
converts an exit/dead end into root debt reduction. Those are the missing game-
facing decoders.

A merely positive or pointwise debt drop is insufficient: it may vanish faster
than the remaining plateau gap. The decrement must be uniform, or accumulated
with a proved divergent total. A local potential exit is not automatically a
new exact Nash--Bellman root. Acceptance requires all quantifiers above and the
existing terminal-to-uniform consumer; fixed-cutoff compactness alone is not
the capstone.
