# D8: concrete equivalences, not a transformation hierarchy

- **Status:** adopted; promotion pending
- **Date:** 2026-07-30
- **Experiment IDs:** EXP-020, EXP-045

## Decision / question

What transformation surface remains public after D7 rejected generic language
certificates and the named language transfers were proved directly.

## Competing designs

1. Promote `FormHom`, `FormEquiv`, payoff-law morphisms, and separate
   deviation-reflection structures.
2. Promote only concrete player reindexing, per-player strategy equivalence,
   independent-product reindexing, and the equilibrium invariance theorems
   those equivalences justify.
3. Keep every transformation theorem bespoke in its current consumer.

Design 2 is adopted. Design 1 has no composition consumer and would recreate
the abstraction cost rejected by D7. Design 3 already duplicates the same
finite-product coordinate theorem in mixed extension and MAID serialization.

## Representative hostile slice

EXP-045 reindexes a dependent signature whose two strategy carriers are
`Bool` and `Fin 3` along the nonidentity Boolean swap. Thus the successful
mixed-extension theorem exercises genuine dependent coordinate transport, not
the constant-family special case.

A second fixture flips both Boolean strategy carriers. Nash transport maps
constant deviations through the coordinate equivalence. Correlated-equilibrium
transport conjugates every recommendation-dependent response by that
equivalence, explicitly witnessing both directions of deviation reflection.

## Measurements

| Measure | EXP-045 result |
|---|---|
| authored experiment size | 395 nonblank lines; 37 declarations including hostile fixtures |
| focused build | 1,721 jobs |
| imported stable root | `GameTheory.Core.Mixed` only |
| transformation structures added | 0 |
| stored capabilities added | 0 |
| source trust/audit tokens | 0 placeholders, native decisions, direct updates, transports, `HEq`, tactic `change`, `Fintype.ofFinite`, or `open Classical` |
| axiom profile | `propext`, `Classical.choice`, `Quot.sound` only |
| deviation transport | Nash and CE are both iff theorems; CE response maps are conjugated in both directions |
| mixed lifting | exact equality of actual play laws for the heterogeneous player swap |
| probability reuse | forward and inverse dependent-product reindexing use one probability proof; the forward law matches the existing MAID consumer |

## Kill condition

Reject or narrow the design if the hostile slice needs a public structure with
only one theorem consumer, a second equilibrium predicate, direct
`Function.update`, user-visible equality transport, stored finiteness or
decidability, a Core import of a language, or equilibrium transport that
silently assumes target deviations lift.

No kill condition fired. The dependent transport is contained inside
Mathlib's `Equiv.piCongrLeft'`; it is absent from theorem statements and
authored proof source.

## Result

Adopt transparent player reindexing and per-player strategy relabeling on
`GameSignature`, `Profile`, and `GameForm`. The public operations expose their
evaluation laws and inverse profile laws. Nash invariance is public for both
operations. Correlated-equilibrium invariance is public for strategy
equivalence, where the proof explicitly conjugates the response map.

Adopt game-free forward and inverse `FinDist.pi` reindexing laws in the
probability layer. Mixed extension consumes the inverse orientation; MAID
serialization consumes the forward orientation and must retire its local
proof.

Do not add `FormHom`, `FormEquiv`, `PayoffLawHom`, `PayoffLawEquiv`, or a
generic equilibrium-transport certificate. A future noninvertible
transformation must name its deviation-reflection hypothesis directly. A new
structure still requires two independent consumers and a theorem unavailable
from these concrete operations.

Promotion closes W1-H only after the shared MAID consumer, source audits,
reachability probes, focused build, and full build pass.
