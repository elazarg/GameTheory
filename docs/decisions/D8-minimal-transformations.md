# D8: concrete equivalences, not a transformation hierarchy

- **Status:** adopted and promoted; W1-H complete
- **Date:** 2026-07-30
- **Experiment IDs:** EXP-020, EXP-045, EXP-106

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
EXP-106 narrows design 2's theorem-only surface: an ordinary profile
equivalence may feed a generic equilibrium theorem when same-player update
reflection in both directions and payoff preservation are explicit theorem
hypotheses rather than fields of a new transformation certificate.

## Representative hostile slice

EXP-045 reindexes a dependent signature whose two strategy carriers are
`Bool` and `Fin 3` along the nonidentity Boolean swap. Thus the successful
mixed-extension theorem exercises genuine dependent coordinate transport, not
the constant-family special case.

A second fixture flips both Boolean strategy carriers. Nash transport maps
constant deviations through the coordinate equivalence. Correlated-equilibrium
transport conjugates every recommendation-dependent response by that
equivalence, explicitly witnessing both directions of deviation reflection.

EXP-106 uses two independent consumers with different policy shapes. FOSG
serialization erases administrative microsteps and transports arbitrary
serialized behavioral profiles. MAID compilation maps one source player's
whole family of site-local rules. A hostile player-coordinate swap preserves
payoffs at every conjugated profile but changes which player can deviate: the
target profile is zero-slack Nash, the source profile is not, and forward
same-player update reflection is machine-refuted.

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
| probability reuse | exact forward and inverse dependent-product laws live together in `GameTheory.Math.Probability.FinDist`; the forward law replaces the MAID-local proof |

EXP-106 promotes one theorem to `GameTheory.Core.Approximate`, with stable
FOSG and MAID consumers and a separate negative test. The combined four-target
build completes in 1,738 jobs warning-free. It adds no transformation
structure, equilibrium predicate, stored capability, or equality-transport
surface.

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

Explicitly allow
`isεNash_iff_of_profileEquiv_of_expectedUtility_eq`: it is a direct theorem
over an ordinary profile equivalence, forward and backward same-player update
reflection, and arbitrary-profile expected-utility equality. Its conclusion
preserves the same real epsilon. This permission does not extend to a bundled
transformation, certificate hierarchy, or an inference from profile/payoff
equivalence without update reflection.

Promotion is complete. `GameTheory.Core.Transform` contains 246 nonblank lines
and `GameTheory.Tests.Transform` contains 67. The focused regression target
builds in 1,722 jobs. MAID now calls `FinDist.pi_reindex` rather than owning a
local probability proof. Phase 2 source audits pass with zero added transport,
direct updates, placeholders, custom axioms, unbucketed files, or opaque
carrier fixtures. Core reaches all six transformation probes; the probability
root reaches both reindexing laws while rejecting `GameForm` and `IsNash`.
Phase 3 records exactly one MAID use of the shared theorem. The full project
build completes in 3,355 jobs, and the promoted flagship axioms remain
`propext`, `Classical.choice`, and `Quot.sound`.
