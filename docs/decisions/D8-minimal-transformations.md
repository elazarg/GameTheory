# D8: concrete equivalences, not a transformation hierarchy

- **Status:** adopted and promoted; W1-H complete
- **Date:** 2026-07-30
- **Experiment IDs:** EXP-020, EXP-045, EXP-106

**Scoped extension:** EXP-120/[D60](D60-noninvertible-strategic-transfer.md)
admits finite-mixture deviation laws and coalition utility coverage as two
narrow records, supported by independent native consumers and checked
composition. Direct profile-local theorems remain the default for isolated
transfers; uniform utility certificates and their bridge are explicit opt-in
imports after their initial default-root admission failed the cold cost budget.
The prohibition below continues to apply to a universal morphism or
adequacy hierarchy; D60 records the measured exception and its exact limits.

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
| imported stable root | `GameTheory.Core.Mixed` only |
| transformation structures added | 0 |
| stored capabilities added | 0 |
| deviation transport | Nash and CE are both iff theorems; CE response maps are conjugated in both directions |
| mixed lifting | exact equality of actual play laws for the heterogeneous player swap |
| probability reuse | exact forward and inverse dependent-product laws live together in `GameTheory.Math.Probability.FinDist`; the forward law replaces the MAID-local proof |

EXP-106 places direct approximate transfer in `Core.Approximate`, with FOSG
and MAID consumers and a negative control. The theorem adds no transformation
structure, equilibrium predicate, stored capability, or equality transport.

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

Adopt game-free forward and inverse `independentProduct` reindexing laws in
`Math.Probability.Product`. Mixed extension consumes the inverse orientation;
MAID serialization consumes the forward orientation. Both use the same PMF
construction and its shared proof.

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

`Core.Transform` owns the transformations; MAID consumes the shared
probability reindexing law instead of proving its own. Probability reindexing
must remain independent of `GameForm` and `IsNash`.
