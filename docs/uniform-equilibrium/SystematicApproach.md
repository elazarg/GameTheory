# Systematic finite-quitting research architecture

This document defines the stable coordination architecture for the finite-
quitting front. It preserves the current theorem families and their exact
scopes. It does **not** replace them with one speculative certificate, assert
that a strategy trichotomy is proved internally, or promote a conditional
compiler to a generic producer.

The organizing asymmetry is unchanged:

- the semantic back end is strong—many supplied certificates compile to
  terminal approximate Nash profiles and then to a uniform payoff;
- the front end is incomplete—an arbitrary reward table does not yet enter a
  proved exhaustive branch producing a positive certificate or a concrete
  negative separator certificate.

The architecture separates three classifications:

1. **root route** — stationary/projective, instant/punishment, proper absorption
   path, or nonexistence;
2. **artifact role** — producer, adapter, verifier, compiler, closure,
   diagnostic, or separator; and
3. **claim level** — semantic waist, verification, bounded synthesis,
   strategy-class coverage, solved subclass, or diagnostic.

These are research and API classifications. A generic function wrapper cannot
prove mathematical provenance. The named certificate definition and theorems
constructing it remain the evidence that an object is genuinely stationary,
path-like, a producer, or a separator.

The machine-readable mirror is
[`systematic-routes.json`](systematic-routes.json). The conjecture-directed
composition order is [`ConjectureDirectedSpine.md`](ConjectureDirectedSpine.md).
The detailed rationale is
[`decisions/SystematicFrontEndDecision.md`](decisions/SystematicFrontEndDecision.md).
Stable methodology is owned by [`Program.md`](Program.md); live priorities
remain owned by [`PIPELINE.md`](PIPELINE.md).

## Semantic waists

The positive routes meet at:

```text
QuittingTerminalApproximationFamily reward
  := for every ε > 0, there is a terminal ε-Nash profile
     against unrestricted behavioral deviations.
```

`QuittingSystematicApproach.lean` proves this equivalent to existence of a
uniform-equilibrium payoff by reusing the landed terminal selection theorem.

The negative semantic waist is the proof-relevant package
`QuittingTerminalGapCertificate reward`: one `gap > 0` together with a proof
that every behavioral profile has a terminal unilateral improvement of at least
that gap. `UniformNonexistenceCertificate.lean` proves both its nonexistence
consequence and the exact equivalence

```text
no uniform-equilibrium payoff
  <=> some fixed positive terminal exploitability gap exists.
```

That exactness does not make the semantic gap a finite separator language.
Concrete LP potentials, support barriers, automata arguments, or other local
certificates still need a negative compiler into this waist.

<!-- systematic-family:terminal-selection -->
The terminal-selection family is the canonical positive consumer. It selects a
fixed payoff from all-accuracy terminal approximate equilibria and invokes the
terminal-to-uniform bridge. It is not a construction front end.

## Fixed-schema quantifier order

The formal conjecture-facing shell now fixes one schema before reward tables:

```text
QuittingSystematicSchema
  = four reward-indexed certificate families
    + three positive compilers
    + one negative compiler.

QuittingSystematicDispatcher schema
  = for every reward table, one resolution under that same schema.
```

A resolution carries one of:

```text
stationary certificate
| instant certificate
| path certificate
| negative certificate.
```

`QuittingSystematicResolution.semantic` returns a tagged
`QuittingSemanticResolution`. It retains the selected route, original
certificate, and either a payoff with its uniformity proof or the compiled
negative gap certificate. It does not collapse to `P ∨ ¬P`.

No generic schema or dispatcher inhabitant is asserted. In particular, the
certificate languages and compilers are not existentially chosen separately
for each reward table after its semantic truth is known.

Lean cannot prohibit a deliberately circular certificate family from hiding
`QuittingTerminalApproximationFamily reward` in its definition. A concrete
schema therefore earns scientific content only when its languages are named
independently, its producers are explicit, and its compilers are proved. This
is an unavoidable provenance audit, not something a phantom type index can
solve.

The generic `QuittingCertificateProducer` and
`QuittingCertificateAdapter` wrappers distinguish compositional API positions.
They do not authenticate provenance by themselves. Likewise, the schema field
names assign route slots; the mathematics of the certificate type establishes
whether the slot is honest.

## Root routes

The routes are broader than any one certificate grammar. They classify existing
work while leaving room for support pivots and genuinely infinite carriers.

<!-- systematic-route:stationary-projective -->
### 1. Stationary/projective

This route covers stationary products, LCP and min-max data,
analytic/projective packets, accepted targets, and bounded semialgebraic
synthesis.

The decisive gate is strategic, not algebraic. A Bellman or complementarity
packet must either:

- compile to the terminal semantic waist;
- identify an owner for the instant/punishment route;
- expose an activity/support failure producing a proper-path pivot; or
- yield a concrete negative certificate or a typed obstruction requiring
  further decoding.

<!-- systematic-family:zero-solo -->
The zero-solo family is a genuine compiler for its exact sign class. It is not
a normal form for weights with a positive solo coordinate.

<!-- systematic-family:stationary-minmax -->
The stationary-minmax family supplies exact stationary punishment values and
full-history cap semantics. Attainment and the finite-horizon bridge remain
separate obligations.

<!-- systematic-family:projective-packets -->
Projective packets are adapter-facing. Matching analytic orders produce
normalized packet algebra, but a cemetery coordinate does not authenticate the
endpoint. Acceptance or retargeting, physical realization, and recurrent
relative return remain producer obligations.

<!-- systematic-route:instant-punishment -->
### 2. Instant/punishment

This route covers a sure first-stage quitter with an off-path continuation that
credibly disciplines refusal to quit.

Failure identifies one of two scalar obstructions:

- the owner’s singleton payoff lies below the punishment value; or
- an outsider gains by joining the sure exit.

Those witnesses should feed support enlargement, a path construction, or a
separator decoder rather than disappear as a failed special case.

<!-- systematic-family:instant-punishment -->
`QuittingInstantPunishment.lean` exactly characterizes this strategy class. It
does not prove that some owner satisfies the conditions in every game.

<!-- systematic-route:proper-absorption-path -->
### 3. Proper absorption path

This route contains finite and infinite absorbing plans: diagonal tails,
support-witness paths, exact cycles, essential APS, face circulations, and the
marked/infinity objects needed when finite length escapes.

A general carrier must retain the strategic state needed by a decoder, not
literal inert calendar length. At minimum it must account for:

- chronological ordered activity and active quitting faces;
- continuation values and terminal absorption data;
- unilateral stopping or Snell caps;
- continuation after a near-sure or terminal jump; and
- enough provenance to reconstruct the relevant terminal packet.

A scalar accumulated-mass trace is not presumed sufficient. Conversely, a
source-retaining finite block with a literal unbounded stage counter is not
presumed compact.

Path consistency is also load-bearing. A global convex combination of
circulations from incompatible recurrent components is not a path. The
conjecture-directed spine therefore asks for a reachable recurrent component
with its own charged flow, or for componentwise separators; it does not use one
global circulation polytope.

<!-- systematic-family:diagonal-target-tail -->
Diagonal target tails are a compiler. Their unresolved input is production of
exact prefixes, player-indexed closed tails, and a common survival certificate.

<!-- systematic-family:support-witness -->
Support witnesses are a compiler family. They close the deviation ledger once
support-wise optimality, continuation-by-continuation individual rationality,
and divergent absorption are supplied.

<!-- systematic-family:essential-aps -->
Essential APS is a producer relative to a compact terminal-free unique-live
component with face avoidance. The generic input is deriving such a component,
or a principled pivot away from it, from arbitrary reward data.

<!-- systematic-family:face-circulation -->
Face circulation is a producer relative to a bounded balanced circulation with
a common phase-ratio ceiling and punishment-valid floor. Any generic extension
must additionally ensure path consistency inside one reachable recurrent class;
cross-component cancellation is not realizable by one chronological path.

<!-- systematic-family:punishment-completed-cycle -->
Punishment-completed cycles are an exact compiler. They enlarge admissibility
by allowing credible punishment in noncontracting coordinates, but exact cycles
are not presumed to arise as limits of relaxed cycles.

<!-- systematic-family:boundary-holonomy -->
Boundary holonomy is finite-block algebra and diagnostics. Fixed-cutoff
compactness and tangent-coordinate compactness do not themselves supply
realized-image closedness or a strategic decoder.

<!-- systematic-family:truncated-ledger-boundary -->
The truncated-ledger package remains a sound sufficient interface and a useful
negative regression. Its counterexample prevents it from being used as a
universal normal form.

<!-- systematic-route:nonexistence -->
### 4. Nonexistence

The negative lane is first-class and runs in parallel with all positive routes.
Failure of stationary, instant, finite-period, bounded-controller, APS, or one
marked-path grammar is not a counterexample.

The semantic acceptance condition is one fixed positive terminal gap against
all behavioral profiles. The systematic front end, however, is symmetric: its
negative constructor carries a certificate in an independently specified
negative language, and `QuittingNegativeCompiler` must compile it to
`QuittingTerminalGapCertificate`.

<!-- systematic-family:nonexistence-certificates -->
`UniformNonexistenceCertificate.lean` owns the exact negative semantic waist and
consumer. Search should export finite violated inequalities, LP potentials,
barriers, or other checkable certificate data—not merely the semantic
nonexistence proposition.

## Cross-cutting families

<!-- systematic-family:two-player-existence -->
The two-player theorem is a solved-subclass producer. It is also a diagnostic
fence: a proposed universal obstruction visible already with two players is
suspect unless it explains how the known classification escapes it.

<!-- systematic-family:reward-closure -->
Reward closure transports existence through uniform reward-table limits on a
fixed skeleton. It turns a proved density theorem into generic coverage, but it
does not provide density itself.

## Central producer target: support-enlarging face pivots

Starting from a failed local certificate on an active face, the desired pivot
theorem returns one of:

1. a valid certificate on a richer face or ordered activity pattern;
2. a sure-exit owner satisfying the instant-punishment gate;
3. a recurrent path or path-consistent circulation consumable by proper-path
   compilers; or
4. a strict local inequality that is either decoded into another boundary or
   compiled by a concrete negative separator language.

This is a research target, not a landed theorem.

A second time scale or vanishing occupation weight is not by itself a pivot. It
may dilute accumulated error, but it cannot repair a pointwise failed best-
response inequality unless support, continuation, or punishment data changes.

## Required route-facing metadata

Every finite-quitting route-facing claim, handoff, or PR records:

1. route;
2. artifact role;
3. claim level;
4. exact remaining obligation; and
5. next consumer or pivot output.

The manifest mirrors these fields for navigation. The checker validates JSON
shape, enumerated values, referenced paths, markers, selected declaration names,
and basic wiring. It does **not** verify that a mathematical classification or
prose obligation is correct or current.

## Promotion fences

The following promotions require named theorems:

- compiler to producer;
- bounded synthesis to unrestricted strategy-class coverage;
- compact projection to closed realized strategic image;
- local Bellman/complementarity data to credible target;
- global circulation to one path-realizable recurrent component;
- failure of one route to a negative certificate; and
- accuracy-indexed family to one exact finite object.

A new certificate grammar is justified only when no existing adapter can carry
its information, or when a no-go theorem identifies a strategic variable that
all existing grammars necessarily forget.

## Balanced scheduling

Balanced does not mean equal staffing. Subject to objective priority:

- keep a stationary/projective or support-pivot producer question active;
- keep the proper-path carrier/decoder front active until completed or
  decisively refuted;
- use instant punishment as an exact boundary test and pivot destination;
- keep one concrete negative-certificate lane active in parallel; and
- keep one formalization lane assigned to the strongest ready upstream result.

Priority follows distance to the semantic waist, reusable failure output,
downstream leverage, risk of false premises, and only then implementation cost.
A new conditional back-end theorem does not displace an upstream front-end
obligation merely because it is easier to formalize.

## What is enforced in code

The architecture has three substantive layers and one modest guardrail:

1. **Lean semantics.** `QuittingSystematicApproach.lean` defines the fixed
   schema, symmetric compilers, routed resolution, tagged semantic output, and
   dispatcher target. `UniformNonexistenceCertificate.lean` owns the exact
   fixed-gap bridge.
2. **Research method.** `Program.md` records metadata, pivot payloads,
   promotion fences, and scheduling rules.
3. **Family inventory.** `systematic-routes.json` records the current declared
   classification and obligations.
4. **Structural check.** `scripts/check_systematic_routes.py` validates schema,
   paths, markers, selected names, and basic wiring. It is neither mathematical
   evidence nor a semantic audit of the inventory prose.

When a theorem changes a family’s role or coverage, its owning claim, the
manifest, and this document should be reconciled in the same change. Live queue
status and project-control identifiers remain in `PIPELINE.md`.
