# D12: where the analytic dependency is allowed to land

Decision: a fixed-point theorem may be taken from outside Mathlib, and
everything that follows from it lives in a root the audited layers do not
import.

Experiment IDs: [EXP-022](../ExperimentLog.md), [EXP-023](../ExperimentLog.md);
post-decision boundary stresses [EXP-030](../ExperimentLog.md) and
[EXP-031](../ExperimentLog.md).

## Hypothesis

The layering was built so that convexity and topology stay out of the semantic
core until a theorem needs them. The question this record settles is what
happens the first time one does.

## Competing designs

*Prove the primitive here.* Brouwer from Sperner's lemma is a topology project
with no game-theoretic content, and the pinned Mathlib supplies neither
endpoint. v1 did not attempt it either.

*Do without it.* Real, and partly taken: a potential game has a pure
equilibrium with no fixed point and no topology, and that theorem is already in
`Core/Potential.lean`. It does not reach general existence, and no argument at
that layer does.

*Take the primitive as an external dependency.* Accepted. The measurement
below is what makes it defensible rather than convenient.

## Measurements

| Measure | Value |
|---|---|
| toolchain skew against `harfe/fixed-point-theorems-lean4` | none; both pin `v4.32.0` |
| license | MIT, Copyright (c) 2026 harfe |
| pre-existing manifest revisions changed by `lake update` | 0 |
| axioms behind `brouwer_fixed_point`, `kakutani_fixed_point` | the three standard ones |
| `sorry`, `admit`, custom axioms in the dependency | 0 |
| additional build jobs | 490 (6 its own, 484 Mathlib) |
| existing reachability probes that fire on it | both (`stdSimplex`, `Polynomial`) |

## Unexpected costs

The last row is the one that shapes the design. Sion's minimax theorem, the
alternative flagship, makes neither probe fire — it can be imported almost
anywhere. The fixed-point package makes both fire, so it spends the entire
convexity budget the audit was written to protect. A dependency that leaks this
much cannot be contained by convention.

## Result: accept, with the boundary enforced rather than intended

`GameTheory.Analysis` is the only root permitted to import
`FixedPointTheorems`, and no module outside it may import `GameTheory.Analysis`.
The existing probes are unchanged and must keep passing: Core and the
executable frontend still may not see `stdSimplex` or `Polynomial`. The new root
is *expected* to see both, and that expectation is recorded as a measurement in
its own right — a probe that asserts the leak exists exactly where it was
allowed to.

The trust argument is separable from the convenience one. Version alignment and
build cost decide whether taking the dependency is pleasant; the axiom profile
decides whether it is admissible at all. Had the package carried a single
`sorryAx`, every theorem above it would be untrusted and no boundary would
repair that.

## The boundary, as checked

`scripts/phase2-audit.ps1` carries the rule rather than the prose. Four numbers,
all verified:

| Check | Expected |
|---|---:|
| `ANALYSIS_IMPORTED_OUTSIDE_ROOT` | 0 |
| `FIXED_POINT_IMPORTERS` | 1 |
| `UNREACHABLE_PROBES_PASSED` | 6 |
| `ANALYSIS_PROBES_REACHED` | 2 |

The last is the unusual one and the one worth keeping. Every other probe asserts
that something is *not* reachable; this one asserts that `stdSimplex` and
`Polynomial` *are* reachable from the analytic root. A probe that only ever
checks absence cannot tell containment from the dependency having quietly
stopped being used, and the two look identical from outside.

## Consequences for public API

None to existing modules. `GameTheory.Analysis` is additive, and nothing in
Core, Probability, Protocol, Languages, or Finite may depend on it — which is
what keeps the executable frontend free of noncomputable analysis.

## Repeated-play boundary stress

EXP-030 creates the RFC's separate `GameTheory.Repeated` root and measures it
before attempting the folk theorem. The stagewise and finite-prefix layer names
no `GameTheory.Analysis` or `FixedPointTheorems` import. Both Basic and
Discounted reject `stdSimplex` and `Polynomial` (four probes), repeated source
contains zero transport tokens, and the authored-import audit reports zero
forbidden dependencies.

Discounted real series therefore do not spend the fixed-point dependency
budget. The pinned full folk theorem did import simplex approximation and
supporting geometry, so EXP-030 left that theorem to a separate competition.
EXP-031, recorded next, ran it with the same mandatory enforcement pattern:
negative probes from `GameTheory.Repeated` and positive probes proving that any
new bridge remains live.

## Discounted folk-theorem amendment

EXP-031 ran that competition rather than treating the bridge as a directory
preference.

| Competing design | Measured result |
|---|---|
| put all support under stable `GameTheory.Repeated` | rejected: feasible-payoff convex geometry and denominator clearing would widen the stable root |
| create `GameTheory.Repeated.Analysis` | rejected: it would place the analytic surface inside the audited stable subtree |
| create `GameTheory.Analysis.Repeated` | accepted: a one-way bridge over stable continuation and trigger theorems |
| leave denominator clearing inside the game theorem | rejected: the 177-line result is game-independent and imports no game semantics |

The representative slice is the approximate discounted folk theorem itself:
every feasible payoff strictly above the opponent-minmax vector is approached
by normalized discounted payoffs of history-dependent Nash profiles in the
observable mixed-action repeated game. Its kill conditions were a leak of
`stdSimplex` or `Polynomial` into the stable root, a second mixed-game/payoff/
security/equilibrium API, an infinite-path probability law, a Protocol import
in the analytic bridge, or more supporting geometry than the focused
greenfield proof.

None fired. Stable continuation, periodic paths, and trigger incentives live
under `GameTheory.Repeated`; convex feasibility, opponent minmax, and the
flagship live under `GameTheory.Analysis.Repeated`; residual-floor denominator
clearing lives in the independent `GameTheoryMath` Lake target. The 2,324-line
apparent v1 support closure narrowed to 1,468 nonblank lines in stable Repeated,
783 in the analytic repeated subtree including its concrete witness and root,
and 185 in `GameTheoryMath` (177 in the approximation module plus its root). In
particular, the old 255-line unused
ambient/interior geometry and 328-line general security hierarchy did not
survive the dependency test.

The enforcement is again two-sided:

| Check | Expected |
|---|---:|
| `REPEATED_ANALYSIS_PROBES_REJECTED` | 6 |
| `REPEATED_BRIDGE_PROBES_REACHED` | 3 |
| `REPEATED_BRIDGE_PROTOCOL_REJECTED` | 1 |
| `GAMETHEORYMATH_GAME_REJECTED` | 1 |
| `TRANSPORT_REPEATED_SOURCE` | 0 |
| `TRANSPORT_ANALYSIS_SOURCE` | 0 |
| `TRANSPORT_GAMETHEORYMATH_SOURCE` | 0 |

The three positive bridge probes reach a trigger profile, the opponent-minmax
vector, and residual-floor counts. Thus the bridge is known to consume each
side it was created to connect, while the negative probes show that
`GameTheory.Repeated`, Protocol, and the independent mathematics target have
not silently changed roles.
