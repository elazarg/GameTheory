# D12: where the analytic dependency is allowed to land

Decision: a fixed-point theorem may be taken from outside Mathlib, and
everything that follows from it lives in a root the audited layers do not
import.

Experiment IDs: [EXP-022](../ExperimentLog.md), [EXP-023](../ExperimentLog.md);
dependency maintenance [EXP-063](../ExperimentLog.md);
post-decision boundary stresses [EXP-030](../ExperimentLog.md) and
[EXP-031](../ExperimentLog.md); Protocol amendments
[EXP-032](../ExperimentLog.md), [EXP-033](../ExperimentLog.md), and
[EXP-034](../ExperimentLog.md), with the Bayes-fiber correction measured by
[EXP-077](../ExperimentLog.md).

## Hypothesis

The layering was built so that convexity and topology stay out of the semantic
core until a theorem needs them. The question this record settles is what
happens the first time one does.

## Competing designs

*Prove the primitive here.* Brouwer from Sperner's lemma is a topology project
with no game-theoretic content, and the pinned Mathlib supplies neither
endpoint. the baseline did not attempt it either.

*Do without it.* Real, and partly taken: a potential game has a pure
equilibrium with no fixed point and no topology, and that theorem is already in
`Core/Potential.lean`. It does not reach general existence, and no argument at
that layer does.

*Take the primitive as an external dependency.* Accepted. The measurement
below is what makes it defensible rather than convenient.

## Measurements

| Measure | Value |
|---|---|
| dependency provenance | `elazarg/fixed-point-theorems-lean4@9571dd7e0ff0af9c9e9becb2738a309cf48387c1`; all theorem sources byte-identical to `harfe/fixed-point-theorems-lean4@770940ddf9878cf61952ed53d910b92bca841838` |
| toolchain skew | none; root and dependency both pin `v4.32.2` |
| license | MIT, Copyright (c) 2026 harfe; retained byte-for-byte in the fork |
| revisions changed by the `v4.32.2` update | root Mathlib and the direct fixed-point pin only; 0 transitive revisions |
| axioms behind `brouwer_fixed_point`, `kakutani_fixed_point`, `GameTheory.exists_isNash_mixed` | `propext`, `Classical.choice`, `Quot.sound` only |
| `sorry`, `admit`, custom axioms in the dependency | 0 |
| additional build jobs | 490 (6 its own, 484 Mathlib) |
| existing reachability probes that fire on it | both (`stdSimplex`, `Polynomial`) |

The original EXP-023 import measurement used the upstream `harfe` commit and
aligned `v4.32.0` pins.  EXP-063 is a maintenance amendment, not a new theorem
dependency: it reproduced the package in a clean clone, restored the upstream
MIT license to the maintained fork, verified byte-identical theorem sources,
and then rebuilt the dependency and this complete repository under `v4.32.2`.
The immutable fork pin removes the competing-fixed-toolchain warning that a
root-only override would have left behind.

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
apparent the baseline support closure narrowed to 1,468 nonblank lines in stable Repeated,
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

## Sequential-equilibrium amendment

EXP-032 tests the predicted collision where analysis applies to Protocol
strategy objects rather than static mixed profiles.

| Competing design | Measured result |
|---|---|
| import topology into stable Protocol | rejected: ownership would be invisible because basic topology names are already transitively reachable |
| keep only a caller-supplied convergence predicate in Protocol | accepted for the stable limit schema, but insufficient as the public Kreps-Wilson specialization |
| put the full notion in an EFG-specific analytic adapter | deferred: it would couple the generic boundary decision to an unvalidated language compiler |
| create `GameTheory.Analysis.Protocol` | accepted: a one-way bridge over existing behavioral policies, Bayes data, and local rationality |

The hostile carrier check changed the stable side. `InfoState` is a total policy
domain and may contain unreachable values; a belief law over the history fiber
of every such value can therefore demand a law on an empty type.
`InformationSite` restricts assessment beliefs to reached decision sites by
carrying a nonterminal history with a genuine action in the menu. The
nonterminal witness cannot be inferred from
`active`, which Protocol deliberately leaves unconstrained after play stops.
Strategies remain the existing total `BehavioralPolicy`. History beliefs
project to the existing state-level `BeliefOn`, and sequential rationality is
the existing `Context.IsLocallyOptimal` over the player's whole continuation
policy. A current-information-set deviation becomes equivalent only through a
separately proved one-shot-deviation theorem. Thus the amendment adds no
parallel policy, state-belief, runner, or equilibrium semantics.

The analytic bridge defines pointwise convergence of finite laws and the
Kreps-Wilson limit of fully mixed, finite-Bayes-consistent assessments. A
vanishing Boolean tremble proves that fully mixed approximants may converge to
a non-fully-mixed target. This needs only finite coordinate topology, not a
measurable law on infinite execution paths and not the fixed-point geometry
used by the static existence root.

Raw probes for names such as `TopologicalSpace` cannot state this boundary:
those names are already reachable from Protocol through Mathlib. The enforced
checks therefore name project declarations and are two-sided:

| Check | Expected |
|---|---:|
| `PROTOCOL_ANALYSIS_PROBES_REJECTED` | 2 |
| `SEQUENTIAL_BRIDGE_INPUTS_REACHED` | 3 |
| `SEQUENTIAL_BRIDGE_GEOMETRY_REJECTED` | 2 |
| `PROTOCOL_FORBIDDEN_IMPORTS` | 0 |
| `TRANSPORT_PROTOCOL` | 0 |

EXP-033 closes the language-adapter half without reversing the dependency.
Stable `GameTheory.Languages.EFG` is a transparent bundle of an
`ExecutionProtocol`, its `InformationModel`, tree-shapedness, and the
single-mover law. It imports neither Analysis nor a solution concept and
defines no second evaluator. The one-way `GameTheory.Analysis.Protocol.EFG`
adapter obtains finite histories from an explicit equivalence with reachable
states and supplies assessment-induced full-policy continuation contexts.

The additional enforced probes are two-sided:

| Check | Expected |
|---|---:|
| `EFG_SYNTAX_SOLUTION_PROBES_REJECTED` | 3 |
| `EFG_SYNTAX_INPUT_PROBES_REACHED` | 3 |
| `EFG_BRIDGE_INPUT_PROBES_REACHED` | 3 |
| `LANGUAGE_FORBIDDEN_IMPORTS` | 0 |
| `TRANSPORT_LANGUAGES` | 0 |

EXP-034 supplies the first concrete theorem through that path. Stable Protocol
normalizes existing history reach masses into an information-site law. EXP-077
clarifies when that law is a Bayes conditional: histories in the site must form
an antichain, so their reach masses are disjoint rather than nested occupancy
events. Stable Protocol exposes this exact `DecisionInformationAntichain`
premise and proves perfect recall sufficient. The analytic bridge then proves a
fully mixed Bayes-consistent assessment sequentially consistent with its
constant approximating sequence. On the hostile hidden-Boolean EFG,
the canonical runner gives both decision histories probability `1 / 2`, and the
resulting assessment is a sequential equilibrium for zero continuation payoff.
This is a concrete witness, not a general finite-EFG existence theorem, and it
does not change the dependency direction.
