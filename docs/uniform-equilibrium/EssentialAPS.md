# Essential APS: executable progress on functional live-successor strata

This module family formalizes the certificate-facing part of the essential APS
approach of Ashkenazi-Golan, Krasikov, Rainer, and Solan, *The APS approach for
undiscounted quitting games* (International Journal of Game Theory 55:19,
2026).

The current result is not the general uniform-equilibrium theorem. It closes
three narrower gaps that were previously conflated:

1. algebraic convexification versus a one-continuation executable segment;
2. false progress caused by zero absorption mass;
3. pointwise finite-window progress versus a uniform positive mass bound.

It also constructs finite executable APS runs from greatest-family membership.
The remaining game-theoretic gap is to iterate these runs while obtaining
opponent-specific contraction, rather than merely positive total absorption
mass.

## Convexification and executable segments

For an arbitrary continuation set `E`, the formulas

```text
exists p in [0,1], v in E, w = p R_i + (1-p) v
```

and

```text
co ({R_i} union E)
```

are not equivalent: the first is a union of segments from `R_i`, while the
second can mix several continuation points. The Lean API therefore keeps both
notions explicit:

- `quittingEssentialAPSPrefix` is the literal convex-hull prefix;
- `quittingSegmentEssentialAPSPrefix` selects one continuation;
- `quittingProperEssentialAPSPrefix` additionally requires `p` in `(0,1)`;
- `quittingSegmentEssentialAPSPrefix_subset` embeds executable segments into
  the algebraic prefix.

Every full owner-step image is convex, even when the raw union of successor
fibers is not. Consequently, the greatest restricted APS family has convex
fibers inside convex carriers.

## Unique live successors

The executable reduction no longer requires graph-theoretic uniqueness. A
displayed successor is *unique live* when every other exact Flesch successor
has an empty continuation fiber. Under this weaker condition,

```text
quittingEssentialAPSSuccessorSet reward family owner = family successor.
```

The principal theorem is

`quittingEssentialAPSGreatestFamily_terminal_or_successor_or_proper_of_unique_live`.

It says that a greatest-family point is terminal, propagates unchanged into
the displayed successor fiber with zero mass, or has a proper positive-mass
segment witness. The total version also handles an empty displayed fiber,
which then forces the viable solo endpoint.

Graph-theoretic uniqueness remains available as a corollary and is still used
by the current compactness bootstrap.

## Finite run construction

`IsQuittingEssentialAPSFiniteRun` records a concrete finite sequence of payoff
values and masses. Every value remains in the appropriate greatest-family
fiber; every mass lies in `[0,1)`; and every edge satisfies the exact
singleton-flow arc equation.

The theorem

`exists_quittingEssentialAPSFiniteRun_or_terminal_of_unique_live`

starts from arbitrary greatest-family membership and constructs such a run to
any requested finite horizon, unless a terminal point is reached earlier.
Thus the local fixed-point trichotomy is now composed into an actual finite
executable object rather than left as a pointwise disjunction.

## Compactness and uniform window mass

On compact convex carriers with a graph-theoretically unique successor at
every owner, the coordinatewise closure of the greatest family is again
subinvariant. Maximality therefore forces the greatest family to be closed,
and hence compact inside the carrier.

A continuous finite active-face gap then has a strictly positive minimum on a
compact greatest fiber avoiding the common active face. Telescoping a bounded
singleton-flow path converts that separation margin into a positive lower
bound on cumulative absorption mass.

The stronger theorem

`exists_uniform_quittingEssentialAPS_windowMass_of_greatest_faceAvoidance`

assumes face avoidance only on the greatest APS fiber, not on the entire
carrier. `exists_uniform_quittingEssentialAPS_windowMass` is retained as the
older carrier-level corollary.

## Module map

1. `QuittingFleschSuccessor.lean`: exact asymmetric successor graph.
2. `QuittingEssentialAPS.lean`: algebraic, segment, and proper APS prefixes.
3. `QuittingEssentialAPSFixedPoint.lean`: greatest restricted fixed family.
4. `QuittingEssentialAPSConvexProgress.lean`: convex prefix equals a segment
   join and proper progress away from endpoints.
5. `QuittingEssentialAPSConvexFixedPoint.lean`: convex greatest fibers and
   unique-live-successor local progress.
6. `QuittingEssentialAPSCircuitProgress.lean` and
   `QuittingEssentialAPSCircuitProgressTotal.lean`: finite zero-mass
   propagation and active-face exclusion.
7. `QuittingEssentialAPSCompactFixedPoint.lean`: closure bootstrap and compact
   greatest fibers on graph-unique compact convex carriers.
8. `QuittingEssentialAPSFiniteRun.lean`: concrete finite run construction.
9. `QuittingEssentialAPSUniformWindowMass.lean`: compact separation and the
   uniform positive finite-window total-mass bound.
10. `QuittingEssentialAPSRegression.lean`: exact zero-mass self-loop
    regression.
11. `QuittingEssentialAPSCycle.lean`: compilation of a supplied finite proper
    cycle to a uniform-equilibrium payoff.

`QuittingEssentialAPSAll.lean` exports the complete layer.

## Current frontier

The branch now proves finite executable run existence and a uniform positive
*total* absorption-mass bound under the stated functional/compact hypotheses.
It does not yet prove that every constructed finite run can be extended
indefinitely, that cumulative mass diverges under iteration, or that every
player sees uniformly positive mass from opponents. The last distinction is
load-bearing: the existing equilibrium compiler requires opponent-survival
contraction, and total mass may in principle concentrate on one owner.

The next decisive composition is therefore:

1. combine finite-run construction with the uniform window bound to obtain
   “terminal before the horizon, or window mass at least `nu`” for the
   constructed run itself;
2. iterate the construction over windows;
3. derive opponent-specific cumulative mass, or establish opponent contraction
   by a separate circuit argument;
4. feed the resulting nonperiodic path into the existing infinite-path
   equilibrium compiler.
