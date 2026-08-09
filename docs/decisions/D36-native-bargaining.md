# D36: finite Nash bargaining has a capability-free native owner

- **Status:** adopted and promoted
- **Date:** 2026-08-09
- **Experiment ID:** EXP-069

## Decision / question

Whether bargaining should begin with a native feasible-utility problem under
`GameTheory.Cooperative`, with an analytic structure storing convexity and
compactness, or with an artificial strategic game whose Nash equilibria encode
bargaining solutions.

## Competing designs

1. Store only an arbitrary feasible predicate and explicit feasible
   disagreement point; put finite-player, convexity, compactness, and existence
   assumptions on the predicates or theorems that need them.
2. Make an analytic feasible-set object the semantic owner and store the
   topological capabilities required by later existence theorems.
3. Introduce players, actions, and payoffs solely to reuse strategic Nash
   equilibrium vocabulary.

Design 1 is adopted.  A Nash bargaining solution is a feasible,
individually-rational maximizer of the product of gains, not a strategic Nash
equilibrium.  Positive componentwise affine transformation is defined once on
the native problem.  Any later topological existence theorem belongs in a
one-way Analysis bridge and may not thicken the semantic record.

## Representative hostile slice

The general slice proves that a Nash-product maximizer is weakly Pareto
optimal, derives equal gains from symmetry plus explicit solution uniqueness,
and proves invariance under player-specific positive scales and arbitrary
shifts.

The concrete two-player feasible set contains disagreement `(0,0)`, balanced
allocation `(2,2)`, and asymmetric allocations `(3,1)` and `(1,3)`.  The
balanced product is four and both asymmetric products are three.  Scaling by
`(2,3)` and shifting by `(5,-1)` produces solution `(9,5)` and transformed
disagreement `(5,-1)`.  The asymmetric feasible and individually-rational
point is machine-refuted as a Nash solution.

## Measurements

| Measure | EXP-069 result |
|---|---|
| semantic owner | native opt-in `GameTheory.Cooperative` branch |
| stored capabilities | none; only feasible predicate and feasible disagreement point |
| Nash-product capability | theorem-local `Fintype Player` |
| imports | ordered-field finite-product algebra and tactics; no project Probability, Core game, Protocol, or Analysis import |
| general results | weak Pareto consequence, symmetry/uniqueness equal gains, positive-affine invariance |
| hostile distinction | product four versus product three; unequal scales and nonzero shifts |
| bounded accounting | all 30 declarations classified; 14-row Nash slice promoted, 16 egalitarian/KS rows deferred |
| boundary probes | 3 bargaining inputs reached; strategic Nash, `FinDist`, Protocol execution, and measurable theory rejected |
| trust | sampled generic and fixture flagships use only `propext`, `Classical.choice`, and `Quot.sound` |
| release gate | warning-clean 3,511-job build with zero build-output commands; Phase 2 and exact coverage `VERIFIED=1` |

## Kill condition

Reject the native owner if the representative results require stored
finiteness, convexity, compactness, topology, probability, logarithms, dummy
strategic players, a parallel affine API, raw function updates/transports, or
a fixture unable to distinguish a maximizer from mere feasibility.

No kill condition fired.  The predecessor's logarithm and probability imports
were unused by the promoted theorem spine.  All additional capability remains
local, and the concrete fixture exercises a strict product comparison and a
nontrivial affine transformation.

## Consequences for the public API

`GameTheory.BargainingProblem` belongs to the opt-in
`GameTheory.Cooperative` root and remains absent from the lightweight
`GameTheory` umbrella.  Egalitarian and Kalai--Smorodinsky solutions must reuse
this problem, disagreement point, Pareto vocabulary, and `positiveAffineMap`.
Convexity, compactness, and existence may enter only through the theorem or an
Analysis bridge that needs them.
