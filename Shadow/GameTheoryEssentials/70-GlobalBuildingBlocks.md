# Global Building Blocks (All Game-Theoretic Theorems)

This is the structural synthesis across the full theorem inventory
(`TheoremInventory.csv`, 567 theorem/lemma declarations).

## B0. Finite Index Algebra

Core shape:

- products/sums over finite types,
- coordinate replacement (`Function.update`),
- fold transport and reindexing.

Shows up in:

- equilibrium existence maps,
- sequential decomposition,
- representation bridges.

Standard anchors:

- `Function.update_*` family (Mathlib)
- `Finset.sum_*`, `Fintype.prod_*`

## B1. Distributional Composition Algebra

Core shape:

- `bind` associativity/commutation where justified,
- pushforward/map normalization,
- support-sensitive extensionality.

Shows up in:

- mixed/behavioral equivalence,
- disintegration/recombination,
- mixed-extension expected-utility rewriting.

Standard anchors:

- `PMF.bind_bind`, `PMF.bind_comm`
- `PMF.bindOnSupport_*`

## B2. Locality / Non-Interference

Core shape:

- modifying coordinates outside dependency footprint leaves target unchanged.

Shows up in:

- sequential process proofs (`Proto*`, `EFGKuhn*`),
- dynamics/potential arguments (`BestResponse*`, `Potential*`, `Dominance*`).

Interpretation-neutral statement:

- update invariance + finite update composition.

## B3. Reachability-Restricted Extensionality

Core shape:

- global evaluation depends only on reachable reads/states.
- agreement on reachable support implies equal outcomes.

Shows up in:

- `EFGKuhn`, `EFGKuhnFull`,
- bridge modules where translations preserve reachable structure.

## B4. Disintegrate-Then-Recombine

Core shape:

- split global stochastic map by observable fibers,
- solve branchwise,
- recombine by outer observable law.

Shows up in:

- mixed→behavioral pipelines,
- conditional mechanism-style decompositions.

## B5. Translation/Refinement Preservation

Core shape:

- representational map preserves evaluation and predicates.

Shows up in:

- `EFG↔NFG`, `MAID↔EFG`, `Proto↔Sequential` bridges.

Non-domain analogue:

- semantics-preserving compilation/refinement.

## B6. Fixed-Point Transfer Skeleton

Core shape:

- map fixed-point identity + normalization inequalities
  => target equilibrium-like predicate.

Shows up in:

- `NashExistenceMixed`, `ProductSimplexBrouwer`, `Minimax*`.

## B7. Well-Founded Recursive Value Construction

Core shape:

- local extremum/select operation + recursive decomposition
  => global determinacy/optimality/value theorem.

Shows up in:

- `Zermelo*`, `Minimax*`, `Sequential*`.

## B8. Convex / Continuity Transfer

Core shape:

- continuity and simplex constraints are transported through map constructors
  (sum/max/normalization/update).

Shows up in:

- existence proofs for mixed equilibria and approximation-to-fixed-point transfer.

## B9. Inequality Preservation and Rearrangement

Core shape:

- nonnegativity + weighted sum manipulations + decomposition into positive/negative parts.

Shows up in:

- gain-map algebra, welfare/comparison results, regret/dominance bounds.

## B10. Adapter Minimality Principle

Core shape:

- all heavy arguments should reside in B0-B9;
- format-specific theorem surfaces should only instantiate interfaces and call core lemmas.

## B11. Feasible-Region Geometry Layer

Core shape:

- define a region by intersecting a feasible set with coordinate lower bounds,
- transport closed/compact/convex properties through this intersection,
- separate geometric envelope facts from strategic construction facts.

Shows up in:

- welfare/value region arguments,
- equilibrium payoff-region abstractions,
- mechanism IR-style constraints when encoded as coordinate floors.
