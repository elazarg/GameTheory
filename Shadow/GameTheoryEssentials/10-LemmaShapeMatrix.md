# Lemma-Shape Matrix (Definition-Free, Cross-Field Names)

This matrix describes reusable proof shapes that recur across game-theory modules.

## G1. Local Non-Interference by Update Invariance

### Shape

Pointwise invariance under `Function.update` on a coordinate set implies invariance under finite update folds.

### Appears in families

- F3 (protocol/trace)
- F5 (dominance/potential updates)

### Other-field names

- program semantics: frame property / non-interference
- compiler theory: dead-store invariance

## G2. Reordering Independent Random Sources

### Shape

Bind order can be swapped/refactored when continuation dependency sets are disjoint.

### Appears in families

- F3 (Kuhn-style factorization)
- F4 (mixed/correlated equivalence constructions)

### Other-field names

- probability: conditional independence factorization
- probabilistic programming: Fubini/commutation for independent effects

## G3. Observable-First Disintegration

### Shape

Decompose global stochastic evaluation by observable fibers, solve branchwise, recombine.

### Appears in families

- F3 (mixed→behavioral constructions)
- F6 (mechanism branch conditioning)

### Other-field names

- measure theory: disintegration
- Bayesian inference: law of total probability / posterior mixture

## G4. Tail Transport of Structural Predicates

### Shape

A structural condition on a full process induces the same kind of condition on suffixes.

### Appears in families

- F3, F5

### Other-field names

- inductive invariants under suffix restriction

## G5. Reachable-Agreement Congruence

### Shape

Two local policy maps that agree on reachable observations induce equal global outcomes.

### Appears in families

- F3, F2

### Other-field names

- semantics: contextual equivalence on reachable states
- model checking: equivalence up to unreachable states

## G6. Representation-Preserving Translation

### Shape

A translation between representations preserves evaluation and target predicates.

### Appears in families

- F2, F4, F7

### Other-field names

- compiler correctness: semantics preservation
- category theory: functor preserving property class

## G7. Backward-Induction / Well-Founded Recursion

### Shape

Local extremum selection + well-founded recursion implies global optimal/determinate value.

### Appears in families

- F3 (Zermelo-like)
- F7 (minimax/value)

### Other-field names

- dynamic programming principle
- Bellman optimality

