# Descent and Well-Foundedness

Goal:

- abstract strict-decrease/no-infinite-improvement reasoning.

GameTheory-side patterns:

- no infinite improving path,
- rank-decrease arguments for termination/stability.

Math-side target:

- generic descent templates from local strict decrease to global termination.

Equivalent names:

- `Descent` (chosen):
  - structure: each step strictly decreases along a well-founded relation.
  - equivalent names: ranking decrease, normalization descent, Lyapunov-style decrease (discrete).
- `Well-founded` (chosen):
  - structure: no infinite descending chain.
  - equivalent names: termination order, founded ordering.

External-field fit:

- program termination, rewrite system normalization, search-tree pruning.

Candidate artifacts:

- strict-decrease chain impossibility,
- local step decrease -> global no-cycle/no-infinite-path statements,
- witness-minimality lemmas for well-founded relations.
