# Disintegration Layer

Goal:

- normalize “project then condition then recombine” proofs.

GameTheory-side patterns:

- branchwise decomposition of global distributions,
- conditional recombination.

Math-side target:

- PMF disintegration wrappers with support/fiber side conditions isolated.

Equivalent names:

- `Disintegration` (chosen):
  - structure: factor a distribution by projection classes and conditionals.
  - equivalent names: total-probability decomposition, mixture-by-fiber decomposition.
- `Fiber` (chosen):
  - structure: preimage class `{x | project x = y}`.
  - equivalent names: slice, conditioning class, bucket.

External-field fit:

- Bayesian filtering, diagnostics by observed class, mixture models.

Candidate artifacts:

- bind-disintegrate normal form,
- fiber-mass support lemmas,
- ratio/cancellation wrappers for conditioned mass.
