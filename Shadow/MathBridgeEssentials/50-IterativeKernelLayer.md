# Iterative Kernel Layer

Goal:

- unify iterate/fold/bind laws in one reusable layer.

GameTheory-side patterns:

- repeated step kernels,
- decomposition by horizon split,
- congruence under local kernel equality.

Math-side target:

- generic PMF iteration API (`iter`, additivity, congruence, successor).

Equivalent names:

- `Kernel` (chosen):
  - structure: map `X -> PMF Y`.
  - equivalent names: stochastic transition operator, Markov step map.
- `Iterative kernel` (chosen):
  - structure: repeated Kleisli composition.
  - equivalent names: n-step transition, rollout operator, propagator iterate.

External-field fit:

- Markov chains, randomized algorithms, stochastic control rollouts.

Candidate artifacts:

- iterate-add (Chapman-Kolmogorov form),
- iterate-congr under pointwise kernel equality,
- fold-bind normalization lemmas.
