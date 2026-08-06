# Uniform-equilibrium payoff stability under reward perturbations

For a fixed finite stochastic-game skeleton—players, states, actions, transition
kernel, and discount field—uniform-equilibrium payoffs are stable under uniform
perturbations of the stage-payoff table.

The formal interface lives in
`GameTheory/Concepts/Stochastic/Uniform.lean`:

- `StochasticGame.withStagePayoff` replaces only the stage-payoff table;
- `abs_finiteAveragePayoff_withStagePayoff_sub_le` proves that a pointwise
  reward perturbation of size `ρ` changes every finite-horizon payoff by at
  most `ρ`, for every behavior profile;
- `IsεHorizonNash.of_withStagePayoff` transfers Nash inequalities with loss
  `2 * ρ`, including arbitrary unilateral behavioral deviations;
- `isUniformEquilibriumPayoff_of_arbitrarily_close_stagePayoffs` is the direct
  dense-approximation interface when nearby equilibrium targets are also close;
- `isUniformEquilibriumPayoff_of_uniform_stagePayoff_limit` gives the
  sequential closedness statement for uniformly convergent reward tables and
  convergent uniform-equilibrium targets.

The proof reuses the nearby game's behavior profile directly. It takes no
limit of strategies and assumes no common memory bound.

## Deliberate scope boundary

This result does **not** yet formalize either of the following stronger claims:

1. continuity under perturbations of the transition kernel; or
2. target-free closedness of mere existence, which additionally requires
   extracting a convergent subsequence from a bounded family of equilibrium
   payoff vectors.

The second step is finite-dimensional compactness, but it is kept separate so
that the Lean theorem records exactly which compactness argument has been
supplied.
