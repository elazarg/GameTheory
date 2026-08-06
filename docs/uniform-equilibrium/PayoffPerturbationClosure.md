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

The target-free layer lives in
`GameTheory/Concepts/Stochastic/UniformPayoffExistenceClosure.lean`:

- `exists_uniformEquilibriumPayoff_of_uniform_stagePayoff_limit` assumes only
  that every approximating reward table has some uniform-equilibrium payoff;
- `exists_uniformEquilibriumPayoff_of_arbitrarily_close_stagePayoffs` proves
  that existence on arbitrarily close fixed-skeleton tables implies existence
  for the original table.

The proof reuses the nearby game's behavior profile directly. It takes no
limit of strategies and assumes no common memory bound. For the target-free
statement, equilibrium targets lie in a common finite-dimensional payoff cube;
only a subsequence of those payoff vectors is passed to a limit.

## Deliberate scope boundary

This result does **not** cover either of the following stronger claims:

1. continuity under perturbations of the transition kernel; or
2. density of any particular proposed class of solved payoff tables.

The second item is now the substantive game-specific obligation: once a class
is proved dense, the target-free closure theorem promotes its existence result
to every payoff table on the same finite skeleton.
