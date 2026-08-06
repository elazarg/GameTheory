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

## Consequences

On every fixed finite skeleton, the reward tables admitting a uniform-equilibrium
payoff form a closed set. Therefore the counterexample tables form an open set.
In particular, proving existence on a dense class proves existence everywhere
on that skeleton. Conversely, any finite quitting-game counterexample can be
perturbed to a rational counterexample.

The quantitative spectral defect developed in
[ReverseConsequences.md](ReverseConsequences.md) is `2`-Lipschitz in the reward
sup norm, giving an explicit robustness radius whenever the defect is positive.

## Beyond pointwise reward closeness

`GameTheory/Concepts/Stochastic/UniformAsymptoticPayoffEquivalence.lean`
isolates a more general transfer interface. It is enough to have one horizon
modulus `gap T → 0` that bounds the finite-average payoff difference for every
behavior profile and player. The theorem
`isUniformEquilibriumPayoff_withStagePayoff_iff_of_tendsto_gap_zero` then proves
exact equality of the fixed-target uniform-equilibrium predicates. This covers
transformations whose stage rewards are not pointwise close but whose cumulative
effect is only a bounded endpoint term.

The principal example is formalized in
`GameTheory/Concepts/Stochastic/UniformExpectedPotentialShaping.lean`. Adding

```text
expect (transition s a) (F i) - F i s
```

to player `i`'s stage reward telescopes in expectation to
`expectedStateValue T - F i s₀`. A bounded potential therefore changes every
finite average by `O(1/T)`, uniformly over prescribed and deviating profiles.
The theorem
`isUniformEquilibriumPayoff_withExpectedPotentialShaping_iff` proves exact
preservation of the entire uniform-equilibrium payoff set. This is the formal
gauge-invariance statement: a valid asymptotic obstruction must be invariant
under bounded expected coboundaries.

## Deliberate scope boundary

These results do **not** prove density of any particular proposed class of
solved payoff tables. That is now the substantive game-specific obligation.

They also do not extend to arbitrary perturbations of the transition kernel.
That stronger statement is **false**, not merely unformalized. The one-player,
one-action, two-state example in
`GameTheory/Concepts/Stochastic/TransitionPerturbationDiscontinuity.lean` has
uniform payoff `1` for every positive transition probability to a good
absorbing state, but payoff `1` fails at the zero-probability limit kernel.
The file additionally proves coordinatewise convergence of the finite kernel
table. Small one-step transition changes can alter recurrent-class entry and
have an order-one long-run effect.
