# Uniform-equilibrium consequences

This page records a small semantic layer around
`StochasticGame.IsUniformEquilibriumPayoff`.  These are invariance, reverse,
and negative diagnostic results; they are not a producer of uniform
equilibria for arbitrary games.

## Vanishing payoff gaps and potential shaping

On a fixed game skeleton, suppose one horizon modulus tends to zero and bounds
the finite-average payoff difference between two reward tables for every
behavior profile and player.  Then each exact uniform-equilibrium payoff target
is preserved in both directions.

Bounded expected-potential shaping is an exact application.  Adding
`E[F_i(s')] - F_i(s)` to player `i`'s stage reward telescopes in expectation
to an endpoint difference.  A bounded potential therefore gives an
`O(1/T)` profile-uniform finite-average gap and preserves every exact target.

## Reverse characterizations

Uniform-payoff existence is equivalent to arbitrarily thin eventual intervals:
for every positive width, some profile eventually keeps prescribed payoff above
the lower endpoint while every unilateral behavioral deviation is below the
upper endpoint.  Consequently, nonexistence gives a fixed positive width that
defeats every such interval.  The extraction compactifies only interval
midpoints in a common payoff cube; it uses no compactness or limit of behavior
profiles.

For a fixed target, uniform equilibrium is equivalent to bounded excess-work
certificates at every positive penalty.  One profile and one finite budget then
control every horizon's deviation excess and prescribed-play deficit.  Its
negation is exactly the corresponding positive unbounded-work obstruction.

For finite quitting games there is an additional exact negative
characterization.  Nonexistence of any uniform-equilibrium payoff is equivalent
to the existence of one fixed `gap > 0` such that every behavioral profile has
a unilateral deviation improving expected terminal reward by at least `gap`.
The forward direction negates terminal approximate Nash existence at every
positive accuracy; the reverse direction is the existing terminal-gap
nonexistence compiler.  This is an exact semantic target for counterexample
search, not a finite separator language by itself.

## Transition warning

Rare transitions give a two-state warning: transition kernels can converge
coordinatewise while a fixed uniform-payoff target holds at every positive
rare-transition probability and fails at the zero-transition limit.  Reward
invariance therefore does not extend to unrestricted transition-kernel
perturbations.

## Lean surface

- `UniformAsymptoticPayoffEquivalence.lean` contains the two transfer directions
  and their fixed-target equivalence.
- `UniformExpectedPotentialShaping.lean` proves the expectation telescope,
  finite-average bound, and exact shaping invariance.
- `UniformTailWidth.lean` and `UniformTailWidthObstruction.lean` contain the
  thin-interval characterization and its positive-width contrapositive.
- `UniformBoundedWork.lean` contains the bounded-work characterization and its
  exact unbounded-work obstruction.
- `UniformNonexistenceCertificate.lean` separately contains the late-horizon
  and terminal exploitability certificates and the exact finite-quitting
  fixed-gap characterization.
- `TransitionPerturbationDiscontinuity.lean` contains the finite counterexample;
  `UniformConsequences.lean` is the public entry point for the generic
  reverse-consequence layer above.
