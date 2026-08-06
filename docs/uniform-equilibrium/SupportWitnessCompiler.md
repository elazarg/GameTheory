# Support-witness quitting-path compiler

The support-witness route retains the one-stage product root certifying each
approximate continuation step.  This is stronger than a probability-weighted
endpoint inequality: whenever Quit or Continue is played with positive
probability, that endpoint is individually within the prescribed tolerance of
the alternative.

## Deterministic clock collapse

For player `i` at stage `t`, let `q_t` be the prescribed Quit probability and
let `D_t` be Quit payoff minus Continue payoff.  The existing ledger identity
is

```text
ledgerIncrement_t = -q_t D_t.
```

The support condition gives `D_t >= -delta` whenever `q_t > 0`, hence

```text
ledgerIncrement_t <= delta q_t.
```

Together with

```text
(product_{t<n} (1-q_t)) (1 + sum_{t<n} q_t) <= 1,
```

this proves that a ledger cannot cross its cap before the player's own planned
survival crosses a corresponding threshold.  At the first crossing among all
players, the selected player's own survival bounds its joint reach and every
other player's deleted reach.  The relevant definitions and estimates are in
`QuittingSupportWitnessClockCollapse.lean`.

## Path compiler

`QuittingSupportWitnessReduction.lean` combines that switch package with a
target-specific closed tail.  The marked player is controlled by the prefix
ledger and its closed continuation; every other player is controlled by the
marked player's deleted-reach bound.  A common punishment tail is not assumed.

`QuittingSupportWitnessIndividualRational.lean` obtains the required closed
tail from approximate individual rationality against
`quittingPunishmentValue`.  `QuittingSupportWitnessPathCompiler.lean` then
proves the quantitative theorem

```text
support error delta
+ rationality error r
+ complete absorption
  ==> terminal Nash error
      2 delta + r + sqrt(delta) (2 + 7 M),
```

where `M = quittingRewardBound reward`.  Nonsummability of the total one-stage
absorption charge implies complete absorption, so divergent-charge paths are a
direct input.  Choosing support accuracy quadratically smaller than the desired
equilibrium error yields the uniform-payoff theorem
`quittingGame_exists_uniformEquilibriumPayoff_of_supportRationalDivergentPaths`.

## Finite periodic adapter

`IsQuittingFiniteSupportRationalCycle` records at every phase:

- exact cyclic Bellman evaluation;
- the support-local endpoint witness; and
- approximate individual rationality.

If one phase has positive absorption, periodic repetition uniquely selects the
cyclic terminal values and repeats a positive absorption charge once per
period.  `QuittingSupportWitnessPeriodic.lean` therefore converts the finite
cycle to the divergent path consumed above and derives both the quantitative
`3 epsilon` theorem and a uniform-payoff theorem for cycles available at every
accuracy.

## Scope boundary

These modules are compilers, not general producers.  They do not prove that an
arbitrary finite quitting game supplies a support-rational divergent path or a
finite cycle at every tolerance.  Periodicity alone also supplies neither the
support inequalities nor individual rationality; both remain explicit fields
of the finite-cycle interface.

`QuittingRankOneCrossing.lean` is a separate abstract survival estimate for a
centered bounded score process with a crossing implication and expected
variation budget.  It does not construct that process and is not used by the
deterministic support-witness compiler.  `QuittingReducedCapConjecture.lean`
likewise remains a distinct all-player truncated-ledger producer route.
