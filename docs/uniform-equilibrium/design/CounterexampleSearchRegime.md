# Searching for a quitting-game counterexample

This document specifies the production constraints that a computational search
for a finite quitting game without a uniform-equilibrium payoff should enforce.
It is a falsification and candidate-ranking protocol, not a claim that the
infinite-horizon conjecture has been reduced to a decidable finite program.

## The combined regime

Fix a finite quitting reward table `reward`.  Let:

- `D_N` be the attained minimum, over zero-boundary exact-D chains of cutoff
  `N`, of the maximum playerwise dynamic debt;
- `P_floor` be the family of finite exact Nash--Bellman prefixes in the
  canonical reward box whose initial value dominates the behavioral punishment
  floor; and
- `q(x) = 1 - ∏ i, x_i(Continue)` be the absorption mass of a product root.

The production counterexample regime consists of three numerical margins

```text
terminal gap η > 0
dynamic-debt floor δ > 0
prefix-charge budget C ≥ 0
```

satisfying:

1. Every behavioral profile has a unilateral terminal-payoff improvement of at
   least `η`.
2. `δ ≤ D_N` at every cutoff `N`.
3. Every `P ∈ P_floor` satisfies `∑ t < |P|, q(P.root t) ≤ C`.

This package is equivalent to nonexistence of a uniform-equilibrium payoff.
The terminal gap supplies the reverse implication by itself; the debt floor and
charge budget are additional restrictions forced on every counterexample.

The Lean interface is `QuittingCounterexampleRegime`.  Its exact
characterization is
`not_exists_uniformEquilibriumPayoff_iff_nonempty_counterexampleRegime`.

## Derived geometry

The debt and charge fields have stronger derived forms.

The positive debt floor produces a subsequential limit of attained finite
minimizers.  The limit is an infinite exact-D path with a positive initial debt
coordinate for some player and a summable opponent clock for that player.

The charge budget extends from anchored prefixes to every path in the
punishment-floor reachable exact-predecessor relation.  Its canonical
budget-to-go function is nonnegative, bounded above by `C`, and satisfies

```text
potential(current) + absorptionCharge(edge) ≤ potential(tail).
```

Every closed reachable exact-predecessor path therefore has zero total charge.
In particular, a reachable positive-charge cycle is a decisive certificate
that the table is not a counterexample.

The positive-debt path and the floor-reachable predecessor relation are not yet
identified.  The first comes from zero-boundary optimized exact-D chains; the
second starts at the behavioral punishment-floor anchor.  Search output must
not silently treat them as one orbit.

## Search lanes

### Reward-table enumeration

Begin with four players.  The one-player case is elementary, and production
theorems cover the two- and three-player tables.  Small rational tables and
tables with symmetry are useful seed families, but symmetry should be a search
parameter rather than an assumed property of a counterexample.

For each proposed normalization, record the original reward table and the
exact affine transformation.  Numerical normalization is useful, but a solver
must not compare margins obtained under different payoff scales as if they
were absolute.

### Exact-D optimization

For increasing cutoffs, solve the compact attained optimization defining
`D_N`.  Record:

- the exact or certified interval value of `D_N`;
- the minimizing chain;
- the active debt owner or tied owner set;
- the successive optimum drop;
- joint and deleted-player survival along the minimizer.

The values are nonincreasing and nonnegative.  Decay toward zero is evidence
for the existing uniform-payoff compiler, while a plausible counterexample
must display a persistent positive floor.  A positive value at one or several
cutoffs is not a proof of a positive infimum.

### Punishment-floor charge optimization

For increasing horizons, maximize total absorption charge over exact
punishment-floor prefixes.  The fixed-horizon constraints consist of simplex,
reward-box, exact Bellman, exact root-Nash, and floor inequalities, so they are
suited to nonlinear, semialgebraic, or interval-certified optimization.

Search separately for a prefix followed by an exact positive-charge cycle.
That finite witness is decisive: repetition gives arbitrarily charged prefixes
and hence a uniform payoff.  In its absence, attempt to synthesize a bounded
potential on the explored predecessor graph.  On a finite abstraction this is
a system of difference inequalities; on a continuous cell decomposition it
can be approached with piecewise-affine, polynomial, or sum-of-squares barrier
templates.

Apparent saturation of the horizon maxima is only candidate evidence.  The
current generic attained finite-horizon API assumes a finite edge type and does
not by itself prove compact continuum-edge attainment for the quitting
relation.

### Terminal exploitability

Estimate the least terminal exploitability over increasingly rich profile
classes.  Include at least stationary, small-period, delayed, elementary-cap,
and marked-cylinder candidates where the corresponding semantic decoder is
available.

Finding terminal approximate Nash profiles at errors tending to zero produces
a uniform-equilibrium payoff.  Failure in a restricted profile grammar does
not establish a terminal gap against all behavioral profiles.  A rigorous
counterexample certificate must ultimately provide one `η > 0` valid against
the entire behavioral profile space.

## Candidate record

A search result should retain enough information to reproduce and compare all
three lanes:

```text
reward table and normalization
player count and declared symmetries
cutoff N
certified D_N interval and minimizing exact-D chain
optimized prefix-charge interval and maximizing exact prefix
best terminal exploitability interval and profile grammar
positive-cycle search result
solver residuals and exact rational reconstruction, when available
```

Do not promote a floating-point candidate solely because all three finite
trends look favorable.  Promotion requires either exact Lean witnesses or
certified inequalities with enough data for reconstruction.

## The cross-lane question

The most useful consistency test is not another independent optimizer.  It is
an adapter or inequality relating the positive optimized exact-D tail to the
floor-reachable bounded-potential relation.

A successful anchoring theorem would put bounded total absorption, positive
dynamic debt, and a summable opponent clock on one compatible path.  The
resulting asymptotic root would be forced toward a narrow all-Continue or
single-owner face.  The next question would then be whether that face can still
support a uniform positive terminal exploitability gap.  Proving that it
cannot would rule out the combined regime and close the remaining
counterexample branch.
