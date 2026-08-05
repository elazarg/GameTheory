# The uniform-equilibrium problem: state of this development

This document states, in ordinary mathematical language, what this
repository has established about the uniform-equilibrium existence problem
for finite stochastic games, what remains open, and what a solution — in
either direction — must look like. Claims marked with a Lean declaration
name are machine-checked; claims marked *(paper)* are proved in ordinary
mathematics within this development but not yet formalized; everything else
is attributed to the published literature.

## The problem

A uniform `ε`-equilibrium of a finite stochastic game is a behavior profile
that, for every sufficiently long horizon simultaneously, delivers a fixed
payoff vector up to `ε` and caps every unilateral deviation at `ε` gain.
Existence for every finite stochastic game is a long-standing open problem.
Known: every two-player game (Vieille, *Israel J. Math.* 2000, via
Vrieze–Thuijsman 1989 for absorbing games), every three-player absorbing
game (Solan, *Math. Oper. Res.* 1999), and various classes of quitting
games (Solan–Vieille, quitting games; Simon, *Adv. Appl. Math.* 38 (2007)).
Open from four players on, already for **quitting games** — each player
chooses only quit-or-continue, the game ends at the first quit, payoffs
depend on the set of simultaneous quitters. This repository attacks the
quitting core. Two intentional `sorry` declarations mark the targets
(`UniformExistenceConjecture.lean`, `QuittingConjecture.lean`); a build-time
audit enforces that they are import-leaves — no landed result depends on
them — and that the landed corpus reports only the standard classical
axioms.

## The reduction (machine-checked)

For quitting games the problem is exactly the production of terminal
approximate Nash families:

- terminal `ε`-Nash profiles for every `ε` exist **iff** a uniform
  equilibrium payoff exists (`QuittingTerminalUniformization`,
  `QuittingTerminalUniformPayoffSelection`);
- finite-horizon average payoffs converge to the terminal payoff
  **unconditionally, for every profile including deviations**
  (`tendsto_finiteAveragePayoff_quittingGame`) — there is no
  order-of-limits trapdoor;
- against fixed opponents, an arbitrary behavioral deviation is a mixture
  of pure stopping times; on the live path, history is calendar time.

## The machine-checked perimeter (existence)

- **Zero-solo weights** (every solo payoff `≤ 0`): payoff `0`
  (`QuittingZeroSoloDisjunct`).
- **Admissible exact cycles** compile to uniform payoffs
  (`QuittingAdmissibleCycleTerminalEquilibrium`).
- **Every two-player quitting game**
  (`quittingGame_exists_uniformEquilibriumPayoff_twoPlayer`) —
  the statement is classical (Vrieze–Thuijsman era); the machine-checked
  route is new: a four-branch classification with no discount limit,
  built to generalize.
- **The circulation engine**: a *singleton-face circulation certificate* —
  a closed polygon of feasible payoff vectors stepping through solo faces,
  each phase owner pinned at its solo value, everything above the
  solo/min-max floor — produces support-perfect rational orbits of
  arbitrarily large quit mass (`SingletonFaceCirculationOrbit`,
  `MultiOwnerFaceCirculationOrbit`), the raw material the conversion
  machinery consumes. Verified instances include the
  Flesch–Thuijsman–Vrieze cyclic weight and a four-player stress point
  lying off every bounded-period exact branch
  (`RepairedFourPlayerStressCirculation`).

## The negative map (machine-checked impossibilities)

Each item is a theorem closing a proof route; each must be read as exactly
that — a certified obstruction to the formalized route, not a metaphysical
claim about all possible proofs.

- **Exact-cycle methods cannot be complete.** An explicit perturbed cyclic
  three-player weight admits **no exact cycle of any period**
  (`PerturbedCyclicWeightNoExactCycle`,
  `PerturbedCyclicWeightCycleExistenceHoleOccupied`) — the mechanism is a
  *label lock*: the active player's continuation value pins at its solo
  value while both neighbours are forced strictly above, so the active role
  can never hand off exactly. The weight still has relaxed cycles at every
  tolerance (Solan, *Int. Game Theory Rev.* 2001, proves the period must
  diverge). Exact objects are not limits of relaxed ones.
- **The weighted one-stage equilibrium notion cannot price motion.**
  Symmetric trembles are weighted-near-Nash at every small tolerance while
  their value motion per quit mass vanishes
  (`WeightedRowMotionSeparation.no_motion_price_scaledCyclicWeight`); the
  same weight has neither stationary nor instant approximate equilibrium
  families (`ScaledCyclicWeightNoApproximateEquilibria`). Consequently the
  support-perfect/weighted distinction is load-bearing everywhere.
- **What the weighted notion does support**: the continue mass of a
  weighted-near row at a rational vector is bounded below
  (`QuittingWeightedContinueMassBound`) — motion is available; the
  difficulty is steering it without driving any player below min-max.
- **No public randomization, and padding smuggles it.** The finite-horizon
  feasible set is provably non-convex (`Feasible.lean`), yet padding action
  sets with payoff-irrelevant duplicates strictly enlarges attainable
  values — duplicate labels carry a jointly controlled lottery
  (`PaddedDuplicateLotterySeparation`). Raw-history padding reductions are
  unsound.
- **The circulation engine has a real boundary.** At two players and
  certificate length one, all four branches of the two-player theorem
  contain weights outside the class
  (`QuittingCirculationTwoCoordinateBoundary`): the certificate's floor
  demands every owner's payoff dominate its own solo value, while Nash
  rationality legitimately compensates sub-solo coordinates with collision
  penalties. **The blind spot is named: sub-solo coordinates under
  collision compensation.**
- Additional closed routes, each with a witness: conservation/budget
  arguments for repair, compactness over periods, uniform tail tightness,
  pointwise purification of trembles, bounded surgery with
  cutoff-independent decrement.

## Proved on paper, formalization pending

- **The min-max of a quitting weight is a stationary stopping value**:
  `χ_j = inf_y max{S_j(y), H_j(y)/(1−c(y))}` over constant opponent rows —
  no non-stationary punishment does better, `ε`-attained by rational rows.
  The solo-clipped ceiling `max{0, d_j}` is not tight in general (a
  machine-checked two-player table has finite-horizon punishment value
  strictly below it: `QuittingPunishmentFloor`).
- **The repaired equivalence.** Simon (2007), Theorem 3, links approximate
  equilibria to relaxed cycles and to unbounded-variation orbit families.
  This development located and repaired defects in its proof: the
  survival-window landing step (repaired by *continuation lifting* —
  replace the next-stage continuation coordinatewise by its max with the
  min-max, rational by construction; formalized:
  `QuittingSurvivalWindowLanding`), and the per-stage bound's proof
  (its stationary-approximate inference fails for the one-shot equilibrium
  notion; the support-perfect version is repaired by Solan–Vieille's
  perfection-to-equilibrium proposition — the very result Simon's own
  Proposition 3 improves).
- **A four-player cyclic two-parameter family solved end to end** *(paper,
  certificate instances machine-checked)*: rational singleton-face
  circulations with explicit payoff at every parameter, and the complete
  lock classification at four coordinates.

## The open core, stated precisely

Two questions, different certificate shapes:

1. **The residual habitat.** Does any quitting weight (`n ≥ 3`, some
   positive solo value) lie outside *stationary ∪ instant ∪ circulation*?
   The candidate shape is explicit from the boundary theorem: every
   potential phase owner carries a sub-solo coordinate requiring collision
   compensation. A weight there either specifies the missing engine or
   seeds a counterexample. The known three-player theorems (Solan 1999)
   guarantee such weights, if any, are covered by *some* mechanism at
   `n = 3` — which makes reproducing three-player existence inside this
   architecture the decisive expressiveness test.
2. **Orbit boundedness — the tractable negative.** By the (repaired)
   equivalence, nonexistence at a weight is equivalent to: for some
   `ε₀ > 0`, every `ε₀`-rational orbit of the one-stage relation has
   bounded total quit mass. This is falsifiable by a *local certificate* —
   a potential function decreasing along every relation step by a
   quit-mass-proportional quantum — and is therefore the machine-tractable
   direction. No such certificate is known at any weight; the search is
   instrumented for them.

A quantitative program sits alongside: exact cycles of period `L` form
semialgebraic strata in weight space, relaxed families exist when strata
pass within backward distance of the weight
(`QuittingRootEndpointBackwardStability`), and the minimal-period law is
conjecturally governed by stratum conditioning. **Caveats, honestly**: the
union over unbounded periods need not be tame, so this route requires a
uniform structure across periods that is not yet identified; and of the
conjectured identification of the three hardness measures (condition
number, lock margin, weighted-gain weakness), one leg is a theorem
(`QuittingBackwardStabilityConditionNumber`) and the rest is hypothesis.

## An invitation

The negative map and the boundary theorem are, deliberately, an attack
surface. A counterexample hunter should look for: a rational quitting
weight, at least three players, positive solo values, every potential owner
sub-solo-compensated, admitting no stationary or instant approximate
equilibria — and then either a circulation-type certificate (which would
extend the engine) or a bounded-orbit potential (which would refute
existence). The fences above say every simpler route is closed.

## References

J. Flesch, F. Thuijsman, O. J. Vrieze, *Cyclic Markov equilibria in
stochastic games*, Int. J. Game Theory 26 (1997). ·
E. Solan, *Three-player absorbing games*, Math. Oper. Res. 24 (1999). ·
E. Solan, N. Vieille, *Quitting games*, Math. Oper. Res. 26 (2001). ·
E. Solan, *The dynamics of the Nash equilibrium correspondence and n-player
stochastic games*, Int. Game Theory Rev. (2001). ·
N. Vieille, *Two-player stochastic games I–II*, Israel J. Math. 119 (2000). ·
O. J. Vrieze, F. Thuijsman, *On equilibria in repeated games with absorbing
states*, Int. J. Game Theory 18 (1989). ·
R. S. Simon, *The structure of non-zero-sum stochastic games*, Adv. Appl.
Math. 38 (2007).
