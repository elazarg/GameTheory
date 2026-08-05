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
quitting core. Three intentional `sorry` declarations mark the targets
(`UniformExistenceConjecture.lean`, `QuittingConjecture.lean`, and the
reduced six-clause ledger-cap package `QuittingReducedCapConjecture.lean`,
whose implication to the quitting conjecture is machine-checked gap-free,
so the program's progress metric is clause shrinkage); a build-time audit
enforces that they are import-leaves — no landed result depends on them —
and that the landed corpus reports only the standard classical axioms.

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
- **The circulation engine — a machine-checked *construction engine*, not
  yet a machine-checked existence theorem.** A *singleton-face circulation
  certificate* — a closed polygon of feasible payoff vectors stepping
  through solo faces, each phase owner pinned at its solo value, everything
  above the solo/min-max floor — produces support-perfect rational orbits
  of arbitrarily large quit mass (`SingletonFaceCirculationOrbit`,
  `MultiOwnerFaceCirculationOrbit`). Verified instances include the
  Flesch–Thuijsman–Vrieze cyclic weight and a four-player stress point
  lying off every bounded-period exact branch
  (`RepairedFourPlayerStressCirculation`). The implication *from* such
  orbit families *to* uniform payoffs is the repaired equivalence of the
  next section — paper-level, formalization the program's first priority —
  so the certificate's payout is currently conditional, and the same
  applies to the negative direction below. **Both exits of the open core
  route through the pending items**; they are the precondition for any
  hunt's output to be a result on the day it is found.

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
- **Why folk-theorem technology dies in quitting games — in one sentence,
  all machine-checked**: the feasible set is non-convex (`Feasible.lean`),
  there is no time-sharing (the game ends at the first quit), and there is
  no on-path signaling capacity (live history is calendar time) — so the
  three standard folk-theorem resources are simultaneously absent. Padding
  action sets with payoff-irrelevant duplicates *smuggles* the missing
  randomization back in — duplicate labels carry a jointly controlled
  lottery, strictly enlarging attainable values
  (`PaddedDuplicateLotterySeparation`) — so raw-history padding reductions
  are unsound. Together with the stationary attainability of the min-max
  *(paper)*, these three legs also fence the correlated-equilibrium
  relaxation route: no on-path channel, no smugglable device, and no need
  for off-path correlation in punishment.
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

- ~~The min-max of a quitting weight is a stationary stopping value~~ —
  **now machine-checked**, see the closing section: `χ_j = inf_y
  max{S_j(y), H_j(y)/(1−c(y))}` over constant opponent rows, both
  inequalities, against all history-dependent plans
  (`QuittingStationaryMinMax`).
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
2. **Orbit boundedness — the compact-certificate negative.** By the
   (repaired) equivalence, nonexistence at a weight is equivalent to: for
   some `ε₀ > 0`, every `ε₀`-rational orbit of the one-stage relation has
   bounded total quit mass. A *local certificate* — a potential function
   decreasing along every relation step by a quit-mass-proportional
   quantum — would settle a negative instance decisively. The converse now
   *exists* and is machine-checked at the abstract level
   (`Math/ChargedPathBudget`): an orbit relation has uniformly bounded
   total quit mass **iff** a bounded potential exists, with exact strong
   duality (the least oscillation equals the budget, attained by the
   budget-to-go), and the negative filters (positive-charge self-loops and
   cycles) refute every potential class at once — calibrated on this
   repository's own one-stage operator, where the two-player quit-bonus
   table's exact half-charge self-loop correctly kills every potential
   (`QuittingQuitBonusSelfLoopBridge`). Read the remaining asymmetry
   correctly, for it is now itself a theorem: the format is semantically
   complete but effectively sufficient-only — the affine level and every
   fixed semialgebraic template are exactly decidable, yet continuous,
   affine, and polynomial classes are provably incomplete (a compact
   relation of budget one admits only discontinuous potentials), and no
   decision procedure covers the full format. Failure of any finite search
   level carries little evidence; finding a certificate is decisive.

   **The shared failure mode of both questions, named.** At any fixed
   certificate length, membership in each engine class is a first-order
   sentence over the reals — decidable, so every cleared weight is
   provably clear *at that length*. The only escape is certificate length
   diverging as tolerance shrinks — which is this program's own signature
   phenomenon (the period-divergence theorems). Both open questions can
   therefore be *true without uniform witnesses*: union-completeness
   holding with diverging certificate length (the search never halts on
   either answer), accumulation holding but not tamely (the geometric
   route never closes). This — not any single caveat — is the
   characteristic unknown of the problem as this program has shaped it.

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
existence). The fences above close every simpler route **within the
cycle/orbit/one-stage-correspondence family, against the pre-2007
technology they formalize**; the later topological line and post-2007
partial results sit outside the fences and are honestly unfenced.

**The habitat has since been re-measured and it moved**
(`QuittingCirculationChiFloorBoundary`). Sharpening the certificate's floor
to the true min-max and freeing the owner's hazard covers, at two players,
exactly the branches the original boundary excluded — the sub-solo blind
spot was an artifact of the solo floor. The two branches that *survive*
outside the sharpened class escape for a structural reason no floor can
touch: their equilibrium payoffs lie **outside the solo-row hull** (the
all-continue payoff, and simultaneous-quit payoffs, are provably not convex
combinations of solo rows — while every circulation target is). So the
corrected habitat specification is: weights whose every equilibrium payoff
leaves the solo hull *and* which admit no exact mechanism (sure-exit sets,
all-continue). The corresponding engine extension is equally explicit:
circulations through arbitrary **coalition faces**, whose per-phase
deterrence condition is the sure-exit-set criterion — no member leaves, no
outsider joins.

**The front end of that road is now closed, formally.** The sure-exit-set
criterion is a theorem (`QuittingSureExitSet`): "exactly `S` quits surely"
is an exact terminal equilibrium iff no member prefers to leave and no
outsider prefers to join, with the unilateral deviation cap computed
unconditionally as the membership-toggle maximum. The gate for the
one-owner branch is also a theorem, and it is *not* the naive one
(`QuittingBlockerIntervalCover`): when every owner rate is blocked, a
single blocking opponent need not exist — the affine no-join gains cut
`(0,1]` into initial and terminal positivity intervals, so the failure is
witnessed by a universal blocker *or a switching pair of blockers*, never
more; with at most two opponents the switching branch is vacuous, so
three players is exactly the threshold at which the naive designation
breaks. And the branch map built from these exact mechanisms is provably
not total: a rational three-player table
(`QuittingSwitchingResidueRegression`) escapes the zero-solo, sure-exit,
one-owner, and every one-stage sure-blocker collision branch — for the
scalar reason, machine-checked, that owner endpoint optimality forces the
collision rate to a boundary value at which either the resulting pair
set fails the sure-exit criterion or the spectator preempts. The
derivation alongside is now machine-checked on both of its legs.

**The punishment floor and the repair criterion are now theorems.** The
min-max formula is formalized in full generality
(`QuittingStationaryMinMax`): the punishment value — infimum over *all*
history-dependent opponent plans of the supremum over all replies — equals
the infimum over constant rows of the two-branch stopping value, with no
attainment asserted; the reply value against a constant row needs no
contraction hypothesis; and the solo-clipped ceiling is *strictly* loose
(an explicit table has punishment value `0` against ceiling `2`). Priced
against that exact floor, the one-stage collision repair is exactly
characterized (`QuittingCollisionRepairCharacterization`): the mechanism
admits accuracy-indexed equilibria **iff** owner endpoint optimality,
every spectator's punishment-independent no-join, and the blocker-floor
balance hold — both directions, arbitrary player count, the sufficiency
leg constructing its punishment row from the min-max theorem. A sub-floor
gap `γ` forces collision intensity `δ ≥ γ/(γ+p)`, the mechanism provably
fails at every rate below `γ/(4M)`, and at the sure rate the criterion
collapses to the sure-exit test.

**The two-scale producer is refuted, and the road turns** *(paper)*. The
conjectured missing engine — rare collision phases at vanishing occupation
repairing a failed one-stage mechanism — cannot exist: the occupation
charge occurs in none of the pointwise phase inequalities, so a
vanishing-error family of such phases exists only where an exact one-stage
repair or sure-exit set already does, and rotating owners against a fixed
blocker does not average failure away. The escaping regression table was
in fact never residual: it carries an exact rational period-one orbit
(row `(1, 2/7, 1)`, value `(5/7, 0, 2/7)`), absorbed by the exact-cycle
engine, with exact floors `(2/3, 0, 2/7)` and no sub-floor gap — the
obstruction lives at the branch interface, not in the orbit relation. The
genuinely missing operation is **support enlargement**: with a sure
blocker, let *both* remaining players mix; the two interior indifference
equations have explicit rational solutions, and together with the
blocker's quit-now inequality and the min-max floors they are necessary
and sufficient for an exact stationary terminal equilibrium on that cell
*(paper)*. After the full catalogue — sure-exit sets, the blocker gate,
collision repair, two-owner roots — the residue at three players is a
finite semialgebraic class; whether it is empty, or which of its members
the cycle and circulation engines absorb, is the current three-player
closing question.

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
