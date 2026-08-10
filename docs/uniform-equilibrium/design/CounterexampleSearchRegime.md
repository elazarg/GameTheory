# Searching for a quitting-game counterexample

This document specifies the production constraints that a computational search
for a finite quitting game without a uniform-equilibrium payoff should enforce.
It is a falsification and candidate-ranking protocol, not a claim that the
infinite-horizon conjecture has been reduced to a decidable finite program.

## The combined regime

Fix a finite quitting reward table `reward`.  Let:

- `D_N` be the attained minimum, over zero-boundary exact-D chains of cutoff
  `N`, of the maximum playerwise dynamic debt;
- `Δ = inf_N D_N`;
- `K = max_i max(0, r_i({i}))` and `M` be the canonical bound on the whole
  reward table;
- `P_floor` be the family of finite exact Nash--Bellman prefixes in the
  canonical reward box whose initial value dominates the behavioral punishment
  floor; and
- `C* = sup { charge(P) | P ∈ P_floor }` in the extended nonnegative reals;
- `q(x) = 1 - ∏ i, x_i(Continue)` be the absorption mass of a product root.

The production counterexample regime consists of two independent conditions:

```text
terminal gap η > 0
canonical prefix-charge capacity C* < ∞
```

satisfying:

1. Every behavioral profile has a unilateral terminal-payoff improvement of at
   least `η`.
2. `C*` is finite; equivalently every `P ∈ P_floor` satisfies
   `∑ t < |P|, q(P.root t) ≤ C*`.

This package is equivalent to nonexistence of a uniform-equilibrium payoff.
The terminal gap supplies the reverse implication by itself; finite charge
capacity is additional structure forced on every counterexample.

Dynamic debt is not an independent field.  The terminal compiler gives the
sharp cross-lane chain

```text
0 < η ≤ Δ ≤ D_N ≤ K ≤ M.
```

Thus every counterexample has a positive optimized exact-D floor, and some own
singleton reward is positive.  The former free parameter `δ` was redundant.
The capacity `C*` is canonical: its real value is the least valid prefix bound,
not a user-chosen larger constant.

The Lean umbrella is `CounterexampleRegimeAll`.  The direct characterization
is `not_exists_uniformEquilibriumPayoff_iff_exists_gap_and_finiteChargeCapacity`.

### Derived finite and asymptotic narrowing

The regime is machine-checked EMPTY below four players
(`QuittingCounterexampleRegime.three_lt_card`): fewer than two players is
refuted by the toggle consequences below, and two or three players by a new
player-reindex transport (`Classification/PlayerReindexNaturality.lean`) of the
unconditional `Bool` and `Fin 3` existence theorems.  A one-player existence
theorem for arbitrary `Unique` player types
(`quittingGame_exists_uniformEquilibriumPayoff_onePlayer`) fills the
previously unformalized base case.

Player relabeling now preserves specified uniform-equilibrium payoffs and
counterexample-regime inhabitation in both directions.  Hence any hypothetical
finite counterexample may be searched on `Fin n`.  It may moreover be chosen
cardinality-minimal with `n ≥ 4`; every smaller nonempty player type, and every
nonempty proper restriction of the minimal table, then has a uniform-equilibrium
payoff as a game in its own right (`MinimalFinCounterexample.lean`).  The
restriction theorem does not extend that payoff to excluded players or control
their joining deviations.

Further machine-checked necessary conditions
(`CounterexampleRegimeToggles.lean`, `CounterexampleRegimePacket.lean`):

- no profile is terminally `ε`-Nash for any `ε < η`
  (`not_isεAsymptoticNash_of_lt_terminalGap`);
- every coalition's sure-exit profile is exploitable by a membership toggle
  at margin `η` (`exists_toggle_gain`), splitting into a leave-or-join
  disjunction (`exists_leave_or_join_gain`); hence no sure exit set exists
  (`not_isQuittingSureExitSet`).  Independently, any stable nonempty pure
  coalition repeats as a unit-charge exact punishment-floor prefix, forcing
  canonical prefix capacity to be infinite
  (`punishmentFloorPrefixChargeCapacity_eq_top_of_coalitionLock`).  This is the
  charge-side connection to the same screen; the terminal-gap theorem remains
  quantitatively stronger;
- some player has solo reward at least `η`
  (`exists_terminalGap_le_soloReward`, which also derives `Nonempty` of the
  player type from the regime alone), and every player whose solo reward
  exceeds `-η` has a distinct opponent whose collision reward beats its
  bystander reward by `η` (`exists_collision_gain`);
- every stationary profile is exploitable through its unilateral Snell cap,
  with no contraction hypothesis (`exists_stationaryCap_gain`);
- the analytic waist (`Classification/AnalyticWaist.lean`, general player
  type) forces a normalized singleton source packet on every counterexample
  table (`nonempty_normalizedSingletonSourcePacket`) — a finite
  semialgebraic system search code can refute directly; and
- that packet cannot be complementary on its active support.  Some owner has
  mass `0 < μ_i < 1` and satisfies

  ```text
  target_i < singletonDelivery_i < refusal_i,
  refusal_i - singletonDelivery_i
    = μ_i / (1 - μ_i) * (singletonDelivery_i - target_i).
  ```

  Otherwise the complementary-singleton circulation compiler would already
  produce a uniform-equilibrium payoff.  Moreover, for each fixed
  counterexample reward table, compactness of the closed mass/target packet
  space supplies one `δ > 0` that works for every normalized packet: some
  active owner has refusal advantage at least `δ`.  This is
  `exists_pos_uniform_normalizedSingletonPacketRefusal`.  It is robust packet
  data, not an identification with late-tail occupation;
- its weighted surplus is a quadratic form depending only on reciprocal
  singleton effects.  The skew component is pure circulation, and some two
  supported owners satisfy a positive reciprocal-effect inequality.  Tables
  whose every reciprocal pair sum is nonpositive are solved by the existing
  complementary-mixture compiler;
- the forced packet has nonempty normalized support.  Its target is at least
  `η` in some coordinate, and one supported singleton atom pays that coordinate
  at least `η` (`exists_terminalGap_le_packetTarget` and
  `exists_supportedSingleton_terminalGap`).  Unless the support is a singleton,
  every supported owner has a distinct weakly preferred supported successor,
  and a finite closed weak-preference walk exists.  This is graph structure,
  not yet a chronological Bellman orbit; and
- exact membership toggles give finite, computable upper envelopes for `η`:
  the pure-toggle ceiling and the stationary-cap ceiling both dominate the
  terminal gap.  A finite closed improvement walk can be selected from the
  exact toggle graph.  Conversely, any ordinal potential that strictly
  increases along improving toggles forces a sure-exit set and therefore a
  uniform-equilibrium payoff.

## Derived geometry

The debt and charge fields have stronger derived forms.

The terminal gap produces a subsequential limit of attained finite minimizers.
The limit is an infinite exact-D path with an owner whose initial debt is at
least `η` and whose opponent clock is summable.  Joint absorption is summable,
the values and debts converge coordinatewise, and the roots converge to
all-Continue.  Their joint limit is an exact dynamic-debt self-loop with the
selected debt still at least `η`
(`exists_terminalGapDynamicDebtTail_selfLoopLimit`).  Its selected value lies
above both the solo reward and the behavioral punishment floor.  This is a
Bellman boundary annotation, not the realized terminal payoff of Never.

Writing `u_t = v_t + d_t` for the augmented cap of an exact dynamic-debt edge,
the exact local transport law is

```text
u_t = T(x_t, u_(t+1)) + p_t ⊙ d_t,
```

where `p_t(i)` is player `i`'s own Quit probability.  The mismatch is diagonal
and nonnegative.  Positive debt therefore does not by itself supply a charged
exact predecessor at the same cap; repair or a support pivot is essential.

Subtracting the prescribed policy equation exposes exact debt conservation:

```text
d_t(i) = jointContinue_t * d_(t+1)(i) + ownQuit_t(i) * d_t(i).
```

Finite iteration and passage to the summable tail give

```text
d_s(i) = jointSurvival_(s,∞) * D_i
       + sum_k jointSurvival_(s,k) * ownQuit_(s+k)(i) * d_(s+k)(i).
```

Every seam series is summable.  For the selected owner, Continue is eventually
positive, deleted survival is exactly the endpoint debt ratio, and one late
start satisfies the dimensionless bound

```text
sum opponentClock_owner ≤ log(K_owner / η).
```

Positive debt is also floor-safe at every finite date: any positive-debt
coordinate already dominates its behavioral punishment value.

Finite exact-D caps nevertheless lie in a common reward-bounded,
punishment-floor-admissible carrier.  Closed projective passage now places every
augmented cap of the optimized infinite tail in that same carrier.  Its limit
is a literal zero-charge all-Continue exact self-loop there.  This does not make
the finite dynamic-debt transitions exact edges of the carrier relation; the
diagonal seam remains.  For a cap-seeded prefix, the difference
between cap evaluation and honest suffix-value evaluation is transported
exactly by joint survival.  If the terminal cap is separately realized as the
actual suffix's complete behavioral best-response envelope, then

```text
terminal gap ≤ joint survival * cap bound,
total prefix absorption ≤ log(cap bound / terminal gap).
```

The realization premise is essential: the cap is Bellman bookkeeping until one
suffix co-realizes both prescribed payoff and the complete deviation envelope.
A rational two-player regression shows that an augmented cap can have a unique
all-Continue exact Nash root and zero charge even though the game has an exact
terminal Nash profile.

The charge budget extends from anchored prefixes to every path in the global
boxed punishment-floor-admissible exact-predecessor relation; reachability from
one distinguished anchor is unnecessary.  Its canonical budget-to-go function
is nonnegative, bounded above by `C*`, and satisfies

```text
potential(current) + absorptionCharge(edge) ≤ potential(tail).
```

Every closed path in this carrier therefore has zero total charge.  More
locally, every recurrent edge has zero absorption.  A positive-charge return,
cycle, or self-loop anywhere in the admissible carrier is therefore a decisive
finite certificate that the table is not a counterexample.

The prefix result is genuinely all-orbits.  Every infinite exact Nash--Bellman
orbit in the canonical box whose initial value dominates the punishment floor
has total absorption at most `C*`.  Each player's quit probabilities are
summable and tend to zero, so every such root sequence converges coordinatewise
to all-Continue.  Nevertheless, the actual behavior profile starting at every
sufficiently late date remains terminally exploitable by at least `η`.

The optimized exact-D path and the floor-prefix family now meet at every date.
Every unaugmented selected-tail value dominates the punishment floor: zero
debt removes the augmented-cap term directly, while positive debt invokes the
floor-persistence/self-loop theorem.  Reversing any finite chronological
segment therefore gives an exact floor prefix with exactly the same total
absorption.  Search code may use this certificate without a punishment-sign or
endpoint filter.  It must still respect orientation: these segments have
different far-end anchors and do not constitute one outward orbit from a fixed
terminal state, nor do their annotations equal honest suffix payoffs.

## Search lanes

### Reward-table enumeration

Begin with four players.  The one-player case is elementary, and production
theorems cover the two- and three-player tables.  Small rational tables and
tables with symmetry are useful seed families, but symmetry should be a search
parameter rather than an assumed property of a counterexample.

For each proposed normalization, record the original reward table and the
exact affine transformation.  Positive scaling preserves root feasibility and
absorption charge while scaling `η`, `Δ`, `D_N`, `K`, and `M`.  Normalizing
`M = 1` puts fixed-player reward tables on a compact unit sphere and forces
`0 < η ≤ Δ ≤ K ≤ 1`.  Normalizing `K = 1` is sharper for the debt lane but does
not compactify the other reward coordinates.  A solver must not compare
payoff-scaled margins across different normalizations.

A candidate counterexample must also satisfy a robust open-neighborhood test.
There must be some `η₀ > 0` such that no reward table within coordinatewise
distance `η₀` carries an absorbing, punishment-admissible exact cycle of any
finite period.  Otherwise solved-cycle compilation followed by reward-table
closure proves existence at the candidate itself.  This is stronger than
failing to find a cycle at the original table.

For a fixed period and fixed product-root word, own-set perturbations have an
exact finite test.  The cyclic continuation correction is unique under joint
absorption and eliminates as `a(t,i) = α(t,i)d(i)`, with `0 ≤ α(t,i) ≤ 1`.
Each player's root signs therefore reduce to finite affine equalities and
half-line constraints in the one scalar `d(i)`.  Search scripts should compute
these interval intersections and the minimum residual before optimizing over
roots or richer reward perturbations.  Infeasibility rejects only this
own-set, fixed-root exactification slice; it is not evidence that the full
nearby solved-cycle stratum is empty.

### Exact-D optimization

For increasing cutoffs, solve the compact attained optimization defining
`D_N`.  Record:

- the exact or certified interval value of `D_N`;
- the minimizing chain;
- the active debt owner or tied owner set;
- the successive optimum drop;
- joint and deleted-player survival along the minimizer.

The values are nonincreasing and nonnegative.  A certified terminal gap `η`
requires `η ≤ D_N` at every tested cutoff and, mathematically, at every cutoff.
Thus `D_N < η` rejects a proposed joint certificate immediately.  Decay toward
zero is evidence for the existing uniform-payoff compiler, while a plausible
counterexample must display a persistent positive floor.  A positive value at
one or several cutoffs is not a proof of a positive infimum.

### Punishment-floor charge optimization

For increasing horizons, maximize total absorption charge over exact
punishment-floor prefixes.  These maxima approximate the canonical capacity
`C*`; unboundedness is exactly `C* = ∞`.  The fixed-horizon constraints consist
of simplex, reward-box, exact Bellman, exact root-Nash, and floor inequalities,
so they are suited to nonlinear, semialgebraic, or interval-certified
optimization.

Search separately for a positive-charge edge with an exact return path.  That
finite witness is decisive: every recurrent edge in a counterexample must have
zero charge.  Also fix thresholds `ρ > 0` and maximize the number of stages
with `q(root) ≥ ρ`.  Arbitrarily large counts at one fixed `ρ` prove existence
without knowing `C*`.  In the bounded branch, synthesize the canonical
budget-to-go potential on the explored predecessor graph.  On a finite
abstraction this is a system of difference inequalities; on a continuous cell
decomposition it can be approached with piecewise-affine, polynomial, or
sum-of-squares barrier templates.

Apparent saturation of the horizon maxima is only candidate evidence.  The
capacity is a supremum and need not be attained.  The current generic attained
finite-horizon API assumes a finite edge type and does not by itself prove
compact continuum-edge attainment for the quitting relation.

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

For every finite window cut from the optimized exact-D tail, periodic restart
does give a canonical profile to test.  Against periodic opponents, the full
behavioral best-response value is exactly the maximum of a finite first-pass
quit-time list and the refusal/`Never` value
(`sSup_range_quittingTerminalPayoff_update_eq_periodicWindow`); no survival
contraction assumption is needed.  In a counterexample regime this exact value
exceeds the restarted payoff by at least `η` for some player
(`exists_cyclicWindow_finiteEvaluation_gap`).  Thus search need not optimize
over arbitrary behavioral deviations for these profiles.  It must record which
finite branch is active: an in-window stop or refusal/`Never`.

There is a canonical family with window `n` equal to the `n+1` tail roots
starting at date `n`.  It is blocked from its first member at margin `η/2`.
On an infinite set of windows the obstructing player is fixed, and so is the
evaluator branch (refusal throughout, or a concrete window-dependent phase
stop throughout).  This is the search-facing stabilized form.  It does not
attach those periodic suffixes to arbitrary earlier exact-D prefixes.

The prescribed Bellman annotation and realized infinite terminal payoff remain
different quantities.  On the optimized tail, honest terminal payoff from a
late start tends to zero, while the selected prescribed coordinate tends to a
limit at least `η`; their difference converges to that positive limit.  Thus
the obstruction is a positive phantom plateau living on the Never boundary.
More generally, the discrepancy is exactly terminal joint survival times the
limiting boundary annotation.  Favorable signed drift can overdeliver while a
restart remains behaviorally unexploitable, so drift magnitude alone is not a
strategic obstruction.

The literal behavioral best-response value of a suffix is nevertheless
searchable without optimizing an infinite hazard sequence.  If `R` is its
remaining joint-absorption charge and `R < 1`, then for every player

```text
|BR_i - max(0,r_i({i}))| <= 2 M R.
```

Together with the `M R` prescribed-payoff bound, suffix exploitability is
within `3 M R` of the largest positive solo reward.  Annotation geometry is
equally rigid: the values have a common coordinatewise boundary with a
`2 M R` modulus, every singleton reward lies below that boundary, and every
player active along a cofinal subsequence is pinned to its singleton reward.
These are certified pruning tests.  They still do not identify a normalized
late occupation with the independently forced packet.

Proper-face candidates have a separate original-coordinate test.  Prescribing
an outsider to literal `Never`, a solo-continuation deficit at most `eta` and
deleted insider absorption at most `delta` imply that every outsider behavior
gains at most `eta + 2 M delta`.  The estimate is exact at deterministic quit
times and uses pure-time extremality for arbitrary behavior.  Search code must
certify both premises; face equilibrium alone is not such a certificate.

Nonsingleton noise is quantitatively negligible in a late window.  If `alpha`
is one-stage absorption and `kappa` is the probability of at least two
quitters, product independence gives

```text
kappa <= choose(|I|,2) * alpha^2.
```

Hence the concentration theorem branches explicitly when a survival-weighted
window has zero absorption.  When total absorption is positive, maximum stage
absorption `rho` bounds conditional collision fraction by
`choose(|I|,2) * rho`, and conditional delivery is within
`M choose(|I|,2) rho` of the singleton mixture normalized by total absorption.
This version has no separate positive-singleton denominator.  Normalization by
singleton mass itself retains the older `2 M` estimate and does require that
denominator.  These facts supply singleton concentration, not funding or the
survival-reweighting needed to identify a refusal law with the original owner
occupation conditioned off one player.

That reweighting now has an exact search-facing bound.  If the refusing
player's hazard is at most `rho` throughout a finite window, then the raw
joint-versus-opponent chronology discrepancy is at most the window's
triangular time factor times `rho`.  With a certified positive lower bound
`lower` on joint-weighted deleted absorption, normalized owner occupation
differs by at most

```text
2 * triangularFactor * rho / lower.
```

This ratio, not hazard decay alone, is the relevant rejection or acceptance
test for the refusal branch.

The canonical finite-window record retains exactly the source roots,
survival-weighted singleton mass by owner, collision mass, total absorption,
normalized owner occupation, and conditional absorbing delivery.  It proves
`absorption = singleton + collision = 1-survival` and branches before every
normalization.  A positive limiting owner coordinate produces an actual
positive-hazard source phase beyond the same cutoff and therefore pins the
annotation boundary to that owner's singleton reward.  This closes the
support-pinning part of the occupation bridge.  On the selected optimized tail
the punishment-floor clause is now automatic; funding and vanishing of the
normalized refusal-reweighting ratio remain independent tests.

The same data give a direct rejection test for charge-scale recurrence.  There
are table- and tail-dependent `speed > 0` and `threshold` such that every
positive-absorption selected-tail window beginning after `threshold` obeys

```text
dist(value[start], value[start + fuel])
  >= speed * absorptionMass(window).
```

Therefore any exact candidate trace with the displayed ratio trending to zero
cannot be the optimized tail of a counterexample.  A ratio bounded away from
zero is not positive evidence for nonexistence: summable absorption allows
ballistic convergence in finite clock time.  Scripts should report the ratio
as a first-class diagnostic and search for exact product-root returns or
terminal realization beyond it.

## Candidate record

A search result should retain enough information to reproduce and compare all
three lanes:

```text
reward table and normalization
canonical player count, minimality status, proper-restriction results, and declared symmetries
M and positive-singleton cap K
candidate terminal gap η
cutoff N
certified D_N interval, check η ≤ D_N ≤ K, and minimizing exact-D chain
optimized prefix-charge interval and maximizing exact prefix
best terminal exploitability interval and profile grammar
positive-return/SCC search and fixed-threshold stage counts
pure-toggle and stationary-cap ceilings
normalized packet support, weak-successor graph, and supported η-atom
packet quadratic energy and a certified supported positive reciprocal pair
uniform packet-defect/refusal lower bound for the fixed reward table
canonical periodic-window obstructing player and refusal/phase branch
raw/normalized singleton occupation, collision share, and denominator branch
remaining suffix charge and the certified `2 M R` best-response interval
active-owner subsequences and singleton-pinning checks
charge-normalized signed endpoint tangent and its negative/active-positive branch
punishment-floor sign pattern
floor-violation gap and division-free opponent-clock budget, when applicable
solver residuals and exact rational reconstruction, when available
```

Do not promote a floating-point candidate solely because all finite trends
look favorable.  Promotion requires either exact Lean witnesses or certified
inequalities with enough data for reconstruction.

## The cross-lane question — collapsed to one branch

The former two-branch alternative is now a theorem with a single surviving
branch (`CounterexampleRegimeViolationCollapse.lean`).  At every exact
Nash--Bellman edge, a value below the punishment floor amplifies through the
opponents-continue mass — `χ - v ≤ c · (χ - w)` — so the violating
coordinate set is monotone along any exact tail: *rotating* violation never
existed.  A perpetually violating tail with any positive debt coordinate has
summable joint absorption (the violator's own value would otherwise sink to
a sub-punishment solo reward, zeroing its debt cap and contradicting the
other players' summable clocks).  Consequently the optimized tail extracted
from a counterexample regime has summable joint absorption UNCONDITIONALLY
(`exists_terminalGapDynamicDebtTail_summableAbsorption`), and its roots
converge coordinatewise to all-Continue.  The later all-date floor theorem
removes the violation branch entirely for this selected optimized tail; the
amplification estimate remains a useful diagnostic for arbitrary exact-D
traces.

The same amplification has a division-free quantitative form.  If at date
`s` player `i` is below punishment by `δ = χ_i - v_s(i) > 0`, then

```text
δ * sum_{t ≥ s} opponentClock_i(t) ≤ χ_i + M.
```

This is an instance of a game-independent survival-amplification theorem for a
positive bounded gap sequence.  It is useful for certified search because it
does not divide by a numerically small gap.

The surviving object is rigid.  Along every infinite exact punishment-floor
orbit the annotations converge with total coordinatewise variation at most
`2·M·C*` (`infiniteOrbit_tsum_abs_value_succ_sub_le`), and the limit is an
exact all-Continue Nash--Bellman self-loop in the canonical box, dominating
the punishment floor and every player's solo reward
(`infiniteOrbit_exists_selfLoop_limit`).  The values are Bellman
annotations, not realized payoffs; the two-player positive-debt plateau
table realizes this entire package inside a game that HAS a uniform payoff,
so no contradiction can come from the tail data alone.

The production seam is now explicit in `CounterexampleRegimeSeam.lean`.
Every counterexample simultaneously carries the strict-refusal packet, the
positive-debt all-Continue tail limit, and the exact pure-time/`Never` gap on
every periodic tail window.  No theorem identifies the packet weights with
late-window owner occupation or the packet target with realized window
delivery.  Those are genuinely different objects.

Even supplying those identifications would not by itself close the regime.
For an absorbing exact Nash--Bellman word, write `C` for joint survival,
`rho_i` for opponent-only survival, and `Delta_i` for endpoint drift.  Exact
periodic evaluation gives the branchwise attachment bound

```text
max (
  C * [-Delta_i]_+ / (1-C),
  (rho_i-C) * [Delta_i]_+ / ((1-rho_i)(1-C))
).
```

The actual identities subtract nonnegative finite-stop and refusal slacks.
Hence search must certify normalized closure, not merely `Delta_i -> 0`.
Under small-charge singleton occupation, the refusal coefficient reads the
same owner share as the packet, while the normalized drift reads the phantom
debt.  The limiting refusal term is therefore the packet refusal defect: the
two objects can be dual descriptions of one obstruction.  Candidate searches
should retain the two displayed ratios and reject any proposed attachment
whose absolute seam shrinks but whose normalized seam stays positive.

When a singleton occupation bridge is available, the two evaluator branches
must be handled differently.  A phase stop at a pinned owner forces
underfunding.  A positive refusal defect at a proper positive owner mass
instead forces strict funding and a quantitative lower bound on that mass; if
the clauses of a generic packet still fail, the scalar algebra leaves the
punishment floor as the missing clause.  On the selected optimized tail that
clause is now automatic.  Consequently charge-scale delivery closure would
produce a forbidden complementary packet, which is exactly the ballisticity
argument.  Thus “the packet lacks funding” is not a branch-independent
diagnosis, and ordinary endpoint convergence is not delivery closure.

The distinction matters.  Noncomplementary singleton matrices exist already
with four players for which every singleton-owner distribution has a positive
promise or refusal escape.  In finite-dimensional notation, if
`M_ij = r_i({j}) - r_i({i})`, the ideal singleton restart is escape-free only
if

```text
M μ ≥ 0  and  μ_i * (M μ)_i = 0 for every i,
```

plus the pure-owner Never condition.  Failure of this complementarity can be
uniformly separated from zero on the simplex.  `FourPlayerSingletonBlocker.lean`
proves this with an exact bounded rational table and a strictly positive compact
separation constant.  Consequently the forced packet may be the source of
perpetual restart blocking rather than its cure.  The table is a regression for
the singleton grammar, not a quitting-game counterexample or a late-window
realization theorem.

The decisive remaining producer must use information absent from the three
seam objects separately: exact product-root dynamics and nonsingleton
collision rewards.  Its useful target is the following alternative:

```text
normalized source packet
  -> complementary singleton mixture
     or support-enlarged positive-charge exact return
     or unblocked periodic restart window.
```

The first branch is consumed by the existing circulation compiler, the second
contradicts finite capacity, and the third contradicts the terminal gap.  A
local theorem converting the diagonal seam directly into charge is too strong;
the support-enlargement or repair branch cannot be omitted.
