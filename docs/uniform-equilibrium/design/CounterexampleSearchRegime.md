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

### Landed narrowing (2026-08-09)

The regime is machine-checked EMPTY below four players
(`QuittingCounterexampleRegime.three_lt_card`): fewer than two players is
refuted by the toggle consequences below, and two or three players by a new
player-reindex transport (`Classification/PlayerReindex.lean`) of the
unconditional `Bool` and `Fin 3` existence theorems.  A one-player existence
theorem for arbitrary `Unique` player types
(`quittingGame_exists_uniformEquilibriumPayoff_onePlayer`) fills the
previously unformalized base case.

Further machine-checked necessary conditions
(`CounterexampleRegimeToggles.lean`, `CounterexampleRegimePacket.lean`):

- no profile is terminally `ε`-Nash for any `ε < η`
  (`not_isεAsymptoticNash_of_lt_terminalGap`);
- every coalition's sure-exit profile is exploitable by a membership toggle
  at margin `η` (`exists_toggle_gain`), splitting into a leave-or-join
  disjunction (`exists_leave_or_join_gain`); hence no sure exit set exists
  (`not_isQuittingSureExitSet`);
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
  semialgebraic system search code can refute directly.

## Derived geometry

The debt and charge fields have stronger derived forms.

The terminal gap produces a subsequential limit of attained finite minimizers.
The limit is an infinite exact-D path with an owner whose initial debt is at
least `η` and whose opponent clock is summable.

The charge budget extends from anchored prefixes to every path in the
punishment-floor reachable exact-predecessor relation.  Its canonical
budget-to-go function is nonnegative, bounded above by `C`, and satisfies

```text
potential(current) + absorptionCharge(edge) ≤ potential(tail).
```

Every closed reachable exact-predecessor path therefore has zero total charge.
More locally, every edge lying in a reachable strongly connected component has
zero absorption.  A positive-charge return, cycle, or self-loop is therefore a
decisive finite certificate that the table is not a counterexample.

The prefix result is genuinely all-orbits.  Every infinite exact Nash--Bellman
orbit in the canonical box whose initial value dominates the punishment floor
has total absorption at most `C*`.  Each player's quit probabilities are
summable and tend to zero, so every such root sequence converges coordinatewise
to all-Continue.  Nevertheless, the actual behavior profile starting at every
sufficiently late date remains terminally exploitable by at least `η`.

The optimized exact-D path and the floor-prefix family are connected exactly
at floor-dominating endpoints: reversing such a finite exact-D segment gives a
floor prefix with the same total absorption.  Consequently the extracted tail
has the alternative

```text
joint absorption is summable
or eventually every endpoint violates the punishment floor in some coordinate.
```

If every punishment value is nonpositive, the zero-boundary approximants and
their projective limit dominate the floor, so the first branch holds and the
extracted tail has summable full joint absorption.  Without that sign condition
the two carriers are still not identified; search output must not silently
treat them as one orbit.

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

## Candidate record

A search result should retain enough information to reproduce and compare all
three lanes:

```text
reward table and normalization
player count and declared symmetries
M and positive-singleton cap K
candidate terminal gap η
cutoff N
certified D_N interval, check η ≤ D_N ≤ K, and minimizing exact-D chain
optimized prefix-charge interval and maximizing exact prefix
best terminal exploitability interval and profile grammar
positive-return/SCC search and fixed-threshold stage counts
punishment-floor sign pattern
solver residuals and exact rational reconstruction, when available
```

Do not promote a floating-point candidate solely because all finite trends
look favorable.  Promotion requires either exact Lean witnesses or certified
inequalities with enough data for reconstruction.

## The cross-lane question — collapsed to one branch (2026-08-09)

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
converge coordinatewise to all-Continue.

The surviving object is rigid.  Along every infinite exact punishment-floor
orbit the annotations converge with total coordinatewise variation at most
`2·M·C*` (`infiniteOrbit_tsum_abs_value_succ_sub_le`), and the limit is an
exact all-Continue Nash--Bellman self-loop in the canonical box, dominating
the punishment floor and every player's solo reward
(`infiniteOrbit_exists_selfLoop_limit`).  The values are Bellman
annotations, not realized payoffs; the two-player positive-debt plateau
table realizes this entire package inside a game that HAS a uniform payoff,
so no contradiction can come from the tail data alone.

The decisive remaining theorem is therefore a delivery mechanism that
constructs profiles and consumes the gap field.  The candidate is periodic
restart of late windows: replay a positive-mass window's roots forever; the
restarted profile absorbs surely and pays exactly the window's normalized
delivery.  The deviator's optimal stopping against the periodic profile
reduces exactly to two window statistics (best phase stop and refusal
value), so late-window exploitability is controlled by three payoff escapes
only — delivery below a solo stop, profitable refusal, and profitable Never
against a sole absorber — while drift-to-mass bias is provably
non-strategic.  Closing the regime on this branch means ruling out
perpetual payoff-escape blocking compatibly with the finite capacity `C*`,
the blocker digraph, and the forced packet.
