# Absorbing cycle carrier

| Lifecycle | Verdict | Priority | Group decision |
| --- | --- | --- | --- |
| `ACTIVE` | `MIXED` | `P0` | The finite-cycle carrier is refuted as complete; its sufficiency is machine-checked. Relaxed objects are not scarce, so the gate is the **conversion**: the fixed-cycle bound `gain ≤ ε·C` is exact with `C` a cyclic fixed point that blows up as the deleted survival product tends to one, and no cycle-independent constant exists even at fixed weight. Decide whether `ε·C` is also necessary, and what the limiting mass path must retain. |

| Scientific object | Status |
| --- | --- |
| [Mismatch vanishes except on isolated negative coordinates](MismatchVanishesExceptOnIsolatedNegativeCoordinates.md) | `PROVED` (`M`), Lean destination named |
| [A solo-quitter cycle exists without a join incentive](SoloQuitterCycleExistsWithoutJoinIncentive.md) | `PROVED` (`M`), formalization in flight |
| [The zero pin is not a realizable continuation](TheZeroPinIsNotARealizableContinuation.md) | `PROVED` (`M+L`) at the exhibited family; general statement `OPEN` |
| [Vanishing absorption is the only remaining case](VanishingAbsorptionIsTheOnlyRemainingCase.md) | `PROVED` (`M`) as a dichotomy; hard branch `OPEN` |
| [Finite cycles are refuted; the carrier is a mass path](FiniteCyclesAreRefutedTheCarrierIsAMassPath.md) | `WRONG` for the finite carrier; replacement `OPEN` |
| [The uniform defect-to-gain conversion is false](UniformDefectToGainConversionIsFalse.md) | `WRONG` for the uniform conversion; replacement `OPEN`; all rows `M [reported]` |
| [Quitting weights have analytic vanishing-discount germs](QuittingWeightsHaveAnalyticVanishingDiscountGerms.md) | `PROVED` (`M+L`); matching scaling case and nondegeneracy `OPEN` |
| [The signed accumulation is the gain](TheSignedAccumulationIsTheGain.md) | `PROVED` (`M`) identity and instance; general statement `OPEN` |
| [Zero-loss projective-tail extraction is hypothetical](ZeroLossProjectiveTailExtractionIsHypothetical.md) | `OPEN`; machinery currently unconsumable |

**Read the last three rows first.** The finite-cycle carrier this group is named
for is refuted as a *complete* carrier in every open case. Its sufficiency
stands and is machine-checked; its completeness does not. The replacement is a
continuous mass-parametrized absorption path, marked in the mixed-sign case.

The gate then moved from existence to **conversion**. Relaxed objects are not
scarce — defect-vanishing families exist, and one two-coordinate weight even has
relaxed admissible cycles at every accuracy with no exact one. What fails is the
bridge: there is no uniform constant `K` with `gain ≤ K · ε` across cycles, so
neither the relaxation route nor the mass-path route may assume that vanishing
defect means vanishing gain. That result is externally reported and unaudited
here, which is why auditing it is the group's cheapest high-value task.

The germ row is infrastructure rather than closure progress: it regularizes the
discounted family the dichotomy runs on, upgrading a convergent subsequence to a
genuine limit, but it has no consumer yet and its nondegeneracy hypothesis is
undischarged precisely on the hard branch.

## Why this group exists

The exact-`D` chain grammar pins the terminal continuation to zero. That pin
manufactures positive optimized-debt plateaus on games that are easy: both
known plateau witnesses are two-player tables whose exact equilibria have debt
zero once the continuation is unpinned, and both are now machine-checked. See
[anchored repair or uniform debt descent](../PositivePlateauBoundaryClosure/AnchoredRepairOrUniformDebtDescent.md)
for the refutation of the descent branch and the diagnosis.

This group carries the replacement. Instead of a finite chain with an inert
zero tail, the carrier is a **cycle**: a finite list of rows that reproduces its
own value and absorbs. The conjecture, in this carrier, becomes a
finite-dimensional existence statement rather than a compactness statement
about escaping middles — which is why `PC-008` deprioritized the latter.

## The carrier

For rows `y_1, … , y_L` and values `z_1, … , z_L`, cyclically:

- `z_k = F_{y_k}(z_{k+1})` with `z_{L+1} := z_1`;
- each `(y_k, z_{k+1})` is complementary;
- **absorbing**: `∏_k c(y_k) < 1`.

Absorption is not a technicality. Without it the all-continue list reproduces
*every* value vector and is complementary whenever `z_i ≥ r_i({i})`; taking
`z = Λ` in particular gives `F_0(Λ) = Λ`, complementarity since
`g_i = r_i({i}) - Λ_i ≤ 0` always, and mismatch exactly zero. So the notion
would be satisfied vacuously by **every** weight, with the values not
determined by the rows at all. Under absorption the cyclic composite contracts
and `z` is uniquely determined by the rows. The same trap appears at the level
of single rows: the all-continue row is exact endpoint-Nash against the
equilibrium value of both plateau tables and reproduces every tail, so an
endpoint certificate plus a fixed point certifies nothing on its own.

## Closure status — what is actually closed

Nothing in this group is closed by a proof alone. The seals separate
believed-true from machine-checked, and the distinction is load-bearing here
because one of these claims already had a wrong proof that survived review and
was caught only by an adversarial audit.

| Result | Believed true | Machine-checked |
| --- | --- | --- |
| Mismatch vanishes when the deleted survival product is below one | yes | yes — general period, sign-free |
| Isolation forces mismatch exactly `[-r_i({i})]₊`, and at most one coordinate is isolated | yes | **no** — the `P_i = 1` branch |
| Solo-quitter criterion, root level, with necessity | yes | yes |
| Solo-quitter criterion, behavioral level | yes | yes (pre-existing) |
| Zero pin unrealizable, exhibited family | yes | yes |
| Both plateau tables' equilibria and zero debt | yes | yes |
| Cycle-pinned debt zero on the stationary chain | yes | yes |
| The dichotomy | yes | **no** — the discounted family has no production analogue |
| **Admissible absorbing cycle implies a uniform equilibrium payoff** | yes | **yes** |
| **Zero solo weights imply a uniform equilibrium payoff, namely `0`** | yes | **yes** |
| **The disjunction of those two implies a uniform equilibrium payoff** | yes | **yes** |
| The disjunction is *complete* — every weight satisfies one branch | **unknown** | no |

**The conditional is closed.** From a cyclic continuation block together with
admissibility — for every coordinate, either its deleted survival product
around the cycle is below one, or its solo weight is nonnegative — the block's
periodic profile is terminal `0`-Nash at every phase, hence terminal
`ε`-Nash at every accuracy, hence the game has a uniform equilibrium payoff by
the landed selection theorem. Machine-checked with clean axioms, and with **no
strategy-class gap**: the consumed predicate quantifies over all behavior
strategies, not merely stopping times.

Note the admissibility hypothesis is exactly the disjunction the mismatch
characterization predicts, and it is genuinely needed — a single-stage block
with `r_i({i}) = -1`, the owner quitting at rate `1/2` and its opponent silent,
satisfies every clause of the block predicate while the owner gains `1` by
continuing forever.

So for finite quitting games the conjecture reduces to one statement — but
**not** the naive one. "Every weight admits an admissible absorbing cycle" is
false; see [the zero-solo disjunct](TheCarrierNeedsTheZeroSoloDisjunct.md) for
the two-coordinate counterexample. The corrected reduction is:

> For every weight, either `Λ = 0` — and the landed zero branch applies — or
> the weight admits an admissible absorbing cycle **of some finite length**.

The first disjunct is landed. The second is open, and by the dichotomy can only
fail in the vanishing-absorption branch. The conditional from an admissible
absorbing cycle to a uniform payoff is machine-checked and unaffected by the
counterexample.

**No bound on the length is required.** The formalized conditional quantifies
over the period with no bound, so "of length at most `L(n)`" — which earlier
statements of this reduction carried — was never needed and should not be
asked for. Relatedly, a uniform absorption bound `θ = 1/2` is free by repeating
a cycle until its survival product drops below `1/2`; that costs length, so
bounded absorption and bounded length are different asks and only the former is
available cheaply. Neither is on the critical path.

The counterexample is instructive rather than damaging: the absorption fence,
required to keep the cycle notion from being vacuous, also excludes the
genuinely **non-absorbing** equilibria — which are exactly the `Λ = 0` weights,
and exactly the ones already solved.

## Dependencies and consumers

Consumes the exact transport law for the finite dynamic debt. Feeds terminal
approximate existence and then the landed terminal-to-uniform selection, by the
same route the zero branch already uses.

## Next group decision

Existence, now sharply localized. Complementary fixed data exist for every
weight, so the question is never whether a cycle exists but whether one
**absorbs**. The dichotomy says: either a discounted limit absorbs, and the
conjecture holds for that weight at length one; or absorption degenerates along
every such limit, and the length-one route is unavailable.

The whole remaining problem is the vanishing-absorption branch. The
solo-quitter criterion settles a sub-case of the easy branch; the blocking
digraph and its square closure system are the candidate construction for the
hard one.
