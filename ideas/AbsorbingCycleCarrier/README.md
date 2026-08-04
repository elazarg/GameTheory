# Absorbing cycle carrier

| Lifecycle | Verdict | Priority | Group decision |
| --- | --- | --- | --- |
| `ACTIVE` | `MIXED` | `P0` | Decide whether every finite quitting weight admits an admissible absorbing complementary cycle. The mismatch half is characterized; existence is the whole remaining question. |

| Scientific object | Status |
| --- | --- |
| [Mismatch vanishes except on isolated negative coordinates](MismatchVanishesExceptOnIsolatedNegativeCoordinates.md) | `PROVED` (`M`), Lean destination named |
| [A solo-quitter cycle exists without a join incentive](SoloQuitterCycleExistsWithoutJoinIncentive.md) | `PROVED` (`M`), formalization in flight |
| [The zero pin is not a realizable continuation](TheZeroPinIsNotARealizableContinuation.md) | `PROVED` (`M+L`) at the exhibited family; general statement `OPEN` |
| [Vanishing absorption is the only remaining case](VanishingAbsorptionIsTheOnlyRemainingCase.md) | `PROVED` (`M`) as a dichotomy; hard branch `OPEN` |

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
*every* value vector, is complementary whenever `z_i ≥ r_i({i})`, and has zero
mismatch — so the notion would be satisfied vacuously by every weight, with the
values not determined by the rows at all. Under absorption the cyclic composite
contracts and `z` is uniquely determined by the rows. The same trap appears at
the level of single rows: the all-continue row is exact endpoint-Nash against
the equilibrium value of both plateau tables and reproduces every tail, so an
endpoint certificate plus a fixed point certifies nothing on its own.

## Closure status — what is actually closed

Nothing in this group is closed by a proof alone. The seals separate
believed-true from machine-checked, and the distinction is load-bearing here
because one of these claims already had a wrong proof that survived review and
was caught only by an adversarial audit.

| Result | Believed true | Machine-checked |
| --- | --- | --- |
| Mismatch vanishes unless a negative-solo coordinate is isolated | yes | **no** — contraction route in formalization |
| Solo-quitter criterion, root level, with necessity | yes | yes |
| Solo-quitter criterion, behavioral level | yes | yes (pre-existing) |
| Zero pin unrealizable, exhibited family | yes | yes |
| Both plateau tables' equilibria and zero debt | yes | yes |
| Cycle-pinned debt zero on the stationary chain | yes | yes |
| The dichotomy | yes | **no** — the discounted family has no production analogue |
| Vanishing branch admits an admissible cycle | **unknown** | no |

The target conditional is: *admissible absorbing cycle of bounded length for
every weight* implies terminal approximate existence for every accuracy, and
then the landed terminal-to-uniform consumer gives the uniform payoff. Proving
that implication on the believed-true premise is worth doing before the premise
is settled, since it converts the conjecture into a single named statement.

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
