# Vanishing absorption is the only remaining case

## Lifecycle

| Field | Value |
| --- | --- |
| Lifecycle | `ACTIVE` |
| Verdict | `PROVED` as a dichotomy; the hard branch `OPEN` |
| Objective priority | `P0` |
| Last audited | 2026-08-04, `1fefc04` |
| Central live claim | For every weight, either a discounted-limit complementary row absorbs — giving a length-one cycle, of zero mismatch unless it isolates a negative-solo coordinate — or every such limit degenerates to vanishing absorption. The second branch is the entire remaining content of the existence question. |
| Next discriminant | Decide the vanishing-absorption branch: does a weight whose only complementary fixed points have absorption tending to zero admit an admissible absorbing cycle of length `> 1`? |
| Production destination | none yet |
| Supersedes / superseded by | none |

## Claim ledger

| Claim | Verdict | Seals | Scope | Consumer |
| --- | --- | --- | --- | --- |
| A complementary row exists against every continuation vector | `PROVED` | `M` | any weight | backward selection, nonemptiness of the chain sets |
| Discounted complementary rows exist for every discount, and a subsequence converges | `PROVED` | `M` | any weight | the dichotomy |
| If the limit row absorbs, it is exactly complementary against its own value, with one-step excess exactly zero | `PROVED` | `M` | any weight | the easy branch |
| That row is a length-one absorbing cycle, hence of zero mismatch unless it isolates a coordinate with `r_i({i}) < 0` | `PROVED` | `M` | via the mismatch characterization | existence, `L = 1` |
| Otherwise the limit row is the all-continue row and absorption vanishes along the approximating sequence | `PROVED` | `M` | any weight | the hard branch |
| The vanishing branch admits an admissible absorbing cycle of some bounded length | — | — | — | `OPEN` — this is the conjecture |

Provenance: the existence and discounted-limit half is external, from the
answered estimator question; the mismatch half is
[the companion claim](MismatchVanishesExceptOnIsolatedNegativeCoordinates.md).
The assembly into a dichotomy is internal.

## Why this is the right localization

The carrier asks whether every weight admits an admissible absorbing cycle.
The dichotomy says the only way to fail at length one is for absorption itself
to degenerate: the complementary fixed points exist, but only with quitting
rates tending to zero, so the limit is the all-continue row, whose value is not
determined by its rows at all.

That is exactly the configuration the carrier's absorption clause exists to
exclude, and exactly the degeneration that makes the naive notion vacuous. It
is not an artifact of the formulation — it is where the difficulty actually
lives, and the formulation is what makes it visible.

Two consequences worth stating plainly.

**The easy branch is genuinely easy.** If some discounted limit absorbs, the
conjecture holds for that weight at `L = 1`, with no cyclic construction
needed. The `L > 1` machinery — the blocking digraph, the square closure
system — is required only on the vanishing branch.

**The hard branch is not empty.** The published three-coordinate cyclic table
has no stationary approximate equilibrium, so it cannot be in the easy branch;
its complementary fixed points must degenerate. Its length-three packet is the
model for what the vanishing branch needs.

## Falsifiers and wrong turns

- **Do not conclude existence from resolvability.** The one-step excess being
  zero — which is precisely complementarity — is not the deviation gain. Every
  weight has complementary fixed data; that says nothing until absorption is
  imposed and the mismatch is measured against the solo-quit anchor. Treating
  the one-step condition as the target is what made the estimator question's
  target class universal and its separation vacuous.
- Do not read the easy branch as covering the plateau tables *because* they are
  plateau tables. They are in the easy branch because their solo-quitter
  criterion is feasible, which is a separate and stronger fact.
- The dichotomy is over discounted limits. A weight could conceivably have an
  absorbing complementary fixed pair that no discounted limit selects; the
  dichotomy would then be pessimistic, not wrong. Deciding whether the
  discounted limit is exhaustive for this purpose is open and worth knowing.

## Production map

Nothing formalized yet. The natural first target is the easy branch: from an
absorbing complementary fixed pair, produce the length-one cycle and its zero
mismatch, reusing the landed root-level solo certificate machinery where the
row happens to be solo. The dichotomy itself needs the discounted family, which
has no production analogue.

## Exit conditions

`MINED` when the vanishing branch is decided. Returns to the front immediately
if a weight is exhibited in the vanishing branch with no admissible absorbing
cycle of any length — that would be a counterexample to the carrier, and would
have to be reconciled with the conjecture rather than assumed to refute it.
