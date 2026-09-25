# D58: reverse infinite Kuhn conditions arbitrary policy measures on finite own records

- **Status:** adopted and promoted
- **Date:** 2026-08-20
- **Experiment IDs:** EXP-118 and EXP-136; builds on EXP-115–117

## Decision / question

How an arbitrary probability law over each player's total pure policies should
be read as one behavioral profile that preserves every finite-prefix law under
perfect recall, including unilateral replacement measures and discounted
payoff consequences.

## Competing designs

1. Require a regular conditional-probability kernel or a full disintegration
   theorem on the total policy space.
2. Condition each player's measure directly on the measurable finite cylinder
   determined by its own recalled record, then push the conditional law through
   the current policy coordinate.
3. Select a new finite-support behavioral witness separately for every horizon.
4. Accept one arbitrary correlated joint law over all players' policies and
   claim an ordinary behavioral-profile representation.

Design 2 is adopted. Design 1 assumes much more measurable structure than the
proof consumes. Design 3 has the wrong quantifier order. Design 4 is false
without an additional public correlating device: ordinary behavioral profiles
encode independent player randomization.

## Representative hostile slice

EXP-118 uses a finite-action perfect-monitoring stochastic game with countably
infinite public histories. It starts from an infinite product policy law and
pushes it through a measurable transformation that forces the choices at two
distinct information states to agree while leaving every other coordinate
untouched. This supplies genuine within-policy correlation rather than the
forward independent-coordinate law. The consumer checks all finite prefixes,
an arbitrary unilateral policy-measure replacement, and a nonconstant bounded
discounted payoff.

## Original finite-law evidence

`ConsistentAt` is a finite intersection of measurable coordinate cylinders.
On a positive-mass cylinder, ordinary `ProbabilityTheory.cond` followed by the
current-coordinate map is a probability measure on a finite discrete choice
carrier and converts exactly to `FinDist`. On a zero-mass cylinder, one fixed
total policy supplies the fallback; it does not change as play advances.

The original proof closes a finite prefix cover under the own-record
coordinates of every covered site. Restricting an arbitrary policy measure to
that finite closure, converting the marginal to `FinDist`, and filling omitted
coordinates from the fallback preserves both the conditioning cylinder and the
current choice. The existing finite-support reverse Kuhn theorem and sole
Protocol runner then prove the prefix law. The behavioral conditional reading
is defined once, independently of every horizon.

The theorem needs only independent per-player probability measures. It does
not use regularity, countability, or standard-Borel hypotheses; hence it is
strictly stronger than the requested regular-measure statement. Those
hypotheses remain relevant to constructing the forward product law in D57, not
to reading a supplied law backward.

## General PMF boundary

With countable local choice carriers, conditional coordinate measures convert
to ordinary PMFs. No finite global cover of the information sites reachable
within a horizon is needed. For each target history, the proof restricts to
its finite queried coordinates and their own records. These target-local
marginals determine its probability. The normalized behavioral PMF then
supplies a common countable support for the integrated history kernel.

Local choices require measurable singletons. Histories need a measurable
space, but their singletons need not be measurable: the final measure equality
is proved on measurable events. Independence is required between players;
within one player's policy law, arbitrary coordinate correlation is allowed.
Fallback choices remain fixed at zero-mass own-record events.

EXP-136 has infinitely many reachable information sites already after two
rounds. Its policy measure is nonatomic, correlates two genuine random choices,
and has no PMF representation. Every finite-prefix law agrees with the one
canonical behavioral reading. This distinguishes the general reverse theorem
from the discrete whole-policy predrawing construction, which still needs an
actual finite-site certificate.

## Evidence from existing libraries

Mathlib supplies ordinary measure restriction, conditioning, map, finite
products, and measurable dependent-product coordinate evaluation. Existing
GameTheory Protocol supplies `recordAt`, `ConsistentAt`, `ConstrainsAlike`,
finite counterfactual covers, the finite-support reverse Kuhn theorem, and the
only history runner. No probability wrapper, disintegration layer, runner, or
equilibrium predicate is added.

## Kill condition

Reject promotion if the implementation treats a correlated joint player law as
independent, constructs a horizon-indexed behavioral object, needs global
information-state finiteness, adds a moving fallback, requires unnecessary
disintegration hypotheses, loses arbitrary unilateral replacement measures,
duplicates the runner, leaks probability representation internals, introduces
visible transport or placeholders, or states discounted equality without an
explicit convergence argument.

No kill condition fired.

## Result and public API consequences

`Protocol.PolicyMeasure` now contains the arbitrary per-player policy-measure
type, own-record conditional behavioral reading, finite-marginal reduction,
all-prefix history-law theorem, exact unilateral replacement theorem, and
summable discounted consequence. `Stochastic.Kuhn` specializes these results
through perfect monitoring and bounded stage utility. The new result composes
with D57: the forward product law is one admissible input to the reverse API,
but the reverse API also handles non-product within-policy correlation.

General correlated joint laws over player profiles and infinite-path outcome
semantics remain separate. Deep reachability audits positively require the new
Protocol and Stochastic declarations while continuing to reject the
experimental infinite-path measure from stable roots.
