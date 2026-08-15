# D50: Make finite root regret uniform and strategically consumable

- **Status:** adopted for decomposition-certified finite deviation families
- **Date:** 2026-08-11
- **Experiment ID:** EXP-088

## Decision

For one finite family of D46 local processes, quantify the D48 root-gain upper
decomposition over an arbitrary deviation carrier. Reach coefficients and
selected local actions may depend on the deviation; the sum of local orthant
distances must not. If every local D46 process approaches its orthant, the same
finite sum drives the positive average gain of every certified deviation to
zero.

Accept an upper decomposition rather than requiring equality. This includes
nonprofitable or unreachable branches without inventing a learner for a site
that contributes no root gain. Exact D48 decompositions remain the usual
special case.

Local boundedness is supplied by a public payoff-range certificate. If every
finite-action utility lies in `[lo, hi]`, its regret vector has norm at most
`card * (hi - lo)`. A normalized counterfactual-reach fiber transfers
pointwise continuation ranges to counterfactual action utilities.

Strategic usefulness is tested against `UtilityGame.externalRegret` for the
canonical compiled behavioral form. The replacement strategy is fixed across
rounds, and `UtilityGame.externalRegret_timeAverage` supplies the time-average
identity; no CFR-specific aggregate regret is introduced.

## Hostile evidence

The two-stage complementarity consumer enumerates all four pure plans on its
two payoff-relevant Boolean coordinates. The first site always has unit
alternative own reach; the off-path second-after-true site has reach one or
zero according to the plan's first action. Thus false-first plans are genuine
zero-reach controls inside the same theorem, while true-first plans retain the
decisive off-path term.

Both local utilities receive proved `[0,1]` certificates from canonical
counterfactual reach and behavioral continuation laws. Those certificates
discharge both D46 norm bounds and yield uniform root convergence without a
convergence premise. Committing both learned coordinates is proved equal to a
round-independent fixed strategy. The resulting scalar gain is exactly Core
external regret, its compiled-game time-average positive part converges to
zero, and separate canonical controls have external regret exactly `1` and
`-1`.

## Rejected alternatives and kill conditions

Reject a maximum over proxy utilities, a deviation-dependent right-hand side,
a round-varying replacement called external regret, omission of a
payoff-relevant pure plan, an assumed root convergence premise, or an
exploitability label before the zero-sum specialization exists.

The experiment also rejects requiring exact local equality for every branch:
an upper decomposition is the useful contract for nonprofitable branches and
strictly contains the D49 equality seam.

## Scope and next gate

This decision provides uniform convergence for every deviation carrying the
finite D48 upper-decomposition certificate. The representative schedule is
complete for all payoff-relevant pure plans in the hostile two-stage game. It
does not synthesize a topological schedule for every Protocol, prove that pure
plans dominate all behavioral replacements, or establish exploitability.

The next gate is a two-player zero-sum specialization: connect both players'
canonical external-regret bounds to an explicit saddle-gap/exploitability
theorem, with a nonzero finite control. Unequal-depth information fibers remain
outside D48 and D50.

## Validation

- `lake build GameTheory.Math.RegretAggregation`
- `lake build GameTheory.Analysis.Approachability`
- `lake build GameTheory.Analysis.Protocol.CounterfactualRegret`
- `lake build GameTheory.Analysis.Protocol.CounterfactualRootRegret`
- `lake build GameTheory.Analysis.Protocol.CounterfactualRootRegretTest`
- `lake build GameTheory.Math GameTheory.Analysis.Protocol`
- `lake build GameTheory`
- `scripts/phase2-audit.ps1 -VerifyExpected`
- `scripts/phase3-audit.ps1 -VerifyExpected`

The hostile consumer's warm build was 9.1 seconds; the stable aggregate build
completed 2,463 jobs in 10.2 seconds, and the package gate completed 3,592 jobs
in 19.1 seconds. Both fast audits reported `VERIFIED=1`. Deep reachability was
not run.
