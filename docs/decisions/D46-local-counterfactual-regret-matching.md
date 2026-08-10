# D46: Reuse canonical regret matching for local counterfactual learning

- **Status:** adopted; local cumulative package promoted
- **Date:** 2026-08-10
- **Experiment ID:** EXP-083

## Decision

Represent the action regrets at one Protocol information site as a Euclidean
vector whose coordinates are D45's `counterfactualActionRegret`. Reuse the
existing `Analysis.Approachability.regretMatch` running-average process and
nonpositive orthant. If a model proves, pointwise for every current action law
and environment, that its Protocol vector equals the ordinary
`regretPayoff` vector, it inherits both a finite squared-distance estimate and
asymptotic convergence of average local counterfactual regret.

Add transport-free `BehavioralPolicy.withLaw` beside pure `commit`. It installs
the current regret-matching law at one information state and preserves every
other behavioral coordinate. The generic finite regret-matching estimate
belongs with the existing approachability engine; the Protocol leaf is only
the realization adapter.

This is local CFR learning at one information site. It is not the global CFR
theorem that bounds root deviation gain or exploitability by the sum of local
counterfactual regrets across a perfect-recall tree.

## Competing designs

1. Reuse canonical regret matching after an exact Protocol realization proof.
2. Define a CFR-specific regret matcher and cumulative vector.
3. Compile every local continuation to a second static game.
4. Defer local learning until the global extensive-form decomposition exists.

Design 1 is adopted. Design 2 duplicates a validated learner and target
geometry. Design 3 adds an intermediary without removing the model-specific
realization obligation. Design 4 withholds an independently useful local
learning theorem and its finite bound.

## Hostile evidence

The two-history asymmetric-payoff site from EXP-082 is generalized from one
fully mixed law to every current finite action law. A syntactically transparent
copy of the same information site keeps the dependent action carrier exact.
The fixture proves that the Protocol action-regret vector equals ordinary
`regretPayoff` pointwise for every law, rather than assuming the equality for a
named trajectory.

The resulting local process satisfies
`t * infDist(average regret, nonpositive orthant)^2 <= 4` and converges to the
orthant. A fixed false law has exact positive regret `1/2` for true. From that
losing regret vector, the actual `regretMatch` update assigns probability one
to true. These controls reject a constant vector, a no-op update, and a theorem
that never reaches D45 semantics.

The narrow source/consumer build completed 2,448 jobs and the stable aggregate
completed 2,449 jobs warning-free. Both fast expected architecture audits
report `VERIFIED=1`. The full `GameTheory` library target completed 3,585 jobs
and the Analysis umbrella completed 3,207 jobs warning-free. Deep reachability
mode was not run.

## Kill conditions and result

Reject the package if the cumulative theorem does not mention D45 action
regret; if the realization premise assumes convergence rather than a
pointwise semantic equality; if arbitrary local laws need raw update or public
transport; if the fixture proves only one distribution; or if local learning
is presented as global exploitability convergence. No kill condition fired.

The realization premise remains explicit because a general proof that a
perfect-recall tree's continuation value is linear in every installed local
law is a separate semantic theorem. The hostile fixture demonstrates that the
premise is dischargeable and nonvacuous.

## Public API consequences

Add `GameTheory.Analysis.Protocol.CounterfactualRegretMatching` to the opt-in
Protocol-analysis root and the finite `regretMatch_sq_infDist_avg_le` result to
`GameTheory.Analysis.Approachability`. Add `BehavioralPolicy.withLaw` and its
self/other equations to Protocol information semantics.

The next gate is the across-information-set performance/deviation
decomposition under perfect recall, followed by a two-player zero-sum average
strategy or exploitability theorem. It must consume the local cumulative
result and include a control where one local learner fails.
