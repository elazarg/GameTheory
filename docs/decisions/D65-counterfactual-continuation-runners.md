# D65: counterfactual regret over continuation runners

- **Status:** adopted
- **Date:** 2026-09-30
- **Evidence:** [EXP-150](../ExperimentLog.md)

## Decision

Counterfactual continuation values, counterfactual regret, action regret and
utility, the Bayes continuation value, the local regret-matching vectors, and
root regret aggregation take a continuation runner, `M.ContinuationRunner`,
instead of a step count. Terminal play and play cut off after a fixed number
of steps are both runners.

Theorems that use the runner's structure name the property they need:

- `RunnerFactorsAt run who site`: installing a law at the site draws a choice
  and plays the corresponding commitment. Terminal play has it at every
  nonterminal site that cannot matter twice; truncated play has it after at
  least one step.
- `RunnerReadsReachable run`: the law from a history depends on a profile only
  at nonterminal histories reachable from it. Both runners have it.
- A root split: the root law is the prefix law at the cut followed by the
  runner. Terminal play splits at every depth with the root law equal to
  terminal play from the root; truncated play splits with a rolling deadline,
  the root cut at the site depth plus the continuation's steps.

Every other counterfactual identity holds for an arbitrary runner.

## Alternatives and mathematical limits

The fuel-indexed family is internally consistent, because the root and the
continuations are truncated compatibly; it is exact for the truncated game but
says nothing about well-founded games without a horizon. A terminal copy
beside it would duplicate every definition and theorem. Stating the family
over a runner keeps one family and makes both readings instances.

The root law remains a parameter because truncated play does not satisfy the
split with the runner itself at the root. A runner-only root statement would
exclude the truncated instance on which the finite existence proof relies.

## Admission and rejection criteria

No counterfactual theorem may gain a hypothesis beyond the named structural
properties, which its truncated form discharges. The terminal instance must be
exercised on a game with no uniform horizon.

## Evidence and result

All counterfactual consumers, including the regret-matching and zero-sum
learning tests, compile against the truncated instances. On the countdown game
the generic root decomposition with the terminal runner gives counterfactual
regret one, equal to the exact root gain, while play cut off after any number
of steps scores it strictly lower. These results support the decision.
