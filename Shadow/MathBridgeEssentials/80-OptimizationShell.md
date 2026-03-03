# Optimization Shell

Goal:

- isolate local/global optimality and fixed-point implications without domain-specific objects.

GameTheory-side patterns:

- “no unilateral improvement” style predicates,
- fixed-point of response/update maps,
- dual-bound witness packaging.

Math-side target:

- generic predicates over `obj : X -> β`, `step : X -> X`, neighborhood relations,
- implications among fixed-point, local no-improvement, and set-restricted global bounds.

Equivalent names:

- `Optimization shell` (chosen):
  - structure: theorem-level interface for local/global optimality statements.
  - equivalent names: variational interface, local-global comparison layer.
- `No-improvement` (chosen):
  - structure: transformed point does not improve objective.
  - equivalent names: descent condition (maximization sign), stationarity inequality.

External-field fit:

- nonlinear optimization, local search analysis, fixed-point algorithm certification.

Candidate artifacts:

- local-optimality from move-family inequalities,
- no-improvement from selected move maps,
- fixed-point -> no-improvement wrappers.
- additive objective decomposition (`NoImprovement` / `LocallyOptimal` under `+`),
- nonnegative scaling transport for objective inequalities.
