# Projection Core

Goal:

- separate state evolution from projection semantics.

GameTheory-side patterns:

- equivalence under equal projections,
- invariance under irrelevant-coordinate changes.

Math-side target:

- `project : State -> Projection`,
- reachable-`EqOn` congruence templates.

Equivalent names:

- `Projection` (chosen):
  - structure: map from full object to reduced observable/readout.
  - equivalent names: feature map, measurement map, view map, classifier key.
- `project` (chosen):
  - structure: deterministic read function.
  - equivalent names: extract, observe, readout, summarize.

External-field fit:

- abstract interpretation, projection-based equivalence, runtime monitoring.

Candidate artifacts:

- reachable-agreement implies evaluation equality,
- support-restricted agreement implies equal stochastic outputs.
