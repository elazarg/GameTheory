# Geometry Envelope

Goal:

- package geometric region arguments independently of domain semantics.

GameTheory-side patterns:

- feasible region intersected with coordinate-wise constraints,
- closedness/compactness/convexity transfer through region construction.

Math-side target:

- set-theoretic and topological lemmas over `lowerBoundRegion`-style constructions,
- monotonicity and decomposition lemmas for region operators.

Equivalent names:

- `Geometry envelope` (chosen):
  - structure: outer geometric constraints around admissible points.
  - equivalent names: feasible envelope, admissible region shell.
- `Lower-bound region` (chosen):
  - structure: `F ∩ ⋂ᵢ {x | vᵢ ≤ coordᵢ x}`.
  - equivalent names: floor-constrained feasible set, half-space intersection region.

External-field fit:

- constrained optimization, control invariant sets, robust feasibility analysis.

Candidate artifacts:

- monotone transport under set/threshold changes,
- closure/compactness/convexity preservation,
- decomposition/recomposition under intersections.

