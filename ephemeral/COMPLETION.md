# Brouwer/Nash Gap Closure Plan

## Objective
Close the final end-to-end gap:
- remove `axiom nashMap_has_fixed_point`,
- prove mixed Nash existence entirely from proved fixed-point machinery.

Current status:
- fixed-point pipeline from scale witnesses to `Function.IsFixedPt` is proved,
- remaining gap is construction of concrete Kuhn/Sperner scale witnesses in higher dimensions.

## Critical Path
1. Construct concrete Kuhn cell family at scale `m`.
2. Prove facet incidence combinatorics (interior `2`, boundary `1/0` pattern).
3. Prove boundary marking from `gridLabel` boundary admissibility.
4. Feed this into `exists_fixedPoint_of_kuhnFacetWitnessPattern_at_scales`.
5. Specialize to Nash map and replace the axiom.

## Work Packages

### WP1: Witness Interface (stabilization layer)
Deliverables:
- A structure bundling per-scale witness obligations in the exact shape used by
  `exists_fixedPoint_of_kuhnFacetWitnessPattern_at_scales`.
- A one-line bridge theorem from this structure family to fixed-point existence.

Acceptance:
- LSP clean.
- No new axioms.
- Geometry development can target this structure directly.

### WP2: Concrete Kuhn Cells
Deliverables:
- Concrete `cells m : Finset (Cell n m)` definition.
- Mesh lemma: `∀ c ∈ cells m, IsMeshCell c`.
- Facet family characterization lemma(s) for these concrete cells.

Acceptance:
- LSP clean.
- Facet membership lemmas usable by incidence counting proofs.

### WP3: Incidence Counting
Deliverables:
- Interior facet pair-witness theorem.
- Boundary unique/none witness theorem.
- Combined per-scale witness theorem in WP1 structure form.

Acceptance:
- LSP clean.
- Directly applicable to existing witness-pattern fixed-point theorem.

### WP4: Nash Specialization
Deliverables:
- Instantiate fixed-point theorem for Nash map.
- Replace `axiom nashMap_has_fixed_point` with theorem.
- Keep `mixed_nash_exists` statement unchanged.

Acceptance:
- LSP clean on `GameTheory/NashExistenceMixed.lean`.
- No axioms in the mixed-Nash chain.

## Parallelization
- Track A (now): WP1 + early WP2 scaffolding.
- Track B: WP2 concrete combinatorics lemmas.
- Track C: WP4 continuity/specialization prep in parallel with WP2/WP3.

## Sprint Definition
Each sprint must add:
- at least one new compile-checked theorem/definition used on critical path,
- one measurable reduction of remaining obligations,
- update `Fixpoint/SPRINTS.md`.

## Done Criteria
- `nashMap_has_fixed_point` is a theorem, not an axiom.
- `KernelGame.mixed_nash_exists` is fully derived from proved fixed-point layer.
- LSP clean on all changed files.
