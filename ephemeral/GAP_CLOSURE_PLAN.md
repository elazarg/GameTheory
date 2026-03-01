# Brouwer Gap Closure Plan (Post-Reduction)

## Objective
Close the final gap for Brouwer on `stdSimplex` by proving:

- `∀ δ > 0, ∃ labeled δ-cluster`

and plug it into the already-proved reduction:

- `exists_fixedPoint_of_arbitrarilyFine_labeled_clusters`.

This yields full Brouwer in the current pipeline with no axioms/sorries.

---

## Current Proven Base (Done)
- Approximate-to-exact fixed point on compact metric spaces.
- `stdSimplex` specialization.
- Sperner-compatible labeling and boundary admissibility primitives.
- Quantitative displacement control.
- Abstract reduction from arbitrarily fine labeled clusters to fixed point existence.

Remaining work is purely combinatorial/geometric (subdivision + Sperner existence + extraction).

---

## Deliverables Needed
1. `KuhnSubdivision` layer:
   - finite subdivision objects, simplex cells, mesh/diameter bounds.
2. `SpernerParity` layer:
   - fully-labeled cell existence from admissible boundary labeling.
3. `ClusterFromSperner` layer:
   - for each `δ`, produce labeled `δ`-cluster.
4. Final Brouwer wrapper:
   - combine cluster theorem with existing reduction.

---

## Recommended Main Route
Use Kuhn triangulation + Sperner parity (matching existing code direction and proven label machinery).

---

## Parallel Workstreams
These can run concurrently with minimal interference.

### Workstream A: Subdivision Geometry
Target file:
- `Fixpoint/KuhnSubdivision.lean`

Tasks:
- Fix combinatorial index type as `Fin (n+1)` for core.
- Define grid vertices at level `m`.
- Define small simplices/cells via monotone increment chains or permutation encoding.
- Prove finite-ness and vertex-membership lemmas.
- Prove mesh bound: any two vertices in one small simplex are within `O(1/m)` in `dist`.

Acceptance criteria:
- Compiles clean via LSP.
- Exposes theorem of form:
  - `same_cell_vertices_dist_le : dist v w ≤ C / m`.

### Workstream B: Sperner Combinatorics
Target file:
- `Fixpoint/SpernerParity.lean`

Tasks:
- Define admissible labeling on subdivision boundary.
- Formalize fully-labeled cell predicate.
- Prove parity/counting theorem:
  - existence (at least one fully-labeled cell) under admissibility.

Acceptance criteria:
- Compiles clean via LSP.
- Exposes theorem of form:
  - `exists_fully_labeled_cell : ...`.

### Workstream C: Analytic Extraction Bridge
Target file:
- `Fixpoint/ClusterFromSperner.lean`

Tasks:
- Use Workstream A mesh bound + Workstream B fully-labeled cell.
- Select one vertex per label.
- Prove:
  - pairwise distances `< δ` (choose `m` large enough),
  - own-label nonnegative displacement via existing label lemmas.
- Produce theorem:
  - `exists_labeled_cluster_for_delta`.

Acceptance criteria:
- Compiles clean via LSP.
- Theorem matches input shape required by:
  - `exists_fixedPoint_of_arbitrarilyFine_labeled_clusters`.

### Workstream D: Integration and Game Closure
Target files:
- `Fixpoint/BrouwerStdSimplex.lean` (or wrapper module)
- `GameTheory/MixedNashExistence.lean` and related imports

Tasks:
- Compose cluster theorem + abstract reduction to full Brouwer theorem.
- Replace mixed-Nash existence axiom path with theorem application.
- Ensure NFG follows immediately as corollary.

Acceptance criteria:
- No axioms/sorries in fixed-point→mixed-nash path.
- LSP clean for touched files.

---

## Suggested Agent Split
- Agent 1: Workstream A
- Agent 2: Workstream B
- Agent 3: Workstream C (starts with stubs; fully activates after A/B interfaces stabilize)
- Agent 4: Workstream D + interface stabilization + final theorem plumbing

Coordination contract:
- Freeze shared theorem signatures early (A/B outputs; C input).
- Keep helper lemmas local unless clearly reusable.
- Rebase/merge only after LSP-clean checks on each file.

---

## Interface Contracts (to avoid merge churn)
Workstream A should provide:
- `SubdivisionCell`
- `cellVertices : SubdivisionCell -> Finset (stdSimplex ... )` (or grid vertices + coercion)
- `cell_diameter_bound`

Workstream B should consume only:
- abstract cell adjacency/boundary notions + labeling function

Workstream C should consume:
- `exists_fully_labeled_cell`
- `cell_diameter_bound`
- existing label admissibility lemmas in `SpernerLabeling`/`SpernerGridLabel`

---

## Milestones (Measurable)
1. M1: Subdivision mesh theorem proved (A done).
2. M2: Sperner fully-labeled existence proved (B done).
3. M3: `exists_labeled_cluster_for_delta` proved (C done).
4. M4: Full Brouwer theorem in repository path (D done).
5. M5: Mixed Nash theorem discharged without axioms (D done).

---

## Risk Register + Mitigation
1. Parity proof complexity:
   - Keep parity algebra isolated (`SpernerParity.lean`).
2. Type coercion noise (`Subtype`, casts, `Fin`):
   - Local helper lemmas; avoid global abstraction early.
3. Over-generalization:
   - Prove core on `Fin (n+1)`, transport to general finite type afterwards.
4. LSP latency:
   - Small modules, frequent `update` + `diagnostics`.

---

## Immediate Next Step
Start Workstream A and B in parallel.

- A first PR: subdivision definitions + mesh bound skeleton.
- B first PR: labeling admissibility + statement of Sperner existence theorem and supporting parity lemmas.

Then C wires both and unlocks final Brouwer closure.
