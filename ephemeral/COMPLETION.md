# Completion Plan: Finite, Discrete Noncooperative Game Theory Core

## Goal
Complete the library so the claim
"This library formalizes the core of finite, discrete noncooperative game theory"
is technically defensible by standard textbook expectations.

## Definition of Done (project-level)
The project is done when all of the following are true:
- General finite mixed-strategy Nash existence is formalized (not only special cases).
- Two-player zero-sum minimax theorem is formalized at the mixed-strategy level.
- Sequential refinements in EFG are upgraded from schemas to concrete definitions with key bridge theorems.
- No placeholder theorems (`sorry`) remain in project-owned core files.
- Core examples demonstrate each major theorem family end-to-end.

## Current Gap Summary
Already strong:
- Kernel game semantics, EU, Nash/dominance, CE/CCE, potential/team/zero-sum/constant-sum.
- NFG/EFG/MAID representations and interoperability bridges.
- Substantial Kuhn-equivalence infrastructure.

Primary missing pieces:
- General mixed Nash existence theorem.
- Full minimax theorem (value equality and equilibrium existence consequences).
- Concrete sequential/PBE layer.
- One known placeholder theorem in `AbstractFolk.lean`.

## Milestones (priority order)

### M1: Mixed Nash Existence (highest priority)
Deliverables:
- New module: `GameTheory/NashExistenceMixed.lean`.
- Theorem (core): finite NFG has a mixed Nash equilibrium.
- Bridge theorem: induced result for kernel games arising from finite NFGs.

Likely prerequisites:
- Best-response correspondence on mixed profiles.
- Convexity/nonemptiness/closed graph lemmas for finite simplex products.
- Fixed-point machinery integration (use mathlib primary results).

Acceptance criteria:
- Public theorem with usable statement for `NFG.IsNashMixed`.
- At least one canonical example (e.g., matching pennies) discharged through the general theorem interface.

### M2: Minimax Theorem (2-player finite zero-sum)
Deliverables:
- New module: `GameTheory/MinimaxTheorem.lean`.
- Value equality theorem:
  `max_min = min_max` (in library's mixed-kernel vocabulary).
- Equilibrium corollaries for zero-sum mixed Nash.

Likely prerequisites:
- Clean definition of maximin/minimax values in current API.
- Reuse M1 existence and zero-sum structure lemmas.

Acceptance criteria:
- Theorem instantiated for finite action spaces.
- Link to `IsNashMixed` in zero-sum games is explicit.

### M3: Sequential Refinements in EFG
Deliverables:
- New modules:
  - `GameTheory/SequentialEq.lean`
  - `GameTheory/SubgamePerfect.lean`
- Replace schema-only predicates with concrete definitions for:
  - sequential rationality
  - belief consistency
  - sequential equilibrium and PBE
- Strengthen SPE definition with practical `isSubgame` conditions.

Likely prerequisites:
- Belief construction on infosets/reachability.
- Additional technical lemmas for off-path beliefs and conditioning.

Acceptance criteria:
- At least one nontrivial EFG example verified as SPE or not SPE.
- At least one bridge theorem from EFG equilibrium notion to strategic-form Nash in special cases.

### M4: Cleanup and Completeness
Deliverables:
- Remove remaining placeholder(s), especially `AbstractFolk.abstract_folk_theorem`.
- If folk theorem is intentionally out-of-scope, move to `ephemeral/` or mark as non-core extension and exclude from top-level claims.
- Audit docstrings in all exported modules for scope/guarantees alignment.

Acceptance criteria:
- `rg "\\bsorry\\b|\\badmit\\b" GameTheory *.lean` returns empty for core library files.
- README claim matches implemented theorem set exactly.

### M5: Consolidation and User-Facing Guarantees
Deliverables:
- Add `GameTheory/CoreTheorems.lean` re-exporting theorems that justify the "core" claim.
- Extend examples:
  - pure and mixed Nash,
  - CE/CCE,
  - minimax,
  - sequential refinement example.
- Optional: add theorem index in `README.md`.

Acceptance criteria:
- One import gives users all core concepts + flagship theorems.
- Examples compile and reference the final theorem names.

## Implementation Strategy
- Keep `KernelGame` as semantic center; prove major theorems once there when possible.
- Use representation bridges (`NFG ↔ KernelGame`, `EFG -> strategic`) to avoid duplication.
- Prefer small lemma modules over monolithic files.
- For hard existence proofs, first land technical simplex/fixed-point lemmas, then final theorem.

## Risk Register
- R1: Fixed-point prerequisites may cause heavy dependency complexity.
  - Mitigation: isolate topology/convex analysis support lemmas in dedicated helper module.
- R2: Sequential-equilibrium formalization can sprawl.
  - Mitigation: deliver minimal concrete SE first, then PBE.
- R3: Naming/API drift across modules.
  - Mitigation: add a stable theorem namespace and a public theorem index.

## Suggested Work Breakdown (short horizon)
1. Land M1 theorem statement + supporting definitions scaffolding.
2. Prove M1 in finite NFG.
3. Build M2 on top of M1 and existing zero-sum modules.
4. Implement concrete SE/SPE (M3) with one validated example.
5. Final cleanup and claim alignment (M4/M5).

## Exit Criteria for Claim Adoption
Only adopt the exact claim in README when M1, M2, M3 (minimum concrete SE/SPE), and M4 are complete.
Until then, use wording like:
"formalizes substantial foundations of finite, discrete noncooperative game theory."
