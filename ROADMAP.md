# GameTheory MVP Completion Roadmap

## Purpose

Define the planned path to an MVP-complete GameTheory library that is stable enough to unblock downstream client work.

This file is a roadmap only. It describes target scope, planned milestones, and acceptance gates.

## Target Scope

In scope for MVP:
1. Finite, discrete game-theory semantics (`PMF`-based).
2. Core abstraction (`KernelGame`) plus `NFG`, `EFG`, and `MAID` representations.
3. Utility-distribution API (`udist`, `udistPlayer`).
4. Preference-parameterized solution concepts over outcome distributions.
5. Bridge theorems that preserve semantics across representations.
6. Utility-distribution corollaries for Kuhn equivalence.
7. Canonical examples showing end-to-end usage.

In scope for the broader roadmap (post-MVP):
1. Additional solution concepts and equilibrium refinements.

Out of scope for MVP:
1. Continuous/infinite probability spaces.
2. Client-specific APIs.
3. Full `InfoArena` semantics.

## Architecture Direction

1. Keep game structures concept-neutral.
2. Keep solution concepts parameterized by preference relations over outcome distributions.
3. Treat expected utility as one specialization, not a privileged primitive.
4. Reuse outcome-kernel equality as the main transfer mechanism between representations.

## Planned Work Items

### A) Utility Distribution Layer

Plan:
1. Define `KernelGame.udist : Profile -> PMF (Payoff i)`.
2. Define `KernelGame.udistPlayer : Profile -> i -> PMF Real`.
3. Add deterministic-collapse lemmas.

Acceptance:
1. API is stable and documented.
2. Lemmas are available for deterministic kernels.

### B) Preference-Parameterized Concepts

Plan:
1. Define `IsNashFor` and `IsDominantFor` using outcome-distribution preference.
2. Prove `dominant_is_nash_for`.
3. Add expected-utility specialization (`euPref`) and iff-theorems.

Acceptance:
1. Concepts are independent of any specific utility functional.
2. EU appears only as specialization.

### C) Bridge Preservation

Plan:
1. Add utility-distribution preservation corollaries for:
   - NFG to KernelGame
   - EFG to strategic KernelGame
   - MAID to EFG to KernelGame
2. Ensure theorem naming is consistent and discoverable.

Acceptance:
1. All bridge targets have theorem-level preservation statements.
2. Statements are phrased so future preference models can reuse them.

### D) Kuhn Utility-Distribution Corollaries

Plan:
1. Add behavioral-to-mixed utility-distribution corollary.
2. Add mixed-to-behavioral utility-distribution corollary.

Acceptance:
1. Both directions are exposed as top-level theorems.
2. Corollaries compose cleanly with bridge theorems.

### E) InfoArena

Status: experimental, definition unclear.

Source lives on branch `experimental/info-arena` (not on master).
State-based imperfect-info transition system — an alternative to tree-based EFG.
Contains `sorry` in `outcomePMF`; semantics need further design work before integration.

### F) Example Suite

Plan:
1. NFG examples for utility distribution + preference-parameterized concepts.
2. EFG examples for utility distribution + strategic bridge.
3. MAID example for reduction and preservation.

Acceptance:
1. Examples compile and demonstrate intended user workflows.

## Release Gates (MVP)

MVP is ready when all are true:
1. `lake build GameTheory` passes.
2. No `sorry` in MVP-surface modules.
3. Utility-distribution API is available.
4. Preference-parameterized concept layer is available.
5. Bridge preservation coverage exists for NFG, EFG, and MAID.
6. Kuhn utility-distribution corollaries are available.
7. `InfoArena` lives on `experimental/info-arena` branch, not on master.
8. README describes scope and delivered capabilities for client consumers.

## Post-MVP Backlog

1. Revisit `InfoArena` design (branch `experimental/info-arena`) — finalize semantics, complete evaluator, add bridges.
2. Add richer preference families (stochastic dominance, risk, regret).
3. Add advanced equilibrium refinements (including subgame perfect, sequential, correlated).
