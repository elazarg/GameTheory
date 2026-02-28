# GameTheory Review: Actual Open Issues

Date: 2026-02-28

This file tracks only current, concrete issues confirmed in the codebase, with proposed fixes.
Previously listed broad/older issues were removed.

## 1) Subgame perfection can be vacuous

- Location: `GameTheory/EFG.lean` (`EFGGame.IsSubgamePerfectFor`)
- Problem:
  - `IsSubgamePerfectFor` quantifies over `t` with premise `isSubgame t`.
  - If `isSubgame` is too weak (e.g., always false, or excludes the root), the condition is trivially true for every profile.
  - This permits meaningless “subgame-perfect” claims.
- Proposed fix:
  - Replace raw `isSubgame : GameTree ... -> Prop` with a structured predicate record carrying minimal laws:
    - root is a subgame
    - subgame well-formedness constraints (as needed by your intended notion)
  - Short-term minimal guard: add a required hypothesis that the root tree is a subgame.

## 2) PBE is currently only a rename of sequential-equilibrium schema

- Location: `GameTheory/EFG.lean` (`EFGGame.IsPerfectBayesianEqFor`)
- Problem:
  - `IsPerfectBayesianEqFor` is definitionally equal to `IsSequentialEqFor`.
  - This collapses two concept names into one logical notion, so users cannot state distinct PBE-vs-SE results.
- Proposed fix:
  - Keep `IsSequentialEqFor` as the generic schema.
  - Redefine `IsPerfectBayesianEqFor` with its own consistency/rationality contract (or via a PBE-specific predicate bundle).
  - If intentional as a temporary alias, mark as deprecated placeholder in docstring and add TODO with acceptance criteria for split.

## Not treated as issues

- Vacuity on empty/degenerate types for `IsNash` / dominance / strict variants:
  - Standard in Lean unless explicitly restricted by `[Nonempty]` or cardinality assumptions.
- Terminal/base-case vacuity (e.g., perfect recall on terminal trees):
  - Standard inductive base case.
- Thin aliases (`updateAt`, `pushforward`, semantics-equality aliases):
  - Intentional convenience wrappers.
