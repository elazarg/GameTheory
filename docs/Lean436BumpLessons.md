# Lean 4.36 / Mathlib v4.36.0: bump lessons for clients

GameTheory uses released Lean and Mathlib 4.36.0. The base package version is
4.36.0.

## Dependency pins

| Component | Pin |
|---|---|
| Lean toolchain | `leanprover/lean4:v4.36.0` |
| Mathlib requirement | `v4.36.0` |
| Resolved Mathlib commit | `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` |
| fixed-point-theorems | `29c7c8a0494b297561150c04e7263376351ce609` |

The [fixed-point update](https://github.com/elazarg/fixed-point-theorems-lean4/commit/29c7c8a0494b297561150c04e7263376351ce609)
replaces the deprecated `toContinuousMap` with `ContinuousMap.ofClass`. Its strict
standalone build (`lake build --wfail`) passed 6,490 jobs, and all six theorem
endpoints use only the standard axioms.

Keep the explicit Mathlib requirement last in each Lake configuration, and
regenerate manifests with `lake update` rather than editing them.

## Extended non-negative sums

Mathlib generalized the `ENNReal` infinite-sum lemmas to complete lattices and
deprecated the specialized names. Each deprecated `ENNReal.X` maps to the
replacement named in its deprecation attribute, usually the root name `X`:
`ENNReal.summable` becomes `CompleteLattice.summable`, `ENNReal.tsum_eq_zero`
becomes `tsum_eq_zero_iff`, and `ENNReal.tsum_add`, `tsum_comm`, `tsum_prod'`,
`tsum_le_tsum` and `le_tsum` lose the prefix. The root `le_tsum` takes the summand
explicitly: write `le_tsum _ a` or `le_tsum (f := g) a`, not `le_tsum a`.
`MeasureTheory.Measure.smul_apply` is likewise replaced by the root `smul_apply`.

## Elaboration and induction

- `Nat.strong_induction_on` names its single case `ind`, not `h`.
- Arguments previously inferred through a definitional unfolding of a set may need
  to be named: the feasible set of `Math.maximal_of_isMaxOn` when the goal states
  a conjunction predicate, and the domain `s` of `ConcaveOn.subset` when the subset
  proof projects from a budget-set membership.
- In `eq_winner_of_bid_gt`, the goal left by `contrapose!` now states `≤` directly,
  so the bid comparison is supplied without `not_lt.mpr`.

## Unused tactic linter

Mathlib's unused tactic linter flags a tactic unless at least one of its
executions changes the goals. `all_goals`, `any_goals` and `<;>` are unused when
they act on at most one goal, and `try t` is unused when `t` always succeeds.
Removing such a wrapper is right when every execution sees exactly one goal.

A branch whose first tactic sometimes closes the goal and sometimes leaves
arithmetic cannot keep a trailing `; all_goals t` or `try t`: neither form is
ever used in the linter's sense. Try the combined proof first and fall back to
the closing tactic alone:

```lean
first | (simp_all; omega) | simp_all
```

When the leftover goals are decidable side conditions, `simp +decide` closes them
in the same call.

## Kernel evaluation through matrix arrays

Mathlib now provides `Matrix.ofArray` in the module
`Mathlib.LinearAlgebra.Matrix.Array`, which does not expose its definitions. The
exact determinant and dictionary computations store matrices through it, so a
test that evaluates them with `decide +kernel` must also have

```lean
import all Mathlib.LinearAlgebra.Matrix.Array
```

beside its existing `import all Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Defs`.
A non-module scratch file sees every definition and therefore does not reproduce
this failure; check such tests with `lake build` on the module.

## Validation

```text
python scripts/audit.py
python -B -m unittest discover -s scripts/tests
```

The base audit passed all 7,849 default build jobs, all 9,696 lint and
transitive axiom-audit jobs, environment lint, source boundaries, coverage and
diagnostic traces. All 44 tooling regression tests passed.
