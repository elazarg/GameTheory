# Standard Library Anchors (Do Not Re-Prove)

Use these canonical Mathlib lemmas directly.

## Function update algebra

From `Mathlib/Logic/Function/Basic`:

- `Function.update_self`
- `Function.update_of_ne`
- `Function.update_eq_self`
- `Function.update_idem`
- `Function.update_comm`
- `Function.curry_update`
- `Function.uncurry_update_update`

Guideline:

- If a proof step is exactly one of these, rewrite to the canonical lemma and
  avoid shadow duplicates.

## PMF bind basics

From `Mathlib/Probability/ProbabilityMassFunction/Monad`:

- `PMF.bind_bind`
- `PMF.bind_comm`
- `PMF.bindOnSupport_*` family

Guideline:

- Prefer `bindOnSupport` forms when the target function is only meaningful on support.
- Use support-aware congruence only when canonical lemmas do not directly apply.

