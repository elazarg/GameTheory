# Extraction Queue (Whole Game-Theory Codebase)

This queue is prioritized for maximum cross-module reuse.

## Q1 (Highest): F3 + F2 bridge-heavy lemmas

1. Definition-free tail transport lemmas (suffix closure templates).
2. Reachable-agreement congruence (no representation assumptions).
3. Update/curry normalization variants where proof scripts currently rely on definitional equality.

Why first:

- Unlocks `Proto*`, `Sequential*`, and representation-bridge proofs.

## Q2: F4 existence and implication kernels

1. Best-response fixed-point skeletons with abstract compactness/finiteness interfaces.
2. Support-restriction congruence lemmas (distribution semantics preserved under support equivalence).

Why second:

- Reused by many equilibrium concept files.

## Q3: F5 dynamics/potential generic descent packages

1. Monotone potential descent under local update.
2. Finite-improvement termination from well-founded order.

Why third:

- Converts many dynamics proofs to short adapter layers.

## Q4: F6 mechanism property combinators

1. Truthfulness decomposition (IC + feasibility + transfer law).
2. Welfare decomposition by additive objective parts.

Why fourth:

- Reduces repetition across auction/social-choice modules.

## Q5: F7 value/determinacy recursion cores

1. Backward recursion theorem schemas over finite branching.
2. Determinacy formulation equivalences (force/guarantee/value).

Why fifth:

- Useful but usually downstream of earlier abstraction cleanup.

## Per-item acceptance rule

Add a lemma only if:

1. it removes assumptions from at least two files, or
2. it shortens at least one large proof by replacing a custom local argument.

## Structural-first gate (before adding lemmas)

1. Identify which structural constraint slot (`A1..A8` from `40-StructuralCore.md`) the step belongs to.
2. If none matches, propose a new slot before adding any code artifact.
3. Keep statements equation/implication-first; postpone intuitive naming.
