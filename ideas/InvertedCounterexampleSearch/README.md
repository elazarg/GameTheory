# Inverted counterexample search

| Lifecycle | Verdict | Priority | Group decision |
| --- | --- | --- | --- |
| `PENDING` | `OPEN` | `P1` | Decide whether the non-algebraic constraints can be finitised — concretely, whether a weight admitting an admissible absorbing cycle admits one of bounded length. That decides whether the exhaustion is a computation. |

Contents:

- [Every proved theorem constrains the hypothetical counterexample](EveryProvedTheoremConstrainsTheHypotheticalCounterexample.md)
  — the accumulating constraint ledger, its seals, and the demonstration that
  the algebraic screen is necessary but nearly inert.

## Why this group exists

The conjecture is attacked from neither end. Instead of searching for a
counterexample or for a proof, assume a counterexample and read every proved
theorem as a constraint on it. The constraint set is monotone: it only grows.
Either a weight satisfying all of it is exhibited — refuting the conjecture —
or the set is shown empty, which proves the conjecture by exhaustion over the
cases the constraints define.

This is a *method* group, not a mechanism group. It owns no mathematics of its
own: each constraint is attributed to the file or module that proved it, and the
group's contribution is the joint object and the discipline of recording, for
each constraint, what it actually excludes.

## Dependencies and consumers

Consumes results from
[`AbsorbingCycleCarrier`](../AbsorbingCycleCarrier/README.md) — the cycle
reduction, the discounted-limit dichotomy, and the defect-vanishing families —
and from the literature axis in
[`UniformEquilibriumLiterature`](../UniformEquilibriumLiterature/README.md).
Its consumer is the open premise `quitting_zeroSolo_or_admissibleCycle` in
`GameTheory/Concepts/Stochastic/QuittingConjecture.lean`, which emptiness of the
constraint set would discharge.

## Standing caution

A constraint can be valid, hand-verified, and immediately computable, and still
cut nothing. The algebraic screen is the group's own worked example: the
canonical three-player hard table passes it while possessing a machine-checked
admissible absorbing cycle. New constraints are not admitted to the ledger
without a statement of what they exclude.
