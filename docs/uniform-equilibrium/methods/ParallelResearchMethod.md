# Method for Parallel and Independent Research

## Scope

This document explains how to run independent investigations without confusing
them with the current critical path. The changing portfolio of concrete ideas
is in [`../FRONTIER.md`](../FRONTIER.md), with priorities in
[`../PIPELINE.md`](../PIPELINE.md).

## Why pursue independent tracks

An independent track may:

- supply a missing theorem;
- produce an exact counterexample which shrinks the search space;
- reveal that the main proof language is too weak or too strong;
- create worthwhile mathematics even without a conjecture-facing consumer.

These outcomes are reported separately.

## Scoping rule

Begin with a standalone mathematical question whose data and conclusion make
sense without this codebase. Avoid questions whose hidden content is “solve
the uniform-equilibrium conjecture.”

The question specifies:

- finite or analytic input data;
- the exact probability and agency model;
- the requested theorem, characterization, algorithm, or counterexample;
- positive and negative tests;
- what counts as a complete answer.

## Evidence standard

An exploration produces one of:

- a rigorous theorem;
- an exact finite counterexample;
- a certified algorithm with a proved guarantee;
- a sharp impossibility boundary;
- a well-defined conjecture supported by exact examples and clearly labelled
  as conjectural.

Analogies, simulations, and floating-point patterns are discovery tools. They
do not become mathematical evidence until converted into one of these outputs.

## Independence discipline

Do not force an exploratory result into current proof terminology. First state
it in its native mathematical language. Only afterward ask whether it supplies
a strategy, occupation, flux, target bridge, punishment, account, progress
measure, or impossibility certificate.

Independent tracks may be pursued in parallel because they do not mutate the
central interface or assume that another open track succeeds.

## Promotion rule

Promote a result to the critical frontier only with a handoff packet containing:

1. the complete proof or exact counterexample;
2. the semantic deficit it changes;
3. the probability/conditioning mode it controls;
4. a concrete mathematical output;
5. a plausible actual-data adapter;
6. a downstream consumer;
7. stress tests against relevant boundary examples.
8. the logical level changed: supplied-object verification, bounded synthesis,
   or strategy-class coverage.

Until then it remains independently valuable exploration and receives no
closure credit.

## Retirement rule

Retire or pause a direction when its key implication is refuted, its output has
no possible consumer, or it only restates an existing obstruction in new
language. Preserve the negative theorem and examples; do not preserve the
direction as an implied obligation.

## Documentation rule

The methodology stays stable. Add, remove, and reprioritize concrete
cross-field ideas only in a claim file under `ideas/<Group>/` or another
dated research note.
