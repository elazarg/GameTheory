# D16: epistemic ownership is separate from Protocol information

- **Status:** adopted and promoted
- **Date:** 2026-07-30
- **Experiment IDs:** EXP-043; PMF generalization under EXP-135

## Decision / question

Whether information partitions, knowledge events, posteriors, and Aumann agreement
should be laws of `Protocol.InformationModel.InfoState`, a separate epistemic
branch, or game-free mathematics.

## Competing designs

1. Treat every Protocol `InfoSet` as a cell of a partition of execution states.
2. Derive partitions only from Protocol models carrying an extra
   unique-history or state-view premise.
3. Give epistemic games a separate state-partition development, sharing the
   canonical probability operations.
4. Put the whole development under `GameTheory.Math`.

Design 3 is adopted. Design 2 remains available as a future named bridge when
a real Protocol consumer supplies its missing premise. Design 1 is refuted.
Design 4 is not earned by the game-theoretic partition and common-prior
consumer; only genuinely reusable lemmas may later be extracted.

## Representative hostile slice

The negative half of EXP-043 is a valid one-player execution and information
model. At the initial state the player chooses a Boolean action. Both actions
reach the same terminal execution state, but `pushInfo` remembers the chosen
action. Menu adequacy still holds.

The merged state is consequently in both distinct state sets
`InfoSet () (.done false)` and `InfoSet () (.done true)`. A second theorem
refutes every function from execution state to view that agrees with `infoOf`
on every trace. Protocol information is history-local by design and is not, in
general, a state partition.

The original positive half defines a finite-cell partition independently and proves
full Aumann agreement from one `FinDist` prior, operation-local decidable
equality, full support, a nonempty public event, self-evidence for both
partitions, and constant posterior reports.

## Original experiment measurements

| Measure | EXP-043 result |
|---|---|
| authored import | `GameTheory.Protocol.Information` only |
| probability representation | existing `GameTheory.Math.Probability.FinDist`; no second law type |
| data-level capabilities | no stored `Fintype`, `Finite`, or `DecidableEq` |
| positive reachability | `FinDist`, `InformationModel`, experimental `InfoPartition`, and Aumann agreement |
| negative reachability | `IsNash`, sequential Analysis convergence, `stdSimplex`, and `Polynomial` rejected |
| Protocol partition probe | one reachable state lies in two distinct `InfoSet`s |
| state-view probe | no state-only view represents both realized histories |

## Kill condition

Reject any design that silently chooses one history for a merging state, adds
partition laws to every `InformationModel`, duplicates finite-law
representation, makes an action profile or game form a premise of Aumann's
theorem, stores enumeration capabilities in epistemic data, or imports
topology/Analysis for the finite theorem.

No kill condition fired for the separate branch. The first two conditions
directly reject the Protocol-as-partition design.

## Result

Adopt a stable `GameTheory.Epistemic` branch. Information partitions are ordinary
`Setoid` values and events are arbitrary sets. Knowledge and common knowledge
are probability-free; their owner imports only elementary set theory.
Posteriors and agreement use ordinary PMFs and shared fiber conditioning.
The branch does not import Protocol, static game forms, solution concepts,
or project Analysis. No finite-cell wrapper or second probability law is needed.

`Protocol.InformationModel.InfoState` remains history-local. No new law is
added to it, and no conversion to an epistemic partition is claimed. A future
Protocol-to-epistemic bridge must name and test the extra premise that makes a
state view well-defined; tree-shaped execution is a candidate, not an implicit
default.

`GameTheory.Epistemic.Knowledge` owns cells, self-evidence, and S5 operators.
`GameTheory.Epistemic.Basic` owns scalar posteriors and their connection to
canonical fiber conditioning. `GameTheory.Epistemic.Agreement` owns weighted
report reconstruction and Aumann agreement.
The public Epistemic root must remain independent of Protocol, static solution
concepts, and Analysis.

## Common-knowledge recovery

The S5 operator, T/4/5, monotonicity and conjunction, mutual knowledge, and
the self-evident-event characterization of common knowledge require neither
state nor agent enumeration. A quotient observation identifies information
cells when the probability layer needs fiber reconstruction.

The approximate operator batch also stays inside D16. `PBelief`,
`mutualPBelief`, `IsPEvident`, and `CommonPBeliefAt` reuse the same posterior,
partition, and set-valued event model. Scalar posterior is the ratio of event
and cell masses and is zero at a null cell. This convention does not construct
a conditional PMF on that cell. Knowing an event therefore implies positive
belief only with positive cell mass; full support is a sufficient convenience
assumption, not part of epistemic data. A null singleton can know the whole
space while assigning it scalar posterior zero.

Exact Aumann agreement requires a nonempty common self-evident event and
constant reports. It does not require full support or positive public mass:
on a null public event every contained cell is null, so both reports are zero.
On a positive event, supported fiber reconstruction proves the weighted-report
identity even when the prior support and cells are infinite.

For quantitative agreement, a strictly positive belief threshold supplies
the positive witness and cell masses used by the proof.
`commonPBelief_posterior_reports_close` establishes the Monderer--Samet bound
`|r i - r j| ≤ 2 * (1 - p)` without finite state/agent carriers or global full
support. EXP-135 tests infinite support and cells, distinct quantitative
reports, and the null-event distinction against the canonical definitions.
