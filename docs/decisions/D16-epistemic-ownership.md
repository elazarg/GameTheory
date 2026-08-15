# D16: epistemic ownership is separate from Protocol information

- **Status:** adopted and promoted
- **Date:** 2026-07-30
- **Experiment IDs:** EXP-043

## Decision / question

Whether finite partitions, knowledge events, posteriors, and Aumann agreement
should be laws of `Protocol.InformationModel.InfoState`, a separate epistemic
branch, or game-free mathematics.

## Competing designs

1. Treat every Protocol `InfoSet` as a cell of a partition of execution states.
2. Derive partitions only from Protocol models carrying an extra
   unique-history or state-view premise.
3. Give epistemic games their own finite-cell partition object, sharing only
   the canonical finite probability law.
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

The positive half defines a finite-cell partition independently and proves
full Aumann agreement from one `FinDist` prior, operation-local decidable
equality, full support, a nonempty public event, self-evidence for both
partitions, and constant posterior reports.

## Measurements

| Measure | EXP-043 result |
|---|---|
| authored size | 287 nonblank lines; 22 declarations |
| stable API change during experiment | 0 declarations and 0 imports |
| authored import | `GameTheory.Protocol.Information` only |
| focused build | 1,718 jobs |
| full build | 3,342 jobs |
| probability representation | existing `GameTheory.Math.Probability.FinDist`; no second law type |
| data-level capabilities | no stored `Fintype`, `Finite`, or `DecidableEq` |
| source trust/audit tokens | 0 placeholders, native decisions, custom axioms, direct updates, transports, `HEq`, tactic `change`, or `open Classical` |
| repository audits | Phase 2/3 expected source measurements and declaration coverage pass |
| axiom profile | `propext`, `Classical.choice`, `Quot.sound` only |
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

Adopt a stable `GameTheory.Epistemic` branch. Its foundational object is an
explicit finite-cell `InfoPartition`; it owns event knowledge, common
knowledge, posteriors, and agreement results. It shares
`GameTheory.Math.Probability.FinDist`, but it does not import Protocol, static game
forms, solution concepts, or Analysis.

`Protocol.InformationModel.InfoState` remains history-local. No new law is
added to it, and no conversion to an epistemic partition is claimed. A future
Protocol-to-epistemic bridge must name and test the extra premise that makes a
state view well-defined; tree-shaped execution is a candidate, not an implicit
default.

Promotion starts with the checked finite-cell, posterior, self-evidence,
disjoint-cell, sum-decomposition, and Aumann-agreement slice. Broader S5 and
approximate-common-knowledge recovery follows only after the D-KNOW
declaration ledger classifies the representative inventory.

That promotion is complete. `GameTheory.Epistemic.Basic` contains the
partition, posterior, and self-evidence interface;
`GameTheory.Epistemic.Agreement` contains the cell decomposition and Aumann
theorem; and `GameTheory.Epistemic` is re-exported by the public root. The
stable branch has 174 nonblank lines and no Protocol, static-solution, or
Analysis import. Full Phase 2/3 reachability audits pass: all three intended
finite-law/epistemic inputs are reached, five forbidden epistemic dependencies
are rejected, and Protocol rejects both public epistemic probes. The stable
Aumann theorem has only the standard `propext`, `Classical.choice`, and
`Quot.sound` axiom profile. The focused build completes in 1,715 jobs and the
full build in 3,345.

## Common-knowledge recovery

The next mature batch validates the same boundary rather than reopening it.
`GameTheory.Epistemic.Knowledge` now owns the finite S5 operator, T/4/5,
monotonicity and conjunction, mutual knowledge, and the public self-evident
event characterization of common knowledge. Enumeration capabilities occur on
`Knows`, mutual knowledge, and the finite common-knowledge event, never on
`InfoPartition`.

All 30 declarations in the pinned `CommonKnowledge.lean` file now have exact
reviewed ledger rows. The expanded Epistemic root has 370 nonblank lines; its
focused build completes in 1,716 jobs and the full build in 3,350. The full
Phase 2 gate positively reaches the new common-knowledge layer (`4/4`
Epistemic inputs) while rejecting the same five static, sequential, and
analytic dependencies. Representative S5/common-knowledge theorems retain the
standard axiom profile.

The approximate operator batch also stays inside D16. `PBelief`,
`mutualPBelief`, `IsPEvident`, and `CommonPBeliefAt` reuse the same posterior,
partition, and finite event model; exact common knowledge implies common
`p`-belief for every threshold at most one. The predecessor's separate
positive-prior predicate is subsumed by `FinDist.FullSupport`.

This raises the expanded Epistemic root to 544 nonblank lines. Its focused
build completes in 1,717 jobs and the full build in 3,351. The Phase 2 audit
now positively reaches all five intended Epistemic layers and still rejects
all five forbidden dependency probes.

The final quantitative batch promotes
`commonPBelief_posterior_reports_close`. Its 13 supporting mass, cell, and
scalar lemmas remain private. The proof uses `FinDist.prob` and `FullSupport`
throughout and establishes the full Monderer--Samet
`|r i - r j| ≤ 2 * (1 - p)` bound.

D-KNOW recovery is now complete: all 62 pinned declarations have exact
reviewed dispositions. The final Epistemic root has 1,149 nonblank lines,
builds in 1,718 focused / 3,352 full jobs, has zero source transport or trust
tokens, and retains the standard axiom profile. The full Phase 2 gate reaches
all six intended Epistemic layers and rejects all five forbidden dependencies.
