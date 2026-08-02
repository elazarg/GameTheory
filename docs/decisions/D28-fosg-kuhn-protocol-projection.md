# D28: FOSG Kuhn theory is a theorem-only Protocol projection

- **Status:** adopted
- **Date:** 2026-08-02
- **Experiment IDs:** EXP-057

## Decision / question

Whether the pinned FOSG native-history/Kuhn stack contains an independently
owned execution semantics, or whether its mature results should be exposed as
named specializations of the canonical `InformationModel` laws selected by
D6/D15.

## Competing designs

1. Port `ObsModelCore`, its execution-state and native-history PMF machines,
   step-invariant predicates, strategy lifts, and point-probability proof
   spine.
2. Expose no FOSG-facing Kuhn names and require every caller to project
   `G.information` manually.
3. Add an opt-in theorem-only `GameTheory.Languages.FOSG.Kuhn` leaf with
   transparent plan/signature abbreviations and named complete-history and
   outcome-law theorems delegated directly to `InformationModel`.

Design 3 is adopted.  It preserves a discoverable domain surface without a
second semantic object.  The FOSG syntax root does not import the leaf.

## Representative hostile slice

EXP-057 reuses one two-vote `ExecutionProtocol` with two information models.
The forgetful model reaches the same information state after distinct own
plays and machine-refutes perfect recall.  The recalling model changes only
the signals and information update; it proves perfect recall and that every
nontrivial information state is used at most once.  Packaging the recalling
model as a genuine FOSG reaches both named Kuhn directions, equality of
realizable complete-history laws, and arbitrary outcome pushforwards.

A one-move model separately satisfies acts-once while refuting perfect recall,
so the behavioral-to-mixed result is not made artificially conditional on the
stronger recall hypothesis.

This slice matters because the same execution supports failure and success:
recall is owned by observation design, not by an FOSG-native runner or a stored
property of the transition graph.

## Measurements

| Measure | EXP-057 result |
|---|---|
| pinned scope | 39 declarations in `Native/History.lean` and `Native/HistoryMarginal.lean` |
| stable surface | transparent behavioral/mixed plan and behavioral-signature abbreviations; five named theorem families; zero new runner/history/strategy data |
| named hypotheses | behavioral-to-mixed uses `ActsOnceWhereItMatters`; the familiar recall-facing mixed-to-behavioral theorem uses `PerfectRecall` through the weaker `ConstrainsAlike` premise |
| retained law | equality of canonical `FinDist ExecutionProtocol.History` laws, plus arbitrary `FinDist.map` outcome projections |
| removed machinery | `ObsModelCore`, PMF product bridges, native execution states, history-machine conversion, semantic step invariant hierarchy, strategy lifts, list-chain/`SeenBefore` coefficient induction |
| pinned dispositions | 13 adapt / 7 subsumed / 19 retired; L-FOSG becomes 372/776 reviewed with 404 queued |
| focused build | FOSG Kuhn leaf and hostile witness build as a 1,724-job target |
| source hazards | no placeholders, raw updates, transports, `Fintype.ofFinite`, EFG/utility imports, PMF compatibility layer, or custom axioms |
| axiom profile | `propext`, `Classical.choice`, and `Quot.sound` only |
| boundary audit | syntax root rejects 3/3 solution/Kuhn probes; opt-in leaf reaches 5/5 named results and rejects EFG 1/1; Phase 3 `VERIFIED=1` |
| full integration | full build 3,415 jobs; Phase 2 static, Phase 3 full reachability, and coverage audits `VERIFIED=1` |

## Kill conditions and result

Reject the design if it defines a second FOSG history, evaluator, runner, or
strategy carrier; hides or conflates the two named information hypotheses;
restores stored/global finiteness or transport helpers; imports EFG to prove a
general FOSG theorem; or claims the separately gated counterfactual-reach/CFR
or continuation-coefficient spines.

No kill condition fired.  The old scalar `marginal_prob` is subsumed more
strongly by complete-law equality and point evaluation.  The old full
observation-locality and posterior predicates were interfaces to the removed
proof machine, not assumptions needed by the canonical mixed-to-behavioral
theorem.  The observation-model inventory beyond these 39 rows remains open;
in particular EXP-057 does not credit the cast-heavy reachable-history/CFR
spine.

## Result and consequences

`GameTheory.Languages.FOSG.Kuhn` is an opt-in theorem leaf over
`G.information`.  Its direction, history-law, and outcome-law statements mirror
the mature EFG-facing vocabulary where the mathematics is genuinely shared,
without importing EFG or routing simultaneous FOSGs through single-mover
syntax.

The old native execution and marginal layers are adapted, subsumed, or retired
row by row.  A named serialization comparison from simultaneous FOSG to EFG is
not this decision: it requires a separate hostile stochastic slice proving
hidden within-round choices and exact mapped law preservation.
