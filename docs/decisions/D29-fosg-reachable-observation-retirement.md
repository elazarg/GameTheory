# D29: Retire the reachable-observation adapter

- **Status:** adopted
- **Date:** 2026-08-02
- **Experiment IDs:** EXP-058

## Decision / question

Whether the pinned
`Languages/FOSG/ReachableHistory/ObsModelFacts.lean` file contains stable FOSG
observation mathematics, or is an adapter for the native reachable-history
machine retired by D6/D15/D28.

## Competing designs

1. Port its reachable-history `ObsModelCore`, scalar PMF runners, invariant
   hierarchy, raw player/public-view lemmas, posterior proof, and strategy
   lifts.
2. Leave all 46 declarations unreviewed until a future counterfactual or CFR
   theorem requests part of the file.
3. Classify the reusable mathematics against its canonical Protocol owners and
   retire the second-machine interfaces.  Require any future CFR theorem to be
   stated and proved from the canonical history law.

Design 3 is adopted.  The file earns no new stable declaration.

## Representative hostile slice

The accepted `ExecutionProtocol` deliberately does not constrain `active` at a
terminal state.  EXP-058 constructs a terminal-initial, active one-player
protocol with two Boolean local choices and a valid `InformationModel`.  The
runner stops without querying a chooser, yet the choice type is not a
subsingleton.  This machine-refutes the pinned terminal-to-`none` and terminal
choice-subsingleton claims as general FOSG facts.  Their valid operation-local
replacement is `InformationModel.subsingleton_choice_of_not_active`.

The existing `Repeat.once` witness supplies the other hostile edge.  Its
compressed information state can agree after histories with distinct own
actions, and `Repeat.single_not_perfectRecall` records the failure.  Equality
of current information therefore cannot inherit the pinned raw player-view
list cancellation laws without an explicit recall premise.

## Measurements

| Measure | EXP-058 result |
|---|---|
| pinned scope | 46 declarations; 1,233 nonblank lines |
| dispositions | 2 adapt / 1 subsumed / 43 retired |
| adapted owners | `reachableHistoryOutcomeDist` to `InformationModel.runBehavioral`; pure outcome law to `InformationModel.run` |
| subsumed owner | `projectActions_snoc_eq` by the richer typed `InfoSignals.ownPlay_extend` |
| raw source hazards | 128 `ObsModelCore`; 47 `PMF`; 32 `ParameterizedChain`; 19 raw updates; 24 `change`; 20 `▸`; 3 `HEq`; 1 `Fintype.ofFinite`; 15 `classical`; 9 noncomputable definitions |
| direct consumers | `ReachableHistory/Law.lean` and the umbrella; the law file uses the adapter for its retired native Kuhn/equilibrium-transfer proof spine |
| focused witness | 1,724 jobs, warning-free |
| full integration | full build 3,416 jobs; Phase 2 static and coverage audits `VERIFIED=1` |
| axiom profile | `propext`, `Classical.choice`, and `Quot.sound` only |

The source file declares no counterfactual reach, regret, or CFR theorem.  Its
posterior-locality and strategy-lift declarations are inputs used downstream
to build the native mixed-to-behavioral law.  D28 already provides that law at
the canonical `InformationModel` layer, so this is not deferred CFR coverage.

## Kill conditions and result

Reject a survivor if it requires `ObsModelCore`, reachable-only strategy or
history carriers, scalar PMF execution, raw observation lists, terminal
inactivity, stored/global finiteness, raw `Function.update`, or public
cast/`HEq` transport.  Also reject classification that credits a future CFR
theorem merely because retired downstream code once imported this adapter.

Both hostile slices compile and no candidate survives the kill conditions.
The raw view and terminal claims are not merely awkward ports: they would
weaken the accepted semantics.  Alternate runners, step invariants,
posterior-locality adapters, and strategy lifts have no surviving consumer
after D28.

## Result and consequences

The exact 46-row batch is closed with no new stable source.  Protocol owns
history extension, information compression, operation-local menus, and the
mixed/behavioral history laws.  FOSG remains a transparent specialization.

The next FOSG DFS gate is the separately named simultaneous stochastic
FOSG-to-EFG serialization comparison.  Future counterfactual or CFR work is a
different theorem family: it must start from canonical `runBehavioral` history
laws and justify its own definitions and proof interface.
