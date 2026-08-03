# D30: Serialize simultaneous FOSGs through hidden explicit EFG phases

- **Status:** adopted for one-round feasibility and explicit ordering; generic
  promotion remains experiment-gated
- **Date:** 2026-08-02
- **Experiment IDs:** EXP-059

## Decision / question

Whether a simultaneous stochastic FOSG can compile to a single-mover EFG
without revealing an earlier within-round choice, changing the behavioral
strategy space, or weakening exact execution-law preservation to payoff
equivalence.

## Competing designs

1. Port the pinned serial-FOSG machine and its separate execution semantics,
   then route the EFG bridge through it.
2. Merge or erase partial decision prefixes to obtain tree shape, or expose the
   prefix through the target information state so the compiler can recover it.
3. Retain the complete serialized prefix in the target execution state, expose
   only the current microstep phase through `InformationModel`, use the source
   players in an explicit finite order, and prove both policy projection and
   exact mapped canonical-run laws.

Design 3 is adopted.  The concrete hostile slice validates the semantic shape;
it does not by itself freeze a generic public compiler API.

## Representative hostile slice

EXP-059 uses two real Boolean players who act simultaneously and a nondegenerate
Boolean chance transition.  Both serialization orders are built as EFGs.  A
target state stores the first and second legal joints and the idle resolution
joint, while its public signal records only `firstTurn`, `secondTurn`,
`resolving`, or `done`.

The second mover reaches the same information value after either first action,
even though the underlying target states are distinct.  Separate witnesses
show that either player's action and the chance bit alter the full mapped
terminal outcome, so the law theorem cannot pass by forgetting the hostile
coordinates.

## Measurements

| Measure | EXP-059 result |
|---|---|
| hostile artifact | 1,320 nonblank lines; 108 declarations |
| import surface | only stable `Languages.EFG` and `Languages.FOSG`; no MAID, Analysis, utility, Frontier, or Challenges import |
| target structure | unique predecessor and unique trace; `IsTreeShaped`; at most one active source player at each microstep |
| information test | phase-only signals; reachable later information equal after distinct stored first choices |
| policy test | source-to-target translation and target-to-source projection; both composites agree at every reached decision information state |
| law test | literal target-history erasure equals the canonical source `InformationModel.runBehavioral` history law for every target profile; forward translation and both explicit orders agree; full action/action/coin projections follow |
| stochastic witness | fair Boolean resolution has both values in support; actions and resolution remain separate outcome coordinates |
| reusable repair | two generic single-mover behavioral-joint lemmas moved from `Languages.MAID.Order` to `Protocol.Information` without changing their proof content |
| focused build | 1,723 jobs, warning-free |
| full integration | 3,417 jobs, warning-free; Phase 2, Phase 3, and exact coverage audits verified |
| source hazards | no placeholders, custom axioms, raw updates, `Fintype.ofFinite`, `open Classical`, cast/`HEq`/recursor tokens, or source-level `change`/`▸` transport |
| axiom profile | `propext`, `Classical.choice`, and `Quot.sound` only |

## Kill conditions and result

Reject the design if the later mover's information depends on the stored first
choice; target behavioral policies cannot project to source policies; either
law is produced by a second runner; order independence forgets an action or
chance coordinate; tree shape is obtained by merging prefixes; microsteps add
synthetic players, dummy actions, implicit reindexing, stored global
finiteness, or public transport.

No kill condition fired.  In particular,
`map_erase_runBehavioral_eq_source` quantifies over every target behavioral
profile and proves a literal equality in canonical source-history space, not
merely a payoff or default-valued terminal projection.  The forward and
order-independence theorems retain the separate action/action/chance
coordinates as corollaries.

## Result and consequences

The candidate public bridge is an opt-in `Languages.Bridges.FOSGToEFG` family,
but EXP-059 does not promote it.  EXP-060 must first compile a two-round
stochastic FOSG with a second-round policy that depends on nontrivial source
public/private resolution signals while still hiding the earlier choice in
each simultaneous round.  It must cover inactive slots and own-action memory,
and prove the `(order.length + 1) * k` canonical-history law, arbitrary target
profile projection, and mapped order independence for the representative
horizon.  Only then may the generic explicit-order API freeze.  Strategic or
equilibrium transfer remains a later leaf over those law theorems and D8's
coordinate/update laws.

Do not port pinned `FOSG.Serial`: its own documentation says it is not
semantics-preserving, and it is not on the mature pinned bridge dependency
path.  Mine `FOSG.Compile`, `Bridges/FOSG/SerialExec`, `AugmentedEFG`, and
`Expressiveness/EFG_FOSG` only after the generic bounded bridge compiles, and
reuse statements rather than their PMF, global-finiteness, or transport API.
