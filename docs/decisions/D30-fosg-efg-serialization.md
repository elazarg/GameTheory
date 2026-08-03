# D30: Serialize simultaneous FOSGs through hidden explicit EFG phases

- **Status:** adopted and promoted through the stable generic explicit-order
  bridge
- **Date:** 2026-08-02
- **Experiment IDs:** EXP-059, EXP-060, EXP-061

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

## Two-round validation

EXP-060 tests composition rather than another one-round outcome encoding.  Its
source is non-tree-shaped: distinct first-round joints merge to the same state,
yet canonical source histories induce different later information.  The first
resolution emits a public bit and player-specific private reports; a hidden bit
controls whether one second-round player is inactive.  The target carries the
exact source history, runs two fixed-width selection slots plus one resolver,
and replays source public/private/own-action signals only at that resolver.

The full target `infoOf` is exactly the current phase paired with the source
`infoOf` of the carried history.  Direct reached witnesses show that the later
mover sees neither an inactive-versus-active hidden slot nor the earlier action
inside the round.  A concrete source policy nevertheless changes its
second-round action with each of the public bit, opponent-private report, and
remembered own action after resolution.

The law result is literal and strategy-space exact.  Every target behavioral
profile projects to a source profile whose two-round canonical history law is
the erasure of the six-microstep target law.  Translation projects back to the
original source profile, both fixed orders agree, and an arbitrary target
profile transports through its source projection to either target order.  No
default outcome or reconstructed state history occurs in this proof.

## Result and consequences

The candidate public bridge is an opt-in `Languages.Bridges.FOSGToEFG` family.
EXP-060 now satisfies the required two-round signal, inactivity, policy, scaled
history-law, and order tests, so implementation of a generic explicit-order
adapter is unblocked.  The concrete Boolean experiment does not itself freeze
or promote that API.  The generic implementation must compile against the
same canonical definitions and reproduce these law-level obligations before
stable bridge coverage is credited.  Strategic or equilibrium transfer remains
a later leaf over those laws and D8's coordinate/update results.

Do not port pinned `FOSG.Serial`: its own documentation says it is not
semantics-preserving, and it is not on the mature pinned bridge dependency
path.  Mine `FOSG.Compile`, `Bridges/FOSG/SerialExec`, `AugmentedEFG`, and
`Expressiveness/EFG_FOSG` now that the generic bounded bridge compiles, and
reuse statements rather than their PMF, global-finiteness, or transport API.

## Generic promotion

EXP-061 promotes `Languages.Bridges.FOSGToEFG`.  `ExplicitOrder` stores an
equivalence `Fin slots ≃ ι`, so exhaustive duplicate-free scheduling is an
invariant without a global finite instance and the empty-player case remains
valid.  The target has one source-player slot per round plus one resolver,
stores the exact canonical source history and partial legal joint, and exposes
only the phase paired with canonical source information.

The generic exact-law theorem quantifies over every target behavioral profile
and every finite round count.  Erasing the fixed-width target history yields
the canonical source `InformationModel.runBehavioral` law under the profile
projected from scheduled target views.  Translation and arbitrary-order
transport are corollaries.  The migrated EXP-060 source directly rechecks both
orders, within-round hiding, hidden inactive slots, resolver-only replay of
public/private/own-action information, and a translated policy sensitive to
each replayed coordinate.

The bridge has only stable EFG/FOSG imports.  The recursive exact-law proof
machinery is private, so the public API exposes no second runner or default
assignment.  The focused 1,727-job build is warning-free and the printed axiom
profile is exactly `propext`, `Classical.choice`, and `Quot.sound`.  The full
3,422-job integration build and Phase 2, Phase 3, and exact coverage audits all
pass.  No D30 kill condition fired.  The pinned live bridge chain may now be
recovered or retired against this canonical adapter; equilibrium transfer
still requires a separate strategic gate.
