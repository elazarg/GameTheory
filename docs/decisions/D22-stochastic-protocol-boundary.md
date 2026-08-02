# D22: stochastic games are native data with a named Protocol bridge

- **Status:** adopted and promoted
- **Date:** 2026-08-02
- **Experiment IDs:** EXP-050

## Decision / question

Where finite-support stochastic-game data, finite-horizon behavioral play, and
uniform equilibrium belong relative to the accepted finite-law, static
equilibrium, Protocol, Repeated, and Analysis boundaries.

The source evidence is the active sibling repository `D:/workspace/GameTheory`
on branch `uniform-existence`, audited at `e7730a1`. Its four relevant files
were unchanged from the initially observed `d35c1d8` through that revision.
The sibling is not imported and is not a dependency.

## Competing designs

1. Store native state/action/transition/utility data and expose a named bridge
   to the canonical Protocol execution, information, and behavioral runner.
2. Define a stochastic game as a transparent specialization carrying an
   `ExecutionProtocol` and information model.
3. Treat a stochastic game as a repeated-game extension.
4. Retain the source branch's `PMF`, independent finite-history runner,
   `KernelGame` horizon wrapper, stored discount, and raw profile updates.

Design 1 is adopted. A stochastic transition kernel is meaningful without an
initial state or information model, so design 2 stores downstream choices too
early. Stochastic state evolution is not repetition of a fixed stage game, so
design 3 forgets native data. Design 4 duplicates accepted probability,
Protocol, and equilibrium semantics.

## Representative hostile slice

Two Boolean players act simultaneously in two public states. Agreement flips
the state deterministically; disagreement reaches both states with positive
probability; stage utility depends on the current state and the player's
action. A fixed initial state compiles to a nonterminating all-active
`ExecutionProtocol` with perfect public monitoring.

One Protocol behavioral profile feeds every finite horizon. The horizon form
is exactly `InformationModel.toBehavioralGameForm`; expected average payoff is
ordinary `expectedUtility`; epsilon-horizon Nash is an abbreviation of the
canonical `IsεNash`; and uniformity adds only the quantifier over all horizons
past one threshold. Horizon zero has the explicit empty-average value zero.

## Measurements

| Measure | EXP-050 result |
|---|---|
| source revision | active sibling branch `uniform-existence` at `e7730a1`; four relevant files unchanged from `d35c1d8` |
| source license | MIT, Copyright (c) 2025 Elazar Gershuni |
| source trust hazards | the general uniform-existence constructor contains `sorry`; excluded identically with every theorem depending on it |
| native object | state, player-indexed action, `FinDist` transition, and stage utility only |
| stored capabilities | zero; initial state, action nonemptiness, player finiteness, and decidable equality are operation-local |
| promoted split | `Basic`, `PerfectMonitoring`, `FiniteHorizon`, `Uniform`, plus opt-in root and hostile Example |
| focused public build | 1,733 jobs |
| full project build | 3,384 jobs |
| authored import closure | 17 modules; no Analysis, Repeated, Frontier, or Challenges import |
| reachability boundary | 5 positive layer/input probes; 2 negative Repeated/fixed-point probes |
| source hazards | zero direct updates, transports, representation leaks, `Fintype.ofFinite`, placeholders, native decisions, or custom axioms |
| axiom profile | `propext`, `Classical.choice`, and `Quot.sound` only |

The first experimental presentation exposed Protocol's proof-carrying
`StepEvent` as the policy information state. The audit rejected that public
shape. The promoted bridge maps each event to a proof-free `StageRecord` and
proves source, target, and every pure joint-action coordinate are retained.
Only proposition-valued legality and support evidence remains internal to
Protocol.

## Kill condition

Reject the design if the hostile slice needs `PMF` or a law on infinite paths,
duplicates the Protocol history runner or behavioral-policy type, defines a
second equilibrium predicate, stores discount or finiteness irrelevant to the
native data, requires raw `Function.update` or user-visible transport, imports
the source conjecture, or leaks Analysis/Repeated dependencies into the new
root.

No kill condition fired. The proof-carrying information-state pressure
narrowed the bridge before promotion rather than changing the native object.

## Result

`GameTheory.Stochastic.Basic` owns the native game and proof-free public stage
records. `Stochastic.PerfectMonitoring` supplies the selected-initial-state
Protocol execution and information model. `Stochastic.FiniteHorizon` owns the
average-payoff evaluation of the canonical history law. `Stochastic.Uniform`
owns transparent horizon and uniform solution concepts through
`Core.Approximate`.

The umbrella `GameTheory.Stochastic` is public and opt-in. At this decision it
remained provisional until the Shapley gate; EXP-051/D23 subsequently closed
that gate through a one-way normalized Analysis bridge. The main `GameTheory` root does not
import it. Positive probes ensure the umbrella
reaches all four layers and canonical approximate Nash; negative probes reject
Repeated theory and the fixed-point dependency.

## Consequences and scope

This decision ports the source branch's basic semantic waist, not its research
claim. There is no theorem asserting general uniform-equilibrium-payoff
existence and no placeholder standing in for it. Future known-case existence
theorems belong above this root, with Analysis used only when their proof
actually needs it.

The adopted data/bridge API is stable. D23 subsequently proved the mature
finite discounted two-player zero-sum slice: its normalized operator is a
contraction with a unique value and stationary statewise saddle selectors, so
the finite stochastic domain is now broadly supported. Uniform equilibrium now has a trustworthy
statement layer on which known special cases or research-facing certificates
can land without weakening mature foundations.

Promotion passed the Phase 0, 1, 2, and 3 expected-value audits, the exact
coverage audit, the full build, and the flagship axiom audit. Phase 2 reports
zero stochastic transport or forbidden imports and no unbucketed files.
