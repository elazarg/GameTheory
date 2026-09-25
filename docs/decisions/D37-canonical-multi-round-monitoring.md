# D37: multi-round monitoring compiles directly to Protocol/FOSG

- **Status:** adopted and promoted
- **Date:** 2026-08-09
- **Experiment ID:** EXP-070

## Decision / question

Whether finite multi-round games with previous-action information and
imperfect monitoring require their own evaluator and compiler, should be
written as raw FOSG data at every use site, or merit a thin native constructor
whose semantics are the accepted Protocol execution/information pair.

## Competing designs

1. Revive the predecessor's `Round.eval`, pure/mixed evaluators, sequential
   linearization, observation compiler, and adequacy stack.
2. Expose only raw `FOSG.Game` records and reconstruct the same monitoring
   mechanics at each consumer.
3. Store action carriers, a finite horizon, initial observations, and a
   monitoring PMF; compile this data directly to canonical
   `ExecutionProtocol`, `InformationModel`, FOSG, and `GameForm` values.

Design 3 is adopted. Hidden execution state records the realized joint-action
and signal history. A player's information state records only its own previous
choices and received public/private signals. Protocol remains the sole owner
of traces, histories, pure/behavioral/mixed policies, runners, and strategic
compilation.

Under [D62](D62-general-pmf-restoration.md), signal laws may have infinite
support. Neither public nor private signal carriers acquire a finiteness
assumption. The historical EXP-070 slice used finite-support laws; the same
constructor now inherits general discrete execution from Protocol.

## Representative hostile slice

Two players act twice with three actions each. The public signal reports only
whether the actions agree. After player zero chooses zero, opponent actions one
and two therefore produce distinct hidden states but equal local information.
Changing player zero's own action changes that information. A second-round
policy repeats the remembered own action; its joint choice is checked at the
canonical `InformationModel.jointAt`, and public strategic play is definitionally
the canonical Protocol run.

The generic constructor also proves `InfoSignals.PerfectRecall`. Thus the
mixed-to-behavioral direction is inherited from Protocol without a
multi-round-specific theorem. Discrete behavioral-to-mixed realization needs
an actual finite information-site cover at the evaluated horizon. Bounded
trace length alone does not supply that cover when signal branching is
infinite. Protocol's separate policy-measure theorems apply under their own
hypotheses, as specified by D57–D59; no multi-round evaluator is introduced.

## Measurements

| Measure | EXP-070 result |
|---|---|
| semantic owner | thin opt-in `GameTheory.Languages.MultiRound` constructor over Protocol/FOSG |
| stored capabilities | none beyond finite horizon and finite-support signal laws; no `Fintype`, decidable equality, utility, equilibrium, topology, or infinite path |
| hidden/local split | full joint actions remain in execution state; policies receive own choices plus public/private signals only |
| canonical reuse | one Protocol trace/history, information model, pure/behavioral/mixed runner, and strategic compiler |
| semantic certificate | generic `MonitoringGame.perfectRecall` |
| hostile distinction | two distinct opponent-action histories merge locally; a changed own action remains distinguishable and changes the second-round policy choice |
| public-surface cleanup | the Phase 3 two-round probe moved from `Languages/Rounds.lean` to `Experimental/PostArchitecture/RoundsWitness.lean` |

## Kill condition

Reject the constructor if it needs a second runner, policy, history, or
probability representation; lets policies inspect hidden opponent actions;
forgets a player's own earlier choice; cannot merge histories under coarse
monitoring; stores avoidable finiteness, utility, equilibrium, or topology; or
requires raw updates or source-level transports.

No kill condition fired. The predecessor's 163 operational, serialization,
and adequacy declarations were implementation cost of the retired parallel
semantics, not independent mathematical payload. The 37 deferred declarations
remain explicit theorem-family work rather than being hidden by the retirement.

## Consequences for the public API

`GameTheory.Languages.MultiRound.MonitoringGame` is the opt-in native owner.
New monitoring examples compile through its `execution`, `informationModel`,
`toFOSG`, and `toGameForm`; they do not introduce alternate evaluators.

This decision is scoped to the finite multi-round language constructor. It does
not claim to replace `Repeated.PublicMonitoring`: that branch's native
`SignalHistory` recursion is the input to repeated continuation, discounted
payoff, and PPE theory and is not presented as a Protocol runner. A consumer
needing own-action recall and an execution/information object uses this
constructor; a repeated public-strategy theorem uses the repeated branch.

Absent-minded-driver value theory, finite-information Kuhn correspondence, and
generic stagewise-Nash convenience are bounded BFS continuations. A richer
constructor for pre-action signals, heterogeneous timing, or unbounded play
requires a new hostile slice rather than extra fields on this finite monitoring
record.
