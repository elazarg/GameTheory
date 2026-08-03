# D31: Keep intrinsic closed-loop semantics native before temporal compilation

- **Status:** adopted; minimal native root and configuration-dependent
  causality surface approved for promotion
- **Date:** 2026-08-03
- **Experiment ID:** EXP-062

## Decision / question

Whether Witsenhausen-style intrinsic games retain theorem-relevant product and
closed-loop structure that deserves a native language root, or whether they
should be encoded directly as Protocol after choosing a temporal execution.

## Competing designs

1. Define a capability-light native configuration, information setoids, pure
   strategies, closed-loop fixed points, solvability, and
   configuration-dependent causality; choose a temporal compiler later.
2. Retire the native language and encode each model directly as Protocol under
   an explicit execution order.
3. Keep only a generic fixed-point theorem with no intrinsic-language surface.

Design 1 is adopted.  It states a unique closed-loop solution theorem and a
future-information counterexample before an execution state, history, or
temporal order exists.  Designs 2 and 3 cannot express both facts at the same
semantic layer without first discarding or re-encoding the product structure.

## Representative hostile slice

The positive witness has two Boolean agents with universal information.  Every
admissible pure strategy is constant on configuration space, so every profile
and nature state has a unique simultaneous closed-loop solution.

The negative witness schedules one Boolean agent before another while the
first agent's information observes the later decision.  Causality rejects the
model without compiling it to Protocol.

The configuration-dependent witness has three agents.  Its later order
branches on a condition involving both a predecessor coordinate and another
configuration coordinate.  Later information classes require both exact
predecessor agreement and agreement on that configuration-cell branch.  Two
concrete configuration pairs separate the premises in both directions:
predecessor agreement does not imply a shared schedule prefix, and a shared
schedule prefix does not imply predecessor agreement.  Thus neither premise
can be erased from the positive causality proof.

## Measurements

| Measure | EXP-062 result |
|---|---|
| hostile artifact | 357 nonblank lines; 39 declarations |
| import surface | only `Mathlib.Logic.Equiv.Bool`; no Protocol, probability, utility, Analysis, Frontier, or Challenges import |
| stored capabilities | none: no `Fintype`, `Finite`, `DecidableEq`, decision nonemptiness, topology, probability, or preference field |
| ordering invariant | `Fin slots ≃ Agent` packages exhaustiveness and no duplication locally |
| closed-loop test | unique fixed point for every pure profile and nature state under universal information |
| negative test | future-decision information is rejected before temporal compilation |
| configuration-cell test | nonconstant three-agent schedule; `SamePrefixThrough` is equivalent to direct `PrefixCell` membership through the current slot |
| independence test | concrete pairs refute each premise-erased causality variant |
| focused check | `lake env lean GameTheory/Experimental/PostArchitecture/IntrinsicOwnership.lean`, warning-free |
| source hazards | no placeholders, custom axioms, native reduction, raw profile updates, stored/global finiteness, `open Classical`, or public transport plumbing |
| axiom profile | `Quot.sound` for solvability; otherwise only `propext`, `Classical.choice`, and `Quot.sound` as applicable |

## Kill conditions and result

Reject native ownership if the hostile statements reduce to existing Protocol
theorems; require temporal execution merely to state; need stored global
finiteness, PMF, utility, duplicate equilibrium semantics, public transports,
or forbidden trust features; or if either causality premise is ornamental.

No kill condition fired.  Sol audit additionally compiled negations of both
premise-erased variants.  EXP-062 therefore supports native ownership and the
configuration-dependent causality representation.

## Consequences for the public API

Promote one opt-in `GameTheory.Languages.Intrinsic` root containing:

- `Config`, `Model`, `Model.Configuration`, `Model.PureStrategy`, and
  `Model.PureProfile`;
- `Model.IsFixedPoint` and `Model.IsSolvable`;
- an explicit-slot `Model.Schedule`, `SamePrefixThrough`, `PrefixCell`,
  `AgreeBefore`, and `Model.IsCausalWith`.

Use independent universes in the stable root.  Store no finite or nonempty
capabilities.  `IsSolvable` is allowed to be vacuous when no pure profile
exists; any operation that extracts or plays a solution carries the
nonemptiness or existence capability it needs.

Do not yet promote a temporal compiler, execution semantics, perfect recall,
mixed or behavioral strategies, PMF outcome laws, player ownership, utility,
equilibrium, or Kuhn theorem.  Each remains a separately measured gate.  The
list-based pinned ordering and coordinate-setoid intermediates are not public
compatibility surfaces; the explicit finite schedule owns those invariants
directly.
