# D31: Keep intrinsic closed-loop semantics native before temporal compilation

- **Status:** adopted; native ownership retained, causality condition corrected
  after the original schedule-prefix validation was refuted
- **Date:** 2026-08-03
- **Amended:** 2026-11-02
- **Experiment IDs:** EXP-062; EXP-171 supersedes its causality justification

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

## Representative hostile slice (EXP-062, historical)

The account below preserves the original validation. EXP-171 refutes its
causality conclusion; see the correction below.

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

## Measurements (EXP-062, historical)

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

## Original kill conditions and result

Reject native ownership if the hostile statements reduce to existing Protocol
theorems; require temporal execution merely to state; need stored global
finiteness, PMF, utility, duplicate equilibrium semantics, public transports,
or forbidden trust features; or if either causality premise is ornamental.

Counterexamples refute both premise-erased variants. EXP-062 therefore
supports native ownership and the configuration-dependent causality
representation.

The preceding result is the original conclusion, not the current causality
claim. Its premise-independence argument tested a condition weaker than the
source definition. The native-ownership evidence remains useful.

## Corrected causality and replacement validation (EXP-171)

Definition 6, equation (18), of
[Kuhn's Equivalence Theorem for Games in Intrinsic Form](https://arxiv.org/pdf/2006.14838)
requires each prefix cell intersected with an information event to be
measurable using nature and predecessor coordinates. Taking the information
event to be the entire configuration space already requires that the prefix
cell itself be determined by those coordinates. The setoid formulation is
therefore:

```text
AgreeBefore schedule slot left right →
  SamePrefixThrough schedule slot left right ∧
  (M.info (schedule.orderAt left slot)).r left right
```

The previous formulation assumed `SamePrefixThrough` and concluded only
information equivalence. It could use future decisions to select a schedule
cell and then hide that dependence inside the assumption. The two-agent
counterexample satisfies that weaker condition but has an admissible profile
with no fixed point. The old three-agent branching fixture has the same
defect: its later information determines agent one's own decision. Its
premise-independence theorem now supplies a negative causality witness, and
its weaker information-locality proof is retained under an explicit name.
The claim that predecessor agreement need not imply a shared prefix is
withdrawn for causal schedules.

The replacement positive witness branches only on agent zero's already-made
decision; later agents observe that coordinate. Negative controls reject the
anticipatory two-agent schedule and every schedule for clapping hands. The
`isSolvable_of_isCausalWith` theorem in the `Solution` leaf derives unique
solvability from corrected causality with decision nonemptiness supplied at
the theorem. This adds no capabilities
to `Model` and requires no Protocol compiler. An empty-decision control proves
the nonemptiness premise necessary. EXP-171 validates the corrected surface:
the focused intrinsic build passes 3,070 jobs, and the full audit passes the
default build (3,872 jobs), complete validation (4,762 jobs), public lint,
source boundaries and transitive standard-axiom checks.

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

`IsCausalWith` concludes both prefix agreement and information equivalence
from predecessor agreement. Its solvability theorem requests nonempty decision
carriers: without them, the configuration space can be empty and causality
can hold vacuously. No compatibility predicate preserves the rejected meaning
in the stable API.

Do not yet promote a temporal compiler, execution semantics, perfect recall,
mixed or behavioral strategies, PMF outcome laws, player ownership, utility,
equilibrium, or Kuhn theorem.  Each remains a separately measured gate.  The
list-based pinned ordering and coordinate-setoid intermediates are not public
compatibility surfaces; the explicit finite schedule owns those invariants
directly.
