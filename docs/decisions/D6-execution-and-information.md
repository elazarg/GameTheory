# D6: execution protocols and information models

- **Status:** decided for v1 — general-state execution as the primary
  interface, finite-first trees retained as a derived presentation
- **Date:** 2026-07-27
- **Experiment IDs:** EXP-010, EXP-011, EXP-012; post-decision evidence
  EXP-016, EXP-017, EXP-018, EXP-021, EXP-025, EXP-029, EXP-030, EXP-033

**Decision:** Execution and information are separate interfaces. The primary
execution interface is the general-state `ExecutionProtocol`. The finite-first
`Tree` is retained as a derived presentation for single-mover games, where it is
measurably cheaper, with its faithfulness limit recorded rather than papered
over.

## What was competed

Two execution candidates, each encoding the same games:

1. `GameTheory/Protocol/Execution.lean` — a state space with a
   proposition-valued `active`, availability, terminality, and a `step` that
   consumes a legal joint action.
2. `GameTheory/Protocol/Tree.lean` — an inductive tree with a binary chance node
   and single-mover decision nodes.

The information model (`GameTheory/Protocol/Information.lean`) layers over the
execution protocol and was tested separately.

## Hostile tests

| RFC D6 test | Result | Where |
|---|---|---|
| terminal play without a total chooser | passed | EXP-010 |
| chance with a normalized law, no dummy data | passed | EXP-010 |
| information locality by typing | passed | EXP-011 |
| cyclic/merging arenas refute tree extraction | passed | `Tests/Arena.lean` |
| finite strategy extraction over own decision sites | passed by both | `Tree.lean`, `Extraction.lean` |
| simultaneous actions | **general-state only** | `Tests/Simultaneous.lean` |

Neither core-invalidating failure fired. RFC 9.1.6 is not triggered:
`terminal_no_legal` is a *theorem*, because legality was defined to include
non-terminality, so a total chooser cannot be written at all. RFC 9.1.7 is not
triggered: `Policy` takes an `InfoState` and no execution state, and two states
in one information set give equal information states, so every local policy
agrees there by `congrArg` with no locality hypothesis.

## The measurement

| Axis | finite-first | general-state |
|---|---|---|
| certificates required | none | `StopsWithin` and `WellFoundedPlay`, which do not derive from each other |
| certificate size | — | 26 lines for recursor plus certificate, 22 for a concrete instance |
| evaluator | structural, total | fuelled, total given `StopsWithin` |
| decision sites | intrinsic to the tree | carved out by `Reachable`, faithfulness proved |
| simultaneous actions | **cannot express** | native |

Two results decided it.

*The certificates are not a second semantics.*
`backwardValue_eq_expect_runFor` proves that wherever `StopsWithin` holds, the
backward-induction value equals the expected payoff of the fuelled run law.
Neither side is defined from the other — one recurses on `Successor`, the other
on fuel — so the general candidate meets the RFC's "small certificate rather
than a second parallel semantics" criterion.

*Sequentializing a simultaneous move is not faithful.*
`Tree.node` carries one `mover`. Encoding a two-player simultaneous match as a
tree requires ordering the moves, and
`sequentialization_enlarges_strategy_space` proves the strategy space grows
strictly: eight contingent plans against four simultaneous profiles.
`respondingPlan` exhibits a plan that conditions on the opponent's call, which
no simultaneous strategy can do. Making the tree faithful therefore requires an
information layer to quotient those plans — precisely the machinery whose
absence made it cheaper on the certificate axis.

## Result

RFC D6's disproof conditions apply asymmetrically. General-state-first is
rejected only if it fails a terminal, chance, locality, or finite-extraction
hostile test; it failed none. Finite-first is rejected if the simultaneous-action
slice needs a duplicate execution or evaluation theory rather than a small
extension; it needs an information layer, which is not small.

So the general-state protocol is the primary interface. The RFC explicitly
permits more than one execution interface — "a universal record is not a success
criterion" — and the tree is genuinely better where it applies, so it is
retained rather than deleted:

- use `Tree` for single-mover games, where it costs no certificate, evaluates
  structurally, and has an intrinsically finite plan type;
- use `ExecutionProtocol` everywhere else, and for anything simultaneous.

The two agree where both apply: `candidates_agree_take` and
`candidates_agree_leave` prove they induce the same outcome law on the shared
example.

## Consequences for public API

Execution and information stay separate structures; the information model
consumes `StepEvent` and never redefines a transition. `Trace` is `Type`-valued,
so `IsTreeShaped` is a real statement and a merging arena refutes it.
`BoundedHorizon` is a predicate over reachable traces, never a stored field.

The strategy types are deliberately attached to the operation that needs them.
`SiteStrategy` is the finite extracted strategy over reachable decision sites;
`Chooser` drives the state-indexed runner; `HistoryChooser` drives the
history-indexed runner. An `InformationModel.Policy` receives only its
`InfoState`, while `BehavioralPolicy` randomizes at each information state and
`MixedPolicy` draws a deterministic policy once. The corresponding history-law
runners are all present, and point-mass and pushforward theorems connect them
to the simpler runners. No one of these types is the universal definition of
"strategy."

Two costs are recorded rather than hidden. The information model's `menu`
ranges over `Option (Action i)`, committing the design to "the information state
determines whether the player moves". And `IsLegalJoint` is written as an
inlined `∀ i, match …`, so its pointwise form is not definitionally equal and
needed a one-off case split; a later refactor to `∀ i, LegalOption …` would
remove that friction.

## Post-decision close-out

D7 has since been rejected for v1 and D0 is final; neither status remains open.
The post-decision history and randomized runners close the execution mismatch
that was recorded at the gate. Both behavioral/mixed directions now hold at the
history-law level, under their distinct no-revisit and recall-like conditions,
and the one-shot principle for state-indexed choosers is an equivalence under
`WellFoundedPlay`.

The composed compiler is now present too. `InformationModel.toGameForm`
compiles pure information-local policies with full histories as outcomes;
`toBehavioralGameForm` compiles local randomization; and the ordinary static
mixed extension is exactly `runMixed`. Their named evaluation and
behavioral/mixed commutation theorems use the existing runners. The
finite-horizon information-local one-shot theorem proves that local one-shot
optimality at every history defeats every whole replacement policy, and its
compiler corollary is ordinary static `IsNash`. The actual history continuation
is packaged as `historyContext`, and the quantified premise is equivalent to
`IsSequentiallyRationalAt` in that context at every history and remaining
horizon.

The remaining SPE-style theorem does not reopen D6. There is no public
subgame-perfect-equilibrium predicate or full well-founded
`oneShotDeviation_iff_spe` analogue. No converse from initial static Nash is
claimed: unlike the one-shot condition, that predicate does not inspect every
off-path history. This is downstream semantics over the accepted execution and
information interfaces, not a missing execution representation.

EXP-029 adds the complementary incomplete-information stress. A common-prior
Bayesian game compiles to a two-step execution protocol whose chance step draws
types and whose simultaneous step records actions. Its `InformationModel`
exposes only player `i`'s own type in `View B i`; policy/plan equivalence and
the exact two-step outcome-law theorem show that this presentation agrees with
the direct static form. The compiler imports Bayesian data but no utility,
preference, or equilibrium theory, preserving the execution/information
boundary while making it useful to the static incentive layer.

EXP-030 adds indefinite public-action repetition without turning Protocol into
an infinite-path probability carrier. The native repeated strategy observes a
chronological list of prior stage profiles. For a finite horizon, that same list
is the execution state and the public information state; one named compiler
theorem proves that restricted repeated strategies generate exactly the native
prefix. The bridge defines neither a second transition nor a second information
interface. Its positive reachability probes assert that both accepted inputs
remain in use, while Basic and Discounted reject Protocol and the Protocol
bridge rejects discounted payoff.

EXP-033 applies the same discipline to finite extensive forms. An EFG is a
transparent specialization containing the canonical execution and information
objects plus tree-shapedness and a single-mover law, not a second inductive
syntax or evaluator. Tree-shapedness identifies histories with reachable
states, so finite-state EFG theorems can enumerate histories explicitly without
storing `Fintype` or using `Fintype.ofFinite`.

The hostile imperfect-information carrier also sharpened assessments. Beliefs
are required only at reached decision sites, witnessed by a nonterminal history
and a genuine menu action, not at reached inactive, chance, or terminal
observations. Sequential rationality compares whole continuation behavioral
policies; reducing that comparison to one local randomized action is a
one-shot-deviation result, not part of the semantic definition.
