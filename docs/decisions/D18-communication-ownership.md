# D18: observable one-stage cheap talk is a static enrichment

- **Status:** adopted and promoted
- **Date:** 2026-07-30
- **Experiment IDs:** EXP-046

## Decision / question

Whether observable pre-play cheap talk belongs to the static `GameForm` layer,
must be represented as a two-stage `ExecutionProtocol`, or should be hidden
behind a generic inert-extension abstraction.

## Competing designs

1. Enrich each static strategy with a public message and a contingent base
   strategy over the complete message profile.
2. Model message choice and action choice as separate Protocol states, then
   compile the protocol back to a static form.
3. Expose only an inert extension with projection and embedding maps.

Design 1 is adopted for one-stage observable cheap talk and the babbling
theorem. Design 2 is reserved for consumers that observe intermediate message
histories, communicate over multiple rounds, or randomize during the
communication stage. Design 3 remains a possible theorem pattern, not the
public communication object: it forgets the message and contingent-plan shape
that downstream communication theorems need.

## Representative hostile slice

EXP-046 gives every player a message and a complete plan from public message
profiles to base strategies. A unilateral deviation may replace both at once.
Against a babbling profile, its realized message profile is the default profile
updated by the deviator's new message, and its realized action profile is the
base profile updated by the action that the new plan selects there.

The generic theorem embeds both pure equilibria of Battle of the Sexes. The
consumer is hostile enough to reject a construction that only lets a deviator
change its message or assumes its plan remains constant.

## Measurements

| Measure | EXP-046 result |
|---|---|
| authored experiment | 141 nonblank lines; 20 declarations |
| authored import | `GameTheory.Examples.Classic` only |
| focused build | 1,738 jobs |
| deviation representation | one canonical `Profile.update` after projection |
| equilibrium surface | ordinary preference-parametric `IsNash` |
| Protocol / Analysis imports | none |
| finite capabilities | none |
| source hazards | zero placeholders, native decisions, direct updates, transports, `HEq`, `Fintype.ofFinite`, `open Classical`, or custom axioms |
| axiom profile | `propext`, `Classical.choice`, `Quot.sound` only |
| hostile consumers | opera and football babbling equilibria |

## Kill condition

Reject static ownership if an arbitrary message-plus-plan deviation cannot be
projected to one base deviation, if the proof needs intermediate histories, if
the extension introduces another evaluator or Nash predicate, or if it requires
direct `Function.update`, dependent transport, stored finiteness, or a Core to
Protocol dependency.

No kill condition fired.

## Result

Adopt a static `GameForm.CheapTalkExtension` construction. It owns the message
carrier, default message profile, enriched strategy and signature, realized
message/action profiles, base projection, babbling embedding, exact play laws,
and one preference-parametric theorem:

```text
base IsNash profile →
  extension IsNash (embedProfile profile)
```

There is no `IsNashFor`, `IsNashMixed`, communication-local equilibrium
predicate, or second outcome evaluator. The result applies to arbitrary weak
preferences because the extension preserves the exact base outcome law around
the projected unilateral deviation.

## Consequences for public API

The construction belongs under Core and must remain Protocol- and
Analysis-blind. Concrete cheap-talk games belong under Examples or their native
language consumer. Protocol owns multi-round messages, private or imperfectly
observed communication histories, signaling during play, and any theorem whose
statement observes an intermediate communication state.

Promotion adds positive Core reachability for the extension and babbling
theorem plus negative probes for Protocol execution and analytic existence.
The four deferred NFG cheap-talk rows are closed by the stable generic theorem
and both Battle-of-the-Sexes witnesses.

## Promotion evidence

`GameTheory/Core/CheapTalk.lean` contains the generic construction and
`GameTheory/Examples/CheapTalk.lean` contains the hostile Battle-of-the-Sexes
consumers. The focused targets build in 1,739 jobs and the full project in
3,361 jobs. The Phase 2 audit preserves the transport and import budgets,
reaches both intended Core symbols, and rejects all four Protocol/Analysis
boundary symbols. The generic theorem and both examples depend only on
`propext`, `Classical.choice`, and `Quot.sound`.

The first post-promotion harvest also recovered the converse:
`actionProfile_isNash_of_isNash` sends every pure cheap-talk equilibrium to
its realized base equilibrium, and `exists_isNash_play_iff` proves equality of
the complete sets of pure-Nash outcome laws. These results remain
preference-parametric and retain the same standard axiom profile.
