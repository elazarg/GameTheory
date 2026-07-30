# D14: general MAID execution by unresolved frontiers

- **Status:** adopted compilation principle; general public syntax still
  delivery-gated
- **Date:** 2026-07-30
- **Experiment IDs:** EXP-014, EXP-037

## Decision / question

Whether the concrete three-node `GameTheory.Languages.MAID` may generalize to
finite acyclic diagrams, and how incomparable decision nodes compile without
inventing a causal order absent from the diagram.

## Competing designs

1. Select a topological order and execute every node sequentially. Hide an
   earlier incomparable decision from a later policy.
2. Execute the current unresolved minimal frontier together. Chance and
   administrative nodes contribute laws; incomparable decisions in the same
   frontier become one simultaneous Protocol joint-action step.
3. Keep only the existing concrete linear MAID in the stable tree and reject
   general MAID recovery for this release.

Design 2 is adopted. Design 1 remains only a comparison baseline because it
matches the pinned implementation shape; it must prove order independence
before it may describe an unordered source. Design 3 remains the fallback if a
general typed-DAG implementation later fires a disproof condition.

## Representative hostile slice

EXP-037 uses a Boolean chance node, two Boolean decision nodes owned by
different agents and incomparable with each other, and one utility node that
depends on both decisions. Both decision policies observe the chance value and
neither observes the other decision. The two decisions must be active in the
same Protocol state and consumed by one joint transition.

The slice must prove the direct outcome law, policy locality, dependence on
both decisions, value of observation, and absence of a state containing only
one of the two decisions.

## Measurements

| Measure | EXP-037 result |
|---|---|
| authored size | 406 nonblank lines; 58 declarations |
| stable API change | 0 declarations and 0 imports |
| authored import | `GameTheory.Protocol.Information` only |
| project import closure | 6 prerequisites: FinDist, Execution, Extraction, History, Randomized, Information |
| source trust/audit tokens | 0 placeholders, native decisions, direct updates, transports, `HEq`, or tactic `change` |
| focused build | 1,718 jobs |
| full build | 3,326 jobs |
| repository audits | Phase 0–3 expected measurements and reachability probes pass |
| axiom profile | `propext`, `Classical.choice`, `Quot.sound` only |
| semantic runner | existing `InformationModel.run`; exact equality to direct frontier evaluation |
| false serialization | no partial-decision state; both agents active and committed in one step |
| hostile sensitivity | each action changes the law; observing the chance parent changes expected payoff from 1 to 2 |

## Kill condition

Reject frontier batching if it needs a fake player, padding action, escape field
on Protocol or InformationModel, dependent transport visible to users, a
language-specific runner, or an intermediate state ordering the incomparable
decisions. Reject serialization unless order independence is proved on the
hostile slice and the later policy cannot observe the earlier incomparable
action. Keep the stable concrete MAID if neither design passes within the
existing source and trust audits.

## Result

Adopt unresolved-frontier batching as the semantic compilation invariant for a
general MAID. EXP-037 shows that the accepted Protocol joint action is exactly
the representation needed for an incomparable decision antichain: the source
players and actions are reused directly, policy views contain only resolved
parents, and the compiled law agrees with direct evaluation.

The experiment does not itself freeze a general node/DAG API. The next slice
must package an arbitrary finite acyclic dependency relation, prove progress of
frontier evaluation, and specialize back to the hostile antichain before T3 is
credited. If that work needs a false order or any kill condition above, the
stable concrete MAID remains the public surface.

The gate also exposed an audit-ownership gap: the new post-architecture
experiment was initially unbucketed by the Phase 2 source audit. It now has its
own zero-transport bucket, leaving the historical Phase 1–4 measurements
unchanged.
