# D14: general MAID execution by unresolved frontiers

- **Status:** adopted; native evaluation and explicit-order EFG compilation
  validated, public recovery unblocked
- **Date:** 2026-07-30
- **Experiment IDs:** EXP-014, EXP-037, EXP-038, EXP-039, EXP-040, EXP-041

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

Design 2 is adopted for the order-free native evaluator. EXP-038 rejects using
one combined per-player frontier view as the general strategy interface.
Design 1 is therefore permitted only for the named EFG target: it must hide
incomparable assignments from decision information and prove both exact
agreement with the native evaluator and order independence. Design 3 remains
the fallback if a general typed-DAG implementation later fires a disproof
condition.

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

## Open strategy-locality challenge

EXP-037 had distinct owners for the two incomparable decisions. It therefore
validated the execution frontier but did not test the harder case in which one
source player owns multiple decision sites in the same frontier. Giving that
player one combined information state and one batched action may let either
site depend on parents observed only at the other site, enlarging the native
MAID strategy space.

EXP-038 supplies the counterexample. A combined-view policy can cross-read the
two sites' disjoint private parents, while no pair of native local rules can
represent it. The mismatch is axiom-free and definitional on the native side.

Consequently:

1. native general-MAID policy is indexed by decision site and its own observed
   parent configuration;
2. frontier batching defines the order-free native evaluation law, not a
   general `InformationModel` strategy space;
3. the EFG translation may serialize an explicit topological order, but each
   decision view exposes exactly its native observed parents;
4. T3 must prove the serialized run equals native evaluation and is independent
   of order before the order-free wrapper is public;
5. equilibrium transfer regroups deviations by the source owner; decision
   sites are never relabelled as players.

This is a narrowing of EXP-037, not a reversal: its execution result and
distinct-owner policy probe remain valid.

## Typed native evaluator

EXP-040 supports the narrowed design. The experimental syntax uses an arbitrary
node carrier and heterogeneous dependent value family, keeps site-local policy
in the type, and derives unresolved frontiers from the EXP-039 acyclicity
certificate. Evaluation samples a dependent product over the whole frontier
and replaces those coordinates simultaneously. The named state certificate
proves all node-law parents resolved; unresolved default coordinates are never
passed to a law.

The same API instantiates both a heterogeneous diamond and EXP-038's
same-owner/disjoint-observation graph. The latter's real runner commits both
decisions together and distinguishes changes at each site. The source contains
no direct update or transport token and stores no finite capability.

This validates the native side of T3 but does not freeze it publicly.
`run_complete_of_remaining_le` and `completesWithin_card` now lift strict
frontier growth to a uniform finite completion certificate. The remaining gate
is the explicit-order EFG compiler: it must prove exact equality with the
frontier law and independence from the chosen order.

## Explicit-order compiler milestone

EXP-041's generic experimental compiler constructs an
accepted `Languages.EFG.Game` from a typed diagram, semantics, and explicit
topological order. Source owners remain the EFG players; their action carrier
is a dependent sum over their own decision sites. An active information state
contains one such site and exactly its declared observed-parent configuration.
The resolved execution prefix is not a policy input.

The compiler proves menu adequacy, tree shape, and the single-mover law. The
same-owner hostile fixture compiles at two opposite topological orders, and
each order proves that changing the earlier incomparable decision leaves the
later site's view unchanged. Its source joint law followed by the actual EFG
transition now equals a named one-node serial step. Both hostile serial orders
produce the same complete assignment law, and each equals the native frontier
runner's assignment law.

The actual Protocol path is now connected too. For every one-owner typed
diagram, the mapped `InformationModel.behavioralJoint` equals the source joint
law, one compiled behavioral transition equals one serialized source step, and
forgetting histories from the behavioral runner equals the serialized stage
runner for every fuel and starting history. On the hostile fixture, the two
opposite-order compiled EFG assignment laws are equal and each is exactly the
native frontier law.

The order algebra is now general. Typed assignment kernels for distinct nodes
with no direct edge commute; this lifts through arbitrary prefixes and suffixes.
A head-bubbling proof shows that any two dependency-compatible, duplicate-free
permutations induce the same law, and every pair of topological orders meets
those conditions. The compiler bridge therefore proves complete serialized
assignment-law equality for arbitrary player and node carriers. No public
swap-reachability certificate is introduced.

The actual behavioral-product bridge is general too. The information-model
product collapses to the all-inactive point mass at chance nodes and to the
sole active owner's local law at decision nodes. Consequently one actual EFG
behavioral step equals one serial step for arbitrary finite source-player
types, forgetting histories equals the serial runner at every fuel, and the
actual compiled-EFG assignment law is order-independent.

The final native comparison uses kernel-checked finite probability algebra.
A dependent product is invariant under coordinate equivalence, and a
duplicate-free sequential list of fixed node laws equals the corresponding
dependent product resolved simultaneously. Nodes within one frontier cannot be
parents of one another, so their dynamic serialized laws remain fixed during
that pass. This proves one native frontier step equals one serialized frontier
pass.

For the recursive lift, the current frontier followed by the nodes remaining
after that frontier is a duplicate-free, dependency-compatible permutation of
the current unresolved topological order. The native completion bound then
supports an induction over frontier layers, including nonsingleton frontiers.
`nativeRun_eq_compiledBehavioralRun` concludes that the native
simultaneous-frontier evaluator and the actual compiled
`InformationModel.runBehavioral` have the same complete assignment law for
arbitrary finite typed diagrams, source-player carriers, and supplied
topological orders.

EXP-041 therefore closes D14's representation, locality, order-independence,
and exact-evaluation gates. Public recovery of the validated typed syntax,
native evaluator, and explicit-order compiler is unblocked. T3's remaining
equilibrium-transfer theorem is a delivery obligation, not a reason to weaken
or reopen the adopted execution design: deviations must be regrouped by source
owner, never by decision site.

The validated surface is now promoted under `GameTheory.Languages.MAID`:
`Basic` owns typed syntax and frontier evaluation, `ToEFG` owns the named
compiler, `Order` owns serialized order algebra, and `FrontierEquivalence`
owns the exact native/compiled theorem. `General` is the public aggregate
import. The hostile fixtures remain under `Experimental/PostArchitecture`;
promotion did not turn experiment-specific diagrams into public API. The
aggregate and both hostile suites build; the full project builds in 3,336 jobs,
Phase 2/3 source and reachability audits pass, and the promoted flagship
theorems retain the standard `propext`, `Classical.choice`, `Quot.sound` axiom
profile.
