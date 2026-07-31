# D20: finite Electronic Mail is a static Examples bridge

- **Status:** adopted and promoted
- **Date:** 2026-07-30
- **Experiment IDs:** EXP-048

## Decision / question

Whether the pinned finite Electronic Mail theory belongs to a static bridge
between Bayesian games and epistemic partitions, or requires Protocol because
its informal story contains multiple message rounds.

## Competing designs

1. Model the three endpoint worlds directly, use one finite law for both the
   epistemic prior and the Bayesian type prior, and place the integration under
   Examples.
2. Model every email attempt and confirmation as an `ExecutionProtocol`, then
   derive the endpoint Bayesian and knowledge claims by compilation.
3. Introduce communication-local priors, expected utility, and Bayes-Nash
   wrappers matching the predecessor surface.

Design 1 is adopted for the pinned finite theorem family. Design 2 is reserved
for a theorem that observes delivery transitions, stopping, failures, or
strategic choices during communication. Design 3 is rejected by D4, D9, and
the single-equilibrium architecture.

## Representative hostile slice

EXP-048 recovers the three endpoint worlds, private views, action plan,
epistemic partitions, and coordinated-attack payoff. A single uniform
`FinDist EmailWorld` is pushed forward to the type-profile prior of the
canonical `BayesianGame` and used directly by the canonical epistemic
posterior.

The slice proves both sides of the Electronic Mail lesson:

- the attack state is mutual `p`-belief at the confirmed endpoint for every
  threshold at most one, but not common `p`-belief above one half; and
- attack-on-message gives player `true` value `-1/3`, while the unilateral
  plan replacement to never attack gives zero, so ordinary `IsNash` fails.

## Measurements

| Measure | EXP-048 result |
|---|---|
| authored experiment | 212 nonblank lines; 24 declarations |
| authored imports | Bayesian equilibrium, approximate epistemics, `linarith`, `norm_num` |
| focused build | 1,725 jobs |
| probability representation | one canonical `FinDist EmailWorld` |
| equilibrium surface | ordinary `IsNash` and `euPreference` |
| deviation representation | canonical `Profile.update` |
| Protocol / Analysis imports | none |
| source hazards | zero placeholders, native decisions, direct updates, transports, `HEq`, `Fintype.ofFinite`, `open Classical`, or custom axioms |
| axiom profile | `propext`, `Classical.choice`, `Quot.sound` only |

## Kill condition

Reject static ownership if an intermediate message history or transition law
is needed to state a pinned theorem, if the endpoint model cannot express the
information result, if two priors or another equilibrium predicate are
required, or if either independent input root must import the other.

No kill condition fired.

## Result

Adopt an Examples bridge. The Bayesian and Epistemic roots remain independent;
only the concrete example imports both. The informal number of email rounds
does not by itself force Protocol ownership: the formal ownership criterion is
what theorem statements observe.

## Consequences for public API

The example exposes endpoint worlds, observations, actions, the shared world
prior and its pushed-forward type prior, the Bayesian game and plans, the
epistemic partition and belief theorems, exact expected-utility values, and the
ordinary non-Nash result. It introduces no new language root or communication
equilibrium API.

Promotion verifies that Bayesian/Core does not reach Epistemic and
Epistemic does not reach Bayesian game semantics, while the Examples module
positively reaches both input families.

## Promotion evidence

`GameTheory/Examples/ElectronicMail.lean` contains the 24-declaration stable
example. The focused target builds in 1,725 jobs and the full project in 3,365
jobs. Phase 2 reaches all four intended bridge symbols, rejects all four
Protocol/Analysis boundary symbols, and verifies both directions of
Bayesian/Epistemic input-root independence. The mutual-belief,
not-common-belief, and non-Nash theorems depend only on `propext`,
`Classical.choice`, and `Quot.sound`.
