# D17: evolutionary stability is static; dynamics are opt-in

- **Status:** adopted; promotion pending
- **Date:** 2026-07-30
- **Experiment IDs:** EXP-044

## Decision / question

Whether ESS/NSS should be another Core response concept, a separate stable
evolutionary branch with a canonical Nash bridge, or part of an analytic
population-dynamics structure.

## Competing designs

1. Add ESS and NSS directly to `Core.Response`.
2. Adopt a stable `GameTheory.Evolutionary` branch for the static payoff
   notions and a one-way bridge to the canonical static form.
3. Bundle ESS with population distributions, replicator dynamics, simplex
   invariants, topology, and convergence under Analysis.

Design 2 is adopted. ESS and NSS are mature static evolutionary concepts, but
they are not generic response predicates over arbitrary game forms: their
meaning depends on one homogeneous two-argument payoff kernel and the mutant
tie-break condition. The separate root keeps that domain vocabulary visible
without enlarging the canonical Core concept surface. Design 3 remains a
future opt-in analytic consumer, not a premise of static stability.

## Representative hostile slice

EXP-044 recovers the complete pinned static theorem family and constructs a
deterministic two-player symmetric `GameForm` whose outcome is its strategy
profile. Its oriented utility is
`payoff (profile who) (profile (opponent who))`. The generic flagship proves
that an ESS resident profile satisfies the existing `IsNash` predicate.

The Boolean witness is deliberately not strict at the first ESS comparison:

```text
payoff true true  = 1
payoff false true = 1
payoff true false = 2
payoff false false = 0
```

Thus the mutant ties against the resident and the second ESS clause is
necessary. The generic bridge checks both player orientations and every
unilateral replacement through the canonical deviation API.

## Measurements

| Measure | EXP-044 result |
|---|---|
| authored size | 134 nonblank lines; 17 declarations including bridge helpers and hostile facts |
| stable API change during experiment | 0 declarations and 0 imports |
| authored import | `GameTheory.Core.Utility` only |
| focused build | 1,720 jobs |
| full build | 3,346 jobs |
| ESS/NSS data | `S → S → ℝ` and one resident; no structure or stored capability |
| Nash surface | canonical `GameForm`, `euPreference`, `Profile.update`, and `IsNash` |
| source trust/audit tokens | 0 placeholders, native decisions, custom axioms, direct updates, transports, `HEq`, tactic `change`, `Fintype.ofFinite`, or `open Classical` |
| repository audit | Phase 2 expected source measurements pass |
| axiom profile | `propext`, `Classical.choice`, `Quot.sound` only |
| positive reachability | `GameForm`, `IsNash`, experimental `IsESS`, and ESS-to-Nash |
| negative reachability | Protocol execution, Analysis Nash existence, `stdSimplex`, and `Polynomial` rejected |
| hostile stability test | mutant ties in the Nash condition and loses the nonvacuous ESS tie-break |

## Kill condition

Reject a design that defines a second Nash predicate, stores a population law,
finite-carrier capability, topology, or dynamics in ESS, duplicates profile
update, requires Analysis for the static theorem, misorients either player's
payoff/deviation, or validates only a strict-Nash witness.

No kill condition fired.

## Result

Adopt a stable `GameTheory.Evolutionary` root with two layers:

- `Evolutionary.Basic` owns `IsESS`, `IsNSS`, and their payoff-kernel facts
  without importing game semantics;
- `Evolutionary.Nash` owns the deterministic symmetric presentation and the
  one-way theorem into Core's ordinary expected-utility `IsNash`.

The public root may re-export the stable evolutionary umbrella. It must remain
Protocol- and Analysis-blind. Population states, finite replicator vector
fields, forward invariance, trajectories, and convergence belong to a future
`GameTheory.Analysis.Evolutionary` root only after a named dynamics theorem
measures their scalar, finite-dimensional, and topological needs.
