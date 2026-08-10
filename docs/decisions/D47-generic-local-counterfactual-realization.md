# D47: Derive local counterfactual regret from runner affinity

- **Status:** adopted; generic qualifying-site realization promoted
- **Date:** 2026-08-10
- **Experiment ID:** EXP-084

## Decision

For a selected Protocol information site, derive D46's pointwise realization
equation from canonical behavioral execution when:

1. the model satisfies `ActsOnceWhereItMatters`; and
2. every history in the selected decision fiber is nonterminal.

Factor the current finite player product at the focal coordinate, then use the
no-revisit condition to show that an installed law and each pure commitment
agree after the first step. Lift this exact runner-law identity through
expectation, the canonical counterfactual history sum, and D45 action regret.
The result identifies the local counterfactual-regret vector with the existing
ordinary `regretPayoff` vector for every current law.

Perfect recall discharges the no-revisit premise. It does not discharge
fiberwise nontermination: Protocol deliberately permits terminal histories to
retain nominal activity and share information with nonterminal histories.
That stronger fact is therefore the named site certificate
`InformationSite.AllNonterminal`.

## Competing designs

1. Derive realization from the existing behavioral runner and local
   no-revisit/nonterminal certificates.
2. Keep a model-specific realization proof at every information site.
3. Add a second counterfactual runner or a stored terminal-inactivity axiom.
4. Add heavily expanded environment-wide convenience wrappers around D46.

Design 1 is adopted. Design 2 duplicates the same semantic proof. Design 3
duplicates execution or strengthens all protocols for a local theorem. Design
4 was experimentally rejected: the dependent wrapper statement made a single
leaf elaborate for more than 180 seconds, while the fixed-environment theorem
and direct D46 consumer build in seconds.

## Hostile evidence

The consumer selects the first decision in the two-stage perfect-recall
complementarity fixture. A two-step continuation necessarily passes through a
second information state, so the affine runner theorem cannot reduce to a
one-step terminal calculation. The test proves the exact runner-law identity,
the local regret-vector realization for every current law, and an asymptotic
regret-matching theorem by passing that realization directly to D46.

The same fixture retains the adverse global control: every actual one-site
deviation test can be harmless while a coordinated two-site policy deviation
is profitable, so the local result is not mislabeled as SPE, root regret, or
global exploitability.

The combined counterfactual consumers completed 2,451 jobs warning-free; the
Protocol-analysis aggregate completed 2,446; and the full library completed
3,586. Fast Phase 2 and Phase 3 audits report `VERIFIED=1`. Deep reachability
mode was deliberately not run.

## Kill conditions and result

Reject or narrow the design if linearity fails despite no revisit; if terminal
inactivity is smuggled in; if global information-state finiteness, raw update,
public transport, or a second runner is required; if only the named fixture
works; or if a convenience API materially slows the implementation loop.

The semantic design is accepted. The environment-wide expanded wrapper is
rejected on compile-time grounds. The promoted API keeps the fast
fixed-environment realization theorem; clients pass it pointwise to D46's
existing finite or asymptotic theorem.

## Public API consequences

Add `InformationSite.AllNonterminal` and `InformationSite.active`; exact
one-step and whole-run law identities for `BehavioralPolicy.withLaw`; affine
ordinary and counterfactual continuation theorems; pure-commitment
`counterfactualActionUtility`; exact action-regret realization; the canonical
`strategyWithLocalLaw`; and vector realization for an arbitrary current law.

The next gate remains global: decompose a whole perfect-recall deviation across
information sets, then control root regret or two-player zero-sum
exploitability using all local learners.
