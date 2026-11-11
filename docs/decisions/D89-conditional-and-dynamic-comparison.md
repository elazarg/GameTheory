# D89: dynamic comparison requires a composition law

- **Status:** direct sufficient hypotheses validated; prototypes experimental, no new context or hierarchy.
- **Date:** 2026-11-11
- **Experiment:** EXP-184

## Question and alternatives

Can a total transitive ranking of terminal laws support conditional-to-ex-ante
or one-shot-to-whole-play reasoning? Compare direct guarded comparison and
support-local mixture hypotheses with changing the numerical Context data or
introducing a dynamic preference record. The latter would need an operation
that the direct form cannot supply; this slice finds none.

## Refuting control

The same ranking scores every Boolean law by `(Pr(true) - 2/5)^2`, with larger
scores preferred. It is reflexive, transitive and total. Both branches of a
fairly observed signal have two genuine actions and strictly prefer the
prescribed action: true prefers sure true to sure false, and false prefers sure
false to a fair outcome. The prescribed policy produces success probability
`1/2`; switching both actions produces `1/4`. The latter is strictly preferred
before observation. All choices and laws are admissible. Thus the failure is
comparison composition, not undefined values, incomplete rankings, empty menus,
ties or an unavailable alternative.

## Positive clients and exact scope

`Experimental.Exp184.Composition.conditional_optimal` reuses `Math.IsOptimalOn`.
It needs conditional comparison only on the prior support, plus admissibility
of the actual chosen and alternative whole laws and preservation of the actual
conditional comparisons. It does not infer whole-law admissibility from
component admissibility or infer incumbent feasibility from optimality.

`backward_optimal` drives well-founded protocol backward laws using the same
raw relation, guarded reflexivity, transitivity, actual whole-chooser
admissibility and a sufficient composition law. The composition prior is the
transition selected by the competing chooser, not just the incumbent's
transition. Its conclusion concerns state-aware `ExecutionProtocol.Chooser`.
It does not establish imperfect-information policy realizability, generic SPE,
PBE or sequential equilibrium. The existing information bridges retain their
separate recall, measurability and terminal-rationality obligations.

The existing possibility preference supplies arbitrary-PMF paired comparison
preservation and fixed-base upper/lower mixture bounds. Its absence of real
expected-utility representation is already proved in `Tests.Potential`.
`Experimental.Exp184.Consumers` instantiates conditional composition with a
stochastic continuation and backward composition with the existing fair-chance,
consequential-decision protocol, against every state-aware competing chooser.
Adding a common sure-success continuation destroys a strict possibility
comparison: weak mixture preservation is weaker than independence cancellation.

This resolves the next consumer question left by D80 without selecting a
universal Mixable interface. These sufficient raw hypotheses do not claim to
characterize every dynamically consistent preference. The non-EU composition
clients remain experimental; promotion still needs an independently requiring
stable consumer, rather than moving evidence into production to satisfy a gate.

## Validation

The three evidence modules compile strictly in a focused 3,072-job build;
source boundaries and audit-driver coverage pass. No public definitions,
Context representation, numerical theorem statements or package imports change.
Existing undefined-expectation and countable-mixture rejection controls remain
in the full validation scope. Full integration is recorded in EXP-184.
On checkpoint `768f22f5`, the full audit passes 3,877 default and 4,795
validation jobs, public lint, authored diagnostics and transitive standard-axiom
checks.

The experiment does not compare a compiled record implementation or make a
performance claim. The result is a semantic separation and two direct proof
clients, not a measured elaboration advantage over an alternative record.
