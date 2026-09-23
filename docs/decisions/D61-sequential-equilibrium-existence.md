# D61: finite perfect-recall sequential-equilibrium existence

- **Status:** adopted
- **Date:** 2026-09-24
- **Experiment ID:** EXP-121

## Decision

Prove existence for the existing behavioral-assessment predicate in an
explicit analytic leaf, `GameTheory.Analysis.Protocol.EFGExistence`. Keep
the assessment, continuation runner, and full-policy deviation quantifier
unchanged. The underlying Protocol theorem also applies beyond EFG syntax
when finite complete histories and a certified terminal horizon are supplied.

The EFG endpoint requires finite players, states, actions, and raw information
states; perfect recall; and a legal total policy for every player. The last
premise inhabits menus even at unused raw information values, because policies
are total functions in the accepted representation. A caller may supply any
positive certified terminal horizon, or use the theorem obtaining a sufficient
horizon from finite EFG histories. Finite states alone do not imply finite
histories in a cyclic protocol.

## Competing routes and proof

1. Obtain perturbed strategic equilibria and separately derive conditional
   continuation optimality.
2. Obtain perturbed information-site fixed points, prove the perfect-recall
   local-to-whole-policy implication, and take a joint assessment limit.

Route 2 is implemented. The existing counterfactual root decomposition assumes
`CommonDepth`; perfect recall does not imply that condition. Reusing that
decomposition alone would narrow the theorem to synchronized information sets.
The new decomposition instead cuts complete histories at possibly different
depths, using the existing history reach and continuation semantics.

The dependency path is:

- `Analysis.LocalChoiceFixedPoint` applies Kakutani to a finite product of
  local probability simplices with continuous action scores. Scores may
  depend on the site's own law; no separate static game is introduced.
- `SequentialPerturbation` mixes each residual law with a positive uniform
  tremble, constructs Bayes beliefs, and obtains exact local optimality among
  the perturbed laws.
- `SequentialRationality` uses a finite occupation telescope, perfect-recall
  reach factorization, and a variable-depth information cut to prove all
  feasible whole-policy continuation inequalities.
- `AssessmentCompactness` extracts one subsequence for strategies and beliefs.
  Strategies converge at every raw information value, so all continuation
  runners are covered, including off-path policy coordinates.
- `SequentialLimits` passes the full-policy inequalities to the limit.
  Every unrestricted deviation is repaired with the same vanishing uniform
  tremble before taking limits. The target need not have full support.
- `SequentialExistence` combines these results; `EFGExistence` supplies finite
  histories from the existing tree equivalence and returns the existing
  `IsSequentialEquilibriumWithin` predicate.

## Hostile slice and kill conditions

`SequentialExistenceTest` constructs a perfect-recall hidden-bit game whose
single acting information set contains histories at depths one and two. Its
`no_commonDepth` theorem rules out the synchronized shortcut. The general
existence theorem applies to its nonconstant hidden-bit-matching payoff.

`SequentialExistenceBoundaryTest` proves a distinct limitation of the existing
fuel-indexed predicate. With fuel two, a forced earlier site prefers the short
reward-one path, while the later choice site prefers the long reward-two path.
No assessment can satisfy both whole-policy inequalities. The same game has a
certified horizon of three and an equilibrium supplied by the general theorem.
Thus arbitrary rolling truncation is a refuted claim, not an open obligation.

The original kill conditions were hidden equilibrium or optimality premises,
inferring equal depth from recall, placeholders, and fixed-point dependencies
leaking into Protocol or lightweight consistency. The final API has none of
the first three; dependency and trust checks are recorded in EXP-121.

## Boundary and validation

The source audit now permits exactly two direct fixed-point package importers:
static Nash and `Analysis.LocalChoiceFixedPoint`. All existing zero budgets
for transport, forbidden imports, placeholders, and custom axioms remain.
`Analysis.Protocol.Sequential` and the lightweight EFG adapter keep their
existing imports; existence is an explicit additional import. This amends
[D12](D12-dependency-boundaries.md), not the stable syntax dependency direction.

The full warning-as-error build passed with 4,163 jobs. EXP-121 records the
final source, reachability, linter, and axiom checks and their commands. The
existence theorem is nonconstructive; no equilibrium algorithm, infinite-game
existence, or payoff-correspondence refinement result is claimed.
