# D84: finite-menu choice and revealed preference

- **Status:** selected after focused validation; integration validation pending.
- **Date:** 2026-11-11
- **Experiment:** EXP-179

## Question and alternatives

Which choice primitive can connect strategic optimization and economic
allocation without numerical utility or a universal problem structure?
Compare direct greatest-element comparisons, maximal elements under incomplete
preferences, and observed finite-menu choice. Use ordinary functions and
named hypotheses rather than a record storing finiteness or preference laws.

## Representation and extraction boundary

`Math.FiniteChoice.best` returns all greatest offered alternatives for an
explicit preferred-first relation. Unlike `Math.IsOptimalOn`, it requires the
chosen alternative to belong to the menu. The existing guarded predicate
continues to require evaluation-domain admissibility even if the allowed set
is empty; these are different requirements, not competing definitions.

The finite-menu representation theorem equates feasible, nonempty choice
satisfying the weak axiom of revealed preference with greatest-element choice
under a total transitive relation. Binary menus reveal the relation; triple
menus establish transitivity. No numerical representation, antisymmetry,
finite ambient carrier, probability or game data enters the theorem. Ties
remain multiple alternatives. Finite existence reuses Mathlib's
`Finset.exists_maximal` with a theorem-local reversed relation, rather than
reproving maximal-element mathematics.

This represents observed choices by a complete preorder. It does not identify
an unknown latent preference: equality-based maximal choice and complete
indifference select exactly the same alternatives on every menu. Equality's
greatest-element correspondence instead fails nonemptiness on a distinct pair.
Feasible nonempty choice without the weak axiom admits cyclic binary choices.

The domain is **all finite menus**. A restricted budget family does not supply
those binary and triple observations automatically. Nonempty choice excludes
rejecting every offered option unless an outside alternative is explicitly
included. There is no demand existence, measurable choice, utility continuity,
general-equilibrium existence or revealed-preference result for arbitrary
restricted budget data here.

## Existing clients and bundle distinction

The canonical best-response predicate is characterized by membership in the
full finite menu's greatest choices without adding order assumptions. The
canonical knapsack welfare selector is a member of the corresponding feasible
allocation choices; its existing direct maximum proof remains unchanged.
Neither client is made to construct a new structure or use a new equilibrium
engine. The original expectation-definedness and feasibility semantics remain
with their owners.

`Rank.exists_best_finset` now delegates to the mathematical existence theorem,
removing its separate induction. The stochastic response consumer offers sure
failure, sure success and a fair lottery. It proves that even these observed
menu choices have no expected-utility representation on outcomes, despite
their complete-preorder representation. A pure-action consumer alone would
not establish that stronger separation.

In the capacity-one allocation consumer, two singleton allocations are tied
maximizers but their union is infeasible. The correspondence returns alternative
**allocations**, not a bundle of simultaneously accepted agents. The independent
represented-bundle control proves that flattening tied singleton-bundle indices
into a union need not yield any represented feasible bundle.

The local MathEconLib reference checkout at `58f602847d7f131994d32ca7a8cc1af35b7e2dbe`
distinguishes these operations: `ChoiceFunction.ofBundleOrder` maximizes over
represented bundle indices, then returns a winning bundle under a linear
order. Its contract-level choice, outside options, substitutability and path
independence are not the correspondence or weak axiom admitted here. No external
source is edited, no dependency is added, and no migration is claimed.

The mathematical owner imports only Mathlib. It is suitable for a later
shared mathematical-economics component, with game and allocation adapters
remaining in their domain modules. A package move or a universal choice
hierarchy is not needed to validate this dependency direction.

## Cost and validation

The comparison is theorem-level: the useful new operation is reverse
rationalization of observed choices, not fewer lines for existing numerical
maximizers. The one-line knapsack `Finset.exists_max_image` proof is retained.
No record candidate is implemented or timed, and no speed or construction-cost
advantage is claimed. General finite-order existence remains Mathlib-owned.

Baseline `bb9f3345`; Lean 4.35.0 / Mathlib v4.35.0. Exact focused and full commands:

```text
lake --iofail build GameTheory.Math.FiniteChoice
lake --iofail build GameTheory.Tests.FiniteChoice GameTheory.Tests.LotteryChoice GameTheory.Experimental.Exp179.ChoiceBoundary
python scripts/audit.py --source-only
python scripts/audit.py
```

The independent mathematical build passes 677 jobs; the focused complete
consumer/control build passes 3,070 jobs. Source checks pass. Independent
semantic review accepts the representation, extraction boundaries and
lottery-choice separation. Full integration evidence is recorded in EXP-179
before collection. No performance advantage is claimed from job counts.
