# D23: discounted stochastic values are an Analysis bridge

- **Status:** adopted and promoted
- **Date:** 2026-08-02
- **Experiment IDs:** EXP-051

## Decision / question

Where the finite two-player zero-sum Shapley operator, its matrix-game value,
and stationary discounted value belong relative to D22's proof-free native
stochastic data and the accepted Analysis boundary.

The source evidence includes the active sibling repository's
`Math/ShapleyOperator.lean` and `Concepts/Stochastic/ZeroSum.lean`, audited
read-only on branch `uniform-existence`. It is evidence, not a dependency. Its
separate PMF/minimax stack and `Fintype.ofFinite` construction are not portable
under the rewrite's accepted boundaries.

## Competing designs

1. Add a small Analysis-owned matrix adapter over the existing canonical
   `GameForm`, mixed extension, minimax theorem, and saddle-point uniqueness;
   put only two-player structural vocabulary below Analysis.
2. Extract a new game-independent matrix-value stack into `GameTheoryMath`.
3. Port the sibling branch's `Math.Minimax` and Shapley stack, retaining its
   simplex/PMF presentation.
4. Put contraction and fixed-point data directly under `GameTheory.Stochastic`.

Design 1 is adopted. The one-shot value is game-semantic and already follows
from `Analysis.Minimax`; design 2 would generalize before a second independent
consumer. Design 3 duplicates accepted finite laws and equilibrium semantics.
Design 4 reverses the enforced one-way Analysis dependency.

## Representative hostile slice

Two Boolean players act in two Boolean states. Payoffs are state-dependent and
zero-sum. Agreement and disagreement induce distinct transition laws, and both
laws put positive mass on staying and switching. For every `beta : NNReal`
with `beta < 1`, the normalized auxiliary matrix has entries

```text
(1 - beta) * stage payoff + beta * expected continuation value.
```

The experiment proves the matrix value is one-Lipschitz in its entries, the
Shapley operator is `beta`-Lipschitz and contracting, its fixed point is unique,
and a canonical mixed saddle profile at every state realizes the Bellman value.

## Literature and dependency review

Shapley's original finite-state, finite-action two-person zero-sum construction
uses controlled transition probabilities and stationary mixed choices:
<https://pmc.ncbi.nlm.nih.gov/articles/PMC1063912/>. The rewrite uses the
equivalent normalized discount convention already public in
`Repeated.discountedPayoff`; this keeps bounded stage payoffs on their original
scale and is the useful convention for later vanishing-discount work.

Mathlib supplies `ContractingWith`, Banach's fixed point, and the finite Pi sup
metric through `Mathlib.Topology.MetricSpace.Contracting`. It supplies no
matrix-game value theorem. The repository's existing `Analysis.Minimax` is
therefore the exact missing input; no new external dependency or independent
mathematics target is needed. Because `Analysis.Minimax` derives minimax from
Nash existence, its transitive closure still contains D12's already admitted
Kakutani dependency even though the Shapley proof does not invoke it directly.

The active sibling's operator uses the unnormalized `u + beta * E[v]` form.
That form is mathematically equivalent up to positive scaling for `beta < 1`,
but was rejected as the public convention because it disagrees with Repeated
and its values grow like `1 / (1 - beta)` near one.

## Measurements

| Measure | EXP-051 experimental result |
|---|---|
| direct imports | `Analysis.Minimax`, `Stochastic.Basic`, Mathlib `Contracting` |
| authored hostile slice | 329 nonblank lines before permanent-module split |
| matrix-value construction | canonical deterministic `GameForm`; `FinDist` mixed actions; existing saddle theorem |
| probability representations | one: `FinDist`; no `PMF` exposure or infinite path law |
| fixed-point use | Banach contraction from Mathlib directly; Kakutani remains transitively reachable through `Analysis.Minimax` |
| focused build | 3,105 jobs; 13 seconds after dependency build |
| source maximum line | 86 characters |
| source hazards | zero placeholders, raw updates, transports, `Fintype.ofFinite`, or representation leaks |
| axiom profile | `propext`, `Classical.choice`, and `Quot.sound` only |

The decisive proof is a saddle squeeze. Against the row half of one selected
saddle and the column half of another, an entrywise payoff perturbation bounds
the common outcome law's expectation; the two saddle inequalities then bound
the two selected values. No simplex optimization API is copied.

The first promoted draft left `Game.IsZeroSum` unused: all operator theorems
were valid for the zero-sum completion of player zero's payoff, but nothing
connected that completion back to the native second player's utility. The
integration audit caught the semantic gap. `auxiliaryUtility_one_eq` now uses
the pointwise zero-sum premise to identify the artificial column utility with
the actual normalized player-one return and negated continuation value. The
Analysis reachability probe names this theorem so the connection cannot
quietly fall out of use.

## Kill condition

Reject the design if it needs a second probability or equilibrium
representation, `PMF`, stored discount/finiteness, `Fintype.ofFinite`, topology
below Analysis, the sibling source as a dependency, a custom axiom, or a
user-visible transport. Also reject a public "stationary optimal strategy"
claim if proving it requires an infinite-path payoff semantics not yet admitted
by D11/D22.

No kill condition fired. The last condition narrows the promoted endpoint:
statewise stationary saddle actions and the Bellman fixed point are proved;
optimality against arbitrary infinite-history strategies is not claimed.

## Result and consequences

`GameTheory.Stochastic.ZeroSum` owns only the pointwise zero-sum predicate and
the proof-free row/column presentation of a two-player joint action.
`GameTheory.Analysis.MatrixValue` owns the canonical matrix adapter and value
perturbation theorem. `GameTheory.Analysis.Stochastic.Discounted` owns the
normalized auxiliary matrices, contraction, unique value, and stationary
saddle selectors. Its zero-sum bridge identifies the constructed column
utility with the native player-one stage payoff and negated continuation value;
the algebraic row-payoff operator itself remains assumption-minimal. The stable
stochastic umbrella does not import Analysis; the analytic stochastic root
imports stable stochastic data in one direction.

The final six-target permanent-module build completes in 3,121 jobs. The
stable stochastic root positively reaches its structural zero-sum surface and
rejects the Shapley operator and Kakutani; the Analysis root positively reaches
the zero-sum interpretation theorem, canonical matrix value, `FinDist`,
contraction, stationary selector, and existing Kakutani/minimax path while
rejecting Protocol and Repeated. Headline axioms remain `propext`,
`Classical.choice`, and `Quot.sound`.

The final reachability counts are 7 positive and 3 negative probes for stable
Stochastic, and 8 positive and 2 negative probes for Analysis.Stochastic. The
run also corrected the probe matcher so an unknown qualified child can no
longer make its known namespace prefix appear unknown.

This closes the mature discounted-value gate without pretending to prove the
active sibling branch's general uniform-equilibrium conjecture. General
history-dependent discounted optimality and vanishing-discount uniform values
remain separately gated Analysis or research work.

D39/EXP-072 later closes the finite general-sum stationary-equilibrium item
that was still open here: `Analysis.Stochastic.Fink` now proves a stationary
Bellman equilibrium by the same one-way analytic boundary. It does not change
this decision's exclusions for arbitrary history-dependent optimality or
uniform-equilibrium existence.
