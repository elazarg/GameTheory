# D88: exchange budgets and market clearing

- **Status:** selected after complete focused validation; integration validation pending.
- **Date:** 2026-11-11
- **Experiment:** EXP-183

## Question and exact scope

Do price-dependent individual choices and an excess-demand price response
produce a competitive exchange equilibrium, or do feasibility and artificial
caps conceal additional obligations? Compare capped fixed-point conditions
with separate budget regularity, exact clearing and uncapped optimality.

The measured slice has two consumers and two divisible goods, with every
consumer endowed with one unit of each good. Aggregate supply is `(2,2)`.
Prices are nonnegative and sum to one; zero coordinates are allowed. Each
utility is a real function on the ambient bundle space `ℝ²`, continuous there,
concave on the nonnegative cone, and strictly monotone on that cone in the
product order. Improving one coordinate while weakly improving the other
therefore strictly improves utility. These hypotheses are stronger than
continuity only on the cone, quasiconcavity or local nonsatiation alone.

No arbitrary-endowment, arbitrary-population or general Arrow–Debreu theorem
is claimed. The native competitive-equilibrium predicate and exchange data
remain experimental; only the independent mathematical budget-continuity
operation is selected for stable admission.

## Reusable budget continuity

`Math.lowerHemicontinuous_linearBudget` works on a fixed convex allowed set
containing zero in a topological real module. Costs are an ordinary family
of linear maps. Each fixed-bundle cost section is continuous in the parameter;
wealth is continuous and strictly positive. A feasible bundle is recovered
at a nearby parameter by the radial factor
`wealth / max wealth (cost bundle)`. The factor lies in `(0,1]`, equals one
at the reference affordable bundle, and makes the recovered bundle affordable.

No compactness, finite dimension, first countability, norm, positive-price or
nonnegative-cost assumption enters this theorem. It uses Mathlib's convex
scaling and hemicontinuity APIs, not a budget record. Joint cost continuity is
a separate hypothesis used by the exchange client to prove a closed feasible
graph. Positive wealth is sufficient, not claimed necessary for every budget
family. The EXP-181 zero-income/free-good example refutes simply dropping it
without a replacement condition.

Unit endowments and price normalization give wealth exactly one for both
consumers, including at boundary prices. It is zero income together with a
free-price boundary that broke the earlier example, not zero prices by
themselves.

## From the fixed point to the economic statement

The analytic envelope is a product of the price simplex and two consumption
boxes `[0,3]²`. One coordinate proposes prices, with a linear objective equal
to the proposed price value of physical excess demand. Each other coordinate
optimizes its own utility over its current budget inside the box. The existing
`exists_feasibleChoice_fixedPoint` supplies simultaneous maximizers. Consumer
utilities are never added to one another.

The economic conclusion requires two further proofs:

1. Aggregate affordability gives current price value of excess demand at
   most zero. Price optimality against each unit commodity-price vector then
   bounds every aggregate quantity by its supply of two. If some good remains,
   giving half the residual bundle to the lower-expenditure consumer remains
   affordable: its expenditure becomes one plus half the difference between
   the consumers' expenditures. This is at most one. The top-up stays within
   the box and strictly improves a product-order coordinate, contradicting
   strict monotonicity and consumer optimality. Thus all markets clear.
2. The resource bounds put each individual quantity at most two, strictly
   below the cap of three. Capped optimality is consequently relative local
   optimality on the full nonnegative budget. The proof uses upper-only
   neighborhoods, so zero chosen quantities cause no problem. Mathlib's
   `IsMaxOn.of_isLocalMaxOn_of_concaveOn` yields global full-budget optimality.

The final existence result includes normalized prices, full uncapped budget
optimality for each consumer, and exact clearing. An explicit instance uses
positive linear weights `(2,1)` and `(1,2)`; the consumers disagree on the
ordering of unit commodity bundles. Independent utility parameters are
therefore used concretely, not merely quantified vacuously.

## Controls and limits

- At half prices, `(2,0)` and `(0,2)` are tied full-budget demands for sum
  utility. Selecting `(2,0)` for both consumers gives individual optima but
  fails clearing and the actual excess-demand price response. Demand selection
  is not itself price coordination.
- With a cap of one, the endowment allocation clears and satisfies price
  response and capped consumer optimality at price `(1,0)`. The full budget
  also permits `(1,2)`, which is strictly better. This is a genuine cap-induced
  false equilibrium even for continuous concave strictly monotone utilities.
  It does not refute the cap-three proof, whose inactivity is established.
- Constant-zero utility is continuous, concave and weakly monotone. Zero
  consumption and half prices satisfy capped consumer optimality and price
  response but do not clear. This refutes clearing of that same point under
  weak monotonicity; it does not refute existence of some clearing allocation
  under weak preferences or establish a local-nonsatiation impossibility.

The lower-expenditure top-up proof uses equal wealth and the two-consumer
identities. General endowments require new accounting, not a silent change to
the statement. General preferences, uncertainty, production, welfare and
algorithmic computation remain separate gates. No economic-problem record,
universal game representation or direct MathEconLib modification is admitted.

## Cost and validation

Baseline `c1431a88`; Lean 4.35.0 / Mathlib v4.35.0. Comment-masked nonblank
whole-file lines, including imports and mechanical visibility, are counted
with `scripts.audit.source_code`:

| Scope | Lines |
| --- | ---: |
| Independent mathematical budget theorem | 56 |
| Native exchange definitions and geometry | 103 |
| Clearing and uncapping | 152 |
| Analytic fixed-point construction and heterogeneous instance | 135 |
| Positive and rejection controls | 153 |

The existing fixed-point and concave local-to-global theorems are reused;
neither is reimplemented. No bundled market candidate was implemented or
timed, and no source-compression, speed or cold-cost advantage is claimed.

Exact commands:

```text
lake --iofail build GameTheory.Math.LinearBudget
lake --iofail build GameTheory.Experimental.Exp183.Exchange GameTheory.Experimental.Exp183.ExchangeClearing
lake --iofail build GameTheory.Experimental.Exp183.ExchangeControls GameTheory.Analysis.ExchangeEconomyTest
python scripts/audit.py --source-only
python scripts/audit.py
```

The standalone mathematical target passes 1,606 strict jobs; native clearing
and uncapping pass 1,700; the complete consumer and controls pass 3,202. Source
checks and independent read-only semantic reviews pass. Analytic use stays
under `Analysis`, preserving D12. Complete integration evidence is recorded
in EXP-183 before collection.
