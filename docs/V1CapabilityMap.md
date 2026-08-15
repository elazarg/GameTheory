# V1 capability map

This is a workflow-level guide for readers arriving from the original
`GameTheory` development. The v2 branch is a source-incompatible successor:
it preserves useful mathematics through successor-native owners rather than
compatibility aliases or declaration-for-declaration ports. The final v1 tree
remains available at the `v1-final` tag.

Status labels:

- **supported**: a public successor workflow and representative consumer
  compile;
- **queued**: the workflow is useful and has a dependency-gated recovery
  package;
- **frontier**: admission requires a new hostile experiment; and
- **retired**: the old abstraction is intentionally replaced by a canonical
  successor owner.

## Current redirects

| If you are looking for... | Use in v2 | Status and scope |
|---|---|---|
| Strategic forms, preferences, deviations, Nash, CE, CCE, welfare, and transformations | `GameTheory.Core` | supported; solution concepts share the canonical deviation waist |
| Finite mixed Nash, correlated-equilibrium existence, minimax, and refinements | `GameTheory.Analysis` | supported, opt-in analytic root |
| Finite-support probability and finite pointwise convergence | `GameTheory.Math.Probability.FinDist`, `.Bounds`, and `.Convergence` | supported; the finite core does not expose a parallel `PMF` wrapper hierarchy |
| Executable finite pure-Nash search | `GameTheory.Finite.Algorithm` and `GameTheory.Finite.Correctness` | supported; rational execution is separated from real-valued correctness |
| Protocol execution, histories, information, assessment, SPE, and backward induction | `GameTheory.Protocol` | supported; one runner and one policy semantics |
| NFG syntax | `GameTheory.Languages.NFG` | supported; compiles directly to the canonical static form |
| EFG strategic extraction, Kuhn correspondence, and Zermelo | `GameTheory.Languages.EFG` and its explicit `Strategic`, `Kuhn`, and `Zermelo` leaves | supported |
| FOSG execution, serialization, strategic transfer, and counterfactual regret | `GameTheory.Languages.FOSG`, `GameTheory.Languages.Bridges.FOSGToEFG`, and `GameTheory.Analysis.Protocol` | supported in the scopes recorded by the capability matrix |
| MAID execution and strategic transfer | `GameTheory.Languages.MAID` | supported; semantic observation pruning is public, graphical requisite analysis is queued |
| Multi-round imperfect monitoring | `GameTheory.Languages.MultiRound` | supported |
| Intrinsic-form closed loops and pure strategic analysis | `GameTheory.Languages.Intrinsic` | supported through explicit opt-in solution/strategic leaves |
| Repeated games, public monitoring, PPE, self-generation, uniform equilibrium, and the folk theorem | `GameTheory.Repeated` and `GameTheory.Analysis.Repeated` | supported; public randomization remains queued |
| Finite stochastic games, chronological histories, continuation/restart, uniform payoffs, and discounted stationary values | `GameTheory.Stochastic` and `GameTheory.Analysis.Stochastic` | supported through ordinary public policies projected onto the canonical runner; no infinite-path law or general uniform-existence claim |
| Bayesian games, BCE, revelation, information design, Groves, auctions, and knapsack | `GameTheory.Core.Bayesian`, `GameTheory.Mechanism`, and `GameTheory.Languages.Bayesian` | supported in the finite/algebraic scopes recorded by the capability matrix |
| Monderer--Tennenholtz-style target implementation by profile transfers | `GameTheory.Mechanism.Implementation` | supported for canonical weak undominance and finite surviving-budget bounds; mixed, correlated, informational, VCG, price, and attainment extensions remain consumer-gated |
| Indivisible-goods EF1 and two-agent EFX | `GameTheory.Mechanism.FairDivision` | supported |
| Coalitional games, Shapley/Banzhaf/Shapley--Shubik values, bargaining, and matching | `GameTheory.Core.Coalitional` and `GameTheory.Cooperative` | supported or partial as recorded in the delivery ledger |
| Congestion games and affine price of anarchy | `GameTheory.Congestion` | supported |
| Finite knowledge, posteriors, common knowledge, and agreement | `GameTheory.Epistemic` | supported |
| ESS/NSS and the symmetric-Nash bridge | `GameTheory.Evolutionary` | supported |

The exact public imports, hostile consumers, and limitations are indexed in
[`CapabilityMatrix.md`](CapabilityMatrix.md) and
[`SupportEvidenceMatrix.md`](SupportEvidenceMatrix.md).

## Useful v1 workflows still queued

The first recovery wave reuses accepted successor owners and therefore does
not reopen the foundational architecture:

- secure equilibrium and constant-sum correlation;
- Sen and median-voter social choice;
- convex-game core results and cost of stability;
- proposer optimality, rural hospitals, stable-matching lattice results, and
  proposer strategyproofness;
- egalitarian and Kalai--Smorodinsky bargaining; and
- envy-cycle EF1 and maximin-share fair division.

The following workflows require one bounded experiment before breadth:

- the analytic Myerson envelope and payment characterization;
- divisible cake cutting, with its measure/KKM dependencies confined to an
  analytic fair-division leaf;
- monitored public randomization;
- absent-minded values for imperfect recall;
- delegation and liquid-democracy infrastructure; and
- finite-game flow/Hodge decomposition.

Each admitted package must have a recognizable public consumer, a hostile
positive witness, and a falsifying or nondegenerate control. Its evidence and
scope update the delivery ledger and capability matrix in the same commit.

## Frontier and retired surfaces

The v1 OpenGame hierarchy has no v2 redirect. It remains **frontier** until a
representative composition theorem and an external semantic comparison pass a
hostile experiment. In particular, v1 code is not promoted merely to recover
an import path.

The universal `KernelGame` hub, duplicate language-specific solution
concepts, broad compatibility/morphism hierarchies, and project-local
probability wrappers are **retired**. Their useful consequences redirect to
the canonical static form, deviation API, explicit transformation squares,
Protocol runner, and `FinDist` listed above.
