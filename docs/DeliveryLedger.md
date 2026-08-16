# Delivery ledger

This is the mutable successor-native delivery index. Status is determined by
compiled public evidence and named remainders, never by module count.

Status labels:

- **complete**: the intended theorem family has no current remainder;
- **supported**: a stable useful surface exists and its next seam is separate;
- **partial**: the current surface is honest but a named theorem in the same
  workflow remains; and
- **frontier**: intentionally excluded from stable dependencies.

## Architecture and cross-cutting gates

| Gate | Status | Evidence | Remainder |
|---|---|---|---|
| Static core and deviation locality | complete | `GameTheory.Core`; locality tests; full Nash/CCE/CE outcome, player, and strategy transformation squares; mixed-play commutation | None for the common equilibrium waist. |
| Reusable mathematics and finite-support probability | complete | separate `GameTheory.Math` target; `GameTheory.Math.Probability.FinDist`; simplex and pointwise-convergence interfaces; finite-index rotations; probability tests; D55/EXP-101 boundary probes | Infinite laws require a measurable layer; extract further domain mathematics only when a consumer justifies the abstraction. |
| Analysis dependency boundary | complete | importable `GameTheory.Analysis` root, one-way imports, structural audits | Keep fixed-point/topology dependencies out of semantic roots. |
| Execution and information | complete | `GameTheory.Protocol`, execution/information tests | No second runner or universal semantic hub. |
| Proper imperfect-information subgames | complete | `Protocol.SubgamePerfect`, crossed-root fixture, EXP-078 complementarity counterexample | Whole-policy deviations are essential; no general single-information-state iff exists under perfect recall. |
| Documentation and support evidence | complete | `CapabilityMatrix.md`, `SupportEvidenceMatrix.md`, `ReviewClosureLedger.md` | Keep claims synchronized with compiled evidence and dispositions. |

## Static and analytic families

| Family | Status | Current evidence | Next seam |
|---|---|---|---|
| Equilibrium, dominance, and response | supported | Core Nash/CE/CCE/strong Nash, distinct correlated and product-belief independent rationalizability with a strict three-player separation, explicitly named pure-elimination survivors, response dynamics | Secure equilibrium and further elimination theorems. |
| Mixed games and refinements | supported | mixed extension, improvement, trembling-hand positive/negative tests | Separately gate additional limit refinements. |
| Correlation and Bayesian obedience | supported | CE/CCE local-obedience iff; BCE interim-obedience iff, BNE outcome laws, and constructive information-structure foundation; dominated-support results | Richer public signaling regimes and further approximation results. |
| Potential and learning | supported | exact/mixed potential, ordinal-not-exact Nash, fictitious-play convergence, and optimally tuned square-root MW regret/CCE rates | Weighted-potential generalization. |
| Zero-sum and minimax | supported | matrix security, selected values, attained maximin--minimax equality, canonical external-regret cancellation to empirical-marginal approximate Nash, a moving same-trace one-site Protocol learner, and a two-type multi-site Bayesian learner controlling complete contingent plans with exact nonzero controls | Reusable finite Protocol schedule synthesis, security extensions, and measurable games remain separate. |
| Welfare and smoothness | supported | IR/Pareto transport, Nash/CCE smoothness | Additional finite welfare consequences. |
| Preferences and social choice | supported | rank foundations, finite vNM with automatic endpoint selection, Arrow, May, Gibbard–Satterthwaite | Axiom independence, Sen, median-voter results. |
| Epistemic theory | complete | finite-cell posterior/conditioning equality, exact agreement, and a `p = 3/4` common-belief bound with unequal reports | Protocol bridge only with an explicit state-view premise. |
| Evolutionary stability | complete | carrier-parametric ESS/NSS, load-bearing second-order tie witness, Nash-but-not-ESS control, mixed Nash bridge | Population dynamics is a distinct future domain. |
| Communication | supported | cheap talk, babbling, electronic mail | Conditional public randomization and zero-sum communication value. |

## Sequential and dynamic families

| Family | Status | Current evidence | Next seam |
|---|---|---|---|
| EFG strategic extraction | complete | pure/mixed strategic law and Nash equivalences | Broader convenience API only. |
| Kuhn correspondence | complete | whole-profile laws plus protocol-level unilateral updated-law equivalence; two-player EFG witness transfers expected-utility Nash in both directions | Broader convenience results are separate from the finite perfect-recall correspondence. |
| Zermelo backward induction | complete | constructive Bellman profile, explicit exit/reward fixture, infinite unreachable-menu witness, pure SPE | A total fallback is structural because contingent plans are total; finiteness is required only at genuine decision histories. |
| Behavioral assessment and sequential equilibrium | supported | decision-fiber antichain contract, perfect-recall certificate, positive/falsifying hidden-state assessments | Broader refinement families. |
| Repeated games | supported | deterministic Protocol prefixes; native public-signal histories; deviation-signal rank; discounting, triggers, PPE, bounded APS self-generation, deterministic uniform equilibrium, folk theorem | Public randomization and monitored uniformity are separate breadth; native monitoring is not claimed as a Protocol runner. EXP-108 is a future gate for distinct `E[liminf Aₙ]`, `E[limsup Aₙ]`, and `lim E[Aₙ]` semantics plus cyclic subgame-perfect uniformity; no coercions are implied. |
| Stochastic games | supported | ordinary public-policy equivalence, chronological fixed-horizon laws, exact proof-free/canonical average-payoff transport, uniform-cap characterization, arbitrary-horizon restart, action-dependent migration fixture, nonconstant transient uniform-payoff certificate, discounted values, stationary Bellman equilibrium | No infinite-path law or general uniform-existence claim; EXP-108 is an in-progress future gate for finite-marginal infinite-play semantics, order-of-limits separation, and cyclic terminal/limiting-average/uniform interfaces. Further specialized continuation algebra is consumer-gated. |

## Languages, mechanisms, and parallel domains

| Family | Status | Current evidence | Next seam |
|---|---|---|---|
| NFG | complete | direct static compilation and shared solution concepts | None for the current language surface. |
| FOSG and bridges | supported | EFG structural projection, explicit-order serialization, whole-round boundary/terminal/continuation support, policy inversion, external history utility, same-epsilon behavioral Nash equivalence in target- and source-facing forms, canonical focal/counterfactual reach, local regret matching with finite/asymptotic bounds, generic no-revisit realization, bounded common-depth root bridge, exact topological decomposition, deviation-uniform root convergence from payoff-range certificates, canonical fixed-strategy/time-average external regret, a moving same-trace learner, and same-depth multi-site Bayesian complete-plan learning reaching empirical Nash | Reusable schedule synthesis, arbitrary behavioral replacements, and unequal-depth information fibers remain separate gates. |
| MAID | supported | typed acyclic execution; multi-owner same-epsilon native/compiled Nash transfer; source-owner observation pruning with exact native/compiled laws; profile-local full-deviation coverage exactly characterizing safe Nash expansion; nested refinement with staged expansion, update/law compatibility, and relative-to-full coverage composition; fair-signal and two-signal safe/live controls; experimentally validated finite utility augmentation and one-site graphical-ignorability-to-coverage with a safe/live relay control; hybrid restore-at-site/s-reachability foundations; site-local nonrelevant-term and factor/optimality endpoints; one-source non-s-reachability optimality transport; the sufficient-recall source-first induction from `SReachAcyclic` plus `IsEdgeAdditionFixpoint` to global `CoversFullDeviationsAt`; and an executable explicit-enumeration checker exactly equivalent to the experimental fixpoint predicate | Experimental global coverage and fixpoint checking are complete but not promoted to stable syntax, and no automatic pruning pass, minimality, or confluence theorem follows. Reopen construction or strategic-reliance promotion only for an independent consumer; refinement and Kuhn-facing extensions remain separate. |
| Multi-round | supported | perfect recall, coarse monitoring, Protocol/FOSG compiler and value consumer | Absent-minded values and stagewise-Nash conveniences. |
| Intrinsic | supported | native closed-loop semantics, selected solution, fixed-nature pure strategic compilation, and canonical Nash with downstream re-solving | Nature lotteries, temporal compilation, and behavioral/mixed strategy are separate gates. |
| Bayesian mechanisms and information design | supported | direct/Protocol Nash transfer, multi-player revelation, posterior splitting construction and feasibility | Analytic envelope theory. |
| Auctions, Groves, and knapsack | supported | general Groves public-choice truthfulness/DSIC, Vickrey/reserve/VCG, zero-reserve payoff bridge, combinatorial allocation, exact and zero-weight-compatible approximate solvers | Truthful approximation still requires monotonicity and payments. |
| Implementation by transfers | supported | profile recording, additive profile transfers, canonical weak-undominance implementation, exact two-player budget witness, non-singleton target, and zero-transfer controls | Mixed, correlated, informational, VCG, implementation-price, and attainment theorems are separate consumer-gated packages. |
| Fair division | supported | finite EF1 and two-agent EFX | Envy cycles and maximin share. |
| Congestion | complete | Rosenthal, Nash existence, affine PoA, Pigou/Braess | None for current scope. |
| Coalitional theory | partial | asymmetric Shapley witness, Banzhaf swing-count identity, bundled simple-game Shapley--Shubik, core-to-balancedness | Balancedness converse and convex-game core result. |
| Matching | supported | general finite stability and balanced perfectness | Proposer optimality, rural hospitals, strategyproofness. |
| Bargaining | supported | Nash-product properties and affine invariance | Egalitarian and Kalai–Smorodinsky solutions. |
| Open/compositional games | frontier | no stable root | Admit only after a representative composition theorem. |

The mutable execution order is maintained in
[`PostArchitectureDeliveryPlan.md`](PostArchitectureDeliveryPlan.md).
