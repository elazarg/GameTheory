# Pinned-v1 coverage ledger

Status: active family-level ledger.

Pinned source: `reference/GameTheory-v1/` at
`a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`.

Last reconciled: 2026-08-02 against the working tree based on `8239c18`.

This ledger answers three different questions separately:

1. Has a family been assigned an honest semantic owner?
2. Has its hostile flagship obligation been completed?
3. Has its full pinned declaration inventory been recovered or disposed?

A strong answer to the first question does not imply either of the other two.
The disposition vocabulary and completion rules are defined in
`PostArchitectureDeliveryPlan.md`.
Detailed work-package ledgers use the schema in
[`coverage/README.md`](coverage/README.md).

The generated pinned index currently contains 436 Lean files and 8,324
declarations. Thirty-five work-package ledgers claim 1,573 declarations: 1,215
have reviewed dispositions and 358 remain seeded `unreviewed`; a further 6,751 are
explicitly unaccounted. `scripts/coverage-audit.ps1` verifies
exclusive family ownership, exact ledger references, disposition vocabulary,
duplicate claims, complete-status consistency, and index freshness. These
numbers do not imply equal mathematical weight and are never converted into a
completion percentage.

## Status vocabulary

Integration status:

- **validated:** the semantic home and dependency direction passed a hostile
  slice;
- **provisional:** a representative slice exists, but a listed design question
  remains;
- **assigned:** the RFC names a likely home, but its domain gate has not run;
- **Frontier:** intentionally outside the stable umbrella;
- **deferred:** outside the finite/discrete successor release.

Recovery status:

- **complete:** every declaration in the stated scope is classified and all
  in-scope recovery obligations build;
- **partial:** some mathematics is integrated, but the exact inventory is open;
- **not started:** no successor theorem-family recovery has begun;
- **retired by design:** the family is accounted as duplicate or architectural
  machinery, not copied as a public surface;
- **out of scope:** excluded by an adopted scope decision.

No broad family below is called complete merely because its flagship exists.

## Frozen flagship reconciliation

| ID | Frozen predecessor result | Delivery status | Successor evidence | Exact remainder |
|---|---|---|---|---|
| F1 | finite mixed Nash existence | **complete** | `Analysis/Nash.lean`, with matching pennies in `Analysis/Examples.lean` | no remainder for the frozen result; solving is separate |
| F2 | no-regret time average implies approximate CCE | **complete** | `Core/Learning.lean`; positive-regret two-round trace; [declaration ledger](coverage/F2-no-regret-cce.md) | no remainder for the frozen theorem; algorithms and asymptotic convergence remain D-LEARN |
| F3 | Kuhn behavioral/mixed correspondence | **complete** | both law directions and realizable-law equality in `Protocol/Information.lean`; constructive EFG wrappers, arbitrary outcome pushforwards, expected utility, and a perfect-recall hostile test; [declaration ledger](coverage/T2-kuhn-correspondence.md) | no remainder for the frozen result; broader EFG/Kuhn inventory is separate |
| F4 | one-shot deviation iff SPE | **complete** | `Protocol/SubgamePerfect.lean`; full well-founded strategic iff, off-path probe, and transparent EFG-facing specialization; [declaration ledger](coverage/F4-one-shot-spe.md) | no remainder for the frozen result; broader EFG refinement inventory is separate |
| F5 | Bayes-Nash outcome law is Bayes-correlated | **complete** | `Core/BayesCorrelated.lean`; fair private-signal probe; [declaration ledger](coverage/F5-bayes-nash-bce.md) | no remainder for the frozen theorem; complete-information BCE/CE and information design remain S-CORR/M-BAYES |
| F6 | incentive compatibility implies truthful Bayesian Nash | **complete** | `Languages/BayesianMechanism.lean`; nondegenerate truthful-report probe; [declaration ledger](coverage/F6-ic-truthful-bayes-nash.md) | no remainder for the frozen theorem; welfare, participation, and revelation remain M-BAYES |
| F7 | discounted folk theorem | **complete** | `Analysis/Repeated/Folk.lean` and a nontrivial Prisoner's Dilemma witness | no remainder for the frozen theorem; monitoring is separate |
| F8 | public-monitoring signal-prefix successor/bind law | **complete** | `Repeated/Monitoring.lean`; noisy branch-dependent two-period probe; [declaration ledger](coverage/F8-public-monitoring-prefix.md) | no remainder for the frozen law; monitoring equilibrium and rank theory remain D-REPEAT |

Headline: every frozen flagship F1-F8 is complete at its accepted semantic
layer, and every frozen transfer T1-T4 now has its named direct theorem. This
closes the architecture-era flagship and transfer queue; broad family recovery
remains separately accounted below.

## Frozen transfer reconciliation

| ID | Frozen transfer | Status | Exact remainder |
|---|---|---|---|
| T1 | finite EFG strategic extraction and pure/mixed Nash transfer | **complete** | information-local contingent plans, finite-carrier capability, exact native-run Nash iff theorems, and a nonconstant-payoff hostile test; [declaration ledger](coverage/T1-efg-strategic-nash.md) |
| T2 | behavioral/mixed correspondence | **complete** | both constructive EFG directions, exact realizable history-law equality, generic outcome-law wrappers, and expected-utility corollaries; [declaration ledger](coverage/T2-kuhn-correspondence.md) |
| T3 | MAID to EFG outcome, utility, and strategy transfer | **complete** | arbitrary typed DAG, same-owner incomparable-decision locality, native/compiled behavioral law equality at every topological order, source-owner policy equivalence, and canonical Nash iff; [declaration ledger](coverage/T3-maid-efg.md) |
| T4 | one-shot NFG to FOSG embedding commuting with compilation | **complete** | stable NFG/FOSG frontends, actual Protocol history-runner equality, arbitrary external utility-law equality, and simultaneous/locality hostile witness; [declaration ledger](coverage/T4-nfg-fosg.md) |

T1-T4 are complete by their named direct theorems. The generic predecessor
certificate wrappers remain retired under D7 and receive no independent
credit.

## Cross-cutting obligations

| Obligation | Status | Delivery owner |
|---|---|---|
| minimal D8 transformation taxonomy | **complete (EXP-045/D8)** | concrete player/strategy equivalences, mixed lifting, Nash/CE invariance, and shared finite-product reindexing |
| nonconstant-payoff finite-EFG rationality stress | **complete (EXP-035)** | arbitrary whole-policy deviations have value `1 / 2` under the canonical Bayes belief |
| well-founded strategic SPE/one-shot equivalence | **complete (EXP-036)** | every whole-policy deviation and typed one-shot deviation are equivalent at all histories under `ActsOnceWhereItMatters` |
| knowledge/`InfoState` hostile probe promised by Phase 0 | **complete (EXP-043/D16)** | separate stable `Epistemic` branch; Protocol counterexample retained as evidence |
| ESS/static-vs-dynamic hostile probe promised by Phase 0 | **complete (EXP-044/D17)** | stable `Evolutionary` definitions plus one-way canonical Nash bridge |
| correlated-equilibrium existence | **open, expected cheap** | Wave 2/Analysis; first try mixed-Nash existence plus Nash-to-CE |
| general fixed-point support stack | **deferred by consumer** | Wave 5; recover only for a selected theorem |
| exact mixed-equilibrium solver | **not a release goal** | D10/D13 reopening only |
| measurable infinite-path and continuous probability | **out of finite scope** | D11 post-release program |

## Family inventory

File counts refer to the pinned predecessor and are context only. Recovery is
declaration-based.

### Shared static theory

| ID | Pinned scope | Files | Intended successor owner | Integration | Recovery | Next gate |
|---|---|---:|---|---|---|---|
| S-FOUND | static `Core/**` except `Babbling`/`Coalition`; `Concepts/Foundations/**`; symmetric/team classes | 28 | `Core`, with independent mathematics below it | validated | partial; 8 response/team/welfare rows reviewed | [response dynamics, team, and welfare seed](coverage/S-FOUND-dynamics-team.md); next VNM, convergence, invariance, equivalence, and duplicate hub machinery |
| S-EQ | `Concepts/Equilibrium/**` | 12 | `Core.Equilibrium`, `Core.Response`, `Core.Approximate` | validated | partial; strict-Nash seed plus approximate Nash 8/8 reviewed | [strict-Nash seed](coverage/S-EQ-strict-nash.md), [approximate-Nash ledger](coverage/S-EQ-approximate.md); next secure and remaining strict theorem families against one Nash surface |
| S-DOM | `Concepts/Dominance/**` | 9 | `Core.Response` and finite correctness | validated | partial | solvability, undominated, and rationalizability inventory |
| S-CORR | `Concepts/Correlation/**` | 10 | `Core.Equilibrium`; existence in `Analysis` | validated | partial; mixed-Nash bridge module 12/12 reviewed, 2 later-slice rows deferred | [mixed Nash and correlated-equilibrium ledger](coverage/S-CORR-mixed-nash.md); next conditional obedience, dominated support, existence, approximation, timing, regret, and hierarchy separations |
| S-MIX | `Concepts/Mixed/**` | 9 | `Core.Mixed`; assessment material in Protocol/Analysis | validated | partial; binary proof spine 15 declarations reviewed | [binary mixed-equilibrium ledger](coverage/S-MIX-binary.md); next dominance, improvement, trembling-hand, uniform/balanced wrappers, and remaining language-facing results |
| S-POT | `Concepts/Potential/**` | 9 | `Core.Potential` | validated | partial; basic potential/FIP/well-founded/team package 22/22 reviewed | [basic potential ledger](coverage/S-POT-basic.md); next decomposition, harmonic, and mixed potential inventory |
| S-ZERO | `Concepts/ZeroSum/**` | 15 | `Core.ZeroSum`; existence in `Analysis` | validated | partial; binary constant-sum correlation proof spine 11 declarations reviewed | [constant-sum correlation ledger](coverage/S-ZERO-constant-sum-correlation.md); next security, general value/correlation, matrix geometry, and complementarity |
| S-WEL | `Concepts/Welfare/**` | 13 | `Core.Welfare`, `Core.RobustWelfare`, domain consumers, plus `Analysis.Repeated` | pure and robust smoothness validated by EXP-052/053 and D24 | partial; Smoothness 4/4 reviewed, no deferred rows | [smoothness ledger](coverage/S-WEL-smoothness.md); next individual rationality and remaining welfare results |
| S-EXIST | `Concepts/Existence/**` | 3 | `Analysis` and `GameTheoryMath` by live consumer | validated for mixed Nash | partial | classify general Nash/Brouwer support and avoid wholesale fixed-point recovery |
| S-TRANS | `Concepts/Transport/**` | 15 | named maps at owning layers only | generic hierarchy rejected | retired by design, accounting open | classify each declaration as subsumed, theorem-specific, or retired |

### Learning, information, and dynamics

| ID | Pinned scope | Files | Intended successor owner | Integration | Recovery | Next gate |
|---|---|---:|---|---|---|---|
| D-LEARN | `Concepts/Learning/**` | 8 | stable finite identities in Core; quantitative composition in `Analysis.Learning` | validated by F2 and EXP-049/D21 | partial; finite and MW self-play package 15/15 reviewed | [self-play ledger](coverage/D-LEARN-self-play.md); next fictitious play on a potential game, then approachability |
| D-COMM | `Concepts/Communication/**`, `Core/Babbling.lean`, `Languages/ElectronicMailGame.lean` | 5 | static core or Protocol according to timing | static ownership validated by EXP-046/D18, EXP-047/D19, and EXP-048/D20 | partial; 87/87 declarations reviewed, 19 cross-family rows deferred | [exact declaration ledger](coverage/D-COMM-communication.md); pure babbling, exact Nash outcome laws, mixed-Nash-to-CE, and finite Electronic Mail recovered; conditional public-signal and zero-sum value results remain gated |
| D-KNOW | `Concepts/Knowledge/**` | 2 | stable `Epistemic` branch; a Protocol bridge only with an explicit state-view premise | validated by EXP-043/D16 | complete; 62/62 declarations accounted | [finite and approximate common-knowledge ledger](coverage/D-KNOW-aumann.md); private mass machinery and the public quantitative bound build |
| D-REPEAT | `Concepts/Repeated/**` | 16 | `Repeated`, finite Protocol bridge, opt-in `Analysis.Repeated` | validated for deterministic and finite public-signal theory | partial | monitoring equilibrium/rank hierarchy and uniform results; no infinite realized-path law |
| D-EVOL | `Concepts/Classes/EvolutionaryStability.lean` | 1 | stable `Evolutionary`; dynamics only in future opt-in Analysis | validated by EXP-044/D17 | complete | [nine-declaration ledger](coverage/D-EVOL-static.md); no pinned population dynamics to recover |

### Languages and sequential theory

| ID | Pinned scope | Files | Intended successor owner | Integration | Recovery | Next gate |
|---|---|---:|---|---|---|---|
| L-NFG | `Languages/NFG.lean`, `Languages/NFG/**` | 10 | transparent language/front-end to `GameForm`; algorithms in `Finite` | validated by EXP-042/T4 | complete recovery; 126/126 reviewed, no deferred rows | [exact declaration ledger](coverage/L-NFG-broad.md); broad examples, observable cheap talk, exact mixed Nash, and the complete Matching Pennies correlated-equilibrium characterization are recovered through canonical shared theory |
| L-EFG | `Languages/EFG.lean`, `Languages/EFG/**` | 15 | transparent Protocol specialization plus named bridges | validated presentation, strategic and Kuhn transfer, nonconstant rationality, and EFG-facing SPE semantics | partial | broad declaration inventory and non-flagship recovery |
| L-KUHN | `Languages/Kuhn.lean`, `Languages/Kuhn/**`, `Theorems/Kuhn.lean`, `Theorems/Kuhn/**` | 15 | Protocol representation theorem with language wrappers | validated core theorem and EFG surface | partial | inventory non-flagship generic and language-specific declarations |
| L-INFO | `Languages/InfoModel.lean`, `Languages/InfoModel/**` | 4 | `Protocol.Information` | validated in replacement architecture | partial | classify old simulation/semantic-form wrappers |
| L-MAID | `Languages/MAID.lean`, `Languages/MAID/**` | 14 | native language compiling to Protocol | validated by EXP-041/T3 | partial | broader refinement, recall, and Kuhn-facing declaration recovery |
| L-FOSG | `Languages/FOSG.lean`, `Languages/FOSG/**` | 24 | transparent Protocol execution/information specialization | validated by EXP-042/T4 | partial; 418/776 reviewed, 358 queued | [exact declaration ledger](coverage/L-FOSG-broad.md); Basic, History, Information, Strategy, Execution, external transition values, Native history/Kuhn, and reachable observation-model facts are classified; next the named FOSG-to-EFG serialization comparison; actual counterfactual reach, CFR, and ordinary continuation coefficients retain separate explicit gates |
| L-ROUND | `Languages/MultiRound.lean`, `Languages/MultiRound/**` | 15 | native language compiling to Protocol | provisional probe | partial | preserve previous actions and imperfect monitoring |
| L-INTR | `Languages/Intrinsic.lean`, `Languages/Intrinsic/**` | 8 | native branch only if it retains theorem-relevant data | assigned | not started | one theorem unavailable from bare Protocol |
| L-BRIDGE | `Languages/Bridges.lean`, `Languages/Bridges/**`, `Languages/Expressiveness.lean`, `Languages/Expressiveness/**` | 22 | named direct bridges; composition only when earned | named-bridge policy validated; T1, T3, and T4 complete | partial/retirement open | declaration accounting; add composition only after two live consumers earn it |
| L-OPEN | `Languages/OpenGame.lean`, `Languages/OpenGame/**` | 15 | `Frontier` | Frontier | not started | one compositional theorem and external semantic comparison |

### Mechanisms, auctions, and collective choice

| ID | Pinned scope | Files | Intended successor owner | Integration | Recovery | Next gate |
|---|---|---:|---|---|---|---|
| M-BAYES | `Mechanism/Bayesian.lean`, `Mechanism/Bayesian/**` | 12 | Bayesian data/equilibrium plus coordinated mechanism modules | validated split; F5/F6 complete | partial | revelation, welfare/participation, and information-design inventory |
| M-CONTRACT | `Mechanism/Contracts/**` | 1 | mechanism branch | assigned | not started | participation/incentive theorem with explicit outside option |
| M-FAIR | `Mechanism/FairDivision.lean`, finite indivisible files | 6 | finite mechanism/fair-division branch | assigned | not started | round-robin EF1 and one algorithmic allocation theorem |
| M-CAKE | divisible fair-division files | 6 | D11/`Analysis` or Frontier | deferred | out of scope | measurable/continuous probability decision |
| M-SOCIAL | `Mechanism/SocialChoice.lean`, `Mechanism/SocialChoice/**` | 9 | ranking/preference foundations plus coordinated domain | validated by Arrow | partial | May, median strategic compilation, Gibbard-Satterthwaite, Sen |
| M-AUCT | `Auctions/**` | 10 | finite auction/mechanism branch; continuous work behind D11 | sealed-bid, reserve, VCG, combinatorial, all-pay, exact natural knapsack search, real pivot-VCG knapsack, and repaired executable knapsack approximation validated | partial; accounted leaves 194/194 reviewed; knapsack is 33 adapted / 35 retired / 2 subsumed / 1 deferred | [basic auction ledger](coverage/M-AUCT-basic.md); [reserve Vickrey ledger](coverage/M-AUCT-reserve-vickrey.md); [VCG ledger](coverage/M-AUCT-vcg.md); [combinatorial ledger](coverage/M-AUCT-combinatorial.md); [all-pay ledger](coverage/M-AUCT-all-pay.md); [knapsack ledger](coverage/M-AUCT-knapsack.md); EXP-056/D27 closes the returned-allocation approximation gate, with exact Myerson payment behind M-BAYES/D11 |
| M-VOTE | `Voting/**` | 7 | coordinated voting branch | validated foundations | partial | delegation, liquid democracy, median, majority, power inventory |

### Potential consumers and parallel domains

| ID | Pinned scope | Files | Intended successor owner | Integration | Recovery | Next gate |
|---|---|---:|---|---|---|---|
| P-CONG | `Congestion/**` | 4 | thin domain over `Core.Potential` and `Core.RobustWelfare` | validated through Rosenthal and EXP-052/053/D24 | complete recovery; Basic/Rosenthal/AffinePoA/Examples 50/50 reviewed, no deferred rows | [Rosenthal ledger](coverage/P-CONG-rosenthal.md); [affine PoA ledger](coverage/P-CONG-affine-poa.md); [Pigou/Braess ledger](coverage/P-CONG-examples.md) |
| P-COAL | `Core/Coalition.lean`, `Cooperative/CoalitionalGame.lean`, `Cooperative/CoalitionalGame/**` | 10 | foundational Core objects, larger `Cooperative` root | validated foundation | partial | convex core, Bondareva, Banzhaf, cost of stability |
| P-MATCH | matching and `GaleShapley/**` files | 8 | native `Cooperative`/market-design branch | assigned | not started | stable perfect matching, then strategyproofness/rural hospitals |
| P-BARG | `Cooperative/Bargaining.lean` | 1 | native feasible-utility branch, Analysis as needed | assigned | not started | Nash solution affine invariance |

### Standalone theorem and mathematics support

| ID | Pinned scope | Files | Intended successor owner | Integration | Recovery | Next gate |
|---|---|---:|---|---|---|---|
| T-CE | `Theorems/CorrelatedEqExistence.lean` | 1 | `Analysis` plus topology-free bridges in `Core.Mixed` | validated by existing Nash boundary | complete; 6/6 reviewed | [exact ledger](coverage/T-CE-existence.md); existence factors through mixed Nash with no LP or duplicate boundedness layer |
| T-MIN | `Theorems/Minimax.lean` | 1 | `Core.ZeroSum` plus `Analysis.Minimax` | validated | partial inventory, flagship complete | exact declaration comparison |
| T-ZER | `Theorems/Zermelo.lean` | 1 | Protocol backward induction | validated substrate | partial | language-independent theorem plus any honest wrapper |
| T-TEST | predecessor theorem tests | 1 | owning domain tests/examples | assigned by theorem | not started | classify with their theorem families |
| MATH | pinned `Math/**` support tree | 56 | Mathlib first, then `GameTheoryMath` or canonical probability by live consumer | owner policy validated; EXP-049/D21 and EXP-053 | partial and demand-driven; finite online-learning 23/23 and finite-sum expectation 1/1 reviewed | [finite online-learning ledger](coverage/MATH-online-learning.md); [expectation ledger](coverage/MATH-probability-expectation.md); continue accounting by consumer, never wholesale port |

## Explicit exclusions and non-equivalences

- The rational finite frontend is not a general NFG language and does not by
  itself complete L-NFG.
- A direct two-bidder auction witness does not complete finite auction theory
  or Bayesian mechanism design.
- The Protocol and EFG-facing behavioral/mixed theorems complete frozen F3/T2,
  but not the broader generic Kuhn or EFG theorem inventories.
- T1's finite-horizon contingent-plan and Nash transfer does not by itself
  complete the EFG syntax, refinement, recall, or language-wrapper inventory.
- The EXP-035 nonconstant-payoff witness validates whole-policy rationality on
  the hostile finite EFG, not a general finite-EFG existence theorem.
- F8's finite stochastic signal-prefix law does not complete monitoring
  equilibrium, rank, or self-generation theory.
- F5/F6 close their recommendation-law and truthful-compiler promises; they do
  not complete revelation, information design, welfare, or participation.
- Rejecting generic transport/certificates does not prove named transfers.
- Arrow and Shapley validate their semantic homes; they do not complete social
  choice or cooperative game theory.
- Beyond-v1 mature and Frontier work is recorded separately and never raises
  pinned-v1 recovery status.
- EXP-050/D22 and EXP-051/D23 promote the active sibling branch's basic
  stochastic/uniform semantic waist and the mature discounted Shapley value
  slice as opt-in stable/Analysis roots. They account for no pinned-v1
  declaration; pinned stochastic rows remain in the L-ROUND review queue.

## Next ledger actions

1. Continue the exact FOSG queue through observation-model batches and named
   comparisons; generated rows remain `unreviewed` until manually classified.
2. Keep every broader family partial until all pinned declarations are
   classified, and update this file in the same commit as each status change.
