# Phase 0 architecture evidence

This document closes the evidence deliverables for RFC Phase 0. All source
observations refer to the ignored v1 snapshot at commit
`a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`; paths below are relative to
`reference/GameTheory-v1/`. No declaration in the snapshot is a dependency of
the rewrite.

## Frozen representative transfers

These are the four transfers that must survive the later vertical slices. A
name in quotation marks is a test label, not a frozen public declaration name.

| ID | Transfer and v1 evidence | Level | Native data actually used | Deliberately forgotten | Direct baseline and certificate evidence |
|---|---|---|---|---|---|
| T1 | Finite EFG strategic extraction: `EFGGame.toNFGGame_eu`, `toNFGGameDet_outcomeKernel`, and the generic mixed lift in `Concepts/Mixed/GameMorphism.lean` | strategic and incentive | tree evaluation, contingent pure plans, outcome kernel, utility evaluation, unilateral deviations | histories after evaluation, information sets, recall | `Languages/Bridges/EFG_NFG.lean`: direct EU theorem 8 nonblank lines; deterministic morphism 12. The snapshot has no named pure/mixed Nash transfer, so the later tests are explicitly “EFG strategic extraction pure Nash iff” and “mixed Nash iff”; neither may be credited before it exists. |
| T2 | Kuhn behavioral/mixed correspondence: `EFG.kuhn_behavioral_to_mixed_udist` and `EFG.kuhn_mixed_to_behavioral_udist` | protocol, then strategic outcome-law | behavioral and pure contingent plans, finite information/action carriers, tree height, reach mass/support factorization, perfect recall; mixed-to-behavioral additionally factors through step-mass invariance, support factorization, and player-local action posteriors | utilities for the core theorem; unreached fallback actions after the witness is chosen | The utility-law wrappers are 9 and 11 nonblank lines. The mixed-to-behavioral EFG adapter contains a 31-line semantic invocation plus a 98-line run/evaluation bridge. The direct native EFG theorem is the baseline; a certificate may not store its conclusion. |
| T3 | MAID to EFG: `maidToEFGAt_outcomeKernel`, `maidToEFGAt_udist`, and `maidToEFGAt_bisimulation` | protocol and strategic | topological order, node kernels, policies, assignment evaluation, explicit per-player strategy equivalence | MAID graph once evaluation and strategy correspondence are proved | In `Languages/Bridges/MAID_EFG.lean`, the direct outcome-law and utility-law proofs are 8 and 12 nonblank lines; the bisimulation is 20 and the morphism is 25. The complete bridge is 981 nonblank lines with a 46-file/15,903-line snapshot import closure, so only the small named laws count as reusable payload. |
| T4 | One-shot NFG embedding into FOSG: `NFG.NFGGame.toFOSG_udist_eq` and `toFOSG_morphism` | syntax through protocol to strategic | one transition, lifted actions, horizon bound one, terminal history utility | the source NFG presentation after the one-step run | In `Languages/Bridges/NFG_FOSG.lean`, the direct utility-law proof is 21 nonblank lines and the morphism wrapper is 9; the file is 374 nonblank lines with a 31-file/11,031-line closure. This is the transformation/compilation commuting test. |

T1's baselines are theorem-specific equalities rather than a second strategic
semantics. T2 is intentionally asymmetric: the expensive Kuhn proof is audited,
not reimplemented. Phase 0 froze both the T3/T4 direct theorem and predecessor
certificate wrapper so Phase 3 could measure whether composition earned the
wrapper. D7 and the completed T3/T4 slices retained the direct theorems and
retired the wrappers: no live composition consumer justified them.

### Kuhn dependency audit

The v1 mixed-to-behavioral hierarchy makes four obligations visible:

1. `StepMassInvariant` and `StepSupportFactorization` control reach weights.
2. `ActionPosteriorLocal` says a player's conditional action law depends only
   on that player's information state.
3. Perfect recall supplies trace-local player recall, but the generic
   `kuhn_mixed_to_behavioral_perfectRecall_of_psar` still states global
   per-step action recall separately.
4. The EFG frontend proves the semantic conditions for reachable compiled
   traces and then bridges run equality back to tree evaluation.

Accordingly, a later adequacy interface must expose reach/support preservation
and player-local posterior information. “Perfect recall” alone is not an
adequate certificate, and an interface field containing the desired outcome
equality receives no credit.

## Frozen flagship theorem list

| ID | Existing declaration | Why it is flagship | v1 disposition |
|---|---|---|---|
| F1 | `KernelGame.mixed_nash_exists` in `Concepts/Existence/NashExistenceMixed.lean` | finite mixed Nash existence and the PMF/simplex/analysis boundary | Harvest after D1/D2; Analysis layer only. |
| F2 | `KernelGame.timeAverage_isεCCE_of_regret_le` in `Concepts/Learning/NoRegretToCCE.lean` | learning-to-CCE reuse of the common deviation logic | Stable static consumer after Phase 2. |
| F3 | `EFG.kuhn_behavioral_to_mixed_udist` and `EFG.kuhn_mixed_to_behavioral_udist` in `Languages/EFG/Kuhn.lean` | both directions of Kuhn with the real locality and reachability obligations | Sequential gate; preserve native proof semantics. |
| F4 | `EFG.oneShotDeviation_iff_spe` in `Languages/EFG/OneShotDeviation.lean` | sequential rationality/backward-induction representative | Sequential gate; never collapse to static `GameForm`. |
| F5 | `BayesNash.outcomeLaw_bayesCorrelatedEq` in `Mechanism/Bayesian/BayesCorrelatedEq.lean` | type-dependent obedience and Bayesian outcome-law transfer | Provisional. The snapshot contains no occurrence of “interim”; Phase 2 must add a genuinely interim conditional-deviation test rather than rename the ex-ante theorem. |
| F6 | `Mechanism.isIC_implies_truthful_bayesNash` in `Mechanism/Bayesian/MechanismDesign.lean` | truthfulness/incentive-compatibility representative | Stable coordinated mechanism layer over shared deviations. |
| F7 | `KernelGame.discounted_folk_theorem_approx` in `Concepts/Welfare/FolkTheorem/Main.lean` | discounted repeated-game flagship | Retain deterministic/stagewise theorem; it does not justify an infinite-path probability core. |
| F8 | `KernelGame.PublicMonitoring.signalHistoryDist_succ_eq_bind_first` in `Concepts/Repeated/Monitoring.lean` | finite-prefix stochastic monitoring law | Stable finite-prefix probability; infinite path laws remain outside v1. |

## Required domain dispositions

| Domain | Concrete v1 probe | Data used and forgotten | v1 disposition and next hostile probe |
|---|---|---|---|
| Mechanism design | `Mechanism.isIC_implies_truthful_bayesNash` | reports, allocation/outcome rule, type-dependent utility, unilateral report deviations; forgets syntax after induced play | Stable coordinated layer over forms/preferences. Re-express this theorem through the Phase 2 local deviation predicate. |
| Bayesian/incomplete information | `BayesNash.outcomeLaw_bayesCorrelatedEq` | common prior, types, actions, type-dependent obedience maps; forgets signals after forming the recommendation law | Provisional native branch. The Phase 2 target “interim deviation iff conditional best response” is mandatory because v1 only exposes ex-ante `BayesNash`. |
| Auctions | `GameTheory.vickrey_truthful_isNash`; continuous audit: `SingleParameterMechanism.payment_formula_of_isDSIC_of_zeroNormalized` | finite bids/outcomes for Vickrey; real reports, continuity, and integration for Myerson | Finite/discrete auctions stable. Continuous Myerson material belongs behind the D11/Analysis boundary and must not enlarge the core probability API. |
| Voting/social choice | `GameTheory.May.may_theorem` and `GameTheory.medianIdeal_strategyproof` | rules and preference profiles; only the strategyproof result needs deviations | Stable coordinated branch. Keep rule/property theorems outside strategic form; compile only `medianIdeal_strategyproof` if Phase 2 gains reuse. |
| Knowledge/epistemic games | `GameTheory.aumann_full_agreement` | finite states, partitions, common prior/posteriors, common knowledge; no action profile | Provisional separate information consumer. Phase 3 must show whether its surviving `InfoState` can state the theorem without reconstructing partitions. |
| Potential games | `KernelGame.IsExactPotential.nash_exists`; concrete witness `CongestionGame.isExactPotential` | payoff differences, potential, finite profiles; forgets outcome histories | Stable static-form theory. Harvest immediately after Phase 2's Nash predicate is fixed. |
| Evolutionary stability | `IsESS.isNash_symmetric` | two-population payoff table and real inequalities; no dynamic population process | Provisional separate static branch. Keep replicator/topological dynamics out until a theorem needs them. |
| Repeated games | `KernelGame.discounted_folk_theorem_approx` and `PublicMonitoring.signalHistoryDist_succ_eq_bind_first` | stage game, discounting, recursive strategies, finite signal histories | Stable recursive and finite-prefix theory. Infinite stochastic path laws remain excluded by D11. |
| Sequential rationality | `EFG.oneShotDeviation_iff_spe` and `EFG.IsPerfectBayesianEq.sequentiallyRational` | histories, subtrees, information sets, conditional beliefs, reachability | Stable target of native protocol/information semantics. It must not import from a static compilation to recover lost histories. |
| Cooperative games, matching, bargaining | `MatchingMarket.stable_matching_perfect`, `CoalGame.shapleyValue_isCore_of_isConvex`, `BargainingProblem.nashSolution_affine_invariant` | coalitions, matchings, feasible utility sets; no strategic profile | Parallel stable branches. No artificial `GameForm` compilation. |

### Coverage of the remaining v1 topical families

This maps every current top-level source family into the disposition above or
records its separate boundary.

| v1 family | Representative declaration | Disposition |
|---|---|---|
| `Core`, static equilibrium, dominance, correlation, mixed games | `GameForm.IsNashFor`, `KernelGame.IsCorrelatedEq_iff_IsCorrelatedEqFor_eu` | Rebuild once at form/preference/deviation level in Phases 1–2; do not port v1 wrappers as parallel definitions. |
| Learning and communication | `timeAverage_isεCCE_of_regret_le`, `CheapTalkExtension.babbling_nash` | Stable consumers of the static core after Phase 2. |
| Congestion | `CongestionGame.nash_exists` | Stable domain wrapper over potential games; harvest with attribution after the potential gate. |
| NFG | `NFGGame.toKernelGame`, `IsNashMixed` | Finite frontend/compilation source. `IsNashPure` is evidence of duplicate logic and is not copied. |
| EFG, FOSG, MAID, intrinsic and multi-round languages | the T2–T4 declarations | Native protocol branches through Phase 3; only named strategic projections target `GameForm`. |
| Open games | `OpenGame.IsEquilibriumAt`, `isEquilibriumIn_iff_efgIsNash` | Frontier/provisional native compositional language. Its carried equilibrium predicate is not a shared solution concept. |
| Expressiveness and transport | `Languages.Expressiveness.utilityDistributionEquivalent_trans`, `GameForm.Transport.comp` | Evidence only until two Phase 3 transfers actually compose; no initial certificate hierarchy. |
| Fair division | `Indivisible.roundRobinRule_isEF1`; measurable `MeasureInstance.envyFree_exists` | Indivisible finite results form a stable parallel mechanism branch. Measurable cake-cutting results live in Analysis/D11, not Core. |
| Standalone theorems | `KernelGame.correlatedEq_exists`, `KernelGame.von_neumann_minimax` | Analysis layer; harvest only through the chosen finite-law/simplex bridge. |
| Voting | `DelegationProfile.resolves_total_iff_acyclic` | Stable parallel voting branch; it needs graph/relation infrastructure, not strategic semantics. |

## Measured v1 hub baseline

The complete pinned snapshot contains the `GameTheory/` library corpus and its
local `Math/` support corpus. Hub-use counts intentionally scan only
`GameTheory/`, where the game architecture lives. “Mentions” means a whole-word
match in authored file text, including comments and strings; transport-token
counts instead strip nested comments, line comments, and strings. Blank lines
are excluded where “nonblank” is stated.

| Measure | Result |
|---|---:|
| Complete snapshot Lean files / nonblank lines | 436 / 117,094 |
| `GameTheory/` Lean files / nonblank lines | 380 / 99,301 |
| `Math/` Lean files / nonblank lines | 56 / 17,793 |
| `GameTheory/` files textually mentioning `KernelGame` | 187 (49.2%) |
| `GameTheory/` files textually mentioning `GameForm` | 38 (10.0%) |
| `GameTheory/Languages/` files textually mentioning `KernelGame` | 47 |
| `GameForm.lean` / `KernelGame.lean` | 259 / 197 nonblank lines |
| `KernelGame.lean` snapshot import closure | 12 files / 4,934 nonblank lines |
| Language bridge files / nonblank lines | 14 / 6,243 |
| Language files with code-level `cast` or `Eq.ndrec` / occurrences | 12 / 84 |
| Generic `Concepts/Transport` files / nonblank lines | 15 / 3,210 |
| Five `GameMorphism` implementation/consumer files / nonblank lines | 5 / 1,015 |
| Bridge morphism definitions / bisimulation definitions | 4 / 7 |
| Language uses of `GameForm.Transport.comp` / `compSameMiddle` / `compOfHom` | 0 |
| Language uses of `KernelGame.Morphism`, `Simulation`, or `Bisimulation` composition | 3, all in expressiveness relations |

Reproduce the corpus, hub, bridge, transport, import-closure, and declaration
line measurements with the checked-in audit:

```text
pwsh -NoProfile -File scripts/phase0-audit.ps1 -VerifyExpected
```

The implementation and expected values are in
[`scripts/phase0-audit.ps1`](../scripts/phase0-audit.ps1). A mismatch makes the
command fail.

The 84 transport tokens (after stripping nested comments, line comments, and
strings) are concentrated: 23 in `Bridges/OpenGame_MAID.lean`, 17 in
`EFG/CompileObsFacts.lean`, 16 in `Bridges/FOSG/AugmentedEFG.lean`, and 14 in
`MultiRound/CompileObsLinAdequacy.lean`. Those four files account for 70/84
(83.3%). The new source-level no-user-visible-transport rule is therefore a measurable
improvement target, not a cosmetic preference.

The hub also did not eliminate duplicate public logical surfaces:
`NFGGame.IsNashPure` restates unilateral-deviation Nash, while
`KernelGame.IsNash`, `GameForm.IsNashFor`, `BayesianGame.BayesNash`, and the
open-game-carried `IsEquilibriumIn` expose different mixtures of duplicates,
wrappers, and genuinely native semantics. In particular, v1's
`BayesianGame.BayesNash` is an `Iff.rfl` wrapper around ex-ante strategic Nash,
whereas open-game equilibrium is native data and cannot honestly be replaced
by the same predicate.

The snapshot has no git history, so Phase 0 cannot measure change
concentration. This is recorded as missing evidence rather than inferred from
file size. D0 remains provisional until the Phase 3 greenfield prototype and
direct bridges provide measured change/build evidence.

## Provisional D0 result

D0 is narrowed by semantic level:

- **Static outcome-law and incentive level:** select the hybrid candidate.
  Share a utility-free `GameForm`, preferences, evaluation, and the one local
  deviation predicate. Do not reproduce the utility-bound universal hub.
- **Protocol and information level:** select coordinated native branches.
  EFG, MAID, FOSG, and other languages retain histories, execution, and
  information data. A compilation exists only for T1–T4 or another named
  theorem added by a later decision record.
- **Certificate level:** no generic hierarchy is selected in Phase 0. Phase 3
  may introduce one named adequacy record only if it beats the direct baseline
  below on an actual consumer or composition. This defers D7 as required.

The universal hub is rejected as the default because its utility-bearing core
touches 49.2% of v1 files, does not retain sequential information, and coexists
with duplicate equilibrium surfaces. Coordinated-only branches are rejected at
the static level because NFG, Bayesian, and other static consumers otherwise
restate the same unilateral-deviation logic. They remain the correct choice at
protocol level, where the native data is observably different.

## Bridge and certificate complexity budget

Every Phase 3 candidate is measured against its direct theorem-specific bridge.

1. Shared semantic objects have zero dummy fields and zero language-specific
   escape fields.
2. A downstream transfer has zero explicit `cast`/`Eq.ndrec`; designated
   transport implementations are reported separately.
3. A certificate's fields state independently meaningful preservation facts,
   never the final transfer theorem.
4. Certificate declaration plus construction is at most twice the nonblank
   lines of its direct baseline and at most 25% of the native semantics it
   summarizes. Exceeding either bound selects the direct bridge unless two
   downstream theorems eliminate more proof than the excess.
5. A reusable certificate level needs either two concrete downstream consumers
   or one checked composition of two same-level transfers. One consumer gets a
   direct named theorem.
6. A certificate consumer must reuse the compiler's named evaluation or law
   correctness theorem; reproving that equality scores zero reuse.
7. The certificate path may be at most 25% slower to elaborate/build than the
   direct path, matching the RFC performance threshold.
8. T1's eventual pure-Nash transfer target is budgeted at 15 nonblank proof
   lines and its mixed lift at 25 after generic mixed-extension lemmas. A miss
   reopens the chosen static transport API before theorem harvesting.

These are kill limits, not goals to fill. Phase 3 records actual proof lines,
import closures, build time ratios, reusable evaluation facts, and composition
before D0 becomes final.

## Phase gate validation

Run from the repository root on 2026-07-22:

```text
lake update
lake env lean --version
```

`lake update` completed with all nine package checkouts at their manifest
revisions and no cache files to download. Lean reported version 4.32.0, commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`. A local audit also checked every
relative Markdown link, every required D0 decision-record field, all nine
checkout revisions, and trailing whitespace. No `GameTheory/` source directory
was created: Phase 0 is an evidence gate, and Phase 1 has not started.
