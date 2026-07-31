# Architecture experiment log

This is the lightweight evidence ledger for the rewrite. The RFC states the
current design; this file preserves what was actually tried and observed.

Use one entry per experiment. Keep it roughly 5–15 lines and link to code,
decision records, or bulky output. Start with one file; split it only when it
becomes difficult to scan.

## Index

| ID | Date | RFC decision | Question/slice | Outcome | Artifacts |
|---|---|---|---|---|---|
| EXP-001 | 2026-07-22 | D0 / Phase 0 | Which semantic layers earn shared infrastructure in v1? | Narrows | [`Phase0ArchitectureEvidence.md`](Phase0ArchitectureEvidence.md); [`decisions/D0-semantic-architecture.md`](decisions/D0-semantic-architecture.md); [`phase0-audit.ps1`](../scripts/phase0-audit.ps1) |
| EXP-002 | 2026-07-22 | D1 / Phase 1 | Indexed signature parameter or bundled signature field? | Narrows | [`decisions/D1-signature-ownership.md`](decisions/D1-signature-ownership.md); `GameTheory/Experimental/Phase1/D1/` |
| EXP-003 | 2026-07-22 | D2 / Phase 1 | PMF-with-finite-support or normalized `Finsupp`? | Narrows | [`decisions/D2-finite-law-representation.md`](decisions/D2-finite-law-representation.md); `GameTheory/Experimental/Phase1/D2/` |
| EXP-004 | 2026-07-23 | D1/D2 / Phase 1 review | Do the original metrics and simplex slice survive adversarial review? | Narrows | [`Phase1CoreCompetition.md`](Phase1CoreCompetition.md); [`phase1-audit.ps1`](../scripts/phase1-audit.ps1) |
| EXP-005 | 2026-07-26 | D5 / Phase 2 | Can one local, law-linear deviation predicate express Nash, mixed Nash, CCE, CE, and strong Nash without losing locality? | Supports | [`decisions/D5-deviation-and-equilibrium.md`](decisions/D5-deviation-and-equilibrium.md); `GameTheory/Core/`; `GameTheory/Tests/Locality.lean` |
| EXP-006 | 2026-07-26 | D4/D9 / Phase 2 | Do separated form/preference/utility and unbundled finiteness survive the incentive slice without duplicate predicates? | Narrows | [`decisions/D4-form-preference-utility.md`](decisions/D4-form-preference-utility.md); [`decisions/D9-finiteness-capabilities.md`](decisions/D9-finiteness-capabilities.md) |
| EXP-007 | 2026-07-26 | D10 / Phase 2 | Can the rational finite-table frontend prove its enumeration correct against the semantic Nash predicate under a clean dependency budget? | Supports | [`decisions/D10-executable-frontend.md`](decisions/D10-executable-frontend.md); `GameTheory/Finite/`; `GameTheory/Examples/Classic.lean` |
| EXP-008 | 2026-07-26 | D5 / Phase 0 F5 | Does an interim, type-dependent Bayesian deviation fit the shared local-deviation interface? | Supports | `GameTheory/Experimental/Phase2/BayesianProbe.lean` |
| EXP-009 | 2026-07-26 | D6/D7 / Phase 3 input | Does the open-game context hint at a better sequential interface, and is its carried equilibrium derivable? | Narrows | read-only audit of the pinned `Languages/OpenGame/` and `Bridges/OpenGame_EFG.lean` |
| EXP-010 | 2026-07-27 | D6 / Phase 3 | Can a general-state execution protocol express terminal play and chance without an impossible total chooser or dummy probability data? | Supports | `GameTheory/Protocol/Execution.lean`; `GameTheory/Tests/Execution.lean` |
| EXP-011 | 2026-07-27 | D6 / Phase 3 | Does a separate information layer keep strategies information-local by construction? | Supports | `GameTheory/Protocol/Information.lean`; `GameTheory/Tests/Information.lean` |
| EXP-012 | 2026-07-27 | D6 / Phase 3 | Finite-first or general-state-first execution for v1? | Decides D6 | [`decisions/D6-execution-and-information.md`](decisions/D6-execution-and-information.md); `GameTheory/Tests/Candidates.lean`; `GameTheory/Tests/Simultaneous.lean` |
| EXP-013 | 2026-07-27 | D6/D7 / Phase 3 | Does an assessment plus continuation express sequential rationality and one-shot deviations without a carried equilibrium? | Supports | `GameTheory/Protocol/Assessment.lean`; `GameTheory/Tests/Assessment.lean` |
| EXP-014 | 2026-07-28 | D6 / Phase 3 | Can an influence diagram and a multi-round simultaneous game share one execution base without dummy data or escape fields? | Supports | `GameTheory/Languages/MAID.lean`; `GameTheory/Languages/Rounds.lean` |
| EXP-015 | 2026-07-28 | D7/D0 / Phase 3 | Do named adequacy certificates beat their bespoke direct bridges on the Phase 0 budget? | Rejects D7 | [`decisions/D7-certificate-stratification.md`](decisions/D7-certificate-stratification.md); `GameTheory/Tests/Transfer.lean` |
| EXP-016 | 2026-07-28 | D6 / Kuhn prerequisite | Can a history-indexed run law carry information-local policies without becoming a second semantics? | Supports | `GameTheory/Protocol/History.lean`; `GameTheory/Tests/History.lean` |
| EXP-017 | 2026-07-29 | D6 / behavioral-mixed equivalence | Where can a player's randomness live, and do the two placements agree? | Supports | `GameTheory/Protocol/Randomized.lean`; `GameTheory/Protocol/Information.lean`; `GameTheory/Tests/Randomized.lean` |
| EXP-018 | 2026-07-29 | D6 / the recall direction | Does the direction that recovers a behavioral profile from a mixed one fit the same layer, and what does conditioning cost? | Supports | `GameTheory/Probability/FinDist.lean`; `GameTheory/Protocol/Information.lean` |
| EXP-019 | 2026-07-29 | D7 / the recall direction | Can the recall direction be restated over reach-mass conditions, stated transport-free, with recall demoted to a sufficient condition? | Narrows; closes D7 again | `GameTheory/Experimental/Phase4/ReachMassStatements.lean`; [`decisions/D7-certificate-stratification.md`](decisions/D7-certificate-stratification.md) |
| EXP-020 | 2026-07-29 | D1 / Phase 4 | Should carrier-bearing structures keep storing their carriers, now that the reducibility cost has been paid across a whole layer? | Decides D1 | [`decisions/D1-signature-ownership.md`](decisions/D1-signature-ownership.md); `GameTheory/Experimental/Phase4/D1/` |
| EXP-021 | 2026-07-29 | D6 / Phase 3 close-out | Does the one-shot deviation principle hold on the accepted sequential interface, and does the certificate already in hand carry it? | Supports | `GameTheory/Protocol/Backward.lean`; `GameTheory/Tests/OneShot.lean` |
| EXP-022 | 2026-07-29 | D12 / Phase 4 | What does an existence theorem at the static layer cost in dependencies, and where should the boundary be drawn? | Refutes the planned route; redirects | measurement only; no code |
| EXP-024 | 2026-07-29 | D4 / Phase 5 | Does the core's preference vocabulary serve a theorem with no probability in it, or was it quietly about lotteries? | Finds a defect; repaired | `GameTheory/Core/Preference.lean`; `GameTheory/Core/SocialChoice.lean`; `GameTheory/Examples/Voting.lean` |
| EXP-023 | 2026-07-29 | D12 / Phase 4 | What does taking the fixed-point primitive from outside Mathlib cost, and does the boundary hold once it is taken? | Supports; reopens general existence | `lakefile.lean`; `lake-manifest.json`; [`decisions/D12-dependency-boundaries.md`](decisions/D12-dependency-boundaries.md) |
| EXP-025 | 2026-07-30 | D6 / Phase 5 close-out | Can information-local policies compile to the static core, with randomization and one-shot deviations commuting through the existing run laws? | Supports; narrows SPE remainder | `GameTheory/Protocol/Strategic.lean`; `GameTheory/Protocol/Assessment.lean`; `GameTheory/Tests/Strategic.lean`; `GameTheory/Tests/Assessment.lean` |
| EXP-026 | 2026-07-30 | D10/D12 / finite certificates | Can an external LP verifier replace hand-expanded rational proofs without widening the trusted base or the audited finite layer? | Narrows; trust passes, adoption does not | [`experiments/EXP-026.md`](experiments/EXP-026.md); [`decisions/D13-lp-certificates.md`](decisions/D13-lp-certificates.md) |
| EXP-027 | 2026-07-30 | D4 / Phase 5 | Does Arrow's pivotal-voter proof work through the accepted weak-ranking vocabulary without a second preference API? | Supports; repairs an import-closure leak | `GameTheory/Core/Rank.lean`; `GameTheory/Core/Arrow.lean`; `GameTheory/Tests/Arrow.lean` |
| EXP-028 | 2026-07-30 | D0 / Phase 5 | Is the parallel `CoalitionalGame` primitive rich enough for the Shapley value and its four-axiom characterization? | Supports the parallel primitive | `GameTheory/Core/Shapley.lean`; `GameTheory/Tests/Shapley.lean` |
| EXP-029 | 2026-07-30 | D0/D5/D6 / Phase 5 | Does the EXP-008 interim theorem survive as stable API and compile through the accepted `InformationModel` without duplicating equilibrium semantics? | Supports; fixes the static/information split | `GameTheory/Core/Bayesian*.lean`; `GameTheory/Languages/Bayesian.lean`; `GameTheory/Tests/Bayesian.lean` |
| EXP-030 | 2026-07-30 | D0/D2/D6/D11/D12 / Phase 5 | Can repeated play reuse Protocol for finite prefixes and ordinary `IsNash` for discounting without inventing an infinite `FinDist` path law? | Supports; narrows public histories to lists | `GameTheory/Repeated/*.lean`; `GameTheory/Tests/Repeated.lean` |
| EXP-031 | 2026-07-30 | D11/D12 / Phase 5 | Does the full discounted folk theorem belong in stable Repeated, under Analysis, or behind a new repeated-analysis bridge? | Supports one-way Analysis bridge | [`decisions/D12-dependency-boundaries.md`](decisions/D12-dependency-boundaries.md); `GameTheory/Analysis/Repeated/`; `GameTheoryMath/` |
| EXP-032 | 2026-07-30 | D6/D12 / Phase 5 | Where should Kreps-Wilson limit consistency live when its topology is on Protocol policies and beliefs? | Supports one-way Analysis bridge; narrows beliefs to reachable sites | [`decisions/D12-dependency-boundaries.md`](decisions/D12-dependency-boundaries.md); `GameTheory/Protocol/BehavioralAssessment.lean`; `GameTheory/Analysis/Protocol/` |
| EXP-033 | 2026-07-30 | D6/D12 / Phase 5 | Can a finite EFG adapter instantiate behavioral assessments and sequential consistency without importing solution concepts into syntax or duplicating Protocol semantics? | Supports transparent specialization; corrects the assessment interface | `GameTheory/Languages/EFG.lean`; `GameTheory/Analysis/Protocol/EFG.lean`; `GameTheory/Analysis/Protocol/EFGTest.lean` |
| EXP-034 | 2026-07-30 | D6/D12 / finite EFG theorem | Can the hostile hidden-information EFG carry an actual sequential-equilibrium witness rather than only the proposition? | Supports; concrete consistency and equilibrium witness | `GameTheory/Protocol/BehavioralAssessment.lean`; `GameTheory/Analysis/Protocol/Sequential.lean`; `GameTheory/Analysis/Protocol/EFGTest.lean` |
| EXP-035 | 2026-07-30 | D6/D12 / finite EFG theorem | Does the hostile EFG remain sequentially rational under a nonconstant hidden-state payoff? | Supports; completes W1-A | `GameTheory/Analysis/Protocol/EFGTest.lean` |
| EXP-036 | 2026-07-30 | D6 / sequential theory | Does well-founded information-local one-shot optimality characterize SPE, including off-path histories? | Supports; completes W1-B | `GameTheory/Protocol/SubgamePerfect.lean`; `GameTheory/Tests/SubgamePerfect.lean` |
| EXP-037 | 2026-07-30 | D6/D14 / MAID gate | Can incomparable MAID decisions compile without asserting a false order? | Supports frontier batching; unlocks general MAID work | [`decisions/D14-general-maid.md`](decisions/D14-general-maid.md); `GameTheory/Experimental/PostArchitecture/MAIDIncomparable.lean` |
| EXP-038 | 2026-07-30 | D6/D14 / T3 strategy gate | Does per-player frontier batching preserve locality when one player owns incomparable decisions? | Refutes combined-view policies; narrows D14 | [`decisions/D14-general-maid.md`](decisions/D14-general-maid.md); `GameTheory/Experimental/PostArchitecture/MAIDSameOwner.lean` |
| EXP-039 | 2026-07-30 | D9/D14 / general MAID substrate | Can the pinned finite-DAG mathematics be recovered without storing finiteness in semantic data or tying it to `Fin n`? | Supports; generalizes the pinned DAG proof | `GameTheoryMath/DAG.lean`; `GameTheory/Experimental/PostArchitecture/DAGDiamond.lean` |
| EXP-040 | 2026-07-30 | D2/D9/D14 / typed MAID semantics | Can heterogeneous site-local MAID semantics evaluate unresolved frontiers without dependent transport or stored finite capabilities? | Supports; promoted after EXP-041 | `GameTheory/Languages/MAID/Basic.lean`; `GameTheory/Experimental/PostArchitecture/TypedMAIDTest.lean`; [`decisions/D14-general-maid.md`](decisions/D14-general-maid.md) |
| EXP-041 | 2026-07-30 | D6/D14 / T3 serialization | Can an explicit topological order compile the typed MAID to an EFG without exposing serialized incomparable decisions? | Supports; native frontier, serialized, and actual compiled-EFG assignment laws are equal for arbitrary finite typed diagrams | `GameTheory/Languages/MAID/{ToEFG,Order,FrontierEquivalence}.lean`; [`decisions/D14-general-maid.md`](decisions/D14-general-maid.md) |
| EXP-042 | 2026-07-30 | D0/D4/D6 / T4 | Can a one-shot NFG compile through FOSG and the actual Protocol history runner with exact outcome and utility laws? | Supports; closes T4 | [`decisions/D15-nfg-fosg.md`](decisions/D15-nfg-fosg.md); `GameTheory/Languages/{NFG,FOSG,Bridges/NFGFOSG}.lean` |
| EXP-043 | 2026-07-30 | D0 / knowledge ownership | Is Protocol information already an epistemic partition, or does Aumann agreement need a separate branch? | Refutes Protocol ownership; decides D16 | [`decisions/D16-epistemic-ownership.md`](decisions/D16-epistemic-ownership.md); `GameTheory/Epistemic/`; `GameTheory/Experimental/PostArchitecture/KnowledgeOwnership.lean` |
| EXP-044 | 2026-07-30 | D0 / evolutionary ownership | Is ESS static Core semantics or part of an analytic dynamics package? | Supports separate static branch; decides D17 | [`decisions/D17-evolutionary-ownership.md`](decisions/D17-evolutionary-ownership.md); `GameTheory/Evolutionary/`; `GameTheory/Experimental/PostArchitecture/EvolutionaryOwnership.lean` |
| EXP-045 | 2026-07-30 | D8 / Wave 1 close-out | What is the smallest consumer-backed transformation API that closes reindexing, relabeling, mixed lifting, Nash, and CE transport? | Supports concrete equivalences; decides D8 | [`decisions/D8-minimal-transformations.md`](decisions/D8-minimal-transformations.md); `GameTheory/Experimental/PostArchitecture/D8Transformations.lean` |
| EXP-046 | 2026-07-30 | D0/D5/D6 / communication ownership | Is observable pre-play cheap talk a static `GameForm` construction, or must even the babbling theorem use Protocol timing? | Supports static ownership; decides D18; promoted | [`decisions/D18-communication-ownership.md`](decisions/D18-communication-ownership.md); `GameTheory/Experimental/PostArchitecture/CheapTalk.lean`; `GameTheory/Core/CheapTalk.lean`; `GameTheory/Examples/CheapTalk.lean` |
| EXP-047 | 2026-07-30 | D8/D18 / public randomization | Does mixed play of the static cheap-talk extension induce a base correlated equilibrium without Protocol timing or a second equilibrium predicate? | Supports static bridge; decides D19; promoted | [`decisions/D19-cheap-talk-public-randomization.md`](decisions/D19-cheap-talk-public-randomization.md); `GameTheory/Experimental/PostArchitecture/CheapTalkPublicRandomness.lean`; `GameTheory/Core/CheapTalkRandomization.lean` |
| EXP-048 | 2026-07-30 | D16/D18 / Electronic Mail ownership | Do the finite Electronic Mail theorems integrate as a static Bayesian/Epistemic example, or do their message rounds require Protocol execution? | Supports static Examples bridge; decides D20; promoted | [`decisions/D20-electronic-mail-ownership.md`](decisions/D20-electronic-mail-ownership.md); `GameTheory/Experimental/PostArchitecture/ElectronicMail.lean`; `GameTheory/Examples/ElectronicMail.lean` |

## Entry template

### EXP-NNN: Short title

- **Date / revision:** YYYY-MM-DD, Git revision or working-tree note
- **Decision / question:** D?, and the claim being tested
- **Representative slice:** the smallest hostile example used
- **Evidence:** exact files, commands, measurements, or linked logs
- **Observation:** what happened, including unexpected behavior
- **Outcome:** supports / refutes / narrows / inconclusive
- **Next action:** decision record, follow-up experiment, or no change

Add the corresponding one-line index row when completing the entry. Preserve
failed and inconclusive runs; a later experiment may supersede their conclusion
but should not erase their evidence.

### EXP-001: Semantic architecture baseline and scope inventory

- **Date / revision:** 2026-07-22, initial uncommitted repository scaffold
- **Decision / question:** D0 and Phase 0; whether the v1 evidence supports a universal hub, coordinated branches, or a stratified hybrid at each semantic level
- **Representative slice:** four named cross-representation transfers, a frozen cross-domain flagship list, and one concrete probe for every proposed v1 domain
- **Evidence:** pinned `reference/GameTheory-v1/` snapshot at commit `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`; run `pwsh -NoProfile -File scripts/phase0-audit.ps1 -VerifyExpected`; interpretation and direct baselines are in [`Phase0ArchitectureEvidence.md`](Phase0ArchitectureEvidence.md)
- **Observation:** the complete snapshot is 436 Lean files/117,094 nonblank lines; its `GameTheory/` corpus is 380/99,301 and `Math/` is 56/17,793. Authored text in 187/380 `GameTheory/` files mentions the utility-bearing hub, including 47 language files. There are 6,243 nonblank bridge lines and 84 code-level language `cast`/`Eq.ndrec` tokens after comments and strings are stripped. Generic transport has no language-level `Transport.comp` consumer. Kuhn mixed-to-behavioral requires reach/support and posterior-locality facts beyond perfect recall. Historical change concentration is unmeasurable because the pinned archive has no git history.
- **Outcome:** narrows — share utility-free static forms and deviation logic; retain coordinated native protocol/information branches; withhold a generic certificate hierarchy pending Phase 3 composition and cost measurements
- **Next action:** run Phase 1's D1/D2 miniature competition under the explicit bridge/certificate budget in [`decisions/D0-semantic-architecture.md`](decisions/D0-semantic-architecture.md)

### EXP-002: Signature ownership miniature

- **Date / revision:** 2026-07-22, Phase 1 working tree based on `e727659`
- **Decision / question:** D1; whether indexing forms by an external signature materially reduces transport burden relative to storing the same signature as a field
- **Representative slice:** two forms sharing one signature, unilateral update, player reindexing, outcome relabeling, product, mixed extension, and six heterogeneous form-hom compositions
- **Evidence:** `pwsh -NoProfile -File scripts/phase1-audit.ps1 -VerifyExpected -Time`; `lake build GameTheory.Experimental.Phase1.D1.Stress GameTheory.Experimental.Phase1.D2.Interop`; source under `GameTheory/Experimental/Phase1/D1/`
- **Observation:** the corrected regex includes `▸` and `Eq.rec`. Raw core counts are 2/2 indexed/bundled; subtracting each candidate's one allowed profile transport and adding its downstream stress namespace gives 1/3. Association proofs are 6/5 lines. The profiled six-composition declarations took 23.057/11.154 ms in one warm run. Indexed reuse takes `F G : Form sig` and one profile directly; bundled reuse needs a signature equality and two `▸` transports. The bundled form also has a higher, non-inferable universe boundary. Reindexed compiler adequacy is `rfl` for both. Because the explicit token baseline is below ten and indexed signatures did not materially reduce it, D1's rejection rule applies; its longer heterogeneous theorem signature is additional negative evidence.
- **Outcome:** narrows — provisionally select the bundled-signature form, with strategy and outcome still owned by the stored signature; do not freeze it before Phase 2 downstream usability tests
- **Next action:** use the provisional bundled form in Phase 2, then run the named transformation trial: nested operations, `e`/`e.symm` reindex round trip, and equivalence lifting through mixed extension

### EXP-003: Finite-law representation miniature

- **Date / revision:** 2026-07-22, Phase 1 working tree based on `e727659`
- **Decision / question:** D2; whether a finite-support `PMF` subtype or normalized `Finsupp` gives the better semantic and Analysis boundary
- **Representative slice:** pure/map/bind/product and laws, real expectation and bind, support, dependent finite products, PMF conversion, a nontrivial finite-support law on `Nat`, and a finite-carrier `stdSimplex` round trip preserving pure/product/expectation/affine mixture
- **Evidence:** `pwsh -NoProfile -File scripts/phase1-audit.ps1 -VerifyExpected -Time`; `lake build GameTheory.Experimental.Phase1.D1.Stress GameTheory.Experimental.Phase1.D2.Interop`; source under `GameTheory/Experimental/Phase1/D2/`; v1 proof ideas attributed in candidate A
- **Observation:** after review-strengthening, the PMF/Finsupp cores are 345/221 nonblank lines; their expectation-bind proofs are 52/19 lines and simplex equivalences 14/12. PMF uses 24 `toReal`, 41 `ENNReal`, 3 transport, and 5 classical/noncomputable tokens; Finsupp uses 0/1/4/8. The Finsupp candidate needs an additional 101-line PMF/dependent-product boundary (3 `toReal`, 3 `ENNReal`, 3 transport, 4 classical/noncomputable), and its dependent product routes through Candidate A rather than constituting an independent implementation. Both now exercise two-point support on `Nat`; Candidate A proves affine mixture and its simplex commutation. Exact current counts are asserted by the audit script.
- **Outcome:** narrows — neither representation dominates, so apply D2's stated fallback and choose a finite-support `PMF` subtype behind the future `FinDist` API
- **Next action:** Phase 2 uses only the chosen PMF-subtype representation; retain the Finsupp candidate solely as EXP-003 evidence

### EXP-004: Phase 1 gate review hardening

- **Date / revision:** 2026-07-23, review amendment based on initial gate `4f308a0`
- **Decision / question:** D1/D2; whether the recorded transport comparison, universe evidence, finite-support hostility, and simplex preservation were strong enough to support the gate
- **Representative slice:** rerun D1 with `▸`/`Eq.rec` counted and the profile allowance isolated; enable universe lint outside declaration-local exceptions; add native two-point `Nat` laws; add PMF-law affine mixing with expectation and simplex commutation
- **Evidence:** `pwsh -NoProfile -File scripts/phase1-audit.ps1 -VerifyExpected -Time`; `lake build`; amended Phase 1 Lean files and D1/D2 records
- **Observation:** the original regex undercounted bundled downstream transport, changing the comparable D1 tally from the recorded 1/1 to 1/3. Bundled forms also pay a higher, non-inferable universe boundary. Candidate B's dependent product was confirmed to route through Candidate A rather than independently implement Finsupp products. The winning PMF law initially lacked affine preservation; `Law.mix`, `expect_mix`, and `simplexEquiv_mix_apply` now close that gap. A direct-elaboration failure in the first pure-vertex proof was exposed by the timed audit and fixed before the gate rerun.
- **Outcome:** narrows — neither decision flips, but D1 remains explicitly provisional and D2 now names its downstream kill tests; the original measurement defect is retained here rather than hidden
- **Next action:** begin Phase 2 depth-first with the bundled form and PMF-subtype law, reopening either decision immediately if the named transformation or semantic slices trigger a kill condition

### EXP-005: One local deviation predicate for five equilibria

- **Date / revision:** 2026-07-26, Phase 2 working tree based on `bc1135f`
- **Decision / question:** D5; whether a single `IsEquilibrium` built from a
  law-linear, information-local `DeviationScheme` expresses pure Nash, mixed
  Nash, CCE, CE, and strong Nash without duplicate logical definitions and
  without letting a deviating unit read nonmember recommendations
- **Representative slice:** the four schemes in `GameTheory/Core/Equilibrium.lean`
  (unilateral-constant, recommendation, unilateral-randomized, nonempty-coalition),
  their three scheme morphisms, and the hostile file `GameTheory/Tests/Locality.lean`
- **Evidence:** `lake build`;
  `pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected`;
  `GameTheory/Core/Deviation.lean`, `Equilibrium.lean`, `Response.lean`
- **Observation:** the audit finds exactly one `def` for each of
  `IsEquilibrium`, `IsNash`, `IsCoarseCorrelatedEq`, `IsCorrelatedEq`,
  `IsStrongNash`, `IsBestResponse`, `WeaklyDominates`, `StrictlyDominatesOn`,
  `IsDominant`, `IsRationalizable`, and `IsParetoEfficient`. Mixed Nash is
  `IsNash F.mixed` and gets no definition at all.
  `isNash_iff_isCoarseCorrelatedEq_pure` is `Iff.rfl`;
  `IsCorrelatedEq.isCoarseCorrelatedEq` is one application of
  `constantToRecommendation`; `IsStrongNash.isNash` is four lines through
  `constantToCoalition` plus preference weakening. Locality is stronger than a
  compile-failure test: `Subprofile.singletonEquiv` proves a unilateral
  deviation's argument type is equivalent to the deviator's own strategy, so a
  recommendation-spying CE deviation is inexpressible rather than merely
  rejected. Result locality is also proved: `exists_agree_off_members` shows
  every reachable deviated profile agrees with a status-quo profile off the
  member set. Law-linearity is structural: `apply` is the only place a
  deviation meets a law, and `apply_bind` holds for every scheme. Under
  expected utility, randomized deviations reduce to deterministic ones
  (`isCoarseCorrelatedEq_randomized`), which needed a finite-support Fubini
  lemma (`FinDist.expect_comm`). The profile-quantified family stayed separate
  and is linked to equilibrium by `IsNash.isRationalizable` and
  `isNash_iff_isBestResponse`, not by aliasing.
- **Outcome:** supports - D5 passes its Phase 2 gate; neither core-invalidating
  failure 9.1.1 nor 9.1.2 was triggered
- **Next action:** record [`decisions/D5-deviation-and-equilibrium.md`](decisions/D5-deviation-and-equilibrium.md);
  re-test the interface against sequential and assessment deviations in Phase 3

### EXP-006: Separated form, preference, and utility under the incentive slice

- **Date / revision:** 2026-07-26, Phase 2 working tree based on `bc1135f`
- **Decision / question:** D4 and D9; whether utility-free forms plus explicit
  preferences avoid a recurring `IsNash_iff_IsNashFor_eu` rewrite pattern, and
  whether finiteness stays an independent per-theorem capability
- **Representative slice:** one `GameForm` used with expected-utility and with
  a purely ordinal preference; positive-affine invariance; outcome relabeling
  with utility pullback; the capability table in
  [`decisions/D9-finiteness-capabilities.md`](decisions/D9-finiteness-capabilities.md)
- **Evidence:** `GameTheory/Core/Preference.lean`, `GameTheory/Core/Utility.lean`;
  `GameTheory/Examples/Classic.lean`
  (`prisonersDilemma_bothDefect_isNash_ordinal`,
  `update_eq_self_serves_both_laws`);
  `pwsh -NoProfile -File scripts/phase2-audit.ps1`
- **Observation:** no `IsNash_iff_..._eu` theorem exists or is needed, because
  the preference is an argument rather than a second definition; the audit's
  duplicate-definition counter is 0. `euPreference_affine` and
  `isNash_mapOutcome` hold with no cast in either statement. The same
  Prisoner's Dilemma form is used with `euPreference` and with a
  non-expected-utility `bestCasePreference`, and one signature-bound profile
  plus one `Profile.update_eq_self` serves two different play laws. Finiteness
  stayed unbundled: the whole equilibrium family needs only `DecidableEq` on
  players, the mixed extension adds `Fintype` on players, and enumeration adds
  finite strategy carriers.
  Two negative findings. First, the D4 spike's proposed ordered-field
  factoring of finite-expectation lemmas earned nothing: the real side goes
  through `FinDist.expect` and the rational side through `Finset.sum` on an
  explicit table, no lemma was duplicated, and no scalar-polymorphic layer was
  added. Second, D1's bundled form needed `@[reducible]` on every signature and
  form transformer (`GameSignature.mapOutcome`, `GameSignature.mixed`,
  `GameForm.mapOutcome`, `GameForm.mixed`, `TableGame.toForm`,
  `BayesianGame.toForm`); without it `F.mixed.sig` does not reduce to
  `F.sig.mixed` at `instances` transparency and `rw`/`simp` produce
  type-incorrect targets. `isNash_mapOutcome` still needs one `show` to restate
  its goal at the transparent type. This cost did not appear in the Phase 1
  miniature.
  A third measurement concerns D12 rather than D4: Core's authored imports are
  clean, but Mathlib's `PMF` transitively imports `MeasureTheory.Measure.Dirac`
  and `Topology.Instances.ENNReal.Lemmas`, so `MeasureTheory.Measure` and
  `ContinuousMap` are reachable from `GameTheory.Core`. Narrowing `FinDist`'s
  import from `ProbabilityMassFunction.Constructions` to `.Monad` removed
  `stdSimplex` and `Polynomial` from that closure; the remainder is unavoidable
  for any real-valued core.
- **Outcome:** narrows - D4 and D9 are accepted as written, the ordered-field
  factoring is rejected, and D1's bundled form accumulates new negative evidence
- **Next action:** record D4, D9, and the D1 amendment; re-examine D1 at
  Phase 4's transformation trial before freezing it

### EXP-007: Executable rational frontend and its correctness boundary

- **Date / revision:** 2026-07-26, Phase 2 working tree based on `bc1135f`
- **Decision / question:** D10; whether a rational finite-table frontend can be
  proved correct against the semantic Nash predicate without duplicating
  solution concepts, and whether its algorithm root stays free of real,
  topological, and noncomputable dependencies
- **Representative slice:** `TableGame` with pure-Nash verification and
  enumeration, weak and strict dominance, dominant profiles, Pareto efficiency,
  iterated strict dominance, and exact rational mixed verification; Prisoner's
  Dilemma, Matching Pennies, Battle of the Sexes, and a three-player unanimity
  game
- **Evidence:** `GameTheory/Finite/Algorithm.lean`,
  `GameTheory/Finite/Correctness.lean`, `GameTheory/Examples/Classic.lean`;
  `pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected`
- **Observation:** every algorithm has a proved equivalence with a Core
  predicate: `mem_enumerateNash_iff`, `weaklyDominates_eq_true_iff`,
  `strictlyDominates_eq_true_iff`, `isDominantProfile_eq_true_iff`,
  `isParetoEfficient_eq_true_iff`, `mem_survivors_iff`, and
  `verifyMixedNash_eq_true_iff`. The executable layer defines no solution
  concept. The dependency budget is checked empirically rather than by reading
  imports: six probe files assert that `GameTheory.Finite.Algorithm` cannot see
  `Real.instAdd`, `PMF`, `MeasureTheory.Measure`, or `stdSimplex`, and that
  `GameTheory.Core` cannot see `stdSimplex` or `Polynomial`. All six pass. The
  algorithm module contains no `open Classical`, `classical`, `noncomputable`,
  or `Fintype.ofFinite`; the game's own `Fintype` and `DecidableEq` fields are
  used throughout.
  One tooling limitation was discovered and is not a design failure: kernel
  `decide` cannot evaluate rational arithmetic, because `Rat.add` and
  `Rat.blt` do not reduce - `decide` gets stuck at `(1/2).blt 0`. Pure-Nash and
  dominance facts, which only compare literals, still decide. Rational
  arithmetic facts, meaning the mixed-profile checks, are therefore run by
  compiled evaluation (`#guard`, `#eval`) and proved by `norm_num` over an
  explicit profile enumeration (`pennyProfiles`, `sum_pennies`).
  `native_decide` is excluded by the trust rules and is not used anywhere.
- **Outcome:** supports - D10 passes, with the rational-kernel-reduction
  limitation recorded as a fact about the toolchain rather than about the
  representation
- **Next action:** record [`decisions/D10-executable-frontend.md`](decisions/D10-executable-frontend.md);
  revisit if a later slice needs large rational computations inside proofs

### EXP-008: Bayesian interim-deviation scope probe

- **Date / revision:** 2026-07-26, Phase 2 working tree based on `bc1135f`
- **Decision / question:** Phase 0 flagship F5; whether an interim,
  type-dependent deviation is expressible through the shared local-deviation
  interface without exposing other players' types or recommendations, or
  whether Bayesian games need their own coordinated branch
- **Representative slice:** a finite common-prior Bayesian game compiled to a
  `GameForm` whose strategies are type-contingent plans, with a prior-weighted
  interim value taking only the deviator's own type and own action
- **Evidence:** `GameTheory/Experimental/Phase2/BayesianProbe.lean` (158
  nonblank lines), theorem `BayesianGame.isNash_iff_interim`
- **Observation:** ex-ante Bayes-Nash is `IsNash` of the compiled form under
  `euPreference`, with no new predicate, unlike v1's `Iff.rfl` wrapper. The
  interim condition is not a renaming: `isNash_iff_interim` needs the prior to
  decompose over the deviator's own type (`prior_expect_eq_sum`) and needs an
  ex-ante deviation to be reconstructed from a single-type change, and it is
  proved in both directions. The argument list of `interimValue` is deviator,
  own type, status-quo plan, own action; no other player's type or
  recommendation is in scope. Using the prior-weighted value avoids any
  positive-probability side condition and keeps conditioning machinery out of
  Core.
- **Outcome:** supports - Bayesian games fit the shared static form and the
  local-deviation vocabulary at the ex-ante and interim level; no separate
  branch is needed for this slice
- **Next action:** keep the probe experimental; interim beliefs off the
  equilibrium path belong to the Phase 3 assessment slice, not to the static
  core

### EXP-009: Open games as a source of core abstractions

- **Date / revision:** 2026-07-26, read-only audit of the pinned v1 snapshot at
  `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`; no new Lean code
- **Decision / question:** D6 and D7; whether the open-game presentation hints
  at a better abstraction for the Phase 3 sequential interface, and whether its
  equilibrium-as-a-field is independent content or derivable from native
  semantics. Phase 0 had classified open games as a Frontier branch on the
  strength of the field alone; this audit tests that classification before
  Phase 3 fixes its information interface.
- **Representative slice:** `OpenGame/Syntax.lean` (the structure and
  combinators), `OpenGame/Compile.lean` (`ShapeN`, `ShapeS`),
  `OpenGame/Theorems.lean`, and `Bridges/OpenGame_EFG.lean`
- **Evidence:** the structure carries four fields, `Strategy`, `play`,
  `coplay : Strategy -> X -> R -> S`, and
  `IsEquilibriumIn : X -> (Y -> R) -> Strategy -> Prop`, with
  `Context X Y R := X x (Y -> R)`. Corpus sizes: about 8,000 nonblank lines of
  open-game material; `Bridges/OpenGame_MAID.lean` is 1,860 nonblank lines and
  holds 23 of the snapshot's 84 code-level transport tokens, the single worst
  concentration in v1; `Bridges/OpenGame_EFG.lean` is 506 nonblank lines for one
  two-stage example; `OpenGame/Theorems.lean` is 64 nonblank lines and contains
  no generic theorem about `OpenGame`.
- **Observation:** three separable findings.
  1. *The carried equilibrium is derivable, and it is subgame perfection rather
     than Nash.* `conditioned_isEquilibriumIn_iff_efg_isSubgamePerfectEq` proves
     both directions against the native EFG concept, and
     `conditioned_isEquilibriumIn_iff_hasNoOneShotDeviation` derives the
     one-shot-deviation form from `oneShotDeviation_iff_spe`, which is Phase 0's
     flagship F4. So the field is redundant with native sequential semantics for
     every compiled shape; quantifying over the continuation `k : Y -> R` is
     exactly what upgrades a static equilibrium to a sequential one.
     `Theorems.lean` states the same decomposition directly:
     `conditioned_iff_plain_and_offPath`.
  2. *Storing it is still wrong, and v1 shows why.* Each constructor writes its
     own field: `ShapeN` hand-writes unilateral-deviation Nash with a raw
     `Function.update`, and `ShapeS` writes a different two-part condition. That
     is an additional duplicate public Nash surface, which RFC 9.1.1 forbids,
     and nothing prevents two components from composing while carrying
     inconsistent notions.
  3. *The co-outcome channel has no consumer.* Every concrete construction sets
     `coplay _ _ _ := ()`; the only nontrivial `coplay` definitions are the
     generic combinators in `Syntax.lean`, which thread the channel so that
     composition typechecks. No compiled game and no theorem reads it. The
     reserved kill condition for the lens presentation therefore fires.
- **Outcome:** narrows - reject the lens structure and the carried equilibrium;
  adopt the *context* idea as a Phase 3 design directive
- **Next action:** Phase 3 should shape its one-shot-deviation and sequential
  rationality interface as "profile plus continuation", with equilibrium derived
  from D5's deviation machinery and no co-outcome channel. Open games stay a
  Frontier branch under D12; this audit removes the temptation to promote them
  and replaces it with the one idea that measured well.

### EXP-010: General-state execution, terminal play, and chance

- **Date / revision:** 2026-07-27, Phase 3 working tree based on the Phase 2 gate
- **Decision / question:** D6; whether a general-state `ExecutionProtocol` can
  give usable terminal, chance, and run semantics. RFC 9.1.6 makes it a
  core-invalidating failure if the selected execution semantics needs an
  impossible total legal-action chooser at terminal states, dummy probability
  data at chance nodes, or evaluation that silently stops at a chance node.
- **Representative slice:** `coinThenMove` in `GameTheory/Tests/Execution.lean` -
  a fair chance node with no mover, followed by a one-player decision, followed
  by a terminal state, so all three failure modes are reachable in one protocol
- **Evidence:** `GameTheory/Protocol/Execution.lean` and
  `GameTheory/Tests/Execution.lean`; `lake build`
- **Observation:** none of the three failure modes occurred.
  1. *No total chooser.* `Chooser` takes a non-terminality proof, so terminal
     states are never queried. Stronger, `terminal_no_legal` is a *theorem*
     rather than the assumed field of the RFC sketch: legality was defined as
     "not terminal, and every active player supplies an available action", so a
     total chooser could not be written even if a runner asked for one.
  2. *Chance is carried by the transition law.* `chanceLaw` is `step` applied to
     the no-op joint action at a state where nobody is active;
     `coinThenMove_chanceLaw_heads`, `..._tails`, and `..._normalized` show the
     law is a genuine fair coin, not dummy data hung on a `none` mover.
  3. *Evaluation does not stop at chance.* `runFor_succ_of_chance` proves the
     runner steps through a chance state, and `runFor_of_terminal` proves
     terminal states absorb. `runFor_one_from_chance` instantiates both.
  4. *The chosen action drives the run.* Review caught that the first version of
     the slice could not detect a runner that consulted the chooser and then
     discarded its answer - for instance one picking a legal action itself via
     `Classical.choice` on `exists_legal` - because `step` ignored the joint
     action outside the chance node. The protocol now splits its terminal state
     into `tookIt`/`leftIt` and lets `step` branch on the move, and
     `takePolicy_ne_leavePolicy` proves the two policies induce *different*
     two-step laws from the chance node (`prob_tookIt_take = 1` against
     `prob_tookIt_leave = 0`). Without that probe the other three tests were
     satisfiable by a runner that never used the chooser's choice.
  Two simplifications relative to the RFC sketch: legality became a definition
  rather than a stored field plus `legal_iff_active_available`, removing one
  field and one law; and `active` is proposition-valued rather than a `Finset`,
  keeping enumeration out of proof semantics (D9). `Trace` is `Type`-valued, so
  `IsTreeShaped := ∀ state, Subsingleton (Trace E state)` is a genuine
  uniqueness statement - the repair for v1's `Subsingleton (Reachable s t)`,
  which was vacuous under proof irrelevance.
  One negative datapoint, and it is not about D6: the concrete protocol needed
  `@[reducible]`, because `coinThenMove.State` does not reduce to its carrier at
  `instances` transparency. This is the *third* module to need that annotation
  after `GameForm` and `TableGame`/`BayesianGame`. RFC 9.3 says an exception
  recurring across two or more modules is promoted to its design decision, so
  this is now formal evidence against D1's bundled-signature form rather than an
  isolated waiver.
- **Outcome:** supports - the general-state candidate survives RFC 9.1.6; the
  question of whether it *beats* finite-first is separate and is reserved as
  EXP-012
- **Next action:** build the finite-first candidate, encode the same
  perfect-information EFG with chance in both, and decide D6 on the measurement
### EXP-011: Information locality by construction

- **Date / revision:** 2026-07-27, Phase 3 working tree
- **Decision / question:** D6; whether an information model layered over an
  execution protocol keeps strategies information-local *by typing* rather than
  by a later proposition. RFC 9.1.7 makes it a core-invalidating failure if the
  strategy type exposes hidden execution state, relies only on a subsequent
  locality proposition, or cannot support conditional beliefs and sequential
  rationality without reopening native information equivalence.
- **Representative slice:** `hiddenCard`, a two-seat imperfect-information
  protocol - nature deals `high`/`low`, the `informed` seat is told privately,
  the `blind` seat is not, both then call simultaneously
- **Evidence:** `GameTheory/Protocol/Information.lean`,
  `GameTheory/Tests/Information.lean`; `lake build`
- **Observation:** RFC 9.1.7 is **not** triggered.
  *Locality is typing, not a hypothesis.* `Policy i` is
  `(info : InfoState i) → { choice // choice ∈ menu i info }`. It has no
  `E.State` argument, which `blind_policy_type` records as an `rfl`-checked type
  equation. `blind_cannot_tell` proves the two dealt states give the blind seat
  equal `InfoState`, and `every_blind_policy_agrees` follows by `congrArg` -
  there is no locality hypothesis and no "assume the policy is constant on the
  information set" lemma anywhere.
  *The information state is history-indexed.* `infoOf` recurses over `Trace`
  rather than mapping states, so information accumulates along a run instead of
  being read off a state.
  *Menu adequacy did not need hidden state.* `menu : (i) → InfoState i → Set …`
  never receives a state; the adequacy *law* quantifies over states and traces,
  which is what a law is for. The payoff is `legalOption_of_mem_menu`: one
  information-local menu is the legal option set at every state in the
  information set, so `jointAt_legal` builds a legal joint action from a profile
  of information-local policies with no state-indexed menu and no native
  equivalence relation on states.
  *The probes have teeth.* `informed_can_tell` proves the *informed* seat's
  `InfoState` values at the same two states differ, which kills
  `InfoState := Unit` and every degenerate information state that would make the
  equalities above vacuous. `blindPolicy` inhabits the policy type, so the
  universally quantified statements are not over an empty type;
  `blind_menu_excludes_passing` shows the menu is not `Set.univ`;
  `hidden_card_matters` shows the two merged states genuinely have different
  futures.
  Two honest costs. First, `menu` ranges over `Option (E.Action i)` rather than
  `E.Action i`, which commits the design to "the information state determines
  whether the player moves, not only what they may play". That is the standard
  assumption and makes `menu` exactly the per-player conjunct of legality, but
  without it a policy would need the hidden state to know whether to return
  `none`. Second, `IsLegalJoint` is written in `Execution.lean` as an inlined
  `∀ i, match …`, and two distinct stuck matchers are not definitionally equal,
  so the pointwise form needed a one-off case split
  (`isLegalJoint_iff_legalOption`) rather than `Iff.rfl`. A future refactor to
  `IsLegalJoint := ∀ i, LegalOption …` would remove that friction.
  A third instance of a now-familiar tactic hazard: `cases` on `Trace` fails
  with an internal motive error unless the index is typed at the protocol's
  `State` projection rather than the reduced carrier.
- **Outcome:** supports - the separated information layer survives RFC 9.1.7 for
  feasibility. A full sequential-rationality and consistency definition was
  deliberately out of scope and was not faked.
- **Next action:** build the assessment and one-shot-deviation slice on this
  interface, shaped as profile-plus-continuation per EXP-009, which is what
  closes 9.1.7's third clause.
### EXP-012: The two execution candidates on one game

- **Date / revision:** 2026-07-27, Phase 3 working tree
- **Decision / question:** D6; finite-first inductive trees or general-state
  transition systems for v1. The RFC's criterion is that the general candidate
  wins only if the finite evaluator and the backward-induction API arise from a
  small well-founded or bounded certificate rather than from a second parallel
  semantics.
- **Representative slice:** one fair coin followed by one consequential
  decision, encoded twice - as `coinThenMove : ExecutionProtocol Unit` and as
  `coinTree : Tree Unit (fun _ => Move) Spot`
- **Evidence:** `GameTheory/Protocol/Tree.lean`,
  `GameTheory/Protocol/Execution.lean`, `GameTheory/Tests/Candidates.lean`
- **Observation:** three probes were built in before measuring, following the
  review lesson from EXP-010.
  1. *Agreement.* `candidates_agree_take` and `candidates_agree_leave` prove the
     two candidates induce the same outcome law, so neither is quietly modelling
     a different game.
  2. *Discrimination.* `takePolicy_ne_leavePolicy` and `takePlan_ne_leavePlan`
     prove each candidate's law depends on the chosen action, so neither set of
     tests would pass an evaluator that discarded the strategy.
  3. *Cost.* Finite-first: `Tree.eval` is structural recursion - total, no fuel,
     no certificate. `Tree.PureStrategy` is defined by recursion on the tree, so
     the plan type is indexed by the tree's *own* decision sites by
     construction; `Fintype` follows from finiteness of the local action
     carriers alone, and `card_pureStrategy_coinTree` computes by `rfl`. That is
     RFC D6's fifth hostile test, passed outright.
     General-state: `runFor` is fuelled and is therefore not yet an evaluator.
     Making it one took `runFor_add` (which needed the new
     `FinDist.bind_congr`), `StopsWithin`, and two stabilization theorems -
     about 25 nonblank lines, and `takePolicy_stopsWithin` discharges the
     certificate for the example in four. On the *evaluator* axis this is a
     small bounded certificate, not a second parallel semantics, so the general
     candidate meets the RFC's criterion there.
  One asymmetry is already visible and counts against general-state. The tree's
  strategy type is over the tree's own decision sites; the protocol's `Chooser`
  is a function over *every* non-terminal state, which is "all syntactically
  possible states" rather than the game's reachable decision sites. Recovering
  the latter needs an extraction step the general candidate does not yet have.
- **Outcome:** narrows, partial - both candidates encode the slice and agree;
  finite-first passes hostile test 5 outright; general-state passes the
  small-certificate criterion for the evaluator but not yet for strategy
  extraction
- **Follow-up (2026-07-27):** both open measurements were made, and a third gap
  appeared.
  *Backward induction.* `GameTheory/Protocol/Backward.lean`. `Successor` is
  `StepEvent` with its data forgotten; `WellFoundedPlay` is one line;
  `backwardRec` is `WellFounded.fix` along it. Terminal states are the
  relation's minimal elements automatically, because `Legal` already contains
  non-terminality, so no separate base-case predicate is needed. Certificate
  plus recursor is 26 nonblank lines; the concrete instance for the probe
  protocol is 22. Decisively, `backwardValue_eq_expect_runFor` proves that
  wherever `StopsWithin` holds the backward-induction value *equals* the
  expected payoff of the fuelled run law - neither is defined from the other,
  so this is not a second parallel semantics. Five probes each pair with an
  explicitly refuted mutant (`oneStepValue`, `sourceOnlyValue`,
  `chooserBlindValue`), making discrimination a theorem.
  *Strategy extraction.* `GameTheory/Protocol/Extraction.lean`. `Reachable`,
  `DecisionSite`, `SiteStrategy`, `Chooser.restrict`, and
  `runFor_congr_of_restrict_eq`: choosers agreeing on the reachable decision
  sites induce the same run law. The `ghostArena` probe exhibits an active,
  non-terminal, *unreachable* state, proves it unreachable, proves the two
  choosers genuinely differ there, and proves the runs agree anyway - so the
  faithfulness theorem is not vacuous.
  *The new gap.* Reviewing the tree candidate against the rest of D6's slice
  list shows `Tree.node` carries a single `mover`, so the finite-first candidate
  as built **cannot express simultaneous actions at all**. The general-state
  candidate handles them natively: `active` is a predicate over players and
  `step` consumes a joint action. RFC D6 explicitly says to reject finite-first
  if the simultaneous-action and MAID/FOSG slices need duplicate execution
  theories rather than a small extension, so this is the decisive remaining
  measurement and it runs the *opposite* way from the certificate count.
- **Running tally:** finite-first needs zero certificates, has intrinsic
  decision sites, and evaluates structurally, but is single-mover. General-state
  needs two certificates that do not derive from each other (`StopsWithin` is
  chooser-indexed and fuel-shaped, `WellFoundedPlay` is chooser-independent and
  order-shaped) plus an extraction construction, but handles simultaneity
  natively and its certificates are provably not a parallel semantics.
- **Simultaneity measurement (2026-07-27):** `GameTheory/Tests/Simultaneous.lean`.
  The general-state protocol takes it natively: `matching_both_active` puts two
  players on move at one state, `matching_legal_forces_both` shows a legal joint
  action must supply a move for each, and `matching_outcome_depends_on_both`
  proves the transition reads both calls. The finite-first tree cannot express
  it at all - `Tree.node` carries one `mover` - so the same game must be
  sequentialized, and `sequentialization_enlarges_strategy_space` proves that is
  not faithful: eight contingent plans against four simultaneous profiles.
  `respondingPlan` exhibits one of the extra plans, conditioning on the
  opponent's call. Making the tree faithful needs an information layer to
  quotient those plans - exactly the machinery whose absence made it cheaper on
  the certificate axis.
- **Outcome (final):** decides D6. RFC D6's disproof conditions apply
  asymmetrically: general-state-first is rejected only on a failed terminal,
  chance, locality, or finite-extraction test, and it failed none; finite-first
  is rejected if the simultaneous-action slice needs a duplicate execution or
  evaluation theory, and it needs an information layer. General-state is the
  primary interface; the tree is retained as a derived presentation for
  single-mover games, where it costs no certificate and evaluates structurally.
  The two provably agree where both apply.
- **Next action:** recorded in
  [`decisions/D6-execution-and-information.md`](decisions/D6-execution-and-information.md).
  D7 remains open, as do the assessment and one-shot-deviation slice and the
  MAID/FOSG encodings; D0 is not final until those are measured.

### EXP-013: Assessment, sequential rationality, and one-shot deviations

- **Date / revision:** 2026-07-27, Phase 3 working tree
- **Decision / question:** D6 and D7, and the third clause of RFC 9.1.7.
  EXP-009 concluded that the open-game *context* is the idea worth taking while
  its carried equilibrium field and co-outcome channel are not. This tests that
  directive.
- **Representative slice:** `Context`, `value`, `IsLocallyOptimal`,
  `IsProfitableDeviation`, `IsSequentiallyRationalAt`, and four probes over a
  two-room protocol
- **Evidence:** `GameTheory/Protocol/Assessment.lean`,
  `GameTheory/Tests/Assessment.lean`
- **Observation:** the directive holds. `Context` has exactly two fields -
  `outcome : Option (Action i) → FinDist State` and
  `continuation : State → ℝ` - which is the open-game context with the
  co-outcome channel dropped, as EXP-009 measured that channel to have no
  consumer. Local optimality is a *definition* over those fields, in deliberate
  contrast to v1, where every open-game constructor stored its own
  `IsEquilibriumIn` and hand-wrote a Nash condition.
  `isLocallyOptimal_iff_no_profitable_deviation` is the one-shot-deviation
  interface, with both sides derived from `value`.
  `IsSequentiallyRationalAt` composes it with the information layer: the policy
  supplies the call, `menu` supplies the allowed set, and the context supplies
  the value. `deviation_legalOption` shows every alternative the deviator may
  consider is legal at every state its belief considers possible - feasibility
  without ever handing a policy a state, which is the remaining clause of
  9.1.7.
  The probes matter here more than usual, because
  `isLocallyOptimal_iff_no_profitable_deviation` is a tautology about `value`
  and would hold just as well if `value` were constant. Each probe therefore
  fixes one field and varies the other: `up_optimal_under_prefersLeft` against
  `up_not_optimal_under_prefersRight` varies only the continuation and flips the
  verdict; `outcome_map_matters` holds the continuation fixed and flips it back
  by changing only where the calls lead; `down_is_profitable_under_prefersRight`
  exhibits an actual profitable deviation rather than only denying one; and
  `belief_matters` shows the belief-built context depends on the belief.
  One honest limitation. A profile of information-local policies is
  *history*-indexed, because `infoOf` recurses over `Trace`, while `runFor`
  consumes a *state*-indexed `Chooser`. Folding a full profile into a context
  therefore needs either a history-indexed runner or a bind that is dependent on
  a law's support, and `FinDist` has neither. `Context.ofBelief` sidesteps this
  by taking a total branch and proving, via `ofBelief_congr`, that only its
  behaviour on the belief's support matters. That is enough for the one-shot
  interface, which is what the RFC asked for, but a full sequential-equilibrium
  development would need the missing piece.
- **Outcome:** supports - the context idea survives, the carried equilibrium and
  the co-outcome channel stay rejected, and 9.1.7's third clause is met for
  feasibility and one-shot deviations
- **Next action:** the history-indexed runner, or a support-dependent bind on
  `FinDist`, is the prerequisite for full sequential equilibrium; record it as a
  known gap rather than a blocker for Phase 3
### EXP-014: One execution base for two native shapes

- **Date / revision:** 2026-07-28, Phase 3 working tree
- **Decision / question:** D6's disproof condition - reduce the interfaces to a
  smaller shared base if the languages cannot share `ExecutionProtocol` without
  fake players, fake actions beyond the canonical no-op, or language-specific
  escape fields. Deliverable is the written list of every language-specific
  workaround. Two native shapes were encoded, not three: an influence diagram
  and a multi-round simultaneous game. The extensive-form leg is covered only
  informally, by the imperfect-information and chance protocols in
  `GameTheory/Tests/Information.lean` and `GameTheory/Tests/Execution.lean`,
  which carry no workaround list of their own.
- **Representative slice:** a three-node MAID - one chance node, one decision
  node observing it, one utility node - compiled into `ExecutionProtocol` and
  `InformationModel`. MAID is the hardest of the three because its native shape
  is a DAG of typed nodes rather than a state machine.
- **Evidence:** `GameTheory/Languages/MAID.lean` (820 nonblank lines), whose
  `## Workarounds` section is the deliverable
- **Observation:** all three named failures are absent, each with a theorem.
  *No fake players*: the protocol's index is the diagram's own agent set, chance
  is carried by the transition law at an ownerless node, and `no_extra_agent`
  records there is no `nature` index. *No fake actions*: an agent with no
  decision node gets `Empty` rather than a padding action, and at every
  non-decision node the only legal joint action is the canonical no-op. *No
  escape fields*: the three structures were used as declared.
  The honest remainder is more interesting than the clean part. The DAG must be
  linearized, so the state space is its prefixes; for this diagram the
  topological order is unique, but the file states plainly that **a MAID with
  two incomparable decision nodes would make the compiled protocol assert an
  order the diagram does not have, and that case is untested**. The utility node
  costs an execution step whose law is a point mass, so `IsChance` cannot
  distinguish a chance node from a deterministic administrative step - node
  kinds are not recoverable from the protocol. And the encoding independently
  rediscovered the mismatch recorded in EXP-013: `runFor` is state-indexed while
  policies are history-indexed, and the bridge is sound here only because the
  stage records every resolved node's value.
  A discriminating probe (`outcome_law_depends_on_decision`) proves the compiled
  run law depends on the decision node's value, so the encoding does not
  collapse the decision away.
- **Multi-round simultaneity (2026-07-28):** `GameTheory/Languages/Rounds.lean`.
  Simultaneity composes across rounds with no encoding trick: `active` is a
  predicate over players so a whole round is one state, `step` consumes a joint
  action so a round resolves in one transition, and the reached state carries
  the round's outcome so round two can depend on round one. The no-op never
  appears, because `all_active_of_not_terminal` shows no state has an idle
  player. Three probes make the claim non-vacuous - both players' first-round
  calls matter, the second round is not vestigial, and the state reached after
  round one genuinely records which outcome occurred - and `stopsWithin_two`
  supplies the horizon certificate. The recorded remainder is that the middle
  state carries the first round's *outcome* rather than its actions, so a game
  whose second round depends on the exact first-round profile would need a wider
  state; nothing in the interface prevents that, but this file does not test it.
- **Outcome:** supports - both encodings share the execution base with no fake
  players, no fake actions beyond the canonical no-op, and no escape fields, each
  recorded with a theorem. Two scope limits are stated plainly rather than
  hidden: an influence diagram with two incomparable decision nodes, and a
  round-based game needing the exact previous profile.
- **Next action:** neither encoding needed an escape hatch, so the shared
  execution base stands. The certificate-versus-direct-bridge measurement is
  the remaining input to D7.
### EXP-015: Certificates against their direct bridges

- **Date / revision:** 2026-07-28, Phase 3 working tree
- **Decision / question:** D7 and the finalization of D0. Phase 0 fixed an
  eight-point bridge and certificate complexity budget; a certificate level
  earns its place only against the bespoke direct bridge it replaces.
- **Representative slice:** the two encoded native shapes - an influence diagram
  and a two-round simultaneous game - each taken to a `GameForm`, with the
  static solution concepts applied to both
- **Evidence:** `GameTheory/Tests/Transfer.lean`
- **Observation:** the direct baseline is *zero*, which no certificate level can
  beat. Each language reached the static core by applying one existing generic
  function; it added no structure, no construction discharging certificate
  fields, and no evaluation theorem of its own. Both obtain their outcome law
  from the same theorem, `ExecutionProtocol.toGameForm_play`, instantiated
  twice, and `IsNash` and `WeaklyDominates` apply to both without either
  language contributing a definition or a lemma. A named adequacy record would
  add a structure, composition laws, and a per-language construction, and would
  enable nothing further: the transfer is function composition, and composing
  functions needs no witness.
  This corroborates EXP-009 from the opposite direction. That audit found a
  compositional presentation whose carried equilibrium field was *derivable*
  from native semantics, whose constructors each hand-wrote their own optimality
  condition, and whose contravariant channel had no consumer. Storing a witness
  for something already derivable is the mechanism by which a certificate
  hierarchy decays into duplicated concepts.
  The rejection is scoped, not universal: it holds for languages that compile
  *into* a shared target, and says nothing about a transfer that must preserve
  something the target forgets, such as recall or the identity of a decision
  site. No such transfer exists here yet, which is itself the reason the
  hierarchy is unamortized.
- **Outcome:** rejects D7 for v1 - keep compilation as functions and named
  evaluation theorems; reopen only on a concrete transfer the shared static form
  provably cannot carry
- **Next action:** record
  [`decisions/D7-certificate-stratification.md`](decisions/D7-certificate-stratification.md);
  D0 can now be finalized at every semantic level.

### EXP-016: A run law indexed by history

- **Date / revision:** 2026-07-28, working tree after the Phase 3 merge
- **Decision / question:** whether the run law can be indexed by history rather
  than state, so that a profile of information-local policies can actually be
  run. The recorded limitation is that `infoOf` recurses over histories while the
  runner consumes a state-indexed chooser, which blocks both the general
  strategic compilation and the one-shot-deviation theorem. The risk to test is
  that a history-indexed runner is a *second semantics*: if the state law is not
  recoverable from it, the sequential layer has two disagreeing notions of play.
- **Representative slice:** a protocol in which chance splits into two branches
  that the player observes and that then merge back into one state, so two
  histories reach the same state carrying different information
- **Evidence:** `GameTheory/Protocol/History.lean`;
  `GameTheory/Tests/History.lean`; `FinDist.bindOnSupport` and its laws
- **Observation:** the missing primitive was a support-dependent composition,
  because extending a history requires evidence that the transition was
  realized. Mathlib's `PMF.bindOnSupport` supplies it from the *same* module the
  finite-support type already imports, so the dependency budget is untouched.
  Not a second semantics: `map_state_runHistoryFor` says the state law is the
  history law's pushforward along the state each history reached, for any
  chooser that ignores the history. Everything proved about the state law
  therefore still holds.
  Strictly more expressive, and measured as such rather than asserted. In the
  merging protocol the profile that reads its branch induces a law with mass one
  half on each ending, while every state-indexed chooser induces a point mass,
  because at the merged state such a chooser has nothing left to condition on.
  The probe is checked against its own control: the profile that ignores the
  branch induces *exactly* a state chooser's law. So what the test detects is the
  use of history, not the fact of running along one — the discrimination is
  itself a theorem rather than a claim about the test.
  One simplification fell out. The state runner needed an induction to show
  everything it reaches is reachable; the history runner needs none, because a
  history is that evidence.
- **Outcome:** supports — adopt the history-indexed runner alongside the state
  one, with the pushforward theorem as the compatibility guarantee
- **Next action:** behavioral and mixed policies over the same `Policy` type,
  then the one-shot-deviation theorem. Both are prerequisites for the
  behavioral/mixed equivalence.

### EXP-017: Two places to put randomness

- **Date / revision:** 2026-07-29, working tree after the history-indexed runner
- **Decision / question:** whether the sequential layer can carry both local and
  global randomization over one `Choice` type, and what an equivalence between
  them would have to assume. The risk is a third notion of play: if randomized
  running does not reduce to deterministic running, the layer accumulates
  competing semantics instead of one with special cases.
- **Representative slice:** a protocol in which one player moves twice and
  observes only whether play has stopped, so both decision points carry the same
  information state
- **Evidence:** `GameTheory/Protocol/Randomized.lean`;
  `GameTheory/Tests/Randomized.lean`; `FinDist.mem_support_pi`
- **Observation:** no third semantics. A chooser answering with point masses
  induces exactly the deterministic law, and reading a deterministic profile as
  behavioral, or as a mixed profile concentrated on it, likewise changes
  nothing — three conservativity theorems rather than three conventions. The
  independence of players' draws comes from the existing finite product of laws,
  so nothing new was needed to combine them, and menu adequacy makes every drawn
  joint action legal without a second argument.
  The two placements do *not* agree in general, and the counterexample is now
  machine-checked rather than inherited. Where one player meets one information
  state twice, a behavioral policy draws afresh and can play both actions, while
  a mixed policy is committed by its single draw and must repeat itself. The
  separating event is exactly a pair of unequal actions at a repeated
  information state.
  That fixes the shape of the eventual equivalence. It cannot be proved without
  forbidding a player to return to an information state it has already acted at,
  which is the condition the pinned snapshot carries under a different name —
  and which is *not* recall. Recall governs the other direction.
- **Outcome:** narrows — keep both randomizations over the shared `Choice`; the
  equivalence needs a no-revisit hypothesis, whose necessity is now recorded as a
  theorem instead of assumed
- **Next action:** state and prove the equivalence under
  `ActsOnceAtEachInfoState`, then the direction that needs recall. The
  factorization primitive is now in place; what is not yet settled is how the
  induction carries the set of already-consulted information states, since the
  coordinates a play consults are themselves random. See the addendum below.

#### Addendum: the primitive the equivalence needs

Predicted before the equivalence was attempted, and then narrowed by building
it. The prediction was a peel law for the finite product, and that is now
`FinDist.pi_eq_map_product`: a finite product factors at any one coordinate into
that coordinate's law and an independent law of the rest. `map_apply_pi`, the
marginal, falls out of it, and the basic mass API it rests on —
`prob_map_of_injective`, `prob_product`, `map_fst_product` — was missing for
operations the module already exported.

What building it clarified is that the peel is not by itself the whole story.
The coordinates a play consults are chosen by the play, so they are random, and
an induction over fuel meets a *growing set of already-consulted information
states* rather than one fixed coordinate. Two shapes are therefore in view: peel
one coordinate and shrink the index type, which is what `pi_eq_map_product`
does; or fix a family of *distinct* coordinates and factor them all at once,
which states the independence the no-revisit condition supplies but needs a
finite-product Fubini for `expect` that this module does not have. Only the
first was built, because only the first has a consumer today.

#### Addendum: the structural half of the equivalence

Two facts that the equivalence needs and that do not touch the probabilistic
gap are now proved, so what remains of the theorem is exactly that gap.

`runFrom_congr_of_act_eq` says a profile is observable only through the
histories a run of that length can pass through — the policy analogue of the
chooser congruence over reachable decision sites. Its hypothesis is stated over
`ReachesWithin`, an over-approximation of what any particular chooser reaches,
so the condition does not mention the profile being varied. The bound is real
rather than vacuous: with no fuel, `ReachesWithin` relates a history only to
itself.

`infoOf_ne_of_actsOnce` converts the no-revisit condition into the form the
peel step consumes: having moved at one history, a player meets that information
state at no later history where it moves again. It rests on the record of where
a player has acted growing along play, which is a suffix relation over
`ReachesWithin`. Before this, the condition had only a refutation as a consumer;
it now has a positive one.

What is left is to combine the peel with these: at each step, factor the drawn
policy at the coordinate about to be consulted, match the first factor against
the behavioral draw, and use the two facts above to show the residual can be
extended arbitrarily at that coordinate.

#### Addendum: how the shrinking index is avoided

The obstruction recorded above — that the index type shrinks while the induction
hypothesis quantifies over full profiles — is avoidable, and both remedies first
recorded here were worse than the one now adopted. **Commit the consumed
coordinate instead of deleting it.**

`BehavioralPolicy.commit` fixes one information state to a point mass and leaves
the rest alone, and `toMixed_commit` is the identity that makes it work:
re-extending the residual of a factored draw with a fixed choice is again the
mixed reading of a behavioral profile — the committed one. It is
`pi_eq_map_product` read for the committed family. So the induction hypothesis
never leaves full profiles; the set of already-consumed information states is
encoded as the coordinates that have become point masses, and point masses need
no bookkeeping.

`runBehavioralFrom_congr` is what then makes the commitment invisible on the
continuation, since `infoOf_ne_of_actsOnce` says the consumed coordinate is
never consulted again.

Why the two alternatives were worse. Generalizing over a consumed set would put
the statement on types that change at every step, and moving between them is
`Equiv` juggling — precisely what produces the source-level transport tokens
this layer budgets at zero. Proving the distinct-family factorization outright
would need a finite-product Fubini for expectations, and the step case does not
need one: mass-level factorization is `prod` algebra over the existing lemmas,
and the sequencing unfolds from `product`'s own definition.

One point worth recording because it nearly went the other way: committing a
coordinate is a pointwise update of a dependent function, which transports a
value along an equality of information states, and both spellings of that —
`Function.update` and `▸` — are already forbidden in this layer. Building it
from `Equiv.piSplitAt`, the same decomposition the factorization uses, needs
neither, and the audits confirm the layer's counts are unchanged.

#### Addendum: two refinements found by attempting the step

The interchange lemmas the step case needs are proved: `pi_map`, that
independent draws commute with coordinatewise pushforward, and `map_pi_product`,
that independent draws of pairs are a pair of independent draws. Neither needed
a Fubini for expectations. `pi_map` does not follow from the injective
pushforward rule, since relabelling coordinatewise is not injective; it goes
through a finite superset of the support and the distributivity of a product of
sums over a product index, which Mathlib already has.

Attempting the step turned up two things the plan as designed does not cover.

*A commitment must also be invisible where the player does not move.* The
no-revisit condition speaks only about information states a player has *acted*
at, but a profile is consulted at every player at every history, so a
commitment could survive to a later visit at which the player is idle. It cannot
matter, and for a reason already in the design: an inactive player's menu is the
single option `none`, so its choices at that information state form a
subsingleton and every law over them is the same law. Locality by typing settles
it with no argument about what play does next.

*Agreement is only needed where play has not stopped.* Both congruences now
quantify over reachable *non-terminal* histories. Otherwise a protocol calling a
player active at a state it has already stopped at would demand agreement the
runner never consults — a hypothesis stronger than the theorem needs, and one
with no fact available to discharge it.

#### Result: the equivalence

`runMixedFrom_toMixed` is proved. Under `ActsOnceAtEachInfoState`, randomizing
at each information state and randomizing once over whole policies induce the
same law over histories, at every fuel and from every history.

The induction follows play and never leaves full profiles. At each step the
drawn policy is factored at the information states about to be consulted, its
first factor is matched against the local draw — the two sides then take
*literally* the same joint action — and the rest is re-read as the mixed profile
that has committed there. The commitment is invisible afterwards for one of two
reasons, and both are needed: the coordinate is never consulted again while the
player moves, or the player does not move there and its menu was a single option
all along.

The theorem is not vacuous and the condition is not idle. Both are checked on
the two protocols in the test file, which differ in exactly the feature the
hypothesis names: voting twice at one information state separates the two
randomizations, voting once satisfies the condition, and the equivalence is
instantiated there.

What this settles about the direction that needs recall: nothing. This is the
direction that needs none, exactly as the pinned snapshot's structure predicted,
and the condition it does need is about being asked twice rather than about
memory.

### EXP-018: Recovering local randomization from a single draw

- **Date / revision:** reserved 2026-07-29, before any attempt
- **Decision / question:** the converse direction. Given a mixed profile, is
  there a behavioral profile inducing the same law, and does the construction
  live in the existing layer? This is the direction that needs recall, and the
  one whose real obligations the architecture record found to be much larger
  than its label suggests. It tests the accepted interfaces, not the certificate
  decision: an equivalence of two strategy representations within one
  information model is not a transfer between languages, and both of its sides
  already live in the same layer. The architecture record has been corrected
  accordingly.
- **Representative slice:** one game under two signal designs. The same two-vote
  protocol that separates the randomizations, given signals that let the player
  see its own vote — so the slice is a change of observation map, not a bigger
  game.
- **Prediction, written before attempting.** The behavioral action law at an
  information state is the mixed law conditioned on reaching it, so the missing
  primitive in the finite-support layer is a *conditional law on an event of
  positive mass* — the analogue of the coordinate factorization that the forward
  direction needed, and predicted here for the same reason: it is the operation
  the definition is phrased in. Two further obligations are expected, both named
  in the architecture record rather than discovered: reach-mass factorization,
  and player-local action posteriors. Perfect recall is expected to enter as the
  hypothesis making the conditioning consistent across the histories in one
  information set, not as a field carrying the conclusion.
  One thing is expected *not* to be a problem. Conditioning is undefined at an
  information state play never reaches, so the constructed profile must be given
  some arbitrary value there. That is already known to be unobservable: the
  congruences say a profile is seen only through the histories a run can pass
  through.
- **Evidence so far:** `GameTheory/Probability/FinDist.lean`, the conditioning
  section; the reachability probe run against
  `Mathlib.Probability.ProbabilityMassFunction.Constructions`
- **Observation so far:** the prediction is confirmed on *what* is needed and
  was wrong about the cost. Conditioning is the right primitive, but the obvious
  route to it is closed: Mathlib's `PMF.filter` and `PMF.normalize` live in
  `ProbabilityMassFunction.Constructions`, and importing that module makes both
  `stdSimplex` and `Polynomial` reachable again — measured directly, and exactly
  the two constants the narrowed import was chosen to exclude and that the phase
  audits probe for. Taking the easy route would have silently widened the
  dependency of everything downstream of the law type.
  Hand-building it costs about fifty lines and needs only the probability monad,
  so the budget is unchanged. `condOn` restricts a law to an event it gives
  positive mass and renormalizes; `probOf` is the event's real mass, positive
  under the same hypothesis. Conditioning on everything changes nothing, which is
  the cheap check that the normalization is the intended one.
  Worth recording as a general lesson rather than a local one: a missing
  primitive being *available in Mathlib* is not the same as it being *available
  here*, and the difference is only visible if the dependency is measured before
  the import is taken.
- **Outcome:** *in progress*
- **Second observation: recall is a property of `infoOf`, and both existing
  slices fail it.** `ownPlay` records the (information state, action) pairs a
  player's own moves leave along a history, and `actedAt` is that record with the
  actions forgotten. `PerfectRecall` then says two histories producing one
  information state leave the same own record. Stating it that way is what
  keeps the conditioning event a function of the information state alone, and it
  structurally excludes the failure the open-game audit warned about: the
  consistent-policy set will be a definition over the record, and recall stays a
  hypothesis about `infoOf` rather than a field carrying the conclusion.
  Neither protocol in the test file satisfies it, and both refutations are
  machine-checked. Each observes only whether play has stopped, so neither can
  tell what it did. That also settles the open question of the representative
  slice: it is a different *signal design* — a player that sees its own
  actions — not a bigger game. And it separates two conditions that could be
  confused: voting once satisfies the no-revisit condition while still failing
  recall.

- **Predicted next, before building.** Two things, recorded now so the outcome is
  evidence either way. First, the default at information states play never
  reaches costs nothing and needs no hypothesis: every law has nonempty support,
  so the given mixed policy admits a witness policy, and that witness supplies a
  legal choice everywhere — including where menu adequacy says nothing and the
  menu could otherwise be empty. The congruences already make the default
  unobservable. Second, the primitives after `condOn` are its tower properties:
  an expectation decomposed through a conditioning over a partition, which is
  what reach-mass factorization is, and iterated conditioning collapsing to the
  intersection event.

- **Third observation: recall is a property of the observation map, and the
  slice shows it.** The same game carries both designs. Told only whether play
  has stopped, the player fails recall and the two randomizations provably
  differ; told its own vote, it satisfies recall *and* the no-revisit condition,
  and the equivalence applies — the separation disappears with nothing about the
  game changed. The information state in the second design *is* the player's own
  record, which is why recall holds by computation rather than by assumption.
  This is also the first slice on which both conditions hold at once, so it is
  the one the recall direction will be built against.

- **Fourth observation: the construction lands, and the default really is
  free.** `recordAt` reads a player's own record off *some* history producing an
  information state, and `recordAt_eq_ownPlay` is where recall does its work:
  with it, that record is the record along *every* such history, so the arbitrary
  choice is no choice. `Consistent` then names the pure policies whose own
  answers match a record, and `toBehavioral` conditions the single draw on them
  and takes the action's law.
  The predicted-free default is confirmed. At an information state no history
  produces, the conditioning event can have no mass, and the value is taken from
  a policy the law does give mass to — which costs nothing, because every law has
  something in its support and a policy already chooses legally everywhere,
  *including* where the menu law says nothing and the menu could otherwise be
  empty. No hypothesis was added, and the degenerate check passes on both
  branches at once: a draw concentrated on one policy reads back as that policy
  whether or not the information state was reachable.

- **Fifth observation: the induction is assembled except for one wrinkle, and
  the wrinkle narrows the earlier prediction.** Every step of the argument is now
  in place. The behavioral draw at a history *is* the marginal of the single
  draw, because the profile's support already lies in the consistency event, so
  conditioning there does nothing. The single draw disintegrates along the joint
  answer it gives, the observed part matches the behavioral draw exactly, and
  the remainder is the profile conditioned on that answer, which splits back
  into one conditioning per player because nothing couples them. What a step
  commits a player to is permanent, so the tower property makes the accumulated
  conditioning invisible afterwards.
  The wrinkle is the default. The earlier prediction — that the value at an
  information state play never reaches costs nothing — is right about
  *well-definedness* and wrong about the *proof*. The default must also be
  **stable under conditioning**, and the one chosen is not: it is read off the
  law's own support, and a conditioned law has a smaller support, so the two can
  disagree at an information state where no consistent policy has mass. The
  behavioral congruence quantifies over histories a run *could* reach rather
  than those a given profile does reach, so that disagreement is visible to it.
  The fix is to parameterize the fallback and hold it fixed across the
  induction, which makes the reading determined up to its behaviour where play
  never goes — a scope statement worth making explicit rather than a defect.
  Recorded rather than applied, because it changes a public definition.

- **Outcome: supports.** `runMixedFrom_toBehavioralWith` is proved. Where every
  player recalls its own play, drawing a whole policy once induces the same law
  as randomizing afresh at each information state — at every fuel and from every
  history the draw could already have reached, which at the start of play is no
  hypothesis at all.
  Parameterizing the fallback closed the gap exactly as diagnosed, and the reason
  is worth keeping: it is the complement of the commitment lemma rather than a
  workaround. Between the original law and the conditioned one the dichotomy in
  the reading is stable — consistent mass survives the conditioning, so the
  marginal branch of one reading is the marginal branch of the other and the
  double conditioning collapses — and the only case the commitment lemma cannot
  reach is fallback against fallback, which a shared fixed parameter makes an
  equality by construction. Together the two cover both branches.
  The statement that results is the honest one: the behavioral reading of a
  single draw is determined up to its behaviour where play never goes.

- **Sixth observation, from comparing with the snapshot.** The conditions proved
  here are cruder than the ones the snapshot proves. Its no-repeat condition
  permits a repeat when the action set there is a subsingleton, and its recall
  direction rests on reach-mass conditions with recall only sufficient. The
  first gap is now closed: the condition is weakened to permit a repeat where the
  *menu* holds a single option — a finer site than the action carrier, since an
  information state can offer many actions and still leave one legal — and the
  counterexample is checked against the weakened form, so the separation survives
  it. The second gap is reserved as its own experiment.
  Two places where the comparison runs the other way, both visible in the
  snapshot's own statements. Its global determinism condition puts a transport
  inside a public hypothesis and its posterior-locality condition is stated
  through `HEq`, both because its information projection lives over
  length-indexed lists; neither appears here, because reachability is intrinsic
  to a history. And its construction takes a global inhabitance instance for the
  action carriers, where the fallback here is derived from the law's own support.

- **Seventh observation: the fallback parameter turned out to be internal.**
  The reading with nothing supplied satisfies the theorem too, because the
  fallback is fixed across the induction whatever it is, and a law's own support
  witness is one such fixed choice. So the parameter is a device the proof needs
  and not part of the result, and the quotable statement carries no trace of it.
  The two directions are now stated together: the laws a profile of locally
  randomizing players can induce are exactly the laws a single draw over policies
  can induce, and both halves are instantiated on the recall-capable slice.

- **Next action:** the reach-mass generalization, reserved separately.

### EXP-019: Reach-mass conditions instead of recall

- **Date / revision:** reserved 2026-07-29, before any attempt
- **Decision / question:** D7, asked again with a candidate consumer. The pinned
  snapshot proves the recall direction not from recall but from three conditions
  about *reach mass*: that two profiles reaching a state give it the same mass,
  that reaching it factors coordinatewise, and that the posterior at an
  information state does not depend on which reaching history produced it.
  Recall is demoted to a sufficient condition. That is strictly more general than
  what is proved here, and it is also, structurally, a named adequacy
  certificate — the stratification rejected earlier on a baseline of zero
  consumers. Restating the theorem over such conditions would be the *first*
  genuine consumer of a certificate level. A second — an encoded language
  discharging the same conditions, or a correlated-realization layer resting on
  the same factorization — would meet the recorded two-consumer budget. So this
  experiment is about the architecture as much as the theorem.
- **Representative slice:** the recall-capable two-vote design, which already
  satisfies both directions' current hypotheses, plus at least one model that
  fails recall while still factoring — the case the generalization is *for*, and
  which nothing here yet exhibits.
- **Prediction, written before attempting.** The three conditions are statable
  transport-free over the existing history and information vocabulary. The
  snapshot states them with a `▸` inside a hypothesis and with `HEq`, because its
  information projection lives over length-indexed lists; histories as data,
  where reachability is intrinsic to the type, should remove both. That is the
  falsifiable part: if the conditions *cannot* be stated without transport, the
  finding is about where the generality belongs — an internal lemma rather than
  a public hypothesis — and it is decision-grade either way rather than a proof
  failure.
  Predicted also: the global determinism side condition the snapshot's
  perfect-recall corollary carries will not be needed, for the same reason, and
  the fallback will not need a global inhabitance instance, since it is already
  derived from the law's own support.
- **Evidence so far:**
  `GameTheory/Experimental/Phase4/ReachMassStatements.lean`
- **First observation: the falsifiable half of the prediction holds.** All three
  conditions are statable in this library's vocabulary with **no transport
  token in any statement** — checked by scanning the file, where the only
  occurrences of `▸` and `HEq` are in prose describing the snapshot.
  How each one avoids it is different, and worth separating. The mass condition
  is direct. The factorization condition needs a pointwise variant of a joint
  action, which *is* a transport in the obvious spelling — the same collision the
  commitment construction met — and none in the coordinate-decomposition
  spelling this layer already uses; so it is avoided by an idiom rather than by
  luck. The posterior condition is the one the snapshot states through
  heterogeneous equality, and quantifying over the information state *before* the
  objects indexed by it removes the need entirely: both sides land in one type by
  construction.
  Sufficiency is checked in the same file, in the direction that matters for not
  fooling oneself: recall implies the posterior condition, because it makes the
  two records equal. So the condition is genuinely weaker than recall rather than
  a restatement of it, and it is not vacuous.
- **Second observation: the generalization is not the snapshot's three
  conditions.** Looking for a model that fails recall while satisfying them
  turned up something better. Nothing downstream reads a player's record except
  through the *set of policies it rules out*, so the hypothesis the proof
  actually uses is that two histories a player cannot tell apart constrain its
  policy the same way. That is `ConstrainsAlike`, it is strictly weaker than
  recall, and the whole recall direction now runs on it — the combined statement
  included.
  The gap is real and cheap to witness: records differing only in the *order* of
  a player's own moves rule out the same policies, so a player that forgets the
  order fails recall and still constrains alike. Multiplicity goes the same way.
  On the snapshot's posterior-locality condition, exactly one direction is
  proved: `ConstrainsAlike` implies it, restated in the experimental file from
  the weaker hypothesis. The converse is an *argument*, not a theorem, and it is
  recorded as such — reweighting by reach probability multiplies the
  compatibility indicator by a constant in the player's own coordinate, and
  constants wash out under normalization. Two gaps keep it from being exact.
  The washout is informal, and the snapshot's condition is *guarded*: it
  constrains nothing when a law's support misses one of the two events, so
  agreement-under-guards is strictly weaker than equality of the constraint
  sets. Closing that would mean guarding `ConstrainsAlike` the same way and
  checking the proof still runs — every use of the set equality does sit inside
  a support-meeting context, so it plausibly does, but it needs a
  support-relative form of the nested-conditioning law and is not attempted
  here.
- **Third observation: the other two conditions have no content here, and the
  reason is structural.** This needs no new experiment — the theorem already
  proved assumes neither, so as hypotheses of *this* theorem in *this* layer
  they are simply unnecessary. What is worth recording is why, and one half of it
  is artifact-backed rather than argued.
  The snapshot must *assume* that reaching a state factors player by player,
  because it conditions on reach probability and reach is not a product event.
  Here the conditioning event is a product event *by construction* — the fibre of
  the joint answer is exactly the per-player answer events — and the split is
  then a theorem about the law type, proved unconditionally: independent draws
  stay independent under conditioning on a product event. So the snapshot's
  factorization hypothesis corresponds to something this layer proves rather than
  assumes.
  The mass condition has no counterpart at all, for the same underlying reason:
  no reach mass is ever formed. The conditioning is on a compatibility event,
  which is `0`/`1`, so there is nothing whose value could depend on the route.
- **Outcome:** narrows, and answers the certificate question negatively for a
  second and better reason. The level rejected earlier had no consumer; this one
  has no *content* — its conditions are either unnecessary or theorems of the
  layer that would have hosted them.
- **Fourth observation: the guarded sharpening is a level without a consumer,
  and the same budget that rejected the certificate rejects it.** Its
  prerequisite is done and was worth doing on its own: nested conditioning now
  asks the smaller event to be smaller only *where the law lives*, which is the
  true statement — what a law does outside its support is not something
  conditioning can see. The earlier form was an artefact of the first proof.
  Threading that through would replace the theorem's hypothesis by one relative
  to the profile being run: the constraint sets need agree only on that
  profile's support. That is genuinely weaker. But it is weaker in a direction
  nothing yet asks for — a model failing the profile-independent condition while
  satisfying the relative one for the profile at hand — and the quotable
  statement would stay the profile-independent one regardless. By the rule this
  project applies to everything else, that is a level to build when something
  needs it and not before.
  Recorded rather than built, and with the extra generality of the underlying
  lemma honestly unexercised at present: its one caller discards it.
- **Next action:** none open. Reopen if a model appears that needs the relative
  condition.

### EXP-020: the reducibility bill for bundled carriers

- **Date / revision:** reserved 2026-07-29, before any change
- **Decision / question:** D1, revisited at its recorded checkpoint. The
  signature-ownership choice — a form *stores* its signature rather than being
  indexed by it — was accepted provisionally, with the cost to be re-measured
  once a second layer had been built on it. That layer exists, and the same
  choice was repeated in it: an execution protocol stores its state and action
  carriers, and an information model stores its signal and information carriers.
  The question is whether the accumulated bill justifies a flip, and it has to be
  asked now because every module added makes a flip more expensive.
- **Measurement, current tree.** Thirty-two `@[reducible]` annotations exist in
  the library and every one of them is forced by a stored carrier. By the
  structure whose instance carries them: execution protocols 12, information
  signals 5, information models 5, the influence diagram's own record 4, and one
  each for a game form, a rational table, a tree strategy type, a Bayesian game,
  and a carrier alias. Not one is there for a reason of its own.
  The unit of cost is therefore *per instance, per structure*: a concrete
  protocol with its signals and its model costs three annotations before it
  proves anything, and forgetting one is not a warning but an elaboration
  failure at some distant use site.
  There is a second cost the count does not show. An induction over the
  history type additionally needs its index written at the structure's
  projection rather than at the carrier the projection reduces to; written the
  other way it fails inside the equation compiler rather than at the statement.
- **Prediction, written before attempting.** A flip removes the annotations and
  replaces them with an index on every mention of the structure, so the question
  is not whether the bill exists but which bill is smaller and which failure mode
  is kinder. Predicted: the indexed form is *not* obviously better, because the
  measured cost is one annotation per instance while the indexed cost is one
  extra argument per *mention*, and mentions outnumber instances by a large
  factor in the proved material. Predicted also that the deciding evidence is
  not the count but the failure mode — an omitted `@[reducible]` fails late and
  confusingly, whereas a missing index fails immediately at the signature.
  If that prediction survives, the outcome is to keep the bundled form and record
  the annotation as a known, bounded tax with a lint rather than a redesign.
- **Evidence:** `GameTheory/Experimental/Phase4/D1/IndexedProtocol.lean` — the
  same execution interface with its two carriers promoted to parameters, carried
  as far as a concrete instance and an induction over histories.
- **Observation: the spike confirms both costs vanish, and refutes the mechanism
  the prediction rested on.**
  Both costs do vanish. The concrete instance needs no reducibility annotation,
  because there is no projection for anything downstream to get stuck on. And
  the induction over histories goes through with its index written at the
  carrier — the spelling that fails under the bundled form, where it must be
  written at the structure's projection instead. Here there is no other way to
  write it.
  The prediction that the count favours bundling is wrong, and wrong about *why*.
  It assumed each mention of the structure pays for the promotion. It does not:
  the thirty-three type positions are absorbed by a `variable` declaration, as
  they are in the spike. What the count actually shows runs the other way — the
  library contains **243** projections of a stored carrier, every one of them a
  site where the reducibility of the instance has to fire, and all of them
  carried by **22** annotations. The bundled form is not paying one annotation
  per instance; it is paying one annotation per instance to keep 243 sites
  elaborating, and an omission is felt at some subset of them rather than where
  it was made.
  So the count does not favour bundling. It is closer to neutral-to-against, and
  the deciding evidence remains the one the prediction did get right: the failure
  mode.
- **Outcome:** *in progress* — the prediction is narrowed rather than confirmed,
  and the decision is not yet made. Two things the spike does not measure: the
  transport burden that made bundling attractive on the static layer in the first
  place, which was the original competition's subject and is not re-run here; and
  whether anything in the library needs a collection of protocols with differing
  carriers, which only the bundled form admits.
- **Second observation: nothing requires bundling, and the static layer halves
  rather than clears.**
  Nothing in the library needs the carriers stored. No structure holds a protocol
  as a field, nothing quantifies over protocols whose carriers must vary, and no
  signature mentions two of them. The one argument that would have settled the
  question in bundling's favour — that some use needs a collection of protocols
  with differing carriers — has no instance here.
  At the static layer, where the decision was actually taken, the cost is
  smaller than the sequential one and the spike says so rather than overstating
  it. Indexing removes the two facts the accepted design must state,
  `mapOutcome_sig` and `mixed_sig`, along with the two annotations that make them
  hold: with no projection there is nothing to state and the form transformers
  can be plain definitions. It does **not** remove the need for the two
  `GameSignature` transformers to be reducible — the indexed form's field types
  still reduce through them. Four annotations against two: a halving, not an
  elimination.
  The cascade is shallow. Exactly two structures store one of these: a form
  stores a signature, and a utility game stores a form.
- **Next action:** the flip cost on real code. Both spikes are greenfield, and
  what a fresh file looks like is not what moving `Execution.lean` and its ten
  dependents costs. That measurement is the one thing still missing, and it is
  the one that decides.

### EXP-021: the one-shot deviation principle

- **Date / revision:** 2026-07-29
- **Decision / question:** the sequential gate recorded the one-shot-deviation
  *interface* but not the principle, and recorded that the principle could not be
  stated because the runner was indexed by state. That obstruction was removed
  earlier. The question is whether the principle now follows, and whether it
  needs anything the layer does not already have.
- **Representative slice:** a coin decides whether the player chooses at all, and
  its one choice is worth `1` against `0` — the smallest protocol in which a
  policy can be locally unimprovable without that being automatic.
- **Evidence:** `GameTheory/Protocol/Backward.lean`;
  `GameTheory/Protocol/Assessment.lean`; `GameTheory/Tests/OneShot.lean`
- **Observation.** The principle holds and needs no new certificate. A chooser
  that no single legal action improves — measured against its *own* continued
  play — is at least as good as every other chooser, at every state. The
  induction runs along the same `Successor` relation the value recursion already
  uses, so the well-foundedness certificate carries both and no second hypothesis
  appears anywhere in the statement.
  It reads forward as well as backward: where both choosers have stopped, the
  same conclusion is a statement about run laws, via the bridge already proved
  between the two semantics. And it meets the assessment interface: a chooser no
  single action improves is *locally optimal* in the context its own continuation
  induces, for any allowed set and any way of turning a choice into a joint
  action.
  **The principle is an equivalence**, and getting there corrected a claim worth
  correcting. It first looked as though the converse were blocked by the same
  pointwise-update obstacle met three times before. It is not, and the reason
  gives the right taxonomy for all four.
  A chooser's *answer* is a joint action, and that type does not mention the
  state — only the legality certificate does. So the chooser that plays one
  action at one state and follows the original elsewhere is constructible with no
  transport of data at all; the certificate is repaired by rewriting inside a
  proof, which is not what the budget measures. The recovery then needs one more
  thing, and the certificate supplies it again: a state is not reachable from its
  own successors, since that would be a descending chain, so the deviant agrees
  with the original everywhere the recursion looks after the first step.
  The taxonomy, replacing the count: the obstacle is real only where a *data*
  type depends on the point being updated. Policies are such a case — a choice's
  type depends on the information state — and that is why the commitment
  construction needed the coordinate decomposition. Choosers are not, and were
  never stuck. Two genuine instances with one shared idiom, one dependent rewrite
  needing its value named, and one case that only looked like the others.
  Both directions are checked on the slice: the grabbing policy satisfies the
  one-step condition, the passing policy provably fails it, and the conclusion is
  not vacuous — passing really is worse at the root. So the principle detects
  optimality rather than something the protocol hands to any policy.
- **Outcome:** supports — the sequential flagship pair is complete.
- **Next action:** the static-core harvest, which has been unblocked since the
  incentive gate and touches none of this. Its first family — elimination of
  strictly dominated strategies — is done and is recorded with the code rather
  than here, since it is ordinary mathematics against a settled API rather than
  an architecture experiment.

### EXP-022: what existence costs, measured before it is bought

- **Date / revision:** 2026-07-29
- **Decision / question:** the harvest's remaining flagship at the static layer
  is an existence theorem that does not assume a potential. The layering was
  built so that convexity and topology stay out of the core until something
  needs them, and the discipline is to measure the import before taking it
  rather than to discover the cost afterwards.
- **Evidence:** probes against the pinned Mathlib, run before writing any proof.
- **Observation, and it refutes the planned route.** **Mathlib has no Brouwer
  fixed-point theorem and no Kakutani fixed-point theorem.** Every occurrence of
  the second name is the Riesz–Markov–Kakutani *representation* theorem, which is
  unrelated; the only fixed-point theorems available are Banach's for contracting
  maps and the order-theoretic ones. Sperner's name is present but attached to
  the antichain theorem, not the lemma about simplex colourings. So the standard
  route to equilibrium existence for finite games is not merely expensive here —
  it is absent *from Mathlib*, and supplying it from scratch would be a topology
  project of its own, far outside this library. **This observation stands; the
  conclusion originally drawn from it did not, and EXP-023 records the
  correction.** Mathlib was treated as the only source of a primitive, which is
  a question about the ecosystem rather than about Mathlib, and the probe run
  here could not answer it.
  The redirect is real and was found by the same search. Mathlib *does* have
  **Sion's version of the von Neumann minimax theorem**, in saddle-point form.
  That reaches the two-player zero-sum flagship, which is the existence result
  this layer can actually have.
  On the dependency question the measurement is more precise than expected.
  Importing Sion's theorem makes **neither `stdSimplex` nor `Polynomial`
  reachable** — the existing probes would not fire on it at all. The budget is
  not spent by the theorem; it is spent by the *bridge*, which has to present a
  finite-support law as a compact convex subset of a topological vector space,
  and that is what pulls convexity in.
- **Outcome:** refutes the planned route and redirects it. General equilibrium
  existence is out of reach at the Mathlib level; zero-sum minimax is in reach,
  and the dependency boundary sits at the law-to-simplex bridge rather than at
  the theorem.
- **Next action:** design that boundary before building on it — a root that Core
  and Protocol do not import, with its own probe expectations recorded rather
  than an exception patched into the existing ones. Nothing needs it until the
  bridge is attempted, so it is queued rather than urgent.
- **Superseded in part by EXP-023.** The redirect to minimax remains available
  and the bridge remains the place the budget is spent. The claim that general
  existence is out of reach does not survive: the primitive exists outside
  Mathlib.

### EXP-023: buying the fixed-point primitive, measured before it is imported

- **Date / revision:** 2026-07-29
- **Decision / question:** EXP-022 concluded that general equilibrium existence
  was out of reach because the pinned Mathlib carries no Brouwer or Kakutani
  theorem. That conclusion silently assumed Mathlib is the only place a
  primitive can come from. It is not: a standalone Lean 4 package proves both.
  The question is therefore not whether the theorem exists but what taking it
  costs, and whether the layering survives the taking.
- **Evidence:** `harfe/fixed-point-theorems-lean4`, pinned in `lakefile.lean` at
  `770940ddf9878cf61952ed53d910b92bca841838`; `lake update`; `lake build
  FixedPointTheorems.kakutani FixedPointTheorems.brouwer`; axiom and
  reachability probes run against the built package.
- **Observation.** Six measurements, all taken before any of our own code
  imported it.

  *Version skew: none.* The package pins `leanprover/lean4:v4.32.0` and
  `mathlib @ v4.32.0`, which are exactly this project's pins. Its README still
  advertises v4.30.0; the repository does not, and the repository is what
  resolves. Predicted skew was two toolchain minors, and the prediction was
  wrong in the favourable direction.

  *Disturbance to the existing dependency graph: none.* After `lake update` the
  manifest gained exactly one entry and every pre-existing revision is
  byte-identical. Mathlib's post-update hook downloaded nothing, which is the
  same fact from the other side.

  *Build cost: six modules, about a minute, and 484 additional Mathlib modules.*
  The full build went from 2558 jobs to 3048. The package's own six are the
  visible cost; the 484 are the real one, and they are convexity, topology, and
  finite-dimensional normed spaces.

  *Trust: clean.* `brouwer_fixed_point` and `kakutani_fixed_point` each depend
  on `propext`, `Classical.choice`, `Quot.sound` and nothing else. No `sorryAx`,
  no custom axiom. This is the measurement that decides admissibility, since a
  dependency carrying a hole would make every theorem above it untrusted.

  *Shape: usable as-is.* Kakutani is stated for a convex compact nonempty
  `s : Set V` in a finite-dimensional real normed space, with `f : s -> Set V`
  having a closed graph and convex nonempty values inside `s`, concluding
  `exists x : s, x.1 in f x`. `closedGraph f` unfolds to
  `IsClosed {z | z.2 in f z.1}`, a plain definition rather than a class. That is
  the best-response correspondence's exact shape, so no restatement layer is
  needed between the package and the equilibrium argument.

  *Containment: the probes fire, and that is the point.* A file importing
  `FixedPointTheorems.kakutani` reaches **both** `stdSimplex` and `Polynomial` —
  the two constants the existing audit requires Core and the executable frontend
  never to see. Where Sion's theorem cost nothing against those probes, this
  package spends the whole convexity budget. So the dependency is admissible
  only behind a root the audited layers do not import, and the audit has to say
  so rather than leave it to discipline.
- **Outcome:** supports, and reopens what EXP-022 closed. The primitive is
  available, trustworthy, and free of version friction; the general existence
  route is a bridge-building problem rather than a topology project. The cost is
  a second external dependency and a genuinely leaky import surface, which the
  boundary exists to contain.
- **Next action:** instantiate `GameTheory.Analysis` as that boundary, with the
  existing six probes required to keep passing and the new root's reachability
  recorded as expected rather than exempted. The v1 snapshot took the same
  dependency and built roughly four and a half thousand lines on it (Schauder,
  KKM, Scarf, the simplex approximation layer, Loomis); the harvest should
  measure how much of that a finite-game existence theorem actually needs before
  porting any of it.
- **Follow-through, same day.** The boundary was instantiated and the theorem it
  was taken for is proved: `GameTheory/Analysis` holds the law-to-simplex
  bridge, the payoff polynomial, and Kakutani applied to the best-reply
  correspondence, and `exists_isNash_mixed` depends on the three standard axioms
  only. Three hundred and fifty-one lines above the dependency, and none of
  v1's four and a half thousand were needed. The containment checks are in
  `scripts/phase2-audit.ps1`; the direction of the new probe is the part worth
  remembering, since it asserts reachability rather than absence.

### EXP-024: what the preference vocabulary is actually about

- **Date / revision:** 2026-07-29
- **Decision / question:** every theorem so far has compared outcome *laws*, so
  nothing has yet tested whether `WeakPreference` is a preference type that
  happens to be applied to laws or a law type wearing a preference's name.
  Social choice is the discriminating case: it ranks alternatives, quantifies
  over all such rankings, and contains no probability at any point.
- **Evidence:** a reading of `GameTheory/Core/Preference.lean` against what a
  social choice theorem needs, followed by the repair and a full rebuild.
- **Observation, and it is a defect.** Of the sixteen declarations in the
  preference vocabulary, **thirteen never mention the law structure they are
  stated over**. Reflexivity, transitivity, totality, the strict part and its
  three lemmas, the weaker-than order, and the whole coalition lifting are
  relation algebra pinned to `FinDist Outcome` for no reason. Only convexity
  under mixing and the pullback along a relabeling use it.
  A second defect sits underneath the first. The vocabulary is *agent-indexed*
  throughout, and a social ranking has no agent: society is one ranking, not a
  family. Stating that society is transitive in the same words the voters are
  transitive was not possible.
  Delegating to Mathlib is not the repair. Its `Transitive`, `Reflexive`, and
  `Total` on bare relations are deprecated in favour of `IsTrans`, `Std.Refl`,
  and `Std.Total`, which are typeclasses — and a preference here must stay an
  argument, since one carrier is routinely studied under several preferences at
  once. Measured, not assumed: the deprecation warnings are what the probe
  returned.
- **Repair, and its cost.** The vocabulary splits in two. `Rank` states each law
  for a single comparison over an arbitrary carrier; `Preference` states it as
  that law holding for every agent, and is *definitionally* that. `Ranking Agent
  α` is the family type and `WeakPreference Agent Outcome` is its specialization
  to laws.
  The cost was zero. Every use site in the library continues to elaborate
  unchanged — 3277 build jobs, no downstream edit, both audits still verified —
  because currying makes the new definitions defeq to the old ones.
- **Downstream theorem.** `Examples/Voting.lean` proves the Condorcet paradox:
  three voters ranking three alternatives in rotation are individually total and
  transitive, and the majority ranking they induce is not transitive, with the
  cycle exhibited. Individual rationality and social irrationality are stated in
  the same words, and no probability appears in either.
- **Outcome:** finds a real defect in a core type and repairs it at no cost. The
  vocabulary was about lotteries by accident rather than by design, and nothing
  had yet asked.
- **Next action:** the repair makes Arrow's theorem statable; it does not make it
  proved. That is the honest next target on this axis, and it will exercise the
  vocabulary far harder than the paradox does.

### EXP-025: information-local compilation and the one-shot bridge

- **Date / revision:** 2026-07-30, working tree based on `ecc927b`
- **Decision / question:** D6 and the RFC's composed execution/information
  requirement; whether information-local pure, behavioral, and mixed policies
  reach `GameForm` through the existing history run laws, and whether a
  unilateral one-shot change has the same law before and after compilation.
- **Representative slice:** compile a finite-horizon `InformationModel` with
  strategies `Policy`, use `run`, `runBehavioral`, and `runMixed` as the only
  evaluators, connect the two randomization representations to the compiled
  form, and instantiate the bridge on the existing imperfect-information test
  protocol.
- **Evidence:** `GameTheory/Protocol/Strategic.lean`,
  `GameTheory/Protocol/Assessment.lean`,
  `GameTheory/Protocol/Information.lean`,
  `GameTheory/Probability/FinDist.lean`,
  `GameTheory/Tests/Strategic.lean`, and
  `GameTheory/Tests/Assessment.lean`. Validation:
  `lake build GameTheory.Protocol.Strategic`,
  `lake build GameTheory.Tests.Strategic`,
  `lake build GameTheory.Protocol.Assessment`,
  `lake build GameTheory.Tests.Assessment`, and the final `lake build`
  (3,278 jobs), all clean. The Phase 0 audit reported
  `EXPECTED_MEASUREMENTS=ok`; the Phase 1, 2, and 3 audits each reported
  `VERIFIED=1`.
- **Observation:** the accepted interfaces carry the slice, with two useful
  refinements exposed by the hostile cases.
  1. Pure information-local policies compile through `run` with histories as
     outcomes. Behavioral policies compile through `runBehavioral`, while the
     ordinary mixed extension of the pure form is definitionally `runMixed`.
     The two existing behavioral/mixed theorems commute with those forms under
     their sharp `ActsOnceWhereItMatters` and `ConstrainsAlike` hypotheses. The
     repeated-information-state counterexample still separates the forms when
     the first hypothesis fails.
  2. The old state-specialized `Context` could not express continuation values
     after two histories merge into one state. Generalizing the same two-field
     concept over its choice and outcome types lets `historyContext` retain the
     history without exposing it to a policy. Menu legality is now carried by
     the typed `Choice`; `IsOneShotOptimalWithin` is exactly
     `IsSequentiallyRationalAt` in these contexts at every history and remaining
     sub-horizon.
  3. Two expectation laws for support-dependent bind are the only new
     probability lemmas needed. Their branchwise monotonicity drives a
     finite-horizon induction: if every current typed choice is locally
     unimprovable, then every whole unilateral replacement policy is no better
     from every history. The from-start corollary is the ordinary static
     `IsNash` of `InformationModel.toGameForm`.
  4. The concrete repeated-vote endpoint is nonvacuous: the accepted profile
     has utility `1`, the down profile has utility `0`, arbitrary replacement
     policies satisfy the global bound, and the compiled profile is Nash.
     Source audits report zero sequential `Function.update`, transport,
     placeholders, and custom axioms. The fixed-player operations require
     decidable equality only for that player's information states.
- **Outcome:** supports and closes the finite-horizon composed-compiler and
  forward one-shot bridge. None of the kill conditions fired: no policy receives
  hidden execution state, no evaluator or equilibrium concept is duplicated,
  and no adequacy record or user-visible transport was introduced. The result
  deliberately does not claim a converse from initial static Nash, which cannot
  inspect off-path histories.
- **Next action:** the remaining sequential theorem is now sharply separate:
  define a genuine subgame-perfect/sequential-equilibrium target before asking
  for a well-founded `oneShotDeviation_iff_spe`. Do not present initial Nash as
  that target. The compiler, finite-horizon context equivalence, and forward
  global theorem are no longer blockers to the next architecture slice.

### EXP-026: kernel-checked finite LP certificates

- **Date / revision:** 2026-07-30, working tree based on `389bfe8`
- **Decision / question:** D10/D12; whether `lp-verify`, `lp-tactic`, or neither
  earns a second external dependency by replacing EXP-007's explicit
  `norm_num` proofs while leaving certificate search outside the trusted base.
- **Representative slice:** first replay one closed rational inequality from
  Matching Pennies, then distinguish that concrete certificate result from the
  stronger claims of correlated-equilibrium feasibility and finite minimax.
- **Competing designs:** keep the current enumeration proofs; import the
  solver-free verifier and check an external certificate; import the tactic but
  provide certificates out of process; or add a solver backend as a separately
  measured dependency.
- **Measurements reserved before import:** toolchain and Mathlib skew; licenses
  of every transitive package; manifest disturbance; source and theorem axiom
  profile; `sorry`, `admit`, `unsafe`, `native_decide`, and FFI use; build jobs
  and platform requirements; import closure with positive and negative
  reachability probes; certificate size, elaboration time, and authored-proof
  reduction against the EXP-007 baseline.
- **Kill conditions:** any checked proof depends on a nonstandard axiom or
  compiler-trust shortcut; the verifier requires a native backend; the
  dependency leaks into Core, Protocol, or `Finite.Algorithm`; no compatible
  pinned revision exists; or the representative proof is not materially
  smaller or more maintainable than the current proof.
- **Evidence:** exact pins, source counts, commands, proof snippets, failed
  goals, and reachability results are preserved in
  [`experiments/EXP-026.md`](experiments/EXP-026.md); the interpretation is
  [`decisions/D13-lp-certificates.md`](decisions/D13-lp-certificates.md).
- **Observation:** trust and containment pass. The verifier, tactic, and
  pure-Lean backend compile on this project's `v4.32.0`; the verifier's tamper
  tests pass; all checked soundness and downstream theorems use only
  `propext`, `Classical.choice`, and `Quot.sound`; and fifteen negative
  reachability probes pass while three positive LP probes fire. The full
  solver-free/tactic/pure-backend candidate adds four Apache-2.0 packages,
  67 Lean files, 9,935 lines, and 49 downstream build jobs including the probe.
- **Disproof:** the representative game theorem does not become smaller.
  `by lp` cannot consume `uniformPennies_verify` before the explicit
  `pennyProfiles`/`sum_pennies` expansion, and after structural simplification
  it rejects the generated goal shape. It can prove the resulting closed
  inequality, but that replaces only the final `norm_num` line. A payoff
  parameter multiplied by an existential probability is rejected as nonlinear,
  so this stack does not by itself prove generic CE existence or minimax.
- **Outcome:** narrows. Kernel-checked LP certificates are admissible in
  principle, but the material-proof-reduction kill condition fired. No package,
  source root, manifest entry, or public API is accepted.
- **Next action:** keep the current EXP-007 proof. Reopen only with a concrete
  finite-game-to-`Problem` bridge plus one generic duality/feasibility theorem,
  or when a downstream theorem can consume a checked certificate without
  retaining the explicit enumeration proof it was meant to replace.

### EXP-027: Arrow through the canonical ranking vocabulary

- **Date / revision:** 2026-07-30, working tree based on `7b184d0`
- **Decision / question:** D4 and Phase 5; whether Arrow's theorem can quantify
  over the accepted `Ranking` family and its named laws, rather than reviving
  v1's separate `PrefRel` vocabulary or silently reinterpreting a weak
  comparison as a strict one.
- **Representative slice:** finite nonempty electorate, at least three
  alternatives, unrestricted profiles of linear weak rankings, collective
  rationality, strict Pareto, and IIA, through the Geanakoplos pivotal-voter
  proof to an exact dictator.
- **Competing designs:** prove directly with weak rankings; use
  `Rank.strict`/reflexive-closure as a private proof representation; or expose a
  second strict-ranking API.
- **Kill conditions:** a second public preference/profile/SWF type is needed;
  constructed profiles cannot be stated through the existing ranking laws;
  public statements must reinterpret argument orientation; or the proof pulls
  probability, game forms, topology, or executable finiteness into its authored
  surface.
- **Evidence:** the theorem inventory is
  `reference/GameTheory-v1/GameTheory/Mechanism/SocialChoice/Arrow.lean` at
  `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`; the adapted proof is
  `GameTheory/Core/Arrow.lean`, and the three-voter/three-alternative public
  witness is `GameTheory/Tests/Arrow.lean`. `lake build
  GameTheory.Tests.Arrow` completed in 842 jobs. `#print axioms
  GameTheory.Arrow.impossibility` reports only `propext`,
  `Classical.choice`, and `Quot.sound`. All four phase audits passed with their
  expected measurements and reachability probes; the final `lake build`
  completed cleanly in 3,281 jobs.
- **Observation:** the pivotal-voter proof reaches an exact dictator while its
  public domain remains `Ranking`, `Rank.Linear`, and `Rank.strict`; strict
  relations, profiles, and aggregators are private proof representations.
  Moving alternatives to the top or bottom and recovering the weak ranking
  require no second semantic type. The first closure probe did expose a real
  leftover defect: importing `SocialChoice` reached `FinDist` because all
  relation algebra still lived physically in `Preference.lean`. Moving that
  algebra to probability-free `Core/Rank.lean` reduced the Arrow target from
  1,715 to 842 jobs. After the repair, both `SocialChoice` and `Arrow` reject a
  `GameTheory.Probability.FinDist` probe.
- **Outcome:** supports D4 with a physical-layer refinement. None of the
  semantic kill conditions fired, and the import-closure defect found by the
  stress test is repaired rather than documented away.
- **Next action:** treat Arrow as closed on this axis. Keep lottery operations
  in `Core/Preference.lean` and all carrier-generic ranking laws in
  `Core/Rank.lean`; proceed to the next Phase 5 stress theorem.

### EXP-028: Shapley value on the parallel coalitional primitive

- **Date / revision:** 2026-07-30, working tree based on `0173c66`
- **Decision / question:** D0 and Phase 5; whether the accepted
  `CoalitionalGame` is sufficient for the Shapley value, its efficiency,
  symmetry, null-player, and additivity laws, and the theorem that those laws
  characterize it uniquely.
- **Representative slice:** finite explicitly enumerable agents, marginal
  contributions, unanimity games and their decomposition, the four Shapley
  axioms, uniqueness on every coalitional game, and the existing three-agent
  majority game as a concrete value calculation.
- **Competing designs:** define the value by weighted marginal contributions;
  average over arrival orders; or introduce extra linear/game-form structure
  and characterize through it.
- **Kill conditions:** the theorem needs strategies, outcomes, probability, or
  `GameForm`; a second coalitional-game or allocation type appears; finiteness
  must be stored in the game; the characterization requires a generic
  certificate hierarchy; or the majority-game witness cannot use the existing
  primitive unchanged.
- **Evidence:** the pinned inventory is
  `reference/GameTheory-v1/GameTheory/Cooperative/CoalitionalGame/Core.lean`
  and `Shapley.lean` at
  `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`; the adapted construction and
  characterization are `GameTheory/Core/Shapley.lean`, and the discriminating
  endpoint is `GameTheory/Tests/Shapley.lean`. `lake build
  GameTheory.Tests.Shapley` completed in 1,070 jobs. Axiom checks for
  `shapleyValue_efficient` and `shapleyValue_characterization` report only
  `propext`, `Classical.choice`, and `Quot.sound`; `Shapley` rejects probes for
  `FinDist`, `GameForm`, and `Polynomial`. All four phase audits passed with
  their expected measurements and reachability probes; the final `lake build`
  completed cleanly in 3,283 jobs.
- **Observation:** the weighted marginal formula, four named rule properties,
  unanimity-basis decomposition, and uniqueness theorem all use the existing
  `CoalitionalGame` and `Allocation`. Explicit `Fintype` enumeration is needed
  by the value and theorems but is not stored in the game. The existing
  majority game is unchanged: its core is empty, its Shapley allocation pays
  each agent `1/3`, and every rule satisfying the four axioms agrees with it.
  The imported proof path is finite algebra only; probability, game forms,
  topology, and the analytic dependency remain unreachable.
- **Outcome:** supports D0's parallel-primitive decision. None of the kill
  conditions fired, and no new semantic wrapper or certificate hierarchy was
  introduced.
- **Next action:** treat the Shapley axis as closed and continue with the next
  Phase 5 stress theorem.

### EXP-029: Bayesian interim semantics through the information boundary

- **Date / revision:** 2026-07-30, working tree based on `9233027`
- **Decision / question:** D0, D5, D6, and Phase 5; whether EXP-008's finite
  common-prior Bayesian form and genuinely interim deviation theorem can leave
  `Experimental`, while the same data compiles through the accepted
  `ExecutionProtocol`/`InformationModel` boundary without a second evaluator
  or equilibrium predicate.
- **Representative slice:** a finite Bayesian game with unstored finiteness
  assumptions; type-contingent plans compiled both directly to `GameForm` and
  through a two-step chance-then-simultaneous protocol whose policies see only
  their own type; exact policy/plan and play-law bridges; and one typed example
  exercising the interim theorem on the protocol-backed presentation.
- **Competing designs:** keep the static probe experimental; make Bayesian
  games a monolithic language module containing equilibrium theory; or split
  stable static data and interim theory from a solution-concept-free protocol
  compiler.
- **Kill conditions:** the protocol policy exposes the full type profile;
  `InformationModel` cannot express the own-type information set or its menu;
  a second Bayes-Nash/evaluation predicate is needed; finiteness must be stored
  in semantic data; the language compiler must import solution concepts; or
  the direct and protocol-induced outcome laws require user-visible transport.
- **Evidence:** `GameTheory/Core/Bayesian.lean` (53 nonblank lines),
  `GameTheory/Core/BayesianEquilibrium.lean` (117),
  `GameTheory/Languages/Bayesian.lean` (386), and
  `GameTheory/Tests/Bayesian.lean` (135). `lake build
  GameTheory.Tests.Bayesian` completed in 1,729 jobs; the final `lake build`
  completed cleanly in 3,287. All four phase audits passed. The Phase 3 audit
  now permanently rejects two solution-concept probes from the Bayesian
  compiler and positively reaches both Bayesian data and the information
  compiler. Axiom checks for `isNash_iff_interim`, `toProtocolForm_play`, and
  `truthful_protocol_isNash` report only `propext`, `Classical.choice`, and
  `Quot.sound`.
- **Observation:** the data module stores no finiteness or decidable-equality
  capability; only the interim decomposition enumerates types. The separate
  equilibrium module promotes EXP-008's theorem without adding `BayesNash`.
  The solution-concept-free language module draws types at chance, exposes
  player `i` only to `View B i`, proves exact policy/plan equivalence, and
  identifies the two-step protocol law with the direct law mapped to completed
  outcomes. In the fair-bit endpoint, truth is interim-optimal and ordinary
  Nash in both presentations.
- **Outcome:** supports D0, D5, and D6 with a physical split. Bayesian games
  need coordinated static and information presentations, but no duplicate
  evaluator, preference, or equilibrium predicate; none of the kill conditions
  fired.
- **Next action:** treat the finite Bayesian axis as closed. Reserve a new
  experiment before starting repeated play or the predicted analytic bridge
  over Protocol.

### EXP-030: repeated play at the finite-prefix/infinite-value boundary

- **Date / revision:** 2026-07-30, working tree based on `d044e1e`
- **Decision / question:** D0, D2, D11, D12, and Phase 5; whether public-action
  repeated games should be represented entirely as protocols, by native
  recursive stage paths plus a finite-prefix protocol compiler, or by a
  stochastic law over infinite histories.
- **Representative slice:** a generic public-action stage game; stationary and
  history-dependent repeated strategies; exact finite-prefix execution through
  `ExecutionProtocol`/`InformationModel`; normalized discounted payoff on the
  deterministic stage path; and the theorem that stationary repetition of a
  bounded stage Nash profile is ordinary Nash of the discounted repeated form.
- **Competing designs:** make Protocol the sole repeated-game representation;
  keep native recursive paths and prove a finite-prefix compiler law; or add an
  infinite-path probability carrier.
- **Kill conditions:** finite-prefix play needs a second transition or
  information interface; discounted equilibrium needs a repeated-specific Nash
  predicate; the stable theorem essentially quantifies over an infinite
  stochastic path law; the fixed-point dependency or measurable probability
  leaks into the stagewise root; or Protocol cannot express public observation
  of the accumulated action history without exposing hidden state.
- **Artifacts / commands:** `GameTheory/Repeated/{Basic,Discounted,Protocol}.lean`,
  `GameTheory/Repeated.lean`, `GameTheory/Tests/Repeated.lean`;
  `lake build GameTheory.Repeated` (1,759 jobs);
  `lake build GameTheory.Tests.Repeated` (1,760 jobs);
  `lake build` (3,292 jobs);
  `scripts/phase2-audit.ps1`; and
  `scripts/phase3-audit.ps1 -VerifyExpected`. The source inventory was
  `Concepts/Repeated/{Basic,Discounted}.lean`,
  `Languages/MultiRound/RepeatedGame.lean`, and
  `Concepts/Welfare/FolkTheorem/Main.lean` in the pinned snapshot at
  `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`.
- **Observations / measurements:** the first candidate stored a dependent
  `Fin t → Profile` history. Equating it with a Protocol prefix immediately
  required proof-dependent transport, firing the kill condition. Replacing the
  canonical history by a chronological `List Profile` makes its length the
  period and lets native recursion and Protocol share the same state
  definitionally. The stable repeated root is 537 nonblank lines (Basic 125,
  Discounted 118, Protocol 280, root 14); the hostile test is 115. It contains
  zero source transport tokens and zero forbidden imports. Basic and Discounted
  reject all four `stdSimplex`/`Polynomial` probes. The three cross-layer
  rejection probes and both positive compiler-input probes pass. The compiler
  exactly reproduces a three-stage history-dependent path. Normalized discounted
  utility is a utility on the existing deterministic repeated form, and
  stationary repetition of a bounded stage Nash profile is ordinary `IsNash`;
  there is no repeated-specific equilibrium predicate and no infinite-path
  `FinDist`. Both flagship paths use only `propext`, `Classical.choice`, and
  `Quot.sound`.
- **Outcome:** supports the native-path/finite-prefix compiler design and D11's
  boundary; narrows public repeated histories to chronological lists. Protocol
  is reused for finite execution and information, not made the sole
  infinite-horizon representation. This experiment does not validate the full
  folk theorem's simplex-approximation geometry.
- **Next action:** reserve a separate experiment before importing or rebuilding
  the full folk-theorem mathematics. Compete a repeated-analysis bridge against
  keeping that geometry inside the stable repeated root, with negative probes
  from `GameTheory.Repeated` and positive probes from any new bridge.

### EXP-031: dependency home for the discounted folk theorem

- **Date / revision:** 2026-07-30, working tree based on `681be12`
- **Decision / question:** D11, D12, and Phase 5; whether the full discounted
  folk theorem's feasible-payoff geometry and simplex approximation belong in
  the stable `GameTheory.Repeated` root, in `GameTheory.Analysis`, or in a new
  one-way analytic bridge over repeated play.
- **Representative slice:** the pinned theorem
  `KernelGame.discounted_folk_theorem_approx`: approximate a feasible payoff
  strictly above every opponent-security level by normalized discounted payoff
  vectors of history-dependent Nash profiles. Preserve its deterministic
  `ℕ`-indexed stage path and ordinary Nash reading.
- **Competing designs:** import the required general mathematics directly into
  stable Repeated; place the theorem under `GameTheory.Analysis.Repeated`,
  importing only Basic/Discounted plus the existing analytic payoff/minimax
  interfaces; or introduce a separate `GameTheory.Repeated.Analysis` bridge
  root with its own reachability budget.
- **Kill conditions:** the stable repeated root starts reaching
  `stdSimplex`/`Polynomial`; the theorem needs a second payoff, mixed-game,
  security, or equilibrium definition; any candidate needs a stochastic law
  over the entire infinite path; the bridge must import Protocol despite using
  no finite execution semantics; or the borrowed geometry costs more or exposes
  more transport than a focused greenfield lemma.
- **Evidence:** the source inventory was
  `Concepts/Welfare/FolkTheorem/{Geometry,Periodic,Trigger,Main}.lean`,
  `Concepts/ZeroSum/SecurityStrategy.lean`, and
  `Math/SimplexApproximation.lean` in the pinned snapshot at
  `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`.
- **Pre-implementation measurement:** the eight apparent v1 support files total
  2,324 nonblank lines. Of those, the 255-line ambient/interior `Geometry.lean`
  contributes no declaration used by the flagship, and the 328-line general
  security file is imported only for a narrower opponent-minmax construction
  already developed inside `Feasible.lean`. The required denominator-clearing
  lemma is a 134-line game-independent file and has no Mathlib equivalent in the
  pinned dependency. Greenfield Analysis currently provides the finite-law
  simplex equivalence, mixed-profile polytope, mixed payoff polynomial, Nash
  existence, and two-player zero-sum minimax. The last two do not directly
  express an `n`-player game against a coalition, so forcing reuse would change
  the punishment value rather than remove duplication. Stable Repeated rejects
  all four `stdSimplex`/`Polynomial` probes; `Analysis.Payoff` reaches both.
- **Selection tested:** place general denominator clearing in the
  independent `GameTheoryMath` target; keep continuation, periodic-path, and
  trigger incentive results in stable Repeated; place feasible-payoff convex
  geometry, opponent-minmax construction, and the existence/approximation
  theorem under `GameTheory.Analysis.Repeated`. Reject
  `GameTheory.Repeated.Analysis`, because directory membership would make the
  audited stable root own the analytic surface. The bridge must import
  Basic/Discounted directly, not the Repeated umbrella, and must not import
  Protocol.
- **Artifacts / commands:** `GameTheoryMath/SimplexApproximation.lean`;
  `GameTheory/Repeated/{Discounted,Periodic,Trigger}.lean`;
  `GameTheory/Analysis/Repeated/{Feasible,Folk,Examples}.lean`;
  `GameTheory/Analysis/Repeated.lean`; `lake build
  GameTheory.Analysis.Repeated.Folk` (1,835 jobs); `lake build
  GameTheory.Analysis.Repeated` (1,844); `lake build
  GameTheory.Analysis.Repeated.Examples` (1,850); and
  `lake build` (3,302); all four phase audits, including
  `scripts/phase2-audit.ps1 -VerifyExpected`.
- **Observations / measurements:** the resulting stable Repeated root is 1,468
  nonblank lines, the analytic repeated subtree including its witness and root
  is 783, and independent `GameTheoryMath` is 185. All three source buckets
  contain zero transport tokens; `GameTheoryMath` imports no game or
  fixed-point module. `GameTheory.Repeated` still rejects both `stdSimplex` and
  `Polynomial` (six negative probes across Basic, Discounted, and the public
  root). The bridge positively reaches the trigger profile, opponent-minmax
  vector, and residual-floor counts, while rejecting `ExecutionProtocol`;
  `GameTheoryMath.SimplexApproximation` rejects `UtilityGame`. No second mixed
  form, payoff evaluator, security hierarchy, equilibrium predicate, or
  infinite-path law was needed. The Prisoner's Dilemma witness proves mutual
  cooperation feasible, permanent defection bounds every mixed best response
  by one, and patient repeated Nash payoffs approach three. The flagship,
  trigger theorem, cycle approximation, and witness use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- **Outcome:** supports the one-way `GameTheory.Analysis.Repeated` bridge and
  the independent `GameTheoryMath` target. None of the kill conditions fired.
  The unused ambient/interior geometry and general security hierarchy were not
  ported.
- **Next action:** treat the deterministic discounted folk-theorem axis as
  closed. Sequential equilibrium remains a separate predicted D12
  renegotiation because its topology sits over Protocol strategy objects.

### EXP-032: analytic boundary for sequential equilibrium

- **Date / revision:** 2026-07-30, working tree based on `fa5bc1e`
- **Decision / question:** D6, D12, and Phase 5; whether pointwise
  Kreps-Wilson consistency should put topology inside Protocol, stay a generic
  user-supplied convergence predicate there, or live in a one-way analytic
  bridge over Protocol.
- **Representative slice:** the finite-information assessment interface over
  behavioral policies and history beliefs; fully mixed approximating
  assessments satisfying Bayes consistency; pointwise convergence to a target
  assessment; and the conjunction with the existing
  sequential-rationality predicate.
- **Competing designs:** import topology into
  `GameTheory.Protocol.Assessment`; keep only a predicate-parameterized limit
  schema in Protocol and define pointwise convergence in
  `GameTheory.Analysis.Protocol`; or specialize the whole notion to a language
  such as EFG under an analytic language bridge.
- **Kill conditions:** Protocol starts reaching `stdSimplex`, `Polynomial`, or
  topology-only constants; policies or beliefs require a second representation;
  the analytic bridge must expose hidden execution state to policies; the
  existing assessment/sequential-rationality API cannot state the rational half
  unchanged; or pointwise convergence needs measurable path probability rather
  than finite-coordinate topology.
- **Evidence:**
  1. The pinned generic assessment, EFG adapter, and convergence helper contain
     406, 560, and 49 nonblank lines respectively. Their topology is isolated
     in the convergence helper; most of the generic file is assessment,
     support, Bayes, and rationality plumbing already represented differently
     by current Protocol.
  2. A pre-import probe after `import GameTheory.Protocol` found
     `TopologicalSpace`, `nhds`, `Filter.Tendsto`, `Continuous`, and
     `Metric.tendsto_atTop` already reachable through Mathlib dependencies.
     Raw topology-name absence therefore cannot enforce this boundary.
     GameTheory declaration probes can: Protocol rejects both
     `FinDistConvergesPointwise` and `IsSequentiallyConsistent`, while the
     bridge positively reaches stable sequential rationality, finite Bayes
     consistency, and its pointwise convergence definition.
  3. The first assessment carrier was refuted before the gate. A raw
     `InfoState` value need not be produced by any history, so requiring a
     `FinDist` over its empty history fiber could make the whole assessment
     type uninhabited. `InformationSite` now pairs an information-state value
     with a nonempty history fiber. `BehavioralAssessment.ofStrategy` proves
     every existing behavioral strategy admits an assessment. Beliefs remain
     over histories, because two histories can merge into one execution state;
     `stateBelief_onInfoSet` projects them to the existing state-level
     `BeliefOn` predicate.
  4. The stable addition is 142 nonblank lines in
     `Protocol/BehavioralAssessment.lean` plus the six-line
     `FinDist.FullSupport` interface. The analytic subtree is 188 nonblank
     lines: pointwise strategy and belief convergence, fully mixed and Bayes
     approximants, sequential consistency/equilibrium, and a Boolean tremble
     witness. Fully mixed laws converge there to a pure law, so the topology is
     load-bearing rather than decorative. No second policy, runner,
     state-belief, local-optimality, or equilibrium semantics was introduced.
  5. The narrow bridge build completed in 1,768 jobs. Phase 2 reports zero
     Analysis imports outside its root, one fixed-point importer, zero
     Analysis transport, and all six stable reachability probes passing.
     Phase 3 reports zero forbidden Protocol imports and transport, two
     Protocol-to-Analysis rejections, three positive bridge inputs, and two
     rejected fixed-point-geometry probes. The full build completed in 3,306
     jobs and all four phase audits pass. Axiom checks for the history-to-state
     belief projection, tremble convergence, and convergence projection use
     only `propext`, `Classical.choice`, and `Quot.sound`.
- **Outcome:** supports a second one-way bridge,
  `GameTheory.Analysis.Protocol`. Stable Protocol owns reachable information
  sites, behavioral assessments, history-supported beliefs, finite Bayes
  consistency, and predicate-parametric limit consistency; the bridge owns
  pointwise topology and its Kreps-Wilson specialization. The raw
  topology-name subcondition was already true at baseline, so it refuted
  vocabulary absence as an enforcement design rather than the bridge; no
  semantic kill condition fired. The experiment validates this presentation
  and dependency direction; it does not claim an EFG compiler or a
  sequential-equilibrium existence theorem.
- **Next action:** treat the generic sequential-consistency boundary as
  closed. Reserve a separate language spike before adapting the pinned
  560-line EFG layer; that compiler must supply continuation contexts and
  finite information-site fibers rather than widening this bridge in advance.
- **Post-experiment correction (EXP-033):** the EFG hostile slice narrowed two
  stable claims without changing this boundary result. A nonempty history fiber
  does not by itself make an information state a decision site: reached chance,
  inactive, and terminal observations need no assessment belief.
  `InformationSite` now also witnesses a nonterminal history and a genuine
  action in the local menu.
  Moreover, local-law optimality is not sequential rationality without a proved
  one-shot-deviation principle. The generic predicate now compares whole
  continuation behavioral policies; a future local-law specialization must
  prove that reduction.

### EXP-033: finite EFG adapter for sequential assessments

- **Date / revision:** 2026-07-30, working tree based on `4db0eb9`
- **Decision / question:** D6, D12, and Phase 5; whether a finite
  extensive-form language can compile through the accepted general-state
  Protocol and instantiate EXP-032's assessment boundary without creating
  parallel policy, evaluator, belief, rationality, or equilibrium semantics.
- **Representative slice:** a finite single-mover tree with chance and two
  distinct decision histories in one information set; compilation to
  `ExecutionProtocol` and `InformationModel`; finite information-site fibers;
  a behavioral assessment and its history-supported belief; and the
  language-specific continuation contexts consumed by
  `IsSequentialEquilibriumFor`.
- **Competing designs:** expose `Protocol.Tree` plus information labels as the
  language; define independent recursive EFG syntax and prove a compiler
  correct; or reject a generic EFG layer and keep sequential assessments
  protocol-native.
- **Kill conditions:** EFG syntax imports a solution concept or
  `GameTheory.Analysis`; compilation introduces a second runner or policy
  representation; finite information-site instances require
  `Fintype.ofFinite`, user-visible transport, or proof-heavy public casts; a
  policy can recover hidden execution state; continuation contexts cannot reuse
  `Context.IsLocallyOptimal`; or the adapter needs measurable path probability.
- **Evidence:**
  1. The pinned `Languages/EFG/Syntax.lean` and `Sequential.lean` contain 452
     and 560 nonblank lines. The current finite `Protocol.Tree` has neither
     information labels nor a law identifying actions at two nodes in one
     information set. Adding those fields would build a second information and
     policy presentation before it supplied any new semantics.
  2. The winning presentation is therefore a transparent specialization:
     `Languages/EFG.lean` is 52 nonblank lines and stores exactly an
     `ExecutionProtocol`, its `InformationModel`, tree-shapedness, and the
     single-mover law. It defines no recursive syntax, transition, runner,
     policy, payoff, belief, or equilibrium. Finiteness is supplied by the
     theorem that needs it rather than stored in the game.
  3. The 300-line hostile test has a nondegenerate chance step, two distinct
     decision histories carrying different hidden Boolean states, and one
     shared `acting` information state. Its belief gives both histories positive
     support. The execution state records the full position, so tree-shapedness
     is proved rather than obtained by merging histories or proof irrelevance;
     the player's view still cannot recover nature's bit.
  4. The test refuted two assumptions inherited from EXP-032. First, a reached
     raw information state may describe chance, inactivity, or termination, so
     assessments now range only over reached decision sites with a witnessed
     nonterminal history and `some action` in the menu. This explicit
     nonterminal witness matters because Protocol deliberately leaves `active`
     unconstrained after play stops. Second, changing only the law at the
     current information state is not a general sequential deviation.
     `IsSequentiallyRationalAt` now compares the player's whole
     `BehavioralPolicy`, and `continuationContext` runs that replacement from a
     history sampled by the assessment belief. A one-shot reduction, if wanted,
     is a theorem with its own hypotheses rather than definitional semantics.
  5. Tree-shapedness gives an explicit equivalence between complete histories
     and reachable states. A finite state carrier therefore supplies
     `Fintype History` through `Fintype.ofEquiv`; the source uses no
     `Fintype.ofFinite`, direct `Function.update`, visible transport, custom
     axiom, or placeholder. The analytic EFG adapter is 63 nonblank lines and
     only supplies these finite instances plus the canonical continuation
     contexts to the generic Protocol predicate.
  6. The analytic adapter plus hostile test build completed in 1,771 jobs. An
     initial placement under `GameTheory/Tests` made Phase 2 report
     `ANALYSIS_IMPORTED_OUTSIDE_ROOT=1`; moving the same integration witness to
     `GameTheory/Analysis/Protocol/EFGTest.lean` restored zero without weakening
     the audit. Phase 3 reports zero forbidden Protocol or Languages imports
     and zero transport. Stable EFG syntax rejects three solution or analysis
     probes while positively reaching all three semantic inputs; the analytic
     adapter positively reaches all three bridge inputs.
  7. The full build completed in 3,309 jobs and all four phase audits pass.
     Axiom checks for the mixture-support lemma, history equivalence and
     enumeration, hostile tree proof, and EFG adapter theorem use only
     `propext`, `Classical.choice`, and `Quot.sound`.
- **Outcome:** supports the transparent specialization and closes the finite
  presentation gate. No independent EFG syntax/compiler survived the
  competition: the language object is a named bundle of the canonical Protocol
  semantics and structural laws, and the analytic adapter is one-way. The
  experiment validates that an imperfect-information assessment and the full
  sequential-equilibrium proposition can be stated on this carrier. It does
  not prove that the exhibited assessment is consistent or rational, and it
  proves neither a concrete sequential equilibrium nor an existence theorem.
- **Next action:** reserve a theorem spike for an actual finite-EFG sequential
  equilibrium witness or existence result. Broad harvesting of the pinned EFG
  theorem surface remains gated on that mathematical slice rather than on more
  presentation machinery.

### EXP-034: concrete sequential equilibrium on the hostile finite EFG

- **Date / revision:** 2026-07-30, working tree based on `adf1acc`
- **Decision / question:** D6, D12, and the finite EFG theorem gate; whether the
  EXP-033 hidden-information carrier supports a proved sequential-equilibrium
  assessment, not merely a well-typed target.
- **Representative slice:** the same fair hidden Boolean chance move and shared
  decision information set; a fully mixed behavioral policy, the conditional
  belief induced by reach probability, sequential consistency, and
  full-continuation-policy rationality for an explicit payoff.
- **Competing designs:** prove the constant fully mixed assessment directly;
  first extract the generic theorem that a fully mixed Bayes-consistent
  assessment is sequentially consistent and instantiate it; or retreat to a
  simpler perfect-information witness if the hostile Bayes denominator cannot
  be controlled without new semantics.
- **Kill conditions:** the proof needs a second path-probability definition,
  hand-asserted consistency, measurable infinite paths, an EFG-specific
  equilibrium predicate, `native_decide`, a custom axiom, or a representation
  change merely to normalize the finite Bayes calculation.
- **Evidence:**
  1. Stable Protocol now constructs `bayesBelief` by normalizing the existing
     `historyReachProbability` weights at any finite positive-mass information
     site. Its probability theorem is definitionally the quotient already used
     by `IsBayesConsistentAt`; no second path law or conditional-belief
     predicate was introduced.
  2. Two generic reductions keep the EFG proof honest and small at the semantic
     boundary. Zero continuation payoff makes every whole replacement policy
     sequentially rational. A fully mixed, finite-Bayes-consistent assessment
     is sequentially consistent via the constant approximating sequence, using
     pointwise convergence of constant finite laws.
  3. The hostile carrier's fully mixed policy maps the fair coin into both
     decision actions and has full support at every genuine information site.
     The actual one-step behavioral runner assigns each hidden decision history
     probability `1 / 2`; this is proved through the canonical randomized
     chooser and runner, not asserted by a second evaluator. One such history
     proves the information mass is positive.
  4. The resulting assessment uses `bayesBelief` at every site, proves finite
     Bayes consistency, then proves `game.IsSequentiallyConsistent` and
     `game.IsSequentialEquilibriumWithin ... payoff 2`. The payoff is
     identically zero, so this slice deliberately makes the Bayes/consistency
     path hostile while keeping the rationality calculation transparent.
  5. The narrow analytic EFG test build completed in 1,770 jobs. Source scans
     find no `Fintype.ofFinite`, direct `Function.update`, transport, custom
     axiom, placeholder, or `native_decide`. Axiom checks for the Bayes
     constructor, zero-payoff rationality, constant-sequence consistency,
     one-step reach calculation, and final equilibrium theorem use only
     `propext`, `Classical.choice`, and `Quot.sound`.
  6. A first direct normalization proof used four `change` tactic tokens, and
     Phase 2 rejected it with `TRANSPORT_ANALYSIS_SOURCE=4`. Rewriting the same
     definitional steps with typed goals restored the enforced value to zero;
     no audit allowance changed. The full build completed in 3,309 jobs and all
     four phase audits pass.
- **Outcome:** supports. The same chance/imperfect-information EFG used to
  validate the adapter now has a kernel-checked sequential-equilibrium witness.
  The result exercises full support, the real behavioral runner, positive
  information mass, Bayes normalization, pointwise consistency, and the
  generic EFG predicate. It is a concrete existence witness, not a general
  finite-EFG existence theorem; zero payoff means it does not yet stress a
  nonconstant continuation calculation.
- **Next action:** the presentation gate is no longer blocking theorem
  recovery. Begin a measured harvest of the pinned finite-EFG theorem inventory,
  with the first nonconstant-payoff or one-shot result kept as the next hostile
  check on whole-policy rationality.

### EXP-035: nonconstant-payoff rationality on the hostile finite EFG

- **Date / revision:** 2026-07-30, working tree based on `f23e3ef`
- **Status:** complete
- **Decision / question:** D6, D12, and delivery gate W1-A; whether the
  EXP-034 fully mixed Bayes assessment is sequentially rational for a
  nonconstant payoff that depends on nature's hidden bit and the player's
  action, using the generic whole-policy continuation context.
- **Hypothesis:** on the fair hidden-bit game, payoff one for matching the
  hidden bit and zero otherwise gives every information-local action law value
  `1 / 2`. The fully mixed assessment is therefore sequentially rational even
  against an arbitrary replacement behavioral policy, while the existing
  Bayes/consistency proof remains unchanged.
- **Representative slice:** define the matching payoff on terminal histories;
  calculate the continuation value from both hidden decision histories through
  `runBehavioralFrom`; average through the canonical Bayes belief; prove
  `IsSequentiallyRationalWithin` for every whole replacement policy; combine it
  with EXP-034 consistency into an EFG sequential equilibrium.
- **Competing designs:** prove the arbitrary-policy value formula directly on
  the existing continuation context; first expose a reusable fair-hidden-state
  expectation lemma; or, if the explicit finite calculation reveals missing
  structure, record the smallest honest assessment/payoff interface change
  before broad EFG harvesting.
- **Kill conditions:** the proof needs an EFG-specific rationality predicate, a
  second evaluator or path-probability law, access to the hidden state through
  the policy, hand-asserted belief probabilities, measurable infinite paths,
  `native_decide`, a custom axiom, or a transport/audit exception.
- **Planned artifacts / commands:**
  `GameTheory/Analysis/Protocol/EFGTest.lean`;
  `lake build GameTheory.Analysis.Protocol.EFGTest`;
  `pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected`;
  `pwsh -NoProfile -File scripts/phase3-audit.ps1 -VerifyExpected`;
  focused axiom and source audits.
- **Evidence:**
  1. `matchingPayoff` pays one exactly when the terminal action equals nature's
     hidden bit. `runBehavioralFrom_decision_matchingPayoff` evaluates that
     payoff through the canonical randomized history runner for an arbitrary
     whole replacement policy. Projecting the dependent legal `Choice` to
     `Option Bool` was sufficient; no policy receives the hidden state.
  2. The history fiber at the acting information state is proved equivalent to
     `Bool` from reachability and tree-shaped trace uniqueness. Consequently
     the existing reach calculation proves the information mass is exactly
     one, and `fullyMixedAssessment_belief_acting` identifies the canonical
     normalized `bayesBelief` with the explicit fair two-history mixture. No
     belief probability is asserted separately.
  3. `continuationContext_matchingPayoff_value` proves value `1 / 2` for every
     replacement behavioral policy. The two hidden states contribute
     complementary action indicators, so legality of the acting menu and total
     probability mass close the calculation without enumerating a particular
     strategy.
  4. The generic whole-policy predicate then proves
     `fullyMixedAssessment_isSequentiallyRationalWithin_matchingPayoff`; the
     unchanged EXP-034 consistency theorem yields
     `fullyMixedAssessment_isSequentialEquilibrium_matchingPayoff`.
  5. `lake build GameTheory.Analysis.Protocol.EFGTest` completed in 1,770 jobs.
     All four phase audits pass their expected measurements. In particular,
     `TRANSPORT_ANALYSIS_SOURCE=0`, `SORRY_OR_ADMIT=0`,
     `CUSTOM_AXIOM=0`, all EFG syntax/bridge probes retain their expected
     direction, and a focused source scan finds none of the experiment's
     forbidden tokens.
  6. Axiom checks for the branch calculation, exact information mass, Bayes
     belief identification, arbitrary-policy value theorem, and final
     sequential equilibrium use only `propext`, `Classical.choice`, and
     `Quot.sound`.
- **Outcome:** supports. Nonconstant payoff and Bayes consistency now coexist
  on the same hostile chance/imperfect-information EFG, and rationality holds
  against arbitrary whole replacement policies through the accepted generic
  continuation context. None of the kill conditions fired; W1-A is complete.
- **Next action:** use this fixed rationality target to close W1-B's public SPE
  and full well-founded one-shot-deviation semantics before broad finite-EFG
  equilibrium harvesting.

### EXP-036: well-founded information-local one-shot deviation iff SPE

- **Date / revision:** 2026-07-30, working tree based on `f23e3ef`
- **Status:** complete
- **Decision / question:** D6 and delivery gate W1-B; whether the accepted
  execution/information split supports a public strategic subgame-perfect
  predicate and a full one-shot-deviation equivalence without returning to
  v1's syntax-recursive EFG evaluator.
- **Hypothesis:** lift `WellFoundedPlay` from states to complete histories and
  define terminal continuation value by well-founded recursion on history
  extension. Subgame perfection can then quantify, for every player and every
  history including off-path histories, over arbitrary replacement
  information-local policies. Under `ActsOnceWhereItMatters`, this is
  equivalent to the existing typed one-choice deviation followed by the
  original profile.
- **Representative slice:** a stable Protocol theorem over an arbitrary
  `InformationModel`; multi-player utility, arbitrary whole-policy deviations,
  every complete history, and a local replacement choice at each nonterminal
  history. Exercise both directions on a finite tree-shaped EFG with an
  explicitly off-path decision history.
- **Competing designs:** port v1's recursive `GameTree`/subtree predicate;
  expose the existing single-controller state-chooser theorem under an SPE
  name; retain only the finite-horizon forward theorem; or add the
  history-level well-founded strategic theorem and keep the finite EFG layer a
  transparent specialization.
- **Kill conditions:** the result calls a controller optimum SPE, quantifies
  only from the initial history, assumes finite outcomes or a uniform numeric
  horizon, requires a second transition/evaluation law, lets a policy inspect
  hidden execution state, imports Analysis into Protocol, needs transport or
  `Function.update`, or cannot prove the converse under the exact no-revisit
  condition already used by the representation theorem.
- **Planned artifacts / commands:**
  `GameTheory/Protocol/SubgamePerfect.lean`;
  a focused Protocol/EFG probe;
  `lake build GameTheory.Protocol.SubgamePerfect`;
  phase 2 and phase 3 audits; focused source and axiom checks.
- **Evidence:**
  1. `HistorySuccessor` is the inverse image of the accepted state successor
     relation under `History.state`, so `WellFoundedPlay` lifts without a new
     path order. `historyBackwardValue` recurses on complete histories while
     every recursive call is still justified by a realized step in the
     canonical transition law.
  2. `historyBackwardValue_eq_expect_runHistoryFor` proves that the new
     well-founded view equals the existing forward history runner wherever the
     latter has stopped. This is the same semantic join used by state-level
     `backwardValue`; no second transition or path-probability law was added.
  3. `InformationModel.IsSubgamePerfect` quantifies over every player, every
     arbitrary whole replacement policy, and every complete history.
     `HasNoProfitableOneShotDeviation` changes one typed legal choice and then
     returns to the original profile. Both use player-specific terminal
     utility, not a controller optimum.
  4. The forward implication is well-founded induction over histories. The
     converse uses `Policy.replaceAt` plus `ActsOnceWhereItMatters` to prove the
     persistent replacement is observationally invisible after the first
     step. The public iff assumes neither finite outcomes, a uniform numeric
     horizon, perfect information syntax, nor bounded utility.
  5. The finite perfect-information probe has an incumbent that exits
     immediately and is optimal against every whole replacement policy from
     the initial history. A legal later decision history is proved absent from
     the incumbent run support, yet rewarding there is worth one and the
     incumbent's punishment is worth zero. The profile therefore fails SPE
     exactly because of an off-path profitable one-shot deviation. The probe
     also specializes both directions of the generic iff.
  6. The focused build completed in 1,732 jobs and the full build in 3,311
     jobs. Phase 2 and Phase 3 audits pass with
     `TRANSPORT_PROTOCOL=0`, `FUNCTION_UPDATE_SEQUENTIAL=0`,
     `SORRY_OR_ADMIT_SEQUENTIAL=0`, `CUSTOM_AXIOM_SEQUENTIAL=0`, and all
     boundary/reachability probes unchanged. Phase 0 and Phase 1 audits also
     retain their expected measurements.
  7. Axiom checks for the forward-run join, both implications, the iff, initial
     optimality, and off-path rejection use only `propext`,
     `Classical.choice`, and `Quot.sound`.
- **Outcome:** supports. The accepted Protocol layer carries an honest
  well-founded strategic SPE predicate and the full one-shot-deviation
  equivalence, including off-path histories. None of the kill conditions
  fired; W1-B and the frozen F4 semantic theorem are complete.
- **Next action:** keep any EFG syntax wrapper thin during L-EFG harvesting,
  and move the Wave 1 critical path to F2 no-regret-to-CCE and F8 stochastic
  monitoring while T1 proceeds independently.

### EXP-037: incomparable MAID decisions without false serialization

- **Date / revision:** 2026-07-30, working tree based on `eb17f87`
- **Status:** complete
- **Decision / question:** D6, D14, and the L-MAID/T3 delivery gate; whether a
  MAID with two causally incomparable decision nodes can compile to the
  accepted execution/information layer without asserting that either decision
  precedes the other.
- **Hypothesis, recorded before implementation:** compile the current minimal
  frontier as one Protocol step. Incomparable decisions are then simultaneous
  active players whose joint action advances the frontier once. Each policy
  sees common resolved parents but neither decision sees the other's current
  action. The exact terminal outcome law should equal direct evaluation of both
  decision rules under the shared chance law.
- **Representative slice:** one nondegenerate Boolean chance node; two Boolean
  decision nodes owned by different agents, both observing chance and
  incomparable with each other; one utility node depending nontrivially on both
  decisions. The hostile tests must show that both players are active at the
  same history, each decision changes the law, observation matters, and there
  is no intermediate state in which only one decision has been recorded.
- **Competing designs:** serialize an arbitrary topological order while hiding
  the first action from the second policy; batch the antichain frontier into a
  simultaneous joint step; or keep the concrete linear MAID and reject a
  general public MAID until a different execution representation exists.
- **Kill conditions:** any fake player or padding action beyond Protocol's
  canonical `none`; a state that records one incomparable decision before the
  other; a policy that can inspect the other current action or hidden execution
  state; a second evaluator; outcome-law dependence on an arbitrary order;
  transport/audit exceptions; or a public API frozen before the hostile slice
  and D14 measurement are complete.
- **Planned artifacts / commands:**
  `GameTheory/Experimental/PostArchitecture/MAIDIncomparable.lean`;
  `lake build GameTheory.Experimental.PostArchitecture.MAIDIncomparable`;
  source and axiom audits; full phase audits if the spike is promoted.
- **Evidence:**
  1. The 406-nonblank-line experimental module has 58 declarations, all under
     `GameTheory.Experimental`; no stable declaration or import changed. Its
     only authored import is `GameTheory.Protocol.Information`. The generated
     project import graph has six prerequisites: `FinDist`, Execution,
     Extraction, History, Randomized, and Information; it reaches no language,
     solution-concept, or Analysis root.
  2. At `.chanceKnown signal`, both source agents are active and one legal joint
     transition records both decisions. The state type has no constructor for
     a partially recorded frontier, and `decisions_commit_together` proves
     every supported target contains both choices.
  3. Policies receive only the shared resolved chance parent. The compiled
     three-step information-local run is proved equal to the direct law; no
     second transition or evaluator was introduced.
  4. Separate hostile theorems prove that changing either decision changes the
     outcome law and that observing the common parent raises expected payoff
     from one to two. The slice is therefore not validated by a vacuous or
     policy-insensitive diagram.
  5. The focused target builds in 1,718 jobs. Source scans report zero
     `sorry`, `admit`, `native_decide`, direct `Function.update`, transport
     tokens, `HEq`, or tactic `change`.
  6. Axiom checks for the run law, simultaneous-commit theorem, and all three
     outcome-dependence theorems use only `propext`, `Classical.choice`, and
     `Quot.sound`.
  7. The full build completes in 3,326 jobs. Phase 0, Phase 1, Phase 2, and
     Phase 3 audits pass with their expected measurements and reachability
     probes. The first Phase 2 run correctly rejected the new file as
     unbucketed; the audit now gives post-architecture experiments an explicit
     zero-transport budget instead of silently folding them into a historical
     phase.
- **Outcome:** supports. Frontier batching passes the hostile incomparable-node
  gate without a fake order, fake player, padding action, hidden-state policy,
  transport exception, or new runner. D14 adopts it as the compilation
  invariant for general MAID work. This fixed antichain is evidence for the
  design, not an implementation of arbitrary finite DAG syntax or T3.
- **Next action:** inventory T3 at declaration level, then implement the
  smallest general finite-DAG MAID whose frontier compiler specializes to this
  slice before proving the named MAID-to-EFG laws.

### EXP-038: same-owner incomparable decisions

- **Date / revision:** 2026-07-30, working tree based on `2964804`
- **Status:** complete
- **Decision / question:** D6, D14, and T3; whether one Protocol action and
  information state per source player can batch multiple incomparable
  decision sites without letting one site depend on another site's private
  parents.
- **Hypothesis, recorded before implementation:** naive per-player batching is
  too permissive. If one player owns two incomparable decisions, the left site
  observes only a left chance bit, and the right site observes only a right
  chance bit, a combined frontier view exposes both bits while choosing both
  actions. It therefore admits a cross-reading action pair that no pair of
  native local decision rules can implement.
- **Representative slice:** two independent Boolean chance parents; one player;
  two incomparable Boolean decisions with disjoint singleton observation
  sets; a candidate compiled policy returning the other site's observed bit at
  each decision. Prove that no `leftRule : Bool → Bool` and
  `rightRule : Bool → Bool` agrees with this policy on all four parent
  assignments.
- **Competing designs:** restrict stable MAIDs so a player's decisions are
  ancestry-comparable; add a named locality certificate around batched
  per-player actions; index Protocol actors by decision sites and regroup
  deviations by owner; or keep order-free frontier evaluation native and
  translate to a serialized EFG whose information sets hide incomparable
  actions, proving the result independent of the chosen topological order.
- **Kill conditions:** calling the combined view information-local without a
  proof; admitting a target EFG strategy with no native counterpart; treating
  decision sites as source players in equilibrium statements; weakening the
  frozen T3 claim silently; or freezing general syntax before the mismatch is
  resolved.
- **Evidence:**
  1. `GameTheory/Experimental/PostArchitecture/MAIDSameOwner.lean` defines
     native policies as site-indexed local Boolean rules and the naive compiled
     policy as a function from the combined parent view to both actions.
  2. `crossReading` sends each action to the parent observed only by the other
     site. Both dependence theorems are nonvacuous, while native left and right
     noninterference are definitional equalities.
  3. `crossReading_not_representable` proves no native local policy maps to
     that compiled policy. Thus the combined-view target is strictly larger,
     not merely presented differently.
  4. The slice is 68 nonblank lines and 13 declarations, imports no GameTheory
     module, builds in 105 jobs, and has zero placeholder, native-decision,
     direct-update, or transport tokens.
  5. Axiom checks for non-representability and both native noninterference laws
     report no axioms.
  6. The integrated full build completes in 3,329 jobs, and Phase 2/3 boundary,
     trust, and reachability audits retain their expected values.
- **Outcome:** refutes naive per-player frontier compilation. EXP-037 remains
  valid as an execution-law result for a distinct-owner antichain, but its
  combined information view cannot generalize to arbitrary MAIDs.
- **Next action:** keep site-local policy in the native typed-DAG semantics and
  use its order-free frontier evaluation as the reference law. Translate to an
  explicitly ordered EFG whose decision information hides all incomparable
  assignments, then prove outcome order independence and a true strategy
  correspondence. Do not expose a general frontier `InformationModel`.

### EXP-039: capability-parametric finite DAG substrate

- **Date / revision:** 2026-07-30, working tree based on `2964804`
- **Status:** complete
- **Decision / question:** D9, D14, and T3; whether the reusable DAG fragment
  needed by general MAIDs can be recovered as game-independent mathematics
  without storing `Fintype`/`DecidableEq` in semantic graph data or fixing the
  public node carrier to `Fin n`.
- **Hypothesis, recorded before implementation:** define acyclicity for any
  relation and a topological-order certificate for any predecessor function.
  Require finite enumeration only on the theorem that constructs an order.
  The predecessor's well-founded construction should generalize from `Fin n`
  to an arbitrary finite carrier while its MAID-specific API is discarded.
- **Representative slice:** a four-node diamond with two incomparable middle
  nodes. Derive a topological order from acyclicity and prove every direct and
  transitive predecessor occurs earlier.
- **Competing designs:** port the pinned `Fin n` API; store an explicit rank or
  order inside every MAID; use an arbitrary node carrier with an acyclic
  predecessor relation and derive an order under operation-local finite
  capabilities; or find an existing Mathlib theorem.
- **Mathlib search:** local source search found undirected
  `SimpleGraph.IsAcyclic` but no directed topological-order construction for a
  finite predecessor relation.
- **Kill conditions:** game imports in the reusable module; finiteness stored in
  graph semantic data; user-visible transport through an equivalence with
  `Fin n`; a custom axiom; or inability to recover parent-before-child and
  ancestor-before-descendant facts on the diamond.
- **Evidence:**
  1. `GameTheoryMath/DAG.lean` is 194 nonblank lines and eight declarations. It
     defines relation acyclicity and a list topological-order certificate for
     an arbitrary carrier. Neither object stores a finite-carrier capability;
     only `topologicalOrder_of_acyclic` assumes `Fintype` and `DecidableEq`.
  2. The well-founded minimal-vertex construction is adapted from pinned
     `Math/DAG.lean`, but its `Fin n`, length-equals-`n`, and game-adjacent
     surface are removed. The public facts are direct-parent order,
     transitive-ancestor order, construction, and the converse acyclicity
     certificate.
  3. The 85-nonblank-line diamond probe derives an order for an arbitrary
     four-constructor carrier, proves the middle vertices incomparable, and
     exercises direct and transitive predecessor ordering.
  4. Focused builds complete in 1,666 jobs. The reusable module has no
     GameTheory import or project dependency, and `GameTheoryMath` continues to
     import no game module.
  5. Both files have zero placeholder, native-decision, direct-update, or
     source transport tokens. Axiom checks use at most `propext`,
     `Classical.choice`, and `Quot.sound`; the choice occurs only when deriving
     an order or choosing the diamond witness.
  6. The integrated full build completes in 3,329 jobs. Phase 2 reports
     `TRANSPORT_GAMETHEORYMATH_SOURCE=0`,
     `GAMETHEORYMATH_FORBIDDEN_IMPORTS=0`, and
     `GAMETHEORYMATH_GAME_REJECTED=1`; all Phase 2/3 expected boundary and
     reachability probes pass.
- **Outcome:** supports. The reusable DAG proof survives with a better
  capability boundary and no public `Fin n` transport. No kill condition
  fired.
- **Next action:** define experimental typed MAID syntax over this arbitrary
  node carrier, with site-local policies and order-free frontier evaluation;
  do not promote the syntax until the same-owner and diamond probes instantiate
  it.

### EXP-040: heterogeneous site-local frontier evaluation

- **Date / revision:** 2026-07-30, working tree based on `9bdc140`
- **Status:** complete
- **Decision / question:** D2, D9, D14, and T3; whether a general typed MAID can
  keep heterogeneous node values and native site-local policies while
  evaluating every currently minimal unresolved node in one order-free
  frontier step.
- **Hypothesis, recorded before implementation:** store only node kinds,
  predecessor/observation finsets, a dependent value family, and acyclicity in
  syntax. Put finite enumeration and decidable equality on evaluation. A state
  may carry a total assignment plus a resolved finset; unresolved coordinates
  contain explicit defaults and are semantically inaccessible. A frontier draw
  is a dependent finite product, and updating all frontier coordinates at once
  needs no equality transport because each sampled coordinate retains its
  original node index.
- **Representative slice:** one typed API instantiated twice: the four-node
  diamond and the same-owner/disjoint-observation graph from EXP-038. Prove
  generic frontier nonemptiness before completion, parent closure after a
  step, exact simultaneous commitment, and a terminal outcome law sensitive to
  both site-local policies.
- **Competing designs:** homogeneous node values; dependent partial maps with a
  transport module; total defaulted assignments plus resolved finsets;
  explicit topological folds; or retaining only the concrete stable MAID.
- **Kill conditions:** user-visible transport, direct `Function.update`,
  unresolved values reaching a node law, combined-view policies, stored
  `Fintype`/`DecidableEq`, order-dependent native evaluation, or failure of
  generic frontier progress.
- **Evidence:**
  1. The promoted `Languages/MAID/Basic.lean` is 327 nonblank lines and 33
     declarations. `Structure`
     stores node kind, causal and observed parent finsets, a dependent value
     family, locality laws, and acyclicity—no order, `Fintype`, or
     `DecidableEq`. `Policy` is indexed by decision site and receives only that
     site's observed-parent configuration.
  2. A frontier state stores a total defaulted assignment, a resolved finset,
     and predecessor closure. `frontier_nonempty` derives a well-founded
     minimal unresolved node whenever the state is incomplete. `extend`
     preserves predecessor closure and
     `resolved_ssubset_extend_of_incomplete` proves strict progress.
     `run_complete_of_remaining_le` lifts that measure through finite-law
     support, and `completesWithin_card` gives the uniform one-step-per-node
     completion bound.
  3. `frontierLaw` uses `FinDist.pi` over the dependent frontier family.
     `Assignment.resolve` updates every sampled coordinate simultaneously
     without `Function.update` or equality transport. A node law is constructed
     only after its causal parents—and, by subset, its observed parents—are
     proved resolved.
  4. The 494-nonblank-line hostile test has 61 declarations. Its diamond uses
     four different dependent alphabets (`Bool`, `Fin 2`, `Unit`, `Bool`) and
     derives the correct initial frontier. Its same-owner fixture has two
     disjointly observed decision sites in one frontier.
  5. The actual generic runner, not a manual second evaluator, reaches a pure
     complete state in two steps under responsive and constant policies.
     Both chance nodes and both decision nodes commit simultaneously at their
     respective frontier. Responsive utility is two; constant-false and
     constant-true utility are one, so separate theorems show right- and
     left-site policy sensitivity.
  6. The evaluator has exactly two project prerequisites, `FinDist` and the
     game-independent DAG module. The focused target builds in 1,715 jobs and
     the full build in 3,331. Source scans find zero placeholders,
     `native_decide`, direct updates, or transport tokens.
  7. Axiom checks for generic frontier progress/strict growth, heterogeneous
     frontier calculation, the two-step run, simultaneous commitment, and both
     policy-sensitivity theorems use only `propext`, `Classical.choice`, and
     `Quot.sound`. Phase 2/3 audits retain all expected trust, boundary, and
     reachability measurements.
- **Outcome:** supports. The total-defaulted assignment design preserves
  heterogeneous indices without a transport surface, and native site-local
  policies survive the exact same-owner falsifier that rejected combined
  Protocol views. No kill condition fired.
- **Next action:** translate an explicit topological order to an EFG whose
  information states expose exactly `observedParents`. Keep the implementation
  experimental until the serialized run equals this frontier law and order
  independence is proved.

### EXP-041: typed MAID serialization through EFG

- **Date / revision:** 2026-07-30, working tree based on `c49f826`
- **Status:** supports; compiler locality, general serialized order
  independence, and exact native/serialized/actual-runner assignment-law
  equality pass
- **Decision / question:** D6, D14, and T3; whether an explicit topological
  order can compile the typed native diagram to the accepted
  `Languages.EFG.Game` while preserving decision-site locality and the native
  terminal law.
- **Prediction:** use a dependent sum of the source owner's decision sites and
  their value types as the EFG action carrier. At a serialized decision state,
  the information state identifies that site and contains exactly its
  `observedParents` configuration; an earlier incomparable decision may exist
  in the execution state but cannot occur in this view. Keep source owners as
  players. Store the complete resolved prefix in the execution state so the
  EFG tree law has a unique predecessor, but do not make that prefix a policy
  input.
- **Representative slice:** compile EXP-040's same-owner,
  disjoint-observation diagram at both topological orders. Prove that the
  second decision's information state is unchanged when the earlier
  incomparable decision changes, map every native site-local behavioral
  policy into the target information model, and compare both serialized
  terminal laws with the native frontier law.
- **Competing designs:** dependent tagged source actions; one synthetic player
  per decision site; a homogeneous sum with value transport; or retaining the
  native frontier evaluator without an EFG bridge.
- **Measurements to collect:** stable/public API delta, authored and import
  size, focused/full build jobs, source trust and transport tokens, axiom
  profile, the exact information-state types, outcome equality in both orders,
  and Phase 2/3 boundary probes.
- **Kill conditions:** a synthetic player or padding action; a policy view
  containing an unobserved or merely earlier node; direct `Function.update`;
  user-visible equality transport; stored finite capabilities; failure of
  `treeShaped` or `singleMover`; unequal native/serialized terminal laws; or
  order-dependent serialized outcomes.
- **Evidence so far:**
  1. The eventual promoted modules `Languages/MAID/ToEFG.lean` and
     `Languages/MAID/Order.lean` are 1,344 nonblank lines/69 declarations and
     866 nonblank lines/24 declarations respectively; the 536-nonblank-line
     hostile test remains experimental with 50 declarations. During the
     experiment the stable API delta was zero.
  2. `Action` is the dependent sum of one real source owner's decision sites
     and their value types. `Stage` stores a dependent-valued path certified
     to equal a prefix of the supplied topological order. Neither syntax nor
     state invents a player, padding value, homogeneous alphabet, or stored
     finite typeclass.
  3. `View.acting` contains exactly one source decision site and a
     `Config` over that site's `observedParents`. `behavioralProfile` maps the
     native site-local law directly to the corresponding menu choice; the
     serialized state is not an argument.
  4. The generic compiler constructs the accepted `EFG.Game`, including
     `menu_adequate`, `treeShaped`, and `singleMover`. Tree shape is proved from
     the resolved prefix: every realized target has one source prefix, and a
     decision target records enough dependent action data to recover the
     unique joint action.
  5. The hostile test supplies two explicit topological orders. In the
     left-first order, changing the earlier left decision leaves the later
     right-site view equal; `left_view_hides_right_decision` proves the
     symmetric fact under the right-first order. Both compiled games and both
     native behavioral profiles elaborate.
  6. The compiler has two project prerequisites, typed MAID semantics and the
     stable EFG specialization. The focused test builds in 1,724 jobs and the
     full build in 3,334. Source scans report zero placeholders,
     `native_decide`, direct updates, transport tokens, or `open Classical`.
     Phase 2/3 expected measurements and all reachability probes pass.
  7. Axiom checks for the generic tree-shaped EFG, behavioral profile, and
     both locality theorems use only `propext`, `Classical.choice`, and
     `Quot.sound`.
  8. `serialNodeLaw` and `serialJointLaw` name the source-facing one-node
     midpoint. `serialJointLaw_bind_transition` proves generically that drawing
     this legal joint law and taking the actual compiled EFG transition is
     exactly `serialStep`; it is not a second transition definition.
  9. The hostile responsive policy runs to completion under both opposite
     serial orders. `serial_assignment_law_order_independent` proves the two
     complete assignment laws equal, while
     `left_serial_assignment_law_eq_native` and its right-order counterpart
     prove each equals the native two-frontier runner's assignment law.
  10. `behavioralJoint_eq_serialJointLaw_unit` identifies the actual
      `InformationModel.behavioralJoint` with the source joint law for any
      one-owner typed diagram. `behavioralJoint_bind_transition_unit` composes
      that law with the real EFG transition, and
      `map_state_runBehavioralFrom_eq_serialRun_unit` lifts the equality through
      the Protocol history runner for every fuel and starting history. The two
      hostile compiled games therefore have equal actual behavioral assignment
      laws, and each equals the native frontier runner.
  11. `assignmentStep_comm` ports the pinned adjacent-kernel idea to arbitrary
      typed node values, while `assignmentRun_swap_adjacent` lifts it under any
      prefix and suffix. `assignmentRun_eq_of_perm` then bubbles matching heads
      through dependency-compatible permutations, so
      `assignmentRun_topological_order_independent` proves the direct general
      theorem without exposing an order-swap reachability certificate.
      `map_assignment_serialRun` connects this algebra to the compiler, yielding
      `serialRun_topological_order_independent` for arbitrary player and node
      carriers.
  12. Two information-model product lemmas collapse inactive coordinates and
      isolate an at-most-one active coordinate. The compiler's single-mover law
      then yields `behavioralJoint_eq_serialJointLaw` for every finite source
      player type, not only `Unit`. `behavioralJoint_bind_transition` and
      `map_state_runBehavioralFrom_eq_serialRun` lift this through the actual
      transition and Protocol history runner.
      `behavioralRun_topological_order_independent` is therefore the general
      actual compiled-EFG assignment-law theorem.
  13. The promoted `Languages/MAID/FrontierEquivalence.lean` is 726 nonblank
      lines and 23 declarations. `finDist_pi_reindex` and
      `fixedAssignmentRun_eq_pi` prove
      that a dependent simultaneous frontier product equals duplicate-free
      sequential draws of the same fixed node laws.
      `map_values_step_eq_assignmentRun` then identifies one native frontier
      step with one serialized pass over that frontier.
  14. The current frontier followed by the still-unresolved topological order
      is proved to be a duplicate-free, dependency-compatible permutation of
      the current unresolved order. The cardinality-bounded induction in
      `map_values_run_eq_assignmentRun_unresolved` lifts the one-step equality
      through every native layer without assuming that frontiers are
      singletons.
  15. `nativeRun_eq_compiledBehavioralRun` is the general end-to-end theorem:
      for arbitrary finite source-player and node carriers, the native
      simultaneous-frontier run mapped to assignments equals the actual
      compiled `InformationModel.runBehavioral` assignment law at any supplied
      topological order. The new module builds in 1,723 jobs; the full project
      builds in 3,335. Source scans report zero placeholders,
      `native_decide`, direct updates, transport tokens, or `open Classical`;
      Phase 2/3 expected measurements pass. Axiom checks use only `propext`,
      `Classical.choice`, and `Quot.sound`.
  16. Post-gate delivery adds the 397-nonblank-line, 19-declaration
      `Languages/MAID/Strategic.lean`. `ownerPolicyEquiv` proves that one
      source owner's complete family of site-local rules is equivalent to that
      owner's compiled behavioral policy; the inactive choice is uniquely
      forced, and every acting choice decodes to its typed source value.
      `behavioralProfileEquiv_update` proves a unilateral update stays at the
      same source-owner coordinate. `isNash_native_iff_compiled` then proves
      the exact native/compiled behavioral Nash equivalence using the canonical
      `IsNash`, without a MAID-specific equilibrium predicate. The strategic
      module builds in 1,732 jobs and the full project in 3,337; source audits
      remain zero for placeholders, custom axioms, direct updates, transport
      tokens, and forbidden imports. Its flagship declarations use only
      `propext`, `Classical.choice`, and `Quot.sound`.
- **Outcome:** supports the prediction and closes EXP-041. General typed MAID
  serialization is local, order-independent, and exactly equal to both the
  native frontier evaluator and the actual compiled-EFG behavioral runner.
  This closed T3's outcome-law half and removed D14's block on public general
  MAID recovery. The subsequent promoted strategic module closes the remaining
  source-owner equilibrium transfer.
- **Next action:** T3 is complete. Inventory and close the remaining T4
  language transfer; general MAID refinements and Kuhn-facing recovery may now
  proceed behind their ordinary dependency gates.

### EXP-042: one-shot NFG through FOSG and Protocol

- **Date / revision:** 2026-07-30, working tree based on `2b659df`
- **Status:** supports; exact outcome and utility laws pass through the actual
  Protocol history runner
- **Decision / question:** D0/T4, D4, D6, and the NFG/FOSG language gates;
  whether a deterministic normal-form game can compile to a genuine
  factored-observation stochastic game, then through the accepted Protocol
  runner, with an exact commuting outcome law and without a second static,
  history, utility, or solution theory.
- **Prediction:** represent the source NFG as transparent finite-language
  syntax compiling to a deterministic `GameForm`. Compile its single
  simultaneous move to a general-state `ExecutionProtocol`; give every player
  an information-local initial menu containing exactly its source actions and
  observations that reveal no opponent's current action. The terminal state
  retains the realized source profile or outcome. Lifting a source profile to
  target policies should make the actual horizon-one history law, mapped to the
  source outcome, definitionally or propositionally equal to the source
  `GameForm.play`.
- **Representative slice:** a two-player action-sensitive game in which both
  players are active at the initial history. Prove simultaneous activation,
  information locality, one-step stopping, the exact generic commuting law,
  and the concrete hostile outcome equation.
- **Competing designs:** a native FOSG syntax compiling to
  `ExecutionProtocol` plus `InformationModel`; a thin wrapper around those two
  canonical objects; sequentialization through the single-mover EFG/tree
  frontend; or retiring T4 and keeping NFG solely static.
- **Measurements to collect:** declaration and nonblank-line delta; imports
  and closure jobs; exact source/target strategy and outcome types; direct
  update and transport tokens; placeholders and axiom profile; simultaneous
  activation and observation visibility; named source and target law equality;
  and Phase 3 positive and negative reachability probes.
- **Kill conditions:** a synthetic player, sequentialized current actions,
  padding/default actions, a target policy that reads hidden execution state or
  an opponent's current action, duplicated transition/history/equilibrium
  semantics, utility stored in execution syntax, a generic morphism or
  certificate hierarchy needed only to package the direct equality, stored
  finite capabilities, direct `Function.update`, user-visible equality
  transport, or failure of the actual compiled target law to equal the source
  play law.
- **Evidence so far:**
  1. The pinned bridge's direct utility-law proof is 21 nonblank lines and its
     morphism wrapper is 9, but its closure is 31 files/11,031 nonblank lines.
     The declaration ledger isolates the one-step law from that predecessor
     infrastructure.
  2. D6 already rules out the superficially smaller tree target:
     `sequentialization_enlarges_strategy_space` exhibits a contingent plan
     unavailable in simultaneous play. T4 must therefore exercise the
     general-state Protocol branch.
  3. The experimental compiler and hostile test are 401 nonblank lines and 42
     declarations. They import `Protocol.Strategic` and add no stable
     declaration or import during the experiment.
  4. `NFG.Game.toGameForm` is the deterministic canonical form.
     `FOSG.Game` contains only an `ExecutionProtocol` and its
     `InformationModel`; `FOSG.Game.toGameForm` is the existing Protocol
     compiler, not a second evaluator.
  5. The one-shot state is either initial or terminal with the full source
     profile. Every real source player is active initially and the certified
     simultaneous joint action is decoded without a default or padding action.
     `Nonempty` actions are requested only by the execution construction's
     progress proof.
  6. Each policy input is only `acting` or `done`. In the hostile two-player
     game, changing the column player's current action leaves the row player's
     initial policy action unchanged, while the terminal law changes from the
     all-false outcome to `(false, true)`.
  7. `toProtocolForm_play_policyProfile` proves the actual horizon-one
     information-local history law, mapped to the source outcome, equals the
     direct NFG play law. `toProtocolForm_utilityLaw_policyProfile` derives the
     predecessor's joint utility-distribution equality for every external
     utility.
  8. The focused test builds in 1,722 jobs and the full project in 3,339.
     Phase 2 and Phase 3 expected source audits pass. Source scans find zero
     placeholders, native decisions, direct updates, transports, custom
     axioms, or `open Classical`.
  9. Axiom checks for both generic laws and all hostile simultaneous/locality
     probes use only `propext`, `Classical.choice`, and `Quot.sound`.
  10. Promotion splits `Languages.NFG`, `Languages.FOSG`, and
      `Languages.Bridges.NFGFOSG`; the hostile fixture stays experimental. The
      focused stable/test build is 1,724 jobs and the full build 3,341.
      Full Phase 2/3 reachability audits pass. New probes report NFG
      boundary/input counts `2/3`, FOSG solution/input counts `2/3`, and all
      four intended bridge inputs reached.
- **Outcome:** supports. No kill condition fired. D15 adopts a utility-free
  deterministic NFG frontend, the transparent Protocol-backed FOSG
  specialization, and the named direct one-shot bridge. The predecessor's
  generic morphism wrapper is retired under D7.
- **Next action:** T4 and every frozen transfer are complete. Continue broad
  NFG/FOSG declaration recovery behind the passed gates; do not generalize the
  retired morphism wrapper without a new composition consumer.

### EXP-043: epistemic ownership versus Protocol information

- **Date / revision:** 2026-07-30, working tree based on `d68e707`
- **Status:** complete
- **Decision / question:** the overdue Phase 0 D-KNOW probe; whether Aumann
  agreement and partition-based common knowledge belong directly on
  `Protocol.InformationModel.InfoState`, in a separate epistemic branch, or in
  game-free mathematics.
- **Prediction:** an arbitrary Protocol information state is history-local,
  not a partition of execution states. A merging protocol can reach one state
  through two histories that leave distinct information states, so no
  state-indexed view can recover `infoOf` and `InformationModel.InfoSet`s may
  overlap. Aumann's theorem should instead use an explicit finite-cell
  epistemic partition and the canonical `FinDist` prior in a separate stable
  branch. Game-free view-induced S5 lemmas may later be extracted to
  `GameTheoryMath` if the epistemic consumer needs them.
- **Representative slice:** construct a one-player merging protocol whose two
  simultaneous actions reach the same terminal execution state while the
  player remembers which action it took. Prove that terminal state lies in two
  distinct `InfoSet`s and refute every state-only view representing `infoOf`.
  Independently adapt the pinned finite-cell posterior and full Aumann
  agreement theorem to a `FinDist` prior with operation-local full support.
- **Competing designs:** define epistemic events directly from Protocol
  `InfoSet`; add a tree-shaped/unique-history premise and derive partitions
  only there; adopt a parallel epistemic partition object; or place the entire
  development in `GameTheoryMath`.
- **Measurements:** the 287-nonblank-line, 22-declaration spike imports only
  `GameTheory.Protocol.Information`; its positive theorem uses the existing
  `Probability.FinDist`, with `DecidableEq` and full support requested only by
  the operations and theorem that need them. The focused build completes in
  1,718 jobs and the full build in 3,342. Source scans find zero placeholders,
  native decisions, custom axioms, direct updates, transports, `HEq`, tactic
  `change`, or `open Classical`. All three flagship declarations report only
  `propext`, `Classical.choice`, and `Quot.sound`. Positive probes reach
  `FinDist`, `InformationModel`, the experimental partition, and Aumann
  agreement; negative probes reject `IsNash`, the sequential-analysis
  convergence declaration, `stdSimplex`, and `Polynomial`. Phase 2/3
  non-reachability audits and the declaration-coverage audit pass.
- **Kill conditions:** silently choose one history for a merging state; add
  partition laws to every `InformationModel`; duplicate the finite-law
  representation; make an action profile or game form a premise of Aumann's
  theorem; store `Fintype` or decidability in epistemic data; or require
  topology/Analysis for the finite agreement theorem.
- **Evidence:** Mathlib has no Aumann/common-knowledge development. The
  pinned theorem uses only finite cells, a common prior, self-evidence, and
  finite sums. Protocol deliberately defines `InfoSet` by existence of a
  history and does not assert a state partition. The hostile model satisfies
  menu adequacy, yet its one merged terminal state belongs to the information
  sets for both `done false` and `done true`; moreover no function of execution
  state can represent `infoOf` on both histories. Recovering a partition from
  Protocol therefore needs an explicit extra premise such as unique history;
  it is not a law of `InformationModel`.
- **Outcome:** supports the predicted separate epistemic branch. D16 adopts a
  finite-cell `Epistemic.InfoPartition` using the canonical `FinDist` prior and
  rejects both adding partition laws to Protocol and duplicating Protocol
  histories inside the epistemic API. The theorem is game-theoretic domain
  semantics, so moving it wholesale to `GameTheoryMath` is not earned.
- **Promotion:** `GameTheory.Epistemic.Basic` and
  `GameTheory.Epistemic.Agreement` now contain the positive slice without a
  Protocol import; the public root re-exports their umbrella. Full Phase 2/3
  reachability audits pass with epistemic input/boundary counts `3/5` and two
  rejected reciprocal Protocol probes. The stable theorem's axiom profile is
  unchanged.
- **Next action:** inventory the remaining D-KNOW declarations before broad S5
  and approximate-common-knowledge recovery. The merging counterexample
  remains experiment evidence, not stable API.
- **Recovery follow-on:** the finite S5 and public-event common-knowledge
  layer is now stable. All 30 declarations from pinned
  `CommonKnowledge.lean` have reviewed rows; 32 approximate-common-knowledge
  declarations remain. The expanded root builds in 1,716 focused / 3,350 full
  jobs, with Epistemic input/boundary probe counts `4/5`.
- **Approximate follow-on:** the `p`-belief, mutual/common `p`-belief,
  threshold-monotonicity, and exact-to-approximate bridge layer is now stable.
  D-KNOW accounting is 48/62; the quantitative approximate-agreement theorem
  and 13 private mass lemmas remain. The expanded root builds in 1,717 focused
  / 3,351 full jobs with input/boundary probe counts `5/5`.
- **Quantitative close-out:** the Monderer--Samet report-distance theorem and
  its 13 private mass/cell lemmas are stable. D-KNOW is complete at 62/62
  declarations. The final root is 1,149 nonblank lines, builds in 1,718
  focused / 3,352 full jobs, and passes input/boundary probes `6/5` with zero
  source transport and the standard axiom profile.

### EXP-044: evolutionary stability static/dynamic ownership

- **Date / revision:** 2026-07-30, working tree based on `fe9cce9`
- **Status:** complete
- **Decision / question:** the remaining Phase 0 D-EVOL probe; whether ESS/NSS
  belongs in the static Core, a separate stable evolutionary branch, or an
  analytic population-dynamics branch.
- **Prediction:** the pinned nine-declaration family is entirely static. ESS
  and NSS need only a two-argument real payoff kernel; the flagship
  ESS-to-symmetric-Nash theorem should cross into Core through one canonical
  deterministic `GameForm` and `IsNash`. Replicator dynamics, simplex
  invariance, topology, and limiting behavior should remain absent until a
  dynamics theorem earns an opt-in `Analysis.Evolutionary` root.
- **Representative slice:** recover ESS, NSS, their elementary implications,
  the symmetric two-player form/utility presentation, and the generic
  ESS-to-Nash theorem. Use a Boolean payoff kernel where a mutant ties the
  resident against the resident, so the second ESS clause is genuinely used
  rather than discharged by strict Nash.
- **Competing designs:** put ESS directly in `Core.Response`; adopt a separate
  stable `Evolutionary` root with a one-way Nash bridge; or make ESS part of a
  simplex/population-dynamics structure under Analysis.
- **Measurements:** the combined hostile slice has 134 nonblank lines and 17
  declarations and imports only `GameTheory.Core.Utility`. ESS and NSS take
  only `S → S → ℝ` and a resident strategy; they store no scalar structure,
  carrier enumeration, population law, or topology. The bridge uses the
  canonical `GameForm`, `euPreference`, `Profile.update` through
  `isNash_iff`, and the single public `IsNash` predicate. The focused build
  completes in 1,720 jobs and the full build in 3,346. Source audits find zero
  placeholders, native decisions, custom axioms, direct `Function.update`,
  transports, `HEq`, tactic `change`, `Fintype.ofFinite`, or `open Classical`.
  The generic bridge, hostile ESS proof, and hostile Nash theorem use only
  `propext`, `Classical.choice`, and `Quot.sound`. Positive probes reach
  `GameForm`, `IsNash`, experimental `IsESS`, and the bridge; negative probes
  reject Protocol execution, Analysis Nash existence, `stdSimplex`, and
  `Polynomial`. The Phase 2 expected source audit passes.
- **Kill conditions:** define a second Nash predicate; store a population law,
  `Fintype`, topology, or dynamics in the ESS object; duplicate profile update;
  require Analysis for the static theorem; orient either player's payoff or
  unilateral deviation incorrectly; or weaken the nonvacuous stability
  example into a strict-Nash-only witness.
- **Evidence:** all nine pinned declarations use a payoff kernel
  `S → S → ℝ`; only the final bridge mentions the old universal game object.
  No pinned declaration defines a population state, replicator equation,
  trajectory, limit, or simplex invariant. The hostile payoff makes
  `u(true,true) = u(false,true)`, so strict Nash cannot establish ESS; the
  checked second clause `u(true,false) > u(false,false)` is necessary. Both
  player orientations then satisfy canonical Nash through the generic theorem.
- **Outcome:** supports the predicted separate stable static branch. D17
  adopts `GameTheory.Evolutionary` for ESS/NSS and a one-way bridge into Core.
  ESS is not added to the Core concept surface, and no dynamics or Analysis
  carrier is bundled with it.
- **Promotion:** `GameTheory.Evolutionary.Basic` now owns the game-free static
  definitions and facts; `GameTheory.Evolutionary.Nash` owns the one-way Core
  bridge; the public root re-exports their umbrella. Full Phase 2/3
  reachability audits pass with Basic input/boundary counts `2/6`, bridge
  input/boundary counts `3/4`, and two rejected reverse probes from each of
  Core and Protocol. The stable root is 119 nonblank lines and the focused
  build completes in 1,722 jobs.
- **Promotion validation:** the full build completes in 3,349 jobs, and the
  complete nine-row D-EVOL ledger passes the declaration-coverage audit.
- **Next action:** keep the hostile payoff as experiment evidence and admit no
  population dynamics until a named analytic theorem reserves a new
  experiment. Continue with the D-KNOW inventory and minimal D8 obligations.

### EXP-045: minimal consumer-backed transformation closure

- **Date / revision:** 2026-07-30, working tree based on `c306f24`
- **Status:** supports; concrete equivalences suffice and no transformation
  structure is earned
- **Decision / question:** D8 and W1-H; which transformation declarations are
  genuinely public infrastructure after the direct language transfers have
  removed the predecessor's generic morphism and certificate wrappers.
- **Prediction:** player reindexing and per-player strategy equivalence need
  only transparent functions and exact laws. A single game-free
  `FinDist.pi_reindex` theorem should serve both mixed extension and the
  existing MAID serialization consumer. Nash and CE invariance should follow
  directly from invertibility, without `FormHom`, `FormEquiv`, a generic
  equilibrium certificate, or user-visible equality transport.
- **Representative slice:** reindex a finite game along a nontrivial player
  equivalence; relabel a player's strategies along a nontrivial equivalence;
  prove that reindexing commutes with independent mixing; and transport both a
  Nash profile and a correlated law. Replace the MAID-local finite-product
  lemma with the shared probability theorem as the second real consumer.
- **Competing designs:** revive `FormHom`/`FormEquiv` plus deviation-reflection
  structures; expose only concrete equivalence operations and preservation
  theorems; or leave every transfer bespoke in its language module.
- **Measurements to collect:** declaration and nonblank-line delta; focused
  and full build jobs; import closure; number of consumers; source transport,
  direct update, placeholder, and axiom audits; and whether CE transport needs
  a law beyond invertibility.
- **Kill conditions:** a public transformation structure with only one
  theorem consumer; a second equilibrium predicate; direct `Function.update`;
  user-visible `cast`, `Eq.ndrec`, `HEq`, tactic `change`, or substitution
  transport; stored finiteness or decidability; Core importing a language; or
  a claimed equilibrium transport that silently assumes target deviations can
  be reflected.
- **Evidence:** the 395-nonblank-line, 37-declaration experiment imports only
  `GameTheory.Core.Mixed`. The player fixture swaps unequal `Bool` and `Fin 3`
  strategy carriers. The strategy fixture flips both Boolean carriers and
  transports a recommendation-dependent correlated law by conjugating every
  response map. Player reindexing commutes with the actual mixed play law via
  forward/inverse dependent `FinDist.pi` reindexing. The forward orientation
  has the exact shape needed by the existing MAID serialization consumer.
- **Measurements:** the focused build completes in 1,721 jobs. Source scans
  find zero placeholders, native decisions, direct updates, transports,
  `HEq`, tactic `change`, `Fintype.ofFinite`, or `open Classical`. Nash, CE,
  mixed lifting, and both hostile witnesses use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- **Outcome:** supports prediction and decides D8. No `FormHom`, `FormEquiv`,
  payoff-law morphism, or equilibrium certificate is earned. D8 adopts
  transparent player/strategy equivalence operations, the two game-free
  finite-product orientations, and direct Nash/CE invariance theorems.
- **Next action:** promote the accepted declarations, replace MAID's local
  probability proof with the shared theorem, add reachability/source audits,
  and close W1-H only after focused and full builds pass.
- **Promotion:** `Probability.FinDist` now owns exact forward and inverse
  dependent-product reindexing laws; `Core.Transform` owns the transparent
  player/strategy operations and Nash/CE/mixed preservation theorems; MAID
  uses the shared forward law. The stable module and regression test contain
  246 and 67 nonblank lines. The focused regression target builds in 1,722
  jobs. Phase 2 source audits pass with no new transport, direct update,
  placeholder, custom axiom, carrier-reducibility, or import-boundary defect.
  Core reaches all six D8 probes; the game-free probability root reaches both
  laws and rejects both game-semantic probes. Phase 3 records the single
  intended MAID use. The full project builds in 3,355 jobs, and every promoted
  flagship retains the standard axiom profile. W1-H is complete.

### EXP-046: ownership of observable pre-play cheap talk

- **Date / revision:** 2026-07-30, working tree based on `ec81e80`
- **Status:** supports static ownership; decides D18
- **Decision / question:** D0/D5/D6 and D-COMM; whether the observable
  cheap-talk extension needed by the NFG babbling examples is a static
  strategy enrichment of `GameForm`, or whether its message-before-action
  timing forces ownership by Protocol.
- **Prediction:** for the pure babbling theorem, the enriched strategy can be
  a message plus a contingent base strategy over the public message profile.
  Its play law is the base form evaluated at the realized contingent actions.
  The ordinary `IsNash` predicate should then prove babbling by projecting an
  arbitrary enriched unilateral deviation to the base action it induces
  against default messages. Protocol is earned only by a theorem that observes
  intermediate message histories or randomizes during the communication
  stage.
- **Representative slice:** a two-message Battle-of-the-Sexes extension in
  which the deviator may change both its message and its entire contingent
  action plan. Embed the opera and football equilibria as babbling profiles
  and prove both with ordinary `IsNash`.
- **Competing designs:** a static `GameForm` construction with a generic
  babbling theorem; a two-stage `ExecutionProtocol` with a compilation theorem;
  or an inert-extension abstraction that forgets the communication-specific
  strategy shape.
- **Measurements to collect:** source/import surface; focused and full build
  jobs; whether the proof uses only `Profile.update`; whether any second
  equilibrium predicate, stored finiteness, transport, or Protocol dependency
  appears; axiom profile; and whether the hostile contingent-plan deviation is
  discharged generically.
- **Kill conditions:** a static construction cannot represent the arbitrary
  contingent-plan deviation; the babbling proof needs intermediate histories;
  the extension introduces another Nash predicate or evaluator; direct
  `Function.update`, user-visible dependent transport, stored finite
  capabilities, or a reverse Core-to-Protocol import is required.
- **Evidence:** the 141-nonblank-line experiment has 20 declarations and one
  authored import, `GameTheory.Examples.Classic`. Its generic construction
  depends only on the static form/equilibrium closure brought by that example;
  it imports no Protocol or Analysis module. The focused target builds in
  1,738 jobs.
- **Observation:** the arbitrary enriched deviation changes both its message
  and its complete contingent plan. `actionProfile_update_embedProfile`
  nevertheless proves that the induced base profile is exactly one canonical
  `Profile.update`; the preference-parametric babbling theorem then closes by
  the ordinary `isNash_iff` characterization. Both Battle-of-the-Sexes
  equilibria instantiate it without further payoff reasoning.
- **Measurements:** source scans find zero placeholders, native decisions,
  direct `Function.update`, transports, `HEq`, stored finite capabilities,
  `open Classical`, or custom axioms. The generic theorem and both witnesses
  use only `propext`, `Classical.choice`, and `Quot.sound`.
- **Outcome:** supports the prediction and decides D18. Observable one-stage
  pre-play cheap talk is a static `GameForm` strategy enrichment. Protocol
  remains the owner only when a theorem observes message histories, staged
  rounds, or during-play randomization. The inert-extension competitor is too
  weak as the public construction because it erases the message/plan shape.
- **Promotion:** `GameTheory/Core/CheapTalk.lean` contains the 17-declaration
  generic construction; `GameTheory/Examples/CheapTalk.lean` contains the
  concrete extension and two witnesses. The focused build passes in 1,739
  jobs and the full project in 3,361 jobs. Phase 2 verifies the original
  transport budget, zero forbidden Core imports, positive reachability of
  both public cheap-talk symbols, and rejection of all four Protocol/Analysis
  boundary probes. The generic theorem and both examples retain the standard
  `propext`, `Classical.choice`, and `Quot.sound` axiom profile.
- **Next action:** inventory the whole D-COMM family, then test public
  randomness and Electronic Mail against the static/Protocol timing boundary.

### EXP-047: static cheap talk as public randomization

- **Date / revision:** 2026-07-30, working tree based on `866f113`
- **Status:** supports the static bridge; decides D19
- **Decision / question:** D8/D18 and D-COMM/S-MIX/S-CORR; whether a mixed
  profile of the static cheap-talk extension can be pushed through its realized
  action profile to a base correlated equilibrium, or whether public
  randomization forces a staged Protocol model.
- **Prediction:** independent mixed play of message-plus-plan strategies
  already supplies the needed public random source. Any recommendation-reading
  base deviation should lift to a cheap-talk deviation that retains the
  message and applies the deviation to the contingent action. Exact commutation
  of the induced laws should let the ordinary `IsNash` and `IsCorrelatedEq`
  predicates prove the result.
- **Representative slice:** define the induced base action-profile law, lift an
  arbitrary recommendation-dependent base deviation, prove the profile-law
  commutation, and derive a base correlated equilibrium from a mixed Nash
  profile of the cheap-talk form. The theorem is preference-parametric if the
  exact-law proof really carries the argument.
- **Competing designs:** keep public randomization as a static bridge over
  `GameForm.CheapTalkExtension` and `GameForm.mixed`; compile a staged public
  signal protocol; or add a communication-specific mixed equilibrium
  predicate.
- **Measurements to collect:** new probability lemmas required; authored
  imports and lines; exact use of `Profile.update`; source hazards; axiom
  profile; focused build cost; and reachability of Protocol/Analysis symbols.
- **Kill conditions:** the induced action law cannot commute with an arbitrary
  recommendation-dependent deviation; the proof needs an intermediate
  communication history; a second Nash/CE predicate or evaluator appears; or
  direct `Function.update`, dependent transport, stored finiteness, or a
  Core-to-Protocol/Analysis dependency is required.
- **Evidence:** the 152-nonblank-line experiment has eight declarations and one
  authored import, `GameTheory.Core.CheapTalk`. The focused target builds in
  1,720 jobs. One general finite-law lemma proves that mapping one coordinate
  of an independent profile law equals mapping that marginal before taking the
  product.
- **Observation:** a recommendation-reading base deviation lifts by retaining
  the cheap-talk message and applying the response to every contingent action.
  The realized profile and induced finite law commute exactly with this lift.
  The mixed-Nash inequality therefore becomes the correlated-equilibrium
  inequality by rewriting both complete outcome laws; expected utility,
  convexity, and public-message conditioning never enter the proof.
- **Measurements:** the final theorem is preference-parametric and uses the
  ordinary `IsNash` of `C.form.mixed` and ordinary `IsCorrelatedEq` of the base
  form. Source scans find zero placeholders, native decisions, direct
  `Function.update`, transports, `HEq`, stored finite capabilities,
  `open Classical`, or custom axioms. The probability lemma and headline
  theorem use only `propext`, `Classical.choice`, and `Quot.sound`.
- **Outcome:** supports the prediction and decides D19. Public randomization
  generated by independent mixed play is a static Core bridge over D18, not a
  Protocol execution. No communication-specific equilibrium predicate is
  admitted. Conditional public-signal disintegration remains a separate
  theorem family and is not silently claimed by this experiment.
- **Promotion:** `GameTheory/Core/CheapTalkRandomization.lean` contains the
  exact-law bridge and the preference-parametric CE and CCE results. The
  focused target builds in 1,720 jobs and the full project in 3,363 jobs.
  Phase 2 verifies every source/import budget, positive reachability of both
  D19 public symbols, and rejection of all four Protocol/Analysis boundary
  probes. The promoted theorems retain the measured standard axiom profile.
- **Next action:** decide whether a live payoff-mixture consumer earns
  message-conditioned public-signal disintegration; otherwise proceed to the
  Electronic Mail ownership slice.

### EXP-048: ownership of the finite Electronic Mail example

- **Date / revision:** 2026-07-30, working tree based on `138c6d1`
- **Status:** supports the static Examples bridge; decides D20
- **Decision / question:** D16/D18 and D-COMM; whether the finite Electronic
  Mail results are a static bridge between the canonical Bayesian and
  Epistemic branches, or whether their messaging interpretation forces a
  Protocol execution model.
- **Prediction:** the pinned theorems observe only endpoint worlds, private
  views, posteriors, common `p`-belief, and a type-contingent action plan. One
  canonical finite prior on worlds should push forward to the Bayesian type
  prior while directly feeding the epistemic partition. No theorem quantifies
  over an execution history, so an Examples bridge should suffice.
- **Representative slice:** recover the three endpoint worlds, views, actions,
  shared finite prior, Bayesian game, candidate and deviating plans, mutual
  `p`-belief and failure of common `p`-belief at the confirmed endpoint, and
  the machine-checked failure of Bayes-Nash.
- **Competing designs:** a static Examples bridge over `BayesianGame` and
  `Epistemic`; a multistage `ExecutionProtocol` modeling each email attempt; or
  parallel communication-local probability and equilibrium APIs.
- **Measurements to collect:** whether one prior serves both branches; import
  and reachability surface; source hazards; axiom profile; focused build cost;
  and whether the non-equilibrium theorem uses ordinary `IsNash`.
- **Kill conditions:** a theorem needs an intermediate message history or
  transition probability, the endpoint abstraction cannot state the
  information result, a second prior/equilibrium concept is required, or the
  example creates a reverse stable dependency or forbidden source construct.
- **Evidence:** the 212-nonblank-line experiment has 24 declarations and four
  authored imports: the canonical Bayesian-equilibrium and approximate
  epistemic roots plus `linarith` and `norm_num`. The focused target builds in
  1,725 jobs.
- **Observation:** one uniform `FinDist EmailWorld` pushes forward to the
  Bayesian type prior and directly supplies every epistemic posterior. The
  confirmed endpoint is mutually `p`-believed up to threshold one but is not
  common `p`-belief above one half. The attack-on-message plan has value
  `-1/3` for player `true`, the canonical `Profile.update` to never attack has
  value zero, and ordinary `IsNash` therefore refutes the plan.
- **Measurements:** no Protocol or Analysis import is present; no transition
  state, second prior, Bayesian-equilibrium wrapper, or communication-local
  evaluator appears. Source scans find zero placeholders, native decisions,
  direct `Function.update`, transports, `HEq`, `Fintype.ofFinite`,
  `open Classical`, or custom axioms. All three headline theorems use only
  `propext`, `Classical.choice`, and `Quot.sound`.
- **Outcome:** supports the prediction and decides D20. The pinned finite
  endpoint theory belongs in Examples as a bridge between the independent
  Bayesian and Epistemic roots. Protocol is reserved for a model that exposes
  email delivery transitions, stopping, or strategies during the exchange.
- **Promotion:** `GameTheory/Examples/ElectronicMail.lean` contains the stable
  endpoint bridge. The focused target builds in 1,725 jobs and the full project
  in 3,365 jobs. Phase 2 reaches all four intended inputs, rejects all four
  Protocol/Analysis boundary probes, and proves both directions of
  Bayesian/Epistemic root independence. The stable headline theorems retain
  the measured standard axiom profile.
- **Next action:** leave Protocol unspent until a dynamic email-process theorem
  is selected; D-COMM's only remaining rows are the explicitly gated
  public-signal and zero-sum value families.
