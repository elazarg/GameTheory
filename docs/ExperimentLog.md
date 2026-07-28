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
| EXP-017 | 2026-07-29 | D6 / behavioral-mixed equivalence | Where can a player's randomness live, and do the two placements agree? | Narrows | `GameTheory/Protocol/Randomized.lean`; `GameTheory/Tests/Randomized.lean` |

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
  behavioral/mixed equivalence transfer, which is the experiment that could
  reopen D7.

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
extended arbitrarily at that coordinate. The obstruction is that the index type
shrinks while the induction hypothesis quantifies over full profiles.
