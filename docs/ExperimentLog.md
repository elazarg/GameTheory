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
| EXP-011 | 2026-07-26 | D6 / Phase 3 | Does a separate information layer keep strategies information-local by construction? | *reserved* | `GameTheory/Protocol/` |
| EXP-012 | 2026-07-27 | D6 / Phase 3 | Finite-first or general-state-first execution for v1? | Narrows (partial) | `GameTheory/Protocol/Tree.lean`; `GameTheory/Tests/Candidates.lean` |

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

- **Date / revision:** 2026-07-26, Phase 3 working tree based on the Phase 2 gate
- **Decision / question:** D6; whether an information model layered over an
  execution protocol keeps strategies information-local *by typing* rather than
  by a later proposition. RFC 9.1.7 makes it a core-invalidating failure if the
  strategy type exposes hidden execution state, relies only on a subsequent
  locality proposition, or cannot support conditional beliefs and sequential
  rationality without reopening native information equivalence.
- **Representative slice:** *(reserved - completed at gate)*
- **Evidence:** *(reserved)*
- **Observation:** *(reserved)*
- **Outcome:** *(reserved)*
- **Next action:** *(reserved)*

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
- **Next action:** D6 is *not* decided. Two measurements remain: a
  backward-induction API for the general candidate, which needs more than
  `StopsWithin` because it needs well-foundedness rather than a step bound; and
  finite strategy extraction over reachable decision sites. Both are required
  before the RFC's criterion can be applied in full.
