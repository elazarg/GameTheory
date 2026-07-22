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
