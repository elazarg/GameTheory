# Proof-engineering audit

**Audit date:** 2026-08-03. **Mathematical checkpoint:** `14d75ff`.
**Repository snapshot during measurement:** `34a9ff8` plus documentation-only
working-tree changes.

This is a measured engineering assessment, not theorem status. Production Lean
is authoritative about declarations; [`PIPELINE.md`](../docs/uniform-equilibrium/PIPELINE.md)
owns priorities and [`FRONTIER.md`](../docs/uniform-equilibrium/FRONTIER.md)
owns the curated mathematical boundary.

## Executive verdict

The repository has a large, coherent, kernel-checked stochastic-game corpus
and currently builds. Its main engineering risk is not lack of mathematical
formalization. It is that the advertised audit/CI layer is presently red and,
because the workflow is misplaced, is not automatically protecting the tree.
The second risk is architectural: research certificates, production APIs,
regressions, and public imports are only partly separated, so the umbrella
module is extremely broad and several valuable modules are orphaned from every
default target.

The best near-term work is therefore narrow and operational:

1. make CI discoverable and make each documented check reflect intentional
   policy;
2. repair the axiom audit and add uniform/quitting keeper declarations;
3. classify the 25 orphan modules and the certificate exceptions; and
4. keep the new claim/literature/pipeline hierarchy link-clean so cold handoff
   does not fall back to ignored notebooks.

No broad refactor of the quitting proof stack is presently justified. The
current modules expose meaningful semantic layers, and the newest fixed-cutoff
holonomy module landed cleanly. Refactor only repeated stable interfaces with
multiple current consumers.

## Measured snapshot

| Measure | Result | Interpretation |
| --- | ---: | --- |
| Tracked Lean files | 1,007 | Includes public libraries, targets, tests, and audit source. |
| Tracked Lean lines (`Measure-Object -Line`) | 345,411 | A rough physical-size measure, not proof-term size. |
| `Quitting*.lean` production modules | 115 files / 39,464 lines | The quitting lane is already a substantial formal sublibrary. |
| Direct imports in `GameTheory.lean` | 570 | The public umbrella is explicit but very wide. |
| Tracked-module closure of `GameTheory` | 917 | Most production work lies below the umbrella. |
| Transitively redundant direct imports | 415 | Redundant relative to other direct roots; some are intentional visibility anchors. |
| Import cycles found | 0 | Strong structural result. |
| Tracked `*Tests.lean` aggregators | 24 | Separate `GameTheoryTest` target exists. |
| Dedicated stochastic `Tests.lean` aggregator | 0 | Stochastic regressions mostly live as production modules. |
| `Counterexample`/`NoGo` stochastic modules | 19 | Valuable permanent regression culture, but mixed with library surface. |
| `set_option maxHeartbeats` occurrences | 12, nine in quitting modules | Small enough to audit individually; several lack a reason comment. |
| Warm `lake build` | 9,645 jobs, 8.22 seconds, success | Machine/cache-specific; not a cold-build benchmark. |

The largest proof files are
`MertensNeymanAccountStrategy.lean` (4,294 measured lines),
`FinkLimit.lean` (3,773), `Math/FixedPoint/Scarf.lean` (2,554),
`MertensNeymanAccount.lean` (2,483),
`DiscountedShapleySystem.lean` (2,380), `ShapleySnow.lean` (2,251), and
`SingleController.lean` (2,133). Size alone is not a refactor mandate, but
these files are the first candidates for compile-profile and API-boundary
inspection.

## What is working well

- The full default build succeeds, including the newly landed
  `QuittingBoundaryHolonomyCompactness.lean`.
- The tracked import graph is acyclic.
- The project usually lands small theorem-oriented commits, with explicit
  theorem comments and reusable interfaces rather than only monolithic
  capstones.
- The quitting work has a real semantic stack: live-root representation,
  pure-time/Never deviations, terminal/uniform bridge, exact finite debt,
  stationary and periodic compilers, provenance, two-ended limits, and finite
  holonomy. This is not premature scaffolding.
- Negative examples are retained as permanent regressions. That discipline has
  repeatedly prevented false compactness, ownership, stationarity, and
  recurrence inferences.
- Apart from the intentionally open uniform-existence constructor, no ordinary
  `sorry`/`admit` was found by the repository checker.
- Axiom output for all 48 requested headline declarations contains only
  `propext`, `Classical.choice`, and `Quot.sound`; the present failure is in
  parsing/report coverage, not evidence of an unexpected axiom.

## P0 findings

### 1. CI is not discoverable

The workflow is at `.github/ci.yml`, but GitHub Actions discovers workflows
under `.github/workflows/`. Consequently the repository can appear protected
while the documented build/audit job never runs. Move the workflow, then test
it on a branch before relying on its badge or policy.

### 2. The advertised CI commands are red by policy mismatch

`python scripts/check_lean_placeholders.py` exits 1 on
`GameTheory/Concepts/Stochastic/Uniform.lean:211`, the intentionally open
`exists_uniformDeviationCapConstructor`. The checker has no allowlist or
declaration-level exception, although project prose treats this as the single
intentional open theorem.

`python scripts/audit_repository.py` also exits 1. At this snapshot it reports:

- four `opaque` declarations;
- ten `native_decide` proofs; and
- 25 tracked modules unreachable from the five default roots.

These may be unacceptable, intentionally quarantined certificates, or missing
imports, but the policy currently makes no distinction. Do not weaken the
audit silently. Add narrow path/declaration exceptions with written rationale,
or replace the mechanisms/import the modules.

### 3. Axiom-audit coverage is silently incomplete

`scripts/AxiomAudit.lean` requests 48 declarations. Lean emits all 48 report
heads, but the Python parser accepts only a single-line format; multiline axiom
lists are skipped. The repository audit merely checks that at least one line
parsed, so partial coverage can pass. Make the Lean output machine-readable or
use a multiline parser, assert `parsed == requested`, and make the prerequisite
build/import step explicit.

The audit also omits the project's load-bearing keepers. Add at least the
terminal-to-uniform quitting bridge/selection, behavioral pure-time/Never
reduction, optimized-debt split, periodic compiler, and fixed-cutoff holonomy
compactness. The intentionally open uniform constructor should be checked by
the placeholder policy, not represented as a proved axiom-clean capstone.

## P1 findings

### Import surface and module lifecycle

`GameTheory.lean` contains 570 direct imports in 613 measured lines. Its closure
contains 917 tracked modules, and 415 direct imports are already reachable via
another direct import. Explicit imports can intentionally advertise modules,
so this is not a request to delete them mechanically. It is evidence that the
umbrella currently serves three jobs at once: public API, build manifest, and
research-certificate registry.

The repository audit identifies 25 modules outside all default target roots.
They include the block-pair certificate stack, several rational/dyadic
certificate utilities, `QuittingDynamicDebtClockDischarge`,
`QuittingMarkedStrictTimeClosing`, the vanishing-charge regression, and two
non-quitting mathematical modules. Classify each as:

- public library (import through an appropriate aggregator),
- production regression (give it a regression aggregator/default target),
- certificate artifact (give it an explicit certificate target and policy),
- or retired research file (move out of production).

There are also three upward dependencies from `Math/` into stochastic-game
modules:
`CurveSelection/AlgebraicReduction.lean` and `AnalyticSign.lean` import
`BellmanCurveGate`, while
`Probability/SupportedMovingKernelEpochAccount.lean` imports
`MovingKernelEpochPotentialAccount`. These invert the advertised foundation
layer. Either move the generic content down behind a neutral interface or
document these files as game-theory applications rather than `Math` roots.

### Tests and regressions

`GameTheoryTest.lean` cleanly separates 24 compilation-test aggregators from
the public target, but there is no `GameTheory/Concepts/Stochastic/Tests.lean`.
Stochastic tests are instead interleaved with production through at least 19
`Counterexample`/`NoGo` modules plus many calibration files. Those are real
theorems and should remain kernel-checked; the missing piece is a lifecycle and
target distinction, not deletion.

Create a stochastic regression aggregator and decide whether it belongs in the
default test target, the public umbrella, or both. Headline semantic regressions
(Big Match, FTV, terminal/nonattainment, owner transfer, fixed-cutoff holonomy)
should remain continuously checked even if bulky numerical certificate data is
moved to a separate target.

### Certificate scripts and ignored experiments

The repository contains 43 Python scripts under `scripts/`; 41 use 689 plain
`assert` statements. Running Python with `-O` disables these checks. Replace
load-bearing assertions with explicit exceptions/check functions, especially
for exact block-pair certificates, and print a versioned certificate summary
or fingerprint.

The entire `experiments/` directory is ignored. Its README/run list covers only
E01--E35 and three Lean probes, while `RESULTS.md` and the directory contain
substantial later work such as `GreedyBufferedExitDecoder.lean`. Thus the
documented runner is not an exhaustive reproducibility surface. The natural
stopping point for the greedy file is correct—abstract greedy return/exit/dead
end is done; the missing theorem is game-facing—but its result should be mined
into a tracked claim and any reusable Lean theorem promoted or explicitly
left experimental.

Adopt a minimal experiment manifest with ID, command, expected output/hash,
claim owner, last audited commit, and promotion status. Do not make ignored
`RESULTS.md` status authority.

### Repeated proof interfaces

At least thirteen stochastic modules redeclare local variants of
`expect_pmfPi_bool`, `expect_uniform_bool`, or the same `PMF Bool` coordinate
calculus. This is a high-confidence small refactor candidate: extract a generic
finite-product Bool expectation lemma in the lowest legitimate probability
layer, then migrate consumers gradually. Preserve specialized names as thin
wrappers where that improves readability.

By contrast, do not prematurely merge the debt, stationary, periodic, and
holonomy structures merely because their equations look affine. They have
different semantic scopes and falsifiers; a common algebra should be extracted
only from two or more stable production consumers.

## P2 findings

- Audit the twelve heartbeat overrides, beginning with the nine quitting
  occurrences. Record why the default is insufficient and whether a local
  lemma split or explicit compactness API removes the cost.
- Profile cold compilation before splitting the largest modules. The 8.22
  second measurement is a warm replay and cannot identify elaboration
  hotspots reliably.
- Consider a generated umbrella manifest or category aggregators after module
  lifecycle is explicit. Until then, deleting the 415 transitively redundant
  imports would obscure intentional public exposure.
- Add a link checker for tracked Markdown. Durable documents should not depend
  on ignored `ephemeral/` or `experiments/` paths for current status.
- Reconcile bibliography metadata and manuscript entries through
  `docs/uniform-equilibrium/references/BibliographyMaintenance.md`.

## Research-state architecture

The new cold-handoff hierarchy is the right maintenance design:

1. `Program.md` — stable method and scope;
2. `PIPELINE.md` — decisions, objective priority, gates, and ownership;
3. `FRONTIER.md` — curated mathematical chain and exact open hinge;
4. `ideas/<group>/<claim>.md` — internal scientific objects;
5. `ideas/UniformEquilibriumLiterature/<result>.md` — attributed external
   results;
6. production Lean — machine truth;
7. the manuscript — derivative exposition; and
8. questions, reviews, experiments, and proof-mining notebooks — intake and
   evidence.

The lifecycle works only if a theorem commit updates its exact claim and a
changed boundary updates the frontier/pipeline immediately. The proof-mining
extraction audit currently classifies all 83 sections: 40 landed/mined, 23 live
mechanisms with owners, 12 independent scientific objects, two pending
standalone targets, one literature boundary, and five frozen/wrong/superseded
mechanisms. Those counts concern research disposition, not formalization.

## Acceptance plan

### P0 release gate

- workflow exists under `.github/workflows/` and runs on a real branch;
- full build succeeds;
- placeholder checker passes with one explicit, declaration-scoped open-problem
  policy;
- repository audit passes or reports only reviewed, narrow certificate
  exceptions;
- axiom audit proves requested count equals parsed count and includes the
  uniform/quitting keepers.

### P1 architecture gate

- all 25 orphan modules have a recorded lifecycle and target;
- stochastic regression/certificate targets are explicit;
- the three `Math -> GameTheory` inversions are removed or documented;
- exact Python certificate checks remain active under `python -O`; and
- tracked status documents pass a relative-link check without requiring
  ignored files.

### P2 maintainability gate

- cold-build profiling justifies any large-module split;
- heartbeat overrides carry reasons;
- repeated `PMF Bool` expectation algebra has one stable home; and
- manuscript and bibliography are checked derivatives of the frontier and
  literature records.
