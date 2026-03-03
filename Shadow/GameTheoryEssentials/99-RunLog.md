# Run Log

## 2026-03-03

- Scope correction:
  - excluded probability-only files from analysis focus.
- Data pass:
  - inventoried non-probability game modules (95 files).
  - exported `Inventory.csv` and `InventoryTop50.json`.
- Artifacts added:
  - family map,
  - lemma-shape matrix with cross-field names,
  - extraction priority queue,
  - assumption-audit template.
- Next move:
  1. pick top-3 large files by theorem count in game modules,
  2. run theorem-level assumption audits using `30-AssumptionAuditTemplate.md`,
  3. identify first one-shot generic extraction candidate spanning at least two files.

## 2026-03-03 (structure-first adjustment)

- User direction: prioritize actual minimal abstraction, delay intuitive naming.
- Action:
  - added `40-StructuralCore.md` with anonymous constraints `A1..A8`,
  - linked extraction queue to structural-first gate.
- Result: helped.

## 2026-03-03 (top-3 theorem audits)

- Target: audit large game-theory modules with structural constraints `A1..A8`.
- Action:
  - added per-module audit sheets for:
    - `EFGKuhnFull`,
    - `NashExistenceMixed`,
    - `EFGKuhn`,
  - added cross-module audit index with high-yield abstraction priorities.
- Result: helped.
- Next move:
  1. instantiate one reusable `A5` schema across both Kuhn modules (prose+one-shot lemma),
  2. draft one definition-free `A7` schema for hard-direction recombination.

## 2026-03-03 (full survey extension)

- Target: complete survey over entire game-theory side (excluding probability-only focus).
- Action:
  - generated full module manifest (`ModuleSurvey.csv`, `ModuleSurveySummary.json`),
  - added complete-survey note (`60-CompleteSurvey.md`),
  - added cross-family embedded abstract lemma catalog (`62-EmbeddedAbstractLemmas.md`),
  - pruned shadow duplicates of standard `Function.update` lemmas and added
    `32-StandardLibraryAnchors.md`.
- Result: helped.

## 2026-03-03 (all-theorems baseline)

- Target: shift from top-theorem sampling to full theorem-level baseline.
- Action:
  - generated `TheoremInventory.csv` (567 theorem/lemma declarations),
  - generated `TheoremInventoryTopFiles.json`,
  - added global block synthesis (`70-*`, `71-*`) and theorem-mapping workflow (`72-*`),
  - removed duplicate shadow update lemmas in favor of standard Mathlib anchors.
- Result: helped.

## 2026-03-03 (F4 theorem-family pass)

- Target: move from global inventory to full-family theorem mapping.
- Action:
  - extracted F4 theorem map (109 rows) with block tags and summaries,
  - added F4 synthesis and manual spot checks for high-impact theorems,
  - added progress tracker for all families.
- Result: helped.
- Next move:
  1. complete F4 manual correction of adapter/uncertain rows (`B10`),
  2. run the same pipeline for F5 (dynamics) and F7 (value/minimax).

## 2026-03-03 (F5 baseline pass)

- Target: extend theorem-family mapping beyond equilibrium family.
- Action:
  - extracted F5 theorem inventory (43 rows),
  - generated F5 block map and block/file distributions,
  - added F5 structural synthesis (`76-F5-Survey.md`).
- Result: helped.
- Next move:
  1. perform manual correction in F5 where `B7` is hidden as pure inequality statements,
  2. run F7 baseline extraction (value/minimax family).

## 2026-03-03 (F7 + geometry layer + F6 baseline)

- Target:
  - continue full-codebase family passes,
  - integrate AbstractFolk-style non-game geometry abstraction into the analysis stack.
- Action:
  - added F7 synthesis note (`77-F7-Survey.md`) from existing F7 artifacts,
  - added geometry-region layer note (`78-GeometryLayer.md`) introducing provisional `B11`,
  - generated F6 family artifacts:
    - `F6Files.txt`,
    - `F6TheoremInventory.csv` (29 rows),
    - `F6TheoremBlockMap.csv`,
    - `F6BlockCounts.json`,
    - `F6FileCounts.json`,
  - added F6 synthesis note (`79-F6-Survey.md`),
  - updated `README.md` and `75-ProgressTracker.md`.
  - added manual non-domain assumption slices for representative F6/F7 theorems
    (`80-F6F7-ManualAssumptionSlices.md`).
  - manually corrected F7 block assignments:
    - reclassified six rows from `B7` to `B9/B0`,
    - retained only `von_neumann_minimax` and `nash_interchangeable` as `B7`.
- Result: helped.
- Next move:
  1. manual correction of F6 transfer-heavy rows (`B5`) and F7 minimax-core rows (`B7`),
  2. extract one one-shot `B11` (geometry region) lemma in Lean without `GameTheory` imports.
