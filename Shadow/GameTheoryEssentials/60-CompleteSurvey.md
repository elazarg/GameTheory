# Complete Survey (Game-Theory Side)

This survey covers all in-scope game-theory modules:

- includes: all `GameTheory/*.lean`
- excludes: `PMFProduct.lean`, `Probability.lean`, and shadow folders

Coverage count: 95 modules.

Machine-readable manifests:

- [ModuleSurvey.csv](D:\workspace\games\GameTheory\Shadow\GameTheoryEssentials\ModuleSurvey.csv)
- [ModuleSurveySummary.json](D:\workspace\games\GameTheory\Shadow\GameTheoryEssentials\ModuleSurveySummary.json)

## Family map usage

Family tags in `ModuleSurvey.csv` are structural-first working tags:

- `F1/F8-CoreMeta`
- `F2-Bridge`
- `F3-Trace`
- `F4-Equilibrium`
- `F5-Dynamics`
- `F6-Mechanism`
- `F7-Value`
- `F8-Meta`

These tags are intentionally non-final and can be revised during extraction.

## What “complete” means here

1. Every in-scope module has a structural family tag.
2. Top-heavy modules already have focused audits:
   - `EFGKuhnFull`
   - `NashExistenceMixed`
   - `EFGKuhn`
3. Cross-family abstraction candidates are enumerated in:
   - `10-LemmaShapeMatrix.md`
   - `20-ExtractionQueue.md`
   - `62-EmbeddedAbstractLemmas.md`

## Next survey refinement step

For each family, pick 2-3 representative modules and run theorem-level
assumption audits using `30-AssumptionAuditTemplate.md`.

