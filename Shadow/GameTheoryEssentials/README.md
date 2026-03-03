# GameTheory Essentials (Shadow, Whole Codebase)

Purpose:

- analyze the game-theory side of the repository with minimal assumptions,
- avoid probability-only abstraction discussion,
- keep format-specific assumptions in thin adapter layers.

Scope:

- see `00-Scope.md`
- generated inventory: `Inventory.csv`, `InventoryTop50.json`

Core docs:

1. `01-ModuleFamilies.md`
2. `10-LemmaShapeMatrix.md`
3. `20-ExtractionQueue.md`
4. `30-AssumptionAuditTemplate.md`
5. `40-StructuralCore.md`
   - anonymous interface constraints (`A1..A9`) and theorem schemas (`T1..T3`)
   - structure-first, name-later workflow
6. top-3 heavy-module audits:
   - `50-Audit-EFGKuhnFull.md`
   - `51-Audit-NashExistenceMixed.md`
   - `52-Audit-EFGKuhn.md`
   - index: `53-AuditIndex-Top3.md`
7. full-codebase coverage:
   - `60-CompleteSurvey.md`
   - `ModuleSurvey.csv`
   - `ModuleSurveySummary.json`
   - `TheoremInventory.csv`
   - `TheoremInventoryTopFiles.json`
8. extracted abstract concepts:
   - `62-EmbeddedAbstractLemmas.md`
   - `70-GlobalBuildingBlocks.md`
   - `71-FamilyToBlocksMap.md`
   - `72-TheoremMappingWorkflow.md`
9. F4 deep pass:
   - `73-F4-Survey.md`
   - `74-F4-ManualSpotChecks.md`
   - `F4TheoremBlockMap.csv`
   - `F4BlockCounts.json`
   - `F4FileCounts.json`
10. overall progress:
   - `75-ProgressTracker.md`
11. F5 family pass:
   - `76-F5-Survey.md`
   - `F5TheoremInventory.csv`
   - `F5TheoremBlockMap.csv`
   - `F5BlockCounts.json`
   - `F5FileCounts.json`
12. F7 family pass:
   - `77-F7-Survey.md`
   - `F7TheoremInventory.csv`
   - `F7TheoremBlockMap.csv`
   - `F7BlockCounts.json`
   - `F7FileCounts.json`
13. geometry/region abstraction layer:
   - `78-GeometryLayer.md`
14. F6 family pass:
   - `79-F6-Survey.md`
   - `F6Files.txt`
   - `F6TheoremInventory.csv`
   - `F6TheoremBlockMap.csv`
   - `F6BlockCounts.json`
   - `F6FileCounts.json`
15. manual assumption slices:
   - `80-F6F7-ManualAssumptionSlices.md`

Process:

- use assumption-audit template per selected theorem,
- extract only high-reuse, definition-free lemmas,
- record backtracking instead of committing early hierarchy.
