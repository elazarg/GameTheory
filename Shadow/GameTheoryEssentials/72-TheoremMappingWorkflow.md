# Theorem Mapping Workflow (All Theorems)

Goal: map every theorem in `TheoremInventory.csv` to structural blocks (`B0..B11`)
without relying on domain mnemonics.

## Input

- `TheoremInventory.csv`
- `ModuleSurvey.csv`
- `70-GlobalBuildingBlocks.md`
- `30-AssumptionAuditTemplate.md`

## Procedure

1. Select one module.
2. For each theorem row `(file, line, name)`:
   - classify into 1 primary block + up to 2 secondary blocks,
   - mark current assumptions as `E/?/A` (essential/maybe-removable/adapter).
3. Record one sentence in block language:
   - equation/implication over update/bind/sum/reachability/recursion.
4. Mark extraction status:
   - `S` standard (already in Mathlib),
   - `R` reusable core candidate,
   - `A` adapter-only.

## Output format (per theorem)

- theorem id: `File:Line Name`
- block tags: `B*`
- assumption tags: `E/?/A`
- status: `S/R/A`
- note: one-line structural restatement

## Quality bar

Mapping is acceptable only if:

1. the note is intelligible without game mnemonics;
2. at least one assumption is tagged `?` or explicitly justified as `E`.

## Backtracking rule

If block mapping is ambiguous:

1. mark as `B?`,
2. add two candidate mappings,
3. defer extraction until ambiguity is resolved by neighboring theorems.
