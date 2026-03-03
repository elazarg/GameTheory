# Execution Checklist (Iteration-Based)

Use this per session.

## Phase A: Select Target

1. Choose one large theorem (`easy` or `hard` direction, or Zermelo recursion).
2. Write its abstract goal shape in 2 lines.
3. Declare current blocked step id from decomposition doc.

## Phase B: Dependency Trim

1. List immediate lemmas used by current proof.
2. For each, tag layer: `L0`, `L1`, `L2`, or adapter.
3. For each assumption in statement, mark:
   - `E` essential
   - `?` maybe removable
   - `F` framework artifact

## Phase C: One-Shot Extraction

1. Extract at most one new local lemma.
2. Keep it independent (no new hierarchy branch).
3. Record exactly which blocked step it unlocks.

## Phase D: Evaluate

1. Did blocked step simplify?
2. If yes: note the simplification pattern.
3. If no: revert conceptual direction (not necessarily code) and log why.

## Phase E: Log

Append to backtracking log:

- date
- target theorem/step
- extracted lemma (if any)
- result (`helped`, `neutral`, `failed`)
- next move

