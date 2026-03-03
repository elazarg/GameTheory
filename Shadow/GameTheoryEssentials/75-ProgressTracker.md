# Progress Tracker (Whole Codebase Structural Survey)

Legend:

- `done`: baseline survey + block synthesis done
- `in-progress`: partial theorem-level mapping
- `pending`: not yet mapped theorem-level

## Family status

- `F1/F8-CoreMeta`: `done` (module-level survey), theorem-level mapping `pending`
- `F2-Bridge`: `done` (module-level survey), theorem-level mapping `pending`
- `F3-Trace`: `in-progress` (Kuhn-heavy audits done), full family mapping `pending`
- `F4-Equilibrium`: `in-progress`
  - theorem inventory extracted
  - heuristic block map complete
  - manual spot checks complete
  - full row-by-row manual correction pending
- `F5-Dynamics`: `in-progress`
  - theorem inventory extracted
  - heuristic block map complete
  - family synthesis complete
  - manual correction pending
- `F6-Mechanism`: `in-progress`
  - theorem inventory extracted
  - heuristic block map complete
  - family synthesis complete
  - manual correction pending
- `F7-Value`: `in-progress`
  - theorem inventory extracted
  - heuristic block map complete
  - family synthesis complete
  - manual correction pending

## Next concrete passes

1. Finish F4 manual correction of all `B10` rows.
2. Manually review F6 `B5` rows (transfer-heavy files) for minimal assumptions.
3. Manually verify F7 `B7` rows (minimax core) and extract one standalone extremal lemma.
4. Revisit F3 and generalize Kuhn-specific abstractions into family-level blocks.

Status note:

- F7 `B7` manual verification complete; only two core rows remain (`von_neumann_minimax`, `nash_interchangeable`).
