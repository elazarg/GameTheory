# Declaration-level coverage ledgers

This directory holds the detailed accounting behind
`../V1CoverageLedger.md`. Add one ledger per bounded work package or coherent
theorem family; do not create one monolithic hand-maintained list.

## Required header

```text
Title:
Family ID:
Pinned roots:
Pinned commit: a3d8c67ed91d58e197b8c978ddcc00ba96f87c29
Successor baseline:
Canonical destination:
Domain contract / decision:
Owner:
Status:
Last verified:
```

## Required table

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|

Allowed dispositions are exactly:

- `port`
- `adapt`
- `subsumed`
- `refuted`
- `deferred`
- `retired`
- `out of scope`
- `unreviewed`

`deferred` and `out of scope` rows name the decision and concrete reopening
gate. `subsumed` rows name a checked theorem chain, not merely a similar
statement. `refuted` rows name the checked counterexample. `retired` rows
explain why the predecessor declaration is compatibility, duplicate semantics,
implementation detail, or unused transport rather than mathematical payload.

Aggregators and test files are classified too. Their declarations are normally
recreated through the owning public umbrella, examples, or tests; source
compatibility is not required.

## Completion rule

A ledger is complete only when:

1. every substantive declaration in its pinned roots occurs exactly once;
2. no row remains `unreviewed`;
3. every `port`, `adapt`, and `subsumed` target exists and builds;
4. every exclusion has its decision evidence;
5. attribution and exact validation commands are recorded;
6. the family summary in `../V1CoverageLedger.md` changes in the same commit.

Generated declaration indices may seed a ledger, but classification is a
mathematical review and is never inferred from matching names.
