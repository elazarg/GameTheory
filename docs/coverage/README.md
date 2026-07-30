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

## Machine-readable coverage gate

`FamilyScopes.tsv` is the exact, non-overlapping ownership routing for every
Lean file in the pinned snapshot. `PinnedDeclarations.tsv` is generated from
that snapshot after nested comments, line comments, and strings are removed.
It records source path, line, family owner, declaration kind, source spelling,
and visibility. It is an index, not a disposition ledger.

Regenerate and verify it with:

```text
pwsh -NoProfile -File scripts/coverage-audit.ps1 -UpdateIndex
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
```

The audit rejects:

- a pinned file with zero or multiple family owners;
- a family route absent from `V1CoverageLedger.md`;
- an unknown family recovery state or declaration disposition;
- a stale generated index;
- a ledger row naming a missing or ambiguous pinned path/declaration;
- duplicate disposition claims for one pinned declaration;
- an exactly `complete` ledger with an unreviewed/deferred row; and
- a broad family marked `complete` while any declaration is unaccounted,
  unreviewed, or deferred.

`UNACCOUNTED_PINNED_DECLARATIONS` is deliberately reported rather than forced
to zero today. It reaches zero only by adding reviewed ledger rows; the
generator never fills it with guessed name matches.
