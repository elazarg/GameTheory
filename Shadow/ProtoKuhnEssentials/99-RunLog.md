# Run Log

## 2026-03-03

- Target: establish a reusable analysis process before touching more proofs.
- Output:
  - workflow definition
  - abstract vocabulary
  - Kuhn-style and Zermelo-style decomposition ledgers
  - execution checklist
  - two one-shot generic lemmas (`curry_update`, `pushforward_comp'`)
- Result: helped.
- Next move:
  1. pick one blocked step (`easy direction` independence refactor),
  2. test whether `curry_update` eliminates local update/curry friction,
  3. if not, extract one additional `L0` normalization lemma only.

## 2026-03-03 (update)

- User constraint: avoid introducing new definitions where possible.
- Action:
  - removed newly-added custom predicates/constructors from `CoreSmallLemmas.lean`,
  - kept only structure-evident lemmas over existing primitives,
  - rewrote catalog entry in definition-free form.
- Result: helped.

## 2026-03-03 (continue)

- Target: continue with definition-free schemas and minimal assumptions.
- Action:
  - added one-shot generic lemma `foldl_update_invariant` (no new defs),
  - added schema catalog `31-DefinitionFreeSchemas.md` with cross-field names.
- Result: helped.
- Next move:
  1. instantiate one schema against a currently blocked proof step,
  2. confirm which assumptions are genuinely needed (especially `Fintype`/`DecidableEq`),
  3. record removable assumptions in the ledger.
