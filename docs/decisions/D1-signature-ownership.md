# D1: signature ownership

- **Status:** provisional
- **Date:** 2026-07-22
- **Evidence:** EXP-002, EXP-004
- **Decision:** A form provisionally stores a `sig` field. Strategy and outcome
  carriers remain fields of that signature; they are not duplicated on the form.

## Competition and hostile slice

The indexed candidate uses `Form sig`; the bundled candidate uses `Form ι` with
`sig : Signature ι`. This foundational miniature implements unilateral update
and simp rules, player reindexing, outcome mapping, product, mixed extension,
heterogeneous form-homs, identity/association laws, a reindexed toy compiler,
and six composed form-homs in both candidates. It is not evidence for the
still-deferred NFG, EFG, CE/CCE, or equilibrium slices. The same fixed
finite-support-PMF law carrier isolates D1 from D2.

The same-signature reuse test favors indexing: `pairedPlay` accepts two
`Form sig` values and one `Profile sig`. The bundled version needs an equality
`F.sig = G.sig` and uses two dependent `▸` transports.

## Measurements

Run:

```text
pwsh -NoProfile -File scripts/phase1-audit.ps1 -VerifyExpected -Time
lake env lean '-Dtrace.profiler=true' GameTheory/Experimental/Phase1/D1/Stress.lean
```

| Metric | Indexed | Bundled |
|---|---:|---:|
| Core nonblank lines | 95 | 99 |
| Raw transport tokens in core code | 2 | 2 |
| Allowed transports inside `Profile` implementation | 1 | 1 |
| Candidate-specific downstream stress transports | 0 | 2 |
| Comparable path after the profile allowance | 1 | 3 |
| Association declaration lines | 6 | 5 |
| Six-composition elaboration, observed warm run | 23.057 ms | 11.154 ms |
| Whole-file warm elaboration, observed review run | 15.570 s | 14.539 s |

The transport regex counts `cast`, `HEq`, `change`, `Eq.ndrec`, `Eq.mpr`,
`Eq.rec`, and `▸` after stripping comments and strings. Each core contains one
allowed `▸` inside `Profile.update` and one local `change` in the form-hom
proof. The downstream bundled `pairedPlay` adds two `▸` transports. After the
explicit profile allowance, the honest comparison is therefore 1 versus 3,
not the original 1 versus 1. The baseline is below ten, so the RFC forbids
using the “at least half” ratio. Reindexed compiler adequacy is `rfl` in both
designs. The indexed six-composition theorem also exposes seven signature
parameters; the bundled theorem exposes only seven forms.

Universe linting was rerun without the former file-wide suppression. Both
`Signature` declarations intentionally keep independent strategy and outcome
universes and use a declaration-local suppression. The bundled `Form ι` needs
a second, documented suppression: storing the signature makes `us` and `uo`
non-inferable from `Form ι`, and its universe is
`max uι (us + 1) (uo + 1)` rather than the indexed form's `max uι us uo`.
This is negative evidence against bundling, though it does not outweigh the
measured downstream signature advantage in this miniature.

The counts are diagnostics, not the design objective. Qualitatively, indexing
makes reusable same-signature mathematics and universe inference cleaner;
bundling makes ordinary generic theorem signatures shorter. The provisional
choice reflects that unresolved API tradeoff, not a line-count victory.

## Result and kill condition

D1 explicitly rejects indexing when it gives no material transport reduction or
makes downstream signatures harder. That condition fired, so bundling is the
provisional winner despite its worse same-signature reuse boundary.

This is not frozen. The transformation-taxonomy recheck must include a nested
operation chain, reindexing along `e` and then `e.symm`, and an equivalence
lifted through mixed extension. Phase 2/4 must overturn the decision if those
tests, or generic preference, utility, and deviation theorems, repeatedly
require signature equalities or user-visible transports. Games remain ordinary
values, never typeclass instances.
