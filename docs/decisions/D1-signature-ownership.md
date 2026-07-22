# D1: signature ownership

- **Status:** provisional
- **Date:** 2026-07-22
- **Evidence:** EXP-002
- **Decision:** A form provisionally stores a `sig` field. Strategy and outcome
  carriers remain fields of that signature; they are not duplicated on the form.

## Competition and hostile slice

The indexed candidate uses `Form sig`; the bundled candidate uses `Form ι` with
`sig : Signature ι`. Both implement unilateral update and simp rules, player
reindexing, outcome mapping, product, mixed extension, heterogeneous form-homs,
identity/association laws, a reindexed toy compiler, and six composed form-homs.
The same fixed finite-support-PMF law carrier isolates D1 from D2.

The same-signature reuse test favors indexing: `pairedPlay` accepts two
`Form sig` values and one `Profile sig`. The bundled version needs an equality
`F.sig = G.sig` and uses two dependent `▸` transports. Those transports are
recorded as API evidence even though D1's prescribed syntax metric does not
include the `▸` notation.

## Measurements

Run:

```text
pwsh -NoProfile -File scripts/phase1-audit.ps1 -VerifyExpected -Time
lake env lean '-Dtrace.profiler=true' GameTheory/Experimental/Phase1/D1/Stress.lean
```

| Metric | Indexed | Bundled |
|---|---:|---:|
| Core nonblank lines | 93 | 93 |
| `cast`/`HEq`/`change`/`Eq.ndrec`/`Eq.mpr` tokens in code | 1 | 1 |
| Association declaration lines | 6 | 5 |
| Six-composition elaboration, observed warm run | 23.057 ms | 11.154 ms |
| Whole-file warm elaboration, observed run | 15.704 s | 13.677 s |

The only counted transport token in either core is a local `change` in the
form-hom commutation proof. The baseline is below ten, so the RFC forbids using
the “at least half” ratio. Reindexed compiler adequacy is `rfl` in both designs.
The indexed six-composition theorem also exposes seven signature parameters;
the bundled theorem exposes only seven forms.

## Result and kill condition

D1 explicitly rejects indexing when it gives no material transport reduction or
makes downstream signatures harder. That condition fired, so bundling is the
provisional winner despite its worse same-signature reuse boundary.

This is not frozen. Phase 2 must overturn the decision if generic preference,
utility, deviation, or transformation theorems repeatedly require signature
equalities or user-visible transports. Games remain ordinary values, never
typeclass instances.
