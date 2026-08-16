# D1: signature ownership

- **Status:** decided; bundling retained after the Phase 4 recheck
- **Date:** 2026-07-22, amended 2026-07-26 and 2026-07-29
- **Evidence:** EXP-002, EXP-004, EXP-006, EXP-020
- **Decision:** A form stores a `sig` field. Strategy and outcome
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
| Core nonblank lines | 96 | 101 |
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

Universe linting's proposed collapses were reviewed before disabling
`linter.checkUnivs` for the library, because that linter cannot express the
declaration-local exceptions this experiment needs. Both `Signature`
declarations document their intentionally independent strategy and outcome
universes locally. The bundled `Form ι` also documents a second universe cost:
storing the signature makes `us` and `uo` non-inferable from `Form ι`, and its
universe is
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

## Phase 2 amendment (EXP-006)

The generic preference, utility, and deviation theorems did **not** require
signature equalities or user-visible transports: Phase 2 source contains one
transport token in total, inside the representation module, and the profile
module contains one, inside `Subprofile.single`. That part of the recheck
passes.

A different cost appeared instead. Storing the signature makes projections out
of a derived form opaque: `F.mixed.sig` does not reduce to `F.sig.mixed`, and
`(F.mapOutcome f).sig.Outcome` does not reduce to the target outcome type, at
`instances` transparency. `rw` and `simp` then build targets that are only
type-correct at default transparency and fail with an application type
mismatch. The repair was to make every signature and form transformer
`@[reducible]`:

```text
GameSignature.mapOutcome   GameSignature.mixed
GameForm.mapOutcome        GameForm.mixed
TableGame.toForm           BayesianGame.toForm
```

Even then, `isNash_mapOutcome` needs one `show` to restate its goal at the
transparent type. Six reducibility annotations plus one `show` is a small but
real tax that the indexed candidate would not pay, because there the carrier
appears in the type of the form rather than behind a projection.

This is recorded as additional negative evidence for bundling. It is not enough
to flip the decision on its own — the Phase 1 downstream-signature advantage
still stands — but D1 stays provisional and the Phase 4 transformation trial
should weigh it explicitly.

---

## Phase 4 recheck and decision (2026-07-29)

- **Status:** decided. A form stores its signature.
- **Experiment ID:** EXP-020.

The provisional decision named three transformations to be rerun and one
condition that would overturn it: the accepted design *repeatedly* needing
signature equalities or user-visible transports. Both have now been done.

### The tests

*Nested operation chain.* Relabel outcomes, take the mixed extension, form a
product, and state the evaluation law. Reduction proves it in both candidates.
Neutral.

*Reindex round trip, along `e` and then `e.symm`.* This one discriminates, and it
discriminates against indexing. Reindexing forward and back does not return to
the same signature by reduction — the strategy carrier becomes
`sig.Strategy (e.symm (e i))`, which is the original only propositionally. Under
indexing the two sides therefore live in different types and the statement
**cannot be written at all** without a signature equality to transport along;
`subst` cannot remove that hypothesis, because the signature occurs on both sides
of it. Under bundling both sides are `Form ι` and the statement needs neither.

*Equivalence lifted through mixed extension.* Reindexing commutes with the mixed
extension only up to interchanging the independent product with the relabelling
of players. That is a real lemma in both candidates — reduction is rejected on
both sides. Neutral, and not free either way.

### The counter-evidence, weighed rather than dismissed

Two spikes measured the other axis and both favour indexing. Every one of the
32 reducibility annotations in the library is forced by a stored carrier; they
carry 243 projection sites; an omission fails late and far from its cause; and
an induction over histories must have its index written at the projection rather
than at the carrier. Nothing in the library requires the carriers to be stored:
no structure holds a protocol as a field, nothing quantifies over protocols whose
carriers must vary. At the static layer indexing would halve the annotations
rather than clear them, since the signature transformers must stay reducible
either way.

### Result

The overturn condition did not fire. It asked whether the accepted design
repeatedly needs signature equalities or user-visible transports; across the
three named tests it needs none in any statement, while the indexed candidate
needs both in one of them. The decision was taken on downstream signature
ergonomics and the recheck was aimed at exactly that axis, which is why it, and
not the annotation count, settles the matter.

Bundling stands. The reducibility tax is real, is now measured, and is accepted
as a known bounded cost rather than left as folklore: `phase2-audit.ps1` fails if
any literal instance of a carrier-bearing structure is not reducible, which
converts the late and confusing failure into an immediate one and recovers most
of what indexing was offering.

**Consequences for public API:** unchanged. Forms keep a `sig` field, protocols
keep their state and action carriers, and every literal instance of such a
structure is `@[reducible]` — now enforced rather than remembered.
