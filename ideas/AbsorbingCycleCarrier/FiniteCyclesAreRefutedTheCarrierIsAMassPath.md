# Finite cycles are refuted; the carrier is a mass-parametrized path

## Lifecycle

| Field | Value |
| --- | --- |
| Lifecycle | `ACTIVE` |
| Verdict | `WRONG` for the finite-cycle carrier; `OPEN` for its replacement |
| Objective priority | `P0` |
| Last audited | 2026-08-04, `1937117` |
| Central live claim | No finite absorbing complementary cycle exists in general, in either open case. What does exist is a family of absorbing cyclic recursions whose **complementarity defect** tends to zero with period tending to infinity, converging to a continuous mass-parametrized absorption path. |
| Next discriminant | Whether a defect-vanishing family suffices for the target, and what the limiting path must retain. |
| Production destination | none yet |
| Supersedes / superseded by | supersedes the finite-cycle premise; reopens the absorption-path route deprioritised by `PC-008` |

## Claim ledger

| Claim | Verdict | Seals | Scope | Consumer |
| --- | --- | --- | --- | --- |
| A three-coordinate weight with every `r_i({i}) = 1/3 > 0` admits no absorbing complementary cycle of any finite length | `PROVED` | **no seal** — the attributed external theorem was audited and **could not be located**; see the caveat | case 2 | refutes the finite carrier |
| A case-3 weight exists whose only cycle-type outcome is an isolated negative discounted limit, with no admissible cycle of any length | `PROVED` | `M` | case 3 | refutes it again, differently |
| For the case-2 weight there are absorbing cyclic recursions of period `3m` with complementarity defect `~ η·log 2 / (3m) → 0` | `PROVED` | `M` | case 2 | the replacement carrier |
| The limit of that family is a continuous mass-parametrized absorption path | `PROVED` | `M` | case 2 | the replacement carrier |
| In case 3 the limiting object must additionally retain the isolated-coordinate mismatch as a mark | `PROVED` | `M` | case 3 | the replacement carrier |
| No length bound exists; the minimum period diverges as the defect tends to zero | `PROVED` | `M` | case 2 family | closes the bounded-length question |

> **Superseding note, 2026-08-04.** The case-2 refutation's premise, *stated
> without a boundedness condition on the values*, is **false**. An explicit
> inverse iterate for that weight has rows `(p,0,0)` and values
> `(1/3, 1, K·q^{-t})`; the third coordinate grows exactly like the inverse of
> the survival product, so the survival prefix times the value does not vanish
> even though the prefix does. That unconsumed homogeneous boundary term is
> what the Lyapunov shape of the intended argument cannot discard.
>
> What survives: repeating a finite cycle produces **bounded** values, so the
> deduction to "no finite absorbing cyclic array" would follow from the
> *bounded* form of the premise. That form is neither proved nor refuted here.
> So the case-2 claim below is **not currently supported**, and whether the
> cited source carries the boundedness hypothesis is precisely what the audit
> is checking. See `PC-010`.
>
> The rest of this file is unaffected: the defect-vanishing family, its limit,
> and the case-3 material do not consume the premise.

**Attribution caveat, load-bearing.** The case-2 refutation is obtained by
repeating a hypothetical finite cycle indefinitely to produce a *completely
absorbing admissible inverse iterate*, and citing an external theorem
(Solan, inverse-iterate counterexample, Thm 2.1) that no such iterate exists
for small positive perturbations of that table. **This repository has not
verified that theorem against its source.** If it is misquoted or its scope is
narrower than used, the case-2 refutation falls. Verifying it is the single
highest-value audit on this claim.

## What was refuted

The carrier previously proposed was: a finite list of rows reproducing its own
value, complementary at every phase, absorbing, and admissible. Its sufficiency
is machine-checked. Its **completeness** is now refuted twice over:

- **Case 2** (`S₊ ≠ ∅`, `S₋ = ∅`, so admissibility is automatic): a
  three-coordinate weight with all diagonal entries `1/3` and a small
  perturbation parameter `η` has *no* absorbing complementary cycle of any
  finite length, so there is nothing for admissibility to be automatic about.
- **Case 3** (`S₊ ≠ ∅`, `S₋ ≠ ∅`): a weight for which the isolated-negative
  discounted limit genuinely obstructs, and no other admissible absorbing cycle
  exists.

Together with the earlier two-coordinate counterexample against the zero-solo
disjunction, the finite-cycle carrier is refuted in every open case.

## What replaces it

For the case-2 weight there is an explicit period-`3m` family in which the
three coordinates act in successive blocks, each block having combined survival
`1/2`, with complementarity defect of order `1/m`. So:

> There are absorbing cyclic recursions with complementarity defect tending to
> zero, but no exact finite complementary cycle.

**Terminology matters here and the distinction is not cosmetic.** The vanishing
quantity is the *complementarity defect*, not the *mismatch*. Mismatch is
defined only after exact complementarity; in case 2 any exact absorbing
complementary cycle would already have mismatch zero, and the obstruction is
that none exists. A claim of the form "cycles whose mismatch tends to zero" is
a category error.

The limit of the family is a **continuous mass-parametrized absorption path**,
with nondecreasing coordinates. In case 3 that path must additionally carry a
**mark** recording the isolated-coordinate mismatch: the old admissible cycles
are exactly the finite-jump, zero-mark members of the enlarged class, and
neither "finite-jump" nor "zero-mark" is closed under the limiting operation.

## Consequence for project control

This **reopens the absorption-path route** that `PC-008` deprioritised, but for
a different and much better reason than the one that motivated it originally.
The old motivation was compactifying escaping middles of the zero-pinned chain
grammar — which was, correctly, diagnosed as an artifact. The new motivation is
that the correct carrier for the *unpinned* problem provably is not finite:
finite cycles do not exist, defect-vanishing families of unbounded period do,
and their limit is a mass path. See `PC-009`.

What does **not** come back is the zero pin, or the optimized-debt plateau, or
the tightness and surgery questions built on them. Those refutations stand.

## Falsifiers and wrong turns

- **The attributed theorem is the weak point.** Audit it before building on the
  case-2 refutation.
- Do not restate the refutation as "mismatch tends to zero"; see above.
- Do not conclude from a defect-vanishing family that the target holds. That
  implication is exactly what is now open: a defect-`ε` cyclic recursion is not
  obviously an `ε`-approximate solution of the intended problem, and the
  conversion has to be proved.
- Do not look for a length bound. The minimum period provably diverges as the
  defect tends to zero.

## Exit conditions

`MINED` when the defect-to-target conversion is decided and the limiting path's
required data is fixed.
