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
| A three-coordinate weight with every `r_i({i}) = 1/3 > 0` admits no absorbing complementary cycle of any finite length | **`OPEN`** — was `PROVED`; the citation is not locatable and the internal route is refuted in the form it was stated | no seal | case 2 | **no longer refutes anything**; see below |
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

**Attribution caveat — audited 2026-08-04, verdict `NOT LOCATABLE`.** The
case-2 refutation is obtained by repeating a hypothetical finite cycle
indefinitely to produce a *completely absorbing* infinite complementary
recursion (the "inverse iterate" of
[`Question147`](../../questions/Question147-NoCompletelyAbsorbingComplementaryArray.md)),
and citing an external theorem recorded here as "Solan, inverse-iterate
counterexample, Thm 2.1" for the assertion that no such iterate exists for all
sufficiently small positive perturbations of that table. **A source audit
failed to find any such theorem, and found positive evidence that it does not
exist under that attribution.** Every Solan quitting-game paper was retrieved
and searched — Solan–Vieille 2001 and 2002a, Solan–Vohra 2001, Solan 2005,
Solan–Solan 2018 and 2020, Munk–Solan 2020, Ashkenazi-Golan–Krasikov–Rainer–Solan
2020 and 2023, Solan–Vieille 2025, and Solan's textbook — together with a full
arXiv author sweep. None of them contains the terms *inverse iterate* or
*completely absorbing*; none of the quitting-game papers has a Theorem 2.1 at
all. So the citation cannot be used, and this row carries no external support.

Three findings bound how much of the claim survives that.

- **The repetition step is sound.** Periodic extension of a cyclic array
  satisfies the inverse-iterate conditions at every stage *including the seam*,
  because the cycle condition already closes `z_{L+1} = z_1` and demands
  complementarity of `(y_L, z_1)`; and `∏_k c(y_k) < 1` forces the infinite
  product to `0`. So the deduction is valid — only its premise is unsupported.
- **The `η = 0` weight is the Flesch–Thuijsman–Vrieze (1997) cubic game
  divided by 3**, on every one of the seven rows, pair rows included. That game
  has an exact absorbing complementary cycle of length 3: each coordinate in
  turn quits with probability `1/2`, values `(1/3, 2/3, 1/3)` cyclically. It is
  FTV's cyclic Markov `0`-equilibrium, and is also the equilibrium exhibited in
  Ashkenazi-Golan–Krasikov–Rainer–Solan 2020, Example 5.4. **So the claim is
  false at `η = 0` and the perturbation carries the entire statement.**
- **The perturbation is aimed exactly at that cycle, and destroys it by a
  knife-edge.** Against `y = (1/2, 0, 0)` the idle third coordinate has
  `g_3 = η/6`: zero at `η = 0`, so complementarity holds with the third
  coordinate exactly indifferent, and strictly positive for every `η > 0`, so
  complementarity fails. That is why the asserted scope is "all sufficiently
  small `η > 0`" rather than a fixed table.

**On the boundedness question raised by the superseding note above:** the audit
cannot answer it from a source, because there is no source to read. Whether the
attributed theorem carries a boundedness hypothesis on the values is not a
question about the literature but about an assertion with no located referent.
What the audit does supply is a data point on the *bounded* form: the length-3
FTV cycle above is a **bounded** completely absorbing inverse iterate, so the
bounded form of the premise is also false at `η = 0`, and it too stands or
falls entirely on `η > 0`.

The premise is therefore non-vacuous, correctly targeted, and consistent with
what is known — three-player quitting games have `ε`-equilibria (Solan 1999),
which does not give exact absorbing ones — but it is **not attested**. Nothing
found refutes the bounded form; nothing found supports it. The row's `PROVED`
verdict rests on `Question147` being settled internally, and this file no longer
supplies a citation for it.

Do not re-cite "Solan, Thm 2.1" anywhere. If a later worker believes the result
exists, the burden is a bibliographic identifier, not a name.

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
