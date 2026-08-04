# Finite cycles are refuted; the carrier is a mass-parametrized path

## Lifecycle

| Field | Value |
| --- | --- |
| Lifecycle | `ACTIVE` |
| Verdict | `WRONG` for the finite-cycle carrier; `OPEN` for its replacement |
| Objective priority | `P0` |
| Last audited | 2026-08-04; attribution located and the case-2 premise restored at its bounded form |
| Central live claim | No finite absorbing complementary cycle exists in general, in either open case. What does exist is a family of absorbing cyclic recursions whose **complementarity defect** tends to zero with period tending to infinity, converging to a continuous mass-parametrized absorption path. |
| Next discriminant | Whether a defect-vanishing family suffices for the target, and what the limiting path must retain. |
| Production destination | none yet |
| Supersedes / superseded by | supersedes the finite-cycle premise; reopens the absorption-path route deprioritised by `PC-008` |

## Claim ledger

| Claim | Verdict | Seals | Scope | Consumer |
| --- | --- | --- | --- | --- |
| A three-coordinate weight with every `r_i({i}) = 1/3 > 0` admits no absorbing complementary cycle of any finite length | `PROVED` | `M` | case 2 | refutes the finite-cycle carrier in case 2 |
| A case-3 weight exists whose only cycle-type outcome is an isolated negative discounted limit, with no admissible cycle of any length | `PROVED` | `M` | case 3 | refutes it again, differently |
| For the case-2 weight there are absorbing cyclic recursions of period `3m` with complementarity defect `~ η·log 2 / (3m) → 0` | `PROVED` | `M` | case 2 | the replacement carrier. The family itself is **published** (AGKRS p. 741); only the defect asymptotic is internal. |
| The limit of that family is a continuous mass-parametrized absorption path | `PROVED` | `M` | case 2 | the replacement carrier. **Published** as AGKRS Example 5.6, an explicit continuous equilibrium. |
| In case 3 the limiting object must additionally retain the isolated-coordinate mismatch as a mark | `PROVED` | `M` | case 3 | the replacement carrier |
| No length bound exists; the minimum period diverges as the defect tends to zero | `PROVED` | `M` | case 2 family | closes the bounded-length question; independently attested by Solan's Theorem 2.2 |

## Attribution: located, and the exact form it holds in

The case-2 refutation is obtained by repeating a hypothetical finite cycle
indefinitely to produce a *completely absorbing* infinite complementary
recursion — the "inverse iterate" of
[`Question147`](../../questions/Question147-NoCompletelyAbsorbingComplementaryArray.md)
— and invoking an external theorem for the assertion that no such iterate
exists for all sufficiently small positive perturbations of that table.

**The source is E. Solan, *The dynamics of the Nash correspondence and
`n`-player stochastic games*, Int. Game Theory Rev. 3, 291–300 (2003);
preprint at `math.tau.ac.il/~eilons/value4.pdf`, local copy
`ephemeral/solan-nash-correspondence-dynamics-value4.pdf`.** Its **Theorem
2.1** is exactly the cited statement, its vocabulary is verbatim
("inverse iterate", "completely absorbing", "admissible sequence"), and the
game `G_ε` of its Figure 1 is the `Question147` weight multiplied by `3` on all
seven entries with `η = ε`. Full record, adapter, and the two further results
it supplies: [`PerturbedFTVGameHasNoBoundedCompletelyAbsorbingInverseIterate`](../UniformEquilibriumLiterature/PerturbedFTVGameHasNoBoundedCompletelyAbsorbingInverseIterate.md).

**The form it holds in is the bounded one.** Theorem 2.1 states no boundedness
hypothesis, and in that literal form it is false: `QuittingUnboundedInverseIterate.lean`
machine-checks a completely absorbing inverse iterate for the weight with rows
`(p,0,0)` and values `(1/3, 1, K·q^{-t})`, for every `η ≥ 0`. Its third
coordinate grows exactly like the inverse of the survival product, so the
survival prefix times the value is a positive constant at every stage and the
homogeneous boundary term is never consumed. The source's proof runs entirely
through its display (1), the convex-hull bound `Σ_i y_i ≤ 4`, which is exactly
where boundedness enters — unstated. In the source's scaling the witness has
`Σ_i y_i = 5 + εp > 4`.

**This does not cost the case-2 row anything**, because repeating a finite
cycle produces values inside that convex hull by construction. So the deduction
runs on the bounded form, which is what the proof establishes.

Two further findings bound the claim's shape.

- **The repetition step is sound.** Periodic extension of a cyclic array
  satisfies the inverse-iterate conditions at every stage *including the seam*,
  because the cycle condition already closes `z_{L+1} = z_1` and demands
  complementarity of `(y_L, z_1)`; and `∏_k c(y_k) < 1` forces the infinite
  product to `0`.
- **The `η = 0` weight is the Flesch–Thuijsman–Vrieze (1997) cubic game
  divided by 3**, on every one of the seven rows, pair rows included — as the
  source itself says. That game has an exact absorbing complementary cycle of
  length 3: each coordinate in turn quits with probability `1/2`, values
  `(1/3, 2/3, 1/3)` cyclically. It is FTV's cyclic Markov `0`-equilibrium, and
  is also the equilibrium exhibited in
  Ashkenazi-Golan–Krasikov–Rainer–Solan 2020, Example 5.4. **So the claim is
  false at `η = 0`, in the bounded form too, and the perturbation carries the
  entire statement** — matching the source's own "for every `ε > 0`
  sufficiently small", with no `ε_0` supplied.
- **The perturbation is aimed exactly at that cycle, and destroys it by a
  knife-edge.** Against `y = (1/2, 0, 0)` the idle third coordinate has
  `g_3 = η/6`: zero at `η = 0`, so complementarity holds with the third
  coordinate exactly indifferent, and strictly positive for every `η > 0`, so
  complementarity fails.

The premise is therefore attested, non-vacuous, correctly targeted, and
consistent with what is known: the source records in its own voice that `G_ε`
**does** admit a uniform equilibrium payoff by Solan (1999), so a weight can be
solved and still have no exact absorbing inverse iterate. That is the whole
point of its Theorem 2.1, and it is the same point this file makes about the
carrier.

**Bibliographic discipline.** The earlier attribution "Solan, inverse-iterate,
Thm 2.1" was accurate but unusable: it named neither the paper nor a year, and
the paper's title mentions neither quitting games nor absorption, so two source
sweeps missed it. Cite the full identifier above.

**Methodological note.** The first sweep was directed at the external
literature and not at `ephemeral/`; the second swept the repository's eleven
local PDFs and also missed it, because the paper is not among them. What found
it was the citation trail: it is reference `[16]` in
Ashkenazi-Golan–Krasikov–Rainer–Solan. A source audit must chase the reference
lists of papers already on disk before returning `NOT LOCATABLE`. Note also
that `ephemeral/old/counterexample-research/sources/aps-quitting-2026.pdf` is a
3 KB HTML bot-block page rather than a paper, so a sweep that trusts filenames
skips it silently.

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

**This family is published, and so is its limit.** The case-2 weight is
Ashkenazi-Golan–Krasikov–Rainer–Solan's own `Γ_η` (Fig. 1, p. 741) under the
map `t ↦ (t+1)/3` on every payoff of every player, all eight rows included. On
that same page they print the family verbatim: each player quits with
probability `ρ` over its own block of `m` stages, `(1−ρ)^m = 1/2`, and the
profile is an `ε`-equilibrium for `m` large. Their Example 5.6, p. 758, gives
the limit as an explicit **continuous equilibrium** `(1,½),(2,½),(3,½),…`,
justified by their Theorem 5.4 because the matrix
`M_{ij} = r_i({j}) − r_i({i})` is a `Q̄`-matrix. `M` is built from the
singleton rows alone, so it is **independent of `η`** — which is exactly why
the continuous object survives the perturbation that destroys every finite
cycle. Record:
[`QBarMatrixQuittingGamesHaveContinuousEquilibria`](../UniformEquilibriumLiterature/QBarMatrixQuittingGamesHaveContinuousEquilibria.md).

Two corrections this forces. The internal `M` seals on the period-`3m` family
and its limit were re-derivations of published results, not new mathematics;
the value of the internal work is the *defect asymptotic* `η·log 2/(3m)`, which
the source does not compute. And the `ε`-equilibrium existence for this weight
is **free**, from Solan (1999) on three-player quitting games — not a
consequence of the `Q̄` condition, which has content only at `|I| ≥ 4`.

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

- **Use the bounded form of the attributed theorem, never the literal one.**
  The literal unbounded statement is machine-checked false; a derivation that
  quantifies over unbounded value arrays is unsound.
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
