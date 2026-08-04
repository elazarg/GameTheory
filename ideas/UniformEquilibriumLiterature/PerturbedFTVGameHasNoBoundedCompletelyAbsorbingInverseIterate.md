# The perturbed FTV game has no bounded completely absorbing inverse iterate

| Field | Value |
| --- | --- |
| Citation of record | E. Solan, *The dynamics of the Nash correspondence and `n`-player stochastic games*, International Game Theory Review **3**(4), 291–299 (2001), DOI [`10.1142/S0219198901000488`](https://doi.org/10.1142/S0219198901000488). Preprint dated 25 January 2001, [`value4.pdf`](https://www.math.tau.ac.il/~eilons/value4.pdf), local copy `ephemeral/solan-nash-correspondence-dynamics-value4.pdf`. |
| Source confidence | `PRIMARY_FULLTEXT` on the 2001 preprint (10 pages, complete with proofs). The year/volume/issue/pages above are cross-checked against the published record (dblp, IDEAS/RePEc); the published version's internal theorem/lemma numbering is not cross-checked against the preprint's. |
| Mathematical status | `PROVED` at the **bounded** form. The literal unbounded statement is **refuted** in this repository — see below. |
| Repository status | `ADAPTED` |
| Lean status | `PARTIAL` — the refutation of the literal form is landed; the theorem itself is not formalized. |
| Objective priority | `P0` |
| Exact scope and quantifiers | One explicit three-player quitting game `G_ε`, for all sufficiently small `ε > 0`. Not a general theorem about quitting games. |
| Source alignment | Definitions match the repository's exactly; see the adapter below. |
| Lean destination | `GameTheory/Concepts/Stochastic/QuittingUnboundedInverseIterate.lean` |
| Acceptance and consumer | Restores the case-2 refutation in [`FiniteCyclesAreRefutedTheCarrierIsAMassPath`](../AbsorbingCycleCarrier/FiniteCyclesAreRefutedTheCarrierIsAMassPath.md); closes `PC-010`. |
| Discrepancies | One, precisely located. The proof needs a boundedness step it does not state. |

## Provenance

This is the source that a prior audit recorded as `NOT LOCATABLE` under the
attribution "Solan, inverse-iterate counterexample, Thm 2.1". The attribution
was **accurate**. Two things hid it: the paper's title names neither quitting
games nor absorption, and it is reference `[16]` in
Ashkenazi-Golan–Krasikov–Rainer–Solan under a year (2003) that does not match
the 2001 preprint every internal note was implicitly dated against. It is not
in the repository's local PDF corpus, and both the external sweep and the
follow-up local sweep missed it.

## The two theorems

**Theorem 2.1.** *For every `ε > 0` sufficiently small, `F_ε` contains only
trivial vectors.*

**Theorem 2.2.** *For every `ε > 0` sufficiently small,
`liminf_{δ→0} d(ε, δ) = +∞`*, where `d(ε, δ)` is the minimal period of a
periodic `δ`-equilibrium of `G_ε`.

Theorem 2.2 is the external attestation of the internal claim "no length bound
exists; the minimum period diverges as the defect tends to zero", which the
`AbsorbingCycleCarrier` ledger carried as an unsourced `M` seal.

Also used from the same paper, and independently useful: **Lemma 3.1**, four
properties of admissible sequences in the unperturbed FTV game `G_0`,
including (4) *`G_0` admits no stationary `ε`-equilibrium for small `ε`*; and
**Lemma 3.2**, that every tail of a completely absorbing admissible sequence
is again one, for small `ε`.

## Adapter

The definitions coincide with the repository's, with no reindexing.

| Source | Repository |
| --- | --- |
| `G_ε(y)`, the one-shot game with continuation payoff `y` | `F_y(z)` and the endpoint game it induces |
| `σ(k)` is an *equilibrium in* `G_ε(y(k+1))` *yielding payoff* `y(k)` | `IsεQuittingRootSuccessorCertificate reward 0`, i.e. `z k = F_{y k}(z (k+1))` with complementarity |
| *admissible sequence* `(y(k), σ(k))_{k∈ℕ}` | `IsQuittingInverseIterate` |
| *completely absorbing*: `∏_k ∏_i (1 - σ_i(k)) = 0` | `IsCompletelyAbsorbing`, i.e. `quittingSurvivalPrefix rows N → 0` |
| `F_ε` | set of `z 0` over inverse iterates |
| `y` *trivial* | no completely absorbing inverse iterate starts at `y` |

**The game.** Solan's Figure 1 is the
[`Question147`](../../questions/Question147-NoCompletelyAbsorbingComplementaryArray.md)
weight multiplied by `3`, entry for entry, with `η = ε`:

| quitter set | source entry | repository entry |
| --- | --- | --- |
| `{1}` | `(1, 3, 0)` | `(1/3, 1, 0)` |
| `{2}` | `(0, 1, 3)` | `(0, 1/3, 1)` |
| `{3}` | `(3, 0, 1)` | `(1, 0, 1/3)` |
| `{1,2}` | `(1+ε, 0, 1)` | `((1+η)/3, 0, 1/3)` |
| `{1,3}` | `(0, 1, 1+ε)` | `(0, 1/3, (1+η)/3)` |
| `{2,3}` | `(1, 1+ε, 0)` | `(1/3, (1+η)/3, 0)` |
| `{1,2,3}` | `(0, 0, 0)` | `(0, 0, 0)` |

At `ε = 0` this is the Flesch–Thuijsman–Vrieze (1997) cubic game, as the paper
itself says.

## The discrepancy, exactly

Theorem 2.1 carries **no boundedness hypothesis**, and in that literal form it
is false. `QuittingUnboundedInverseIterate.lean` machine-checks, for every
`η ≥ 0` and every `p ∈ (0,1)`, a completely absorbing admissible sequence with
rows `(p, 0, 0)` and values `(1/3, 1, K/(1-p)^t)`, `K = (1 + ηp)/3`. In
Solan's scaling its first vector is `y = (1, 3, 1 + εp)`.

The proof's load-bearing step is its display (1):

> Note that if `y ∈ F_ε` is not trivial, then `y` is in the convex hull of the
> payoffs in the entries of the matrix in the game `G_ε`. In particular,
> `Σ_i y_i ≤ 4` and `0 ≤ y_i ≤ 3`.

Everything after — Lemma 3.6, the limit set `F`, and both theorems — consumes
this. It is asserted on the strength of an earlier sentence, that a completely
absorbing admissible sequence makes `y(1)` *the equilibrium payoff of the
induced profile*. That implication requires the homogeneous boundary term
`(∏_{t<N} c(y_t)) · y(N)` to vanish, which needs the values bounded. The
witness above has `(∏_{t<N} c) · y(N)_3 = K` for **every** `N`
(`survivalPrefix_mul_value_two`), so the term is never consumed; correspondingly
`Σ_i y_i = 5 + εp > 4`, violating (1) directly. And the induced profile — only
player 1 ever quits — is indeed not an equilibrium of `G_ε`: player 3 receives
`0` and can profit by quitting.

**So boundedness is present in the proof as an unstated, unjustified step, not
as a hypothesis.** What the argument establishes is the bounded form, and the
bounded form is the one every downstream consumer needs, because repeating a
finite cycle produces values inside the convex hull by construction.

This is a gap in a step, not in the result. Nothing here suggests the intended
theorem is wrong, and no attempt has been made to check whether display (1)
can be re-derived under a weaker condition than boundedness.

## What it buys the program

The case-2 refutation is **restored**: if a finite absorbing complementary
cycle existed for this weight, its periodic extension would be a *bounded*
completely absorbing inverse iterate, which Theorem 2.1 excludes for small
`ε > 0`. So that weight admits no finite absorbing complementary cycle of any
length, and the finite-cycle carrier is refuted in case 2 on an attested basis.

The paper also records, in its own voice, that `G_ε` **does** admit a uniform
equilibrium payoff, by Solan, *Three-Player Absorbing Games*, MOR 24(3):
669–698 (1999) (recorded at
[`ThreePlayerAbsorbingGamesHaveUniformEquilibria`](ThreePlayerAbsorbingGamesHaveUniformEquilibria.md);
`PRIMARY_FULLTEXT` on Solan's own doctoral dissertation, MOR-typeset text
itself unread). Together
with Theorem 2.2 that is the whole picture the program had reconstructed
internally: the weight is solved, its solutions have diverging period, and it
has no exact discrete inverse iterate — so the carrier for it is a limit
object, not a finite one.

## Nonclaims

- Not a theorem about quitting games in general. It is one three-player game,
  for all sufficiently small `ε > 0`, with no stated `ε_0`.
- Not a nonexistence result for equilibria. The paper states the opposite for
  this game.
- Does not say that `E_0` has no periodic points for other games, nor that
  periodic points are useless — Solan–Vieille's `ε^{1/6}` construction from a
  periodic point is cited approvingly in the same paper.
- The bounded form is not formalized here, and the repository's
  `NoBoundedCompletelyAbsorbingInverseIterate` remains an unproved `Prop`.
