# The subgame gluing step is only a remark

## Lifecycle

| Field | Value |
| --- | --- |
| Lifecycle | `ACTIVE` |
| Verdict | `OPEN` |
| Objective priority | `P0` |
| Last audited | 2026-08-04 |
| Central live claim | A solution of a subgame, along which every excluded player earns at least the continue payoff, is a solution of the whole game. Stated in the literature as a remark, with no proof. |
| Next discriminant | Prove it, or exhibit a four-player weight where an excluded player has non-negative payoff along a subgame solution and still profits by deviating. |
| Production destination | `none yet` |
| Supersedes / superseded by | `none` |

## The statement

Fix a finite quitting game `Γ` on players `I`, normalized so that
`r_i({i}) = 0` for every `i` (see the group
[`README`](README.md) for why that normalization is free). Let `J ⊆ I` be
nonempty and let `Γ_J` be the subgame in which players outside `J` always
continue.

> **G.** If `π` is a sequentially `0`-perfect object for `Γ_J`, and every
> `i ∉ J` receives a non-negative payoff along `π` at every time, then `π` —
> extended by zero quit rates outside `J` — is sequentially `0`-perfect for
> `Γ`.

The intuition is one line: a player outside `J` compares her payoff along `π`
against what she gets by quitting, which after normalization is `0`; if her
payoff is at least `0` she has no incentive to quit, and she has nothing else
to do.

## Why it is not free

The one-line intuition is the *stationary* intuition, and the objects here are
not stationary. Three specific ways it can fail, none of which the remark
addresses.

1. **Timing.** A player outside `J` may have non-negative payoff *from time
   zero* and still gain by quitting *at a particular later time*, when the
   conditional continuation from that point is negative. Sequential perfection
   is a condition at every time `t`, not only at `t = 0`, so the hypothesis has
   to be the pointwise one — and the remark's phrasing ("obtain non-negative
   payoffs along this AP") is ambiguous between the two.
2. **The insiders' problem changes.** If an outsider quits with positive
   probability, the terminal rows the players in `J` face are no longer the
   `J`-rows but the multi-quitter rows involving that outsider. Perfection of
   `π` for `Γ_J` says nothing about those. This is harmless only if the
   outsider's rate stays exactly zero — which is what the conclusion asserts,
   so the argument must not assume it.
3. **What "solution of the subgame" means.** `Γ_J`'s solution may be
   stationary (via the non-`Q` route) or continuous (via the `Q̄` route), and
   these are different objects with different perfection conditions. A gluing
   lemma has to be stated for whichever class the induction actually produces,
   and the two routes produce different ones.

## Provenance

Ashkenazi-Golan–Krasikov–Rainer–Solan, *Absorption paths and equilibria in
quitting games*, Math. Program. **203**, 735–762 (2024), Remark 5.5(1), in the
course of explaining that Theorem 5.4 is not tight:

> Indeed, it may be that the restriction of `R(Γ)` to a subset `J` of players
> satisfies the condition of Theorem 5.4, and therefore there is a continuous
> equilibrium `π` for the subgame that involves those players (when players not
> in `J` are restricted to always continue), and it may further happen that the
> players not in `J` obtain non-negative payoffs along this AP. In such a case,
> all players are sequentially `0`-perfect at `π`.

That is the whole of it. It is a remark, unnumbered as a result, with no proof,
used only to argue that the `Q̄` condition is sufficient and not necessary.

## Why it is worth building

It is the induction step. The residual open class of the finite-quitting
problem is exactly the weights whose normalized solo matrix is a `Q`-matrix but
not a `Q̄`-matrix — which says precisely that **some proper principal
submatrix fails `Q`**, and therefore that some proper subgame is solved by the
non-`Q` route. `G` is what turns that into a solution of the whole game. With
`G`, the conjecture reduces to a single corner:

> `M` is a `Q`-matrix; and for every proper `J` with `M_J` not a `Q`-matrix,
> every solution of `Γ_J` leaves some player outside `J` strictly negative.

Without `G` there is no reduction at all, and the residual class is a
description rather than a route.

The base of the induction is external and solid: `n ≤ 3` is settled by Solan,
*Three-player absorbing games*, Math. Oper. Res. **24**(3), 669–698 (1999),
recorded at
[`ThreePlayerAbsorbingGamesHaveUniformEquilibria`](../UniformEquilibriumLiterature/ThreePlayerAbsorbingGamesHaveUniformEquilibria.md)
— `PRIMARY_FULLTEXT` on Solan's own doctoral dissertation (MOR-typeset PDF
itself still unread, but the dissertation carries a full formal proof of the
uniform reading, not just a gloss), so the base of this induction inherits
only that residual exposure.

## Falsifiers and wrong turns

- The cheapest refutation is a four-player weight, an explicit `J` of size two
  or three, an explicit subgame solution, and an outsider with non-negative
  payoff who nonetheless profits. Search for that before attempting a proof.
- Do not prove `G` for stationary objects and then use it for continuous ones,
  or the reverse. State which class it is about.
- Do not read "non-negative payoff along `π`" as a condition at time zero only.
  If the pointwise version is what is needed, say so, and check whether the
  non-`Q` route actually delivers it.
- `G` says nothing about weights where **no** proper submatrix fails `Q` —
  that is the `Q̄` case, already covered — nor about the corner above.

## Exit conditions

`MINED` when `G` is proved or refuted, in a stated class, with the induction
step written out and the corner named.
