# `Q̄`-matrix quitting games have continuous equilibria

| Field | Value |
| --- | --- |
| Citation of record | G. Ashkenazi-Golan, I. Krasikov, C. Rainer, E. Solan, *Absorption paths and equilibria in quitting games*, Math. Program. **203**, 735–762 (2024), DOI [`10.1007/s10107-022-01807-6`](https://doi.org/10.1007/s10107-022-01807-6). Local copy `ephemeral/s10107-022-01807-6.pdf`; arXiv:2012.04369. |
| Source confidence | `PRIMARY_FULLTEXT`, published version, sign matrices read from rendered page images. |
| Mathematical status | `PROVED`, with one exposition gap (Theorem 4.15's hypothesis) patched below and four printed defects fenced. |
| Repository status | `RECORDED` |
| Lean status | `NONE` |
| Objective priority | `P1` for the theorem; `P0` for the two examples it carries. |
| Exact scope and quantifiers | `R(Γ)` a `Q̄`-matrix ⟹ Γ admits a continuous equilibrium. Nontrivial only for `|I| ≥ 4`; see the scope warning. |
| Source alignment | Adapter below is exact. The repository's canonical hard weight *is* this paper's `Γ_η`. |
| Lean destination | none selected |
| Acceptance and consumer | External attestation of the period-`3m` family and its continuous limit in [`FiniteCyclesAreRefutedTheCarrierIsAMassPath`](../AbsorbingCycleCarrier/FiniteCyclesAreRefutedTheCarrierIsAMassPath.md). |
| Discrepancies | Four printed defects, listed and fenced. |

## The results

**Definition 5.1.** `LCP(R,q)`: find `w ∈ ℝⁿ₊` and `z ∈ Δ({0,…,n})` with
`w = z₀ q + Σᵢ zᵢ Rⁱ` (`Rⁱ` the `i`-th **column**) and `zᵢ = 0 or wᵢ = 0` for
every `i`. `R` is a `Q`-matrix when `LCP(R,q)` is solvable for every `q`.
`z₀ = 0` is permitted, so this is **weaker** than the textbook `Q`-matrix.

**Definition 5.2.** `R` is a `Q̄`-matrix when `R` and all its principal minors
are `Q`-matrices.

**Theorem 5.4.** *If `R(Γ)` is a `Q̄`-matrix, then Γ admits a continuous
equilibrium.* Here `R(Γ) = (rⁱ(Q^j, C^{-j}))_{i,j∈I}` — **row `i` = payoff
receiver, column `j` = the sole quitter** — under the section's standing
normalization `rⁱ(Qⁱ, C^{-i}) = 0`.

**Theorem 3.4** (Simon 2007, Thm 3 + Solan–Vieille 2001, Prop. 2.13). *A
quitting game admits an `ε`-equilibrium for every `ε > 0` **iff** at least one
of:* (S.1) stationary `ε`-equilibria for all small `ε`; (S.2) `ε`-equilibria in
which one player quits with probability 1 at the first stage and is thereafter
punished to within `ε` of her min-max level; (S.3) an absorbing profile at
which every player is sequentially `ε`-perfect, for all small `ε`. This is an
*iff*, and it is the closest published statement to the internal trichotomy.

**Theorem 3.5** (Solan–Vieille 2001, Props. 2.4 and 2.13). *For small `ε > 0`,
every absorbing profile at which all players are sequentially `ε`-perfect is an
`ε^{1/6}`-equilibrium.* The exponent is `1/6` on `ε`, not a factor.

> ⚠ **Do not import Theorem 3.5 as printed.** This repository already holds a
> record — [`SourceCorrections-QuittingAbsorptionPaths.md`](../../docs/uniform-equilibrium/references/SourceCorrections-QuittingAbsorptionPaths.md),
> §3 — asserting that the source propositions it rests on
> (Solan–Vieille 2001, Prop. 2.4, restated as 2.6) prove a **disjunction**:
> the absorbing sequentially-perfect profile is globally approximately optimal
> **or** a stationary approximate equilibrium exists. Theorem 3.5 states the
> first disjunct alone, and that record supplies a machine-checked two-player
> regression against it: `r(Q₁,C₂) = (−1,0)`, `r(C₁,Q₂) = (0,0)`,
> `r(Q₁,Q₂) = (−1,0)`, non-absorption payoff `0`, player 1 quitting at a fixed
> rate `h ∈ (0,1)` while player 2 always continues. That profile absorbs almost
> surely and is exactly sequentially perfect, yet player 1 gains `1` by always
> continuing — the missing stationary alternative being the all-continue
> profile.
>
> **Two records in this repository therefore disagree about one published
> theorem, and the reconciliation is owed.** The loose joint is most likely the
> mapping from the regression's profile to AGKRS's exact Definition 4.13
> (`SP.1`/`SP.2`) rather than an error in a refereed theorem, and the same
> file's §1 independently records a defect in that very definition's endpoint
> convention. Until someone checks the regression against Definition 4.13
> verbatim, use the **2001 disjunction**, not the 2024 restatement. Nothing
> else in this file depends on Theorem 3.5.

**Theorem 4.15.** For a game with neither a sure-first-stage-termination
`ε`-equilibrium nor an all-continue one, `ε`-equilibria for every `ε > 0` exist
**iff** a `0`-AP exists.

## Adapter, and the scope warning

The repository model fixes the never-terminate payoff at `0`; this paper leaves
`r(C)` free and uses it (its own `Γ_η` has `r(C) = (−1,−1,−1)`). Adding a
constant `cᵢ` to **every** payoff of player `i`, `r(C)` included, shifts
`γⁱ(x) = E_x[1_{θ<∞} rⁱ(a_θ) + 1_{θ=∞} rⁱ(C)]` by exactly `cᵢ` for every
profile, so it preserves `ε`-equilibria, best responses and min-max levels
exactly, in both directions. It also preserves sequential `0`-perfectness,
because the AP payoff path renormalizes over absorbed mass and the total mass
is `1`. So the transported condition is: **`Mᵢⱼ := rᵢ({j}) − rᵢ({i})` is a
`Q̄`-matrix ⟹ `ε`-equilibria for every `ε > 0`.**

The normalization is **not cosmetic** — the proof of Theorem 5.4 uses the zero
diagonal substantively (its Eqs. 13–14, the viability set `Y = ∂ℝ^I₊`, and the
`γᵢ_t(π) = 0` conclusion). A raw solo-payoff matrix must not be fed to it.

**Two gaps in the chain from Theorem 5.4 to `ε`-equilibria.** A continuous
equilibrium is a `0`-AP, and Theorem 4.15's *converse* direction is the one
used, so no implication runs backwards. But Theorem 4.15 is *stated* under a
hypothesis its converse proof does not use. Patch: if that hypothesis fails,
the game has an `ε`-equilibrium of one of the two excluded shapes for
arbitrarily small `ε`, and an `ε`-equilibrium is an `ε'`-equilibrium for every
`ε' ≥ ε`, so the conclusion holds on that branch too. The case split is not in
the paper.

> **Scope warning.** For `|I| ≤ 3` this theorem buys **nothing**:
> three-player quitting games have `ε`-equilibria for every `ε > 0`
> unconditionally (Solan, *Three-Player Absorbing Games*, MOR 24(3):669–698
> (1999), recorded at
> [`ThreePlayerAbsorbingGamesHaveUniformEquilibria`](ThreePlayerAbsorbingGamesHaveUniformEquilibria.md);
> `PRIMARY_FULLTEXT` on Solan's own doctoral dissertation),
> as the paper itself says on p. 738. Theorem
> 5.4's content is at `|I| ≥ 4`, which is why its non-trivial examples (5.7,
> 5.8) are five-player. Do not cite it as the reason a three-player weight is
> solved.

## What it does buy: the canonical hard weight is this paper's `Γ_η`

The weight carried internally as the "case-2 weight" — the one in
[`Question147`](../../questions/Question147-NoCompletelyAbsorbingComplementaryArray.md)
— **is this paper's `Γ_η` of Figure 1, p. 741**, under the affine map
`t ↦ (t+1)/3` applied to every payoff of every player, all eight rows including
`r(C)`. It is equally Solan's `G_ε` of
[`PerturbedFTVGameHasNoBoundedCompletelyAbsorbingInverseIterate`](PerturbedFTVGameHasNoBoundedCompletelyAbsorbingInverseIterate.md)
divided by `3`. All three are one game up to positive affine transformation.

Two consequences, both of which turn internally-sealed claims into published
ones.

- **The period-`3m` family is printed on p. 741**, verbatim: *"at stages
  `1,…,m` (resp. `m+1,…,2m`, resp. `2m+1,…,3m`) Player 1 (resp. 2, 3) quits
  with probability `ρ`, where `(1−ρ)^m = ½`, while the other two players
  continue"* is an `ε`-equilibrium of `Γ_η` for `m` sufficiently large. That is
  the internal replacement carrier — three coordinates acting in successive
  blocks of combined survival `½` — with the same block survival constant.
- **Its continuous limit is Example 5.6, p. 758.** The paper prints
  `R(Γ) = ((0,−1,2),(2,0,−1),(−1,2,0))`, states that it is a `Q̄`-matrix, and
  exhibits the continuous equilibrium `(1,½),(2,½),(3,½),(1,½),…`. That matrix
  is exactly `3M` for the internal weight, and `M` is **independent of `η`**,
  because `η` perturbs only the pair rows while `M` is built from the singleton
  rows alone. So the continuous object survives the perturbation that destroys
  every finite cycle — which is the whole content of the internal "mass path"
  reframing, now attested.

Verified independently of Remark 5.3: `M` has the cyclic sign pattern, zero
diagonal, `det M = 7/27 > 0`; every proper principal submatrix has a
non-negative column with zero diagonal entry; the full `3×3` has **no**
convex-combination solution at all, so it qualifies only as a standard
`Q`-matrix — checked by exact-rational enumeration over all eight complementary
supports. `M` is **not** strictly semi-monotone, so Definition 5.1's weakening
of `Q` is load-bearing here.

## Printed defects — fenced, do not quote as-is

| Location | Defect |
| --- | --- |
| Remark 5.3, first `3×3` bullet, entry `(3,3)` | prints `?`. Definition 5.2 forces every diagonal entry `≥ 0` via the `1×1` case, so the printed pattern admits non-`Q̄` matrices (take `R₃₃ = −1`). Must read `≥`. |
| Remark 5.3, `2×2` case | "non-negative **row** whose diagonal entry is `0`" should be **column**; Definition 5.1 combines columns. `[[0,−1],[5,3]]` is a counterexample. Harmless for zero-diagonal `2×2`, where rows and columns give the same condition. |
| Definition 5.1, `Q`-matrix sentence | "for every `q ∈ ℝ`" should be `ℝⁿ`. |
| p. 756, item 3, clause (b) | omits `Rz ≥ 0`, which Definition 5.1 requires via `w ∈ ℝⁿ₊`. As printed it is too permissive. |

## Nonclaims

- Theorem 5.4 is **not** a characterization; Remark 5.5 says so, and the
  authors record that they do not know whether a continuous equilibrium with
  all players quitting forces `Q̄`.
- It does **not** solve quitting games. The residual class is `R(Γ)` a
  `Q`-matrix but not `Q̄` — some principal minor failing `Q` — with
  Solan–Solan covering the non-`Q` side under its own audited hypotheses.
- Nothing here bears on the inverse-iterate question. Values in this paper are
  payoff paths of actual APs and are bounded by `‖r‖_∞` as an axiom
  (Remark 4.12(1)); the unbounded arrays of `Question147` have no counterpart
  in this model. `ε`-equilibrium existence and the existence of a completely
  absorbing unbounded inverse iterate coexist without tension.
- The terminal-jump convention defect recorded in
  [`20-nonzero-sum-equilibrium.md`](../../docs/uniform-equilibrium/references/20-nonzero-sum-equilibrium.md)
  is untouched by this file and still gates literal use of the path/nonexistence
  equivalence.
