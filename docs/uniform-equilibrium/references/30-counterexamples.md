# Counterexamples and benchmarks

The published examples that constrain any proof. These are the walls: a
candidate construction that does not survive them is dead, and it is cheaper to
check against these than to discover the obstruction from the inside.

Markers: see [README](README.md).

---

## THE BIG MATCH — history-dependence is necessary, optimal strategies may not exist

`[primary]` Blackwell & Ferguson, *The Big Match*, Annals of Mathematical
Statistics **39**(1), 159–163 (1968),
DOI [`10.1214/aoms/1177698513`](https://doi.org/10.1214/aoms/1177698513).
Game due to Gillette (1957).

**Theorem 1, verbatim** (verifiers read the scanned PDF page by page):

> The value of the big match is `1/2`. An optimal strategy for player 2 is to
> toss a fair coin every day. Player 1 has no optimal strategy, but for any
> non-negative integer `N` he can get `V(N) = N/2(N+1)` by using strategy `N`,
> defined as follows: having observed player 2's first `n` choices
> `x₁,…,xₙ`, `n ≥ 0`, calculate the excess `kₙ` of 0's over 1's among
> `x₁,…,xₙ`, and predict 1 with probability `p(kₙ + N)`, where
> `p(m) = 1/(m+1)²`.

⚠ **BF's criterion is the infinite-horizon `lim sup` of the average** — the
*limiting-average* value, **not** the Mertens–Neyman uniform value, which
postdates the paper.

**Non-existence of an optimal strategy for player 1** is proved by an argument
the paper credits to **Lester Dubins**: against any `σ`, either `σ` never
predicts 1 against `ω* = (1,1,1,…)` and wins `0`, or `m` is the least initial
run of 1's after which it predicts 1 with probability `ε > 0`, and player 2
counters by playing `m` 1's, then a 0, then a fair coin, yielding player 1
expected income exactly `(1−ε)(1/2) < 1/2`.

**In Renault's uniform framing** `[secondary]` (Prop. 1.8): `vₙ = v_λ = 1/2`
for **all** `n` and `λ`; player 2 uniformly guarantees `1/2` by playing i.i.d.
`(½L, ½R)`; **no stationary or Markov strategy of player 1 uniformly guarantees
any positive number**; and `σ_M` (play `T` at stage `t` with probability
`1/(m_t + M + 1)²`, `m_t = R_t − L_t`) uniformly guarantees `M/(2(M+1))`, with
`E(1/T · Σ_{t≤T} g_t) ≥ M/(2(M+1)) − M/(2T)` for all `T ≥ 1` and all `τ`.

A verifier independently re-derived `vₙ = v_λ = 1/2` from the Shapley recursion
(stage matrix `[[n,0],[V_{n−1}, 1+V_{n−1}]]`, equalizing `p = 1/(n+1)` gives
value `n/2`; the discounted matrix equalizes at `p = L/(1+L)` giving `1/2` for
every discount factor). So Renault's "for all `n` and `λ`" is not a sloppy
upgrade of "lim".

⚠ **CORRECTION — propagate this.** The sub-claim that **counter-based** history
dependence is *necessary* is **FALSE**. History-dependence is necessary; the
excess counter is one sufficient witness. Hansen, Ibsen-Jensen & Neyman, *The
Big Match with a Clock and a Bit of Memory*, Math. of OR **48**(1), 419–432
(2023), DOI [`10.1287/moor.2022.1267`](https://doi.org/10.1287/moor.2022.1267),
show a clock plus **two memory states** suffice for ε-optimality. Kohlberg
(1974) uses a different counter formula (absorb w.p. `ε²` if `kₙ < 0`,
`ε²(1−ε)^{kₙ}` otherwise).

**Repo status.** `L`, and this is the repository's deepest worked instance.
`BigMatchUniform.lean:1913` proves `exists_uniformEquilibriumPayoff_live`
(sorry-free, axiom-audited), with the BF potential `φ(D) = (D−1)/(2D)` and its
submartingale step formalized. `BigMatchNoMarkov.lean` independently
reproduces, in checked form, the Markov-insufficiency content that Thuijsman's
*The Big Match and the Paris Match*
(DOI [`10.1007/978-94-010-0189-2_12`](https://doi.org/10.1007/978-94-010-0189-2_12))
records as Lemmas 1–2 (stationary `max min = 0 < 1/2 = min max`; Markov
`sup inf = 0`). `BigMatchDeficitIndexNoGo.lean` and `BigMatchFinkEndpoint.lean`
are the permanent falsifiers built on it.

**The Hansen–Ibsen-Jensen–Neyman result is already cited in the manuscript** —
and it is the sharper statement of what `BigMatchNoMarkov` is really saying.
Worth making sure the two are cross-referenced in the Lean docstring.

---

## FLESCH–THUIJSMAN–VRIEZE 1997 — stationarity fails at n = 3

The single most important benchmark for the multiplayer program, and the one
this repository is closest to consuming.

`[primary]` J. Flesch, F. Thuijsman and O.J. Vrieze, *Cyclic Markov equilibria
in stochastic games*, International Journal of Game Theory **26**(3), 303–314
(1997), DOI [`10.1007/BF01263273`](https://doi.org/10.1007/BF01263273). Full
published PDF read from the authors' institutional repository.

**Abstract, p.303, verbatim:**

> We examine a three-person stochastic game where the only existing equilibria
> consist of cyclic Markov strategies. Unlike in two-person games of a similar
> type, stationary ε-equilibria (ε > 0) do not exist for this game. Besides we
> characterize the set of feasible equilibrium rewards.

**Introduction, p.304:** "For two-person recursive repeated games with
absorbing states Flesch et al. [1995] showed the existence of stationary
ε-equilibria. In the game presented below, no stationary ε-equilibria exist, so
the two-person result does not extend to the `n`-person case."

### The exact game (p.305)

Three players, two actions each: player 1 `T`/`B`, player 2 `L`/`R`, player 3
`N`/`F`. All cells absorb (`*`) except `(T,L,N)`.

```text
layer N (player 3 plays N)          layer F (player 3 plays F)
             L          R                        L          R
   T    (0,0,0)    (0,1,3)*             T   (3,0,1)*   (1,1,0)*
   B    (1,3,0)*   (1,0,1)*             B   (0,1,1)*   (0,0,0)*
```

Cyclic symmetry: `r₁(i₁,i₂,i₃) = r₂(i₃,i₁,i₂) = r₃(i₂,i₃,i₁)`.

### The results

| # | Statement |
|---|---|
| Lemma 3.1 | There is no stationary equilibrium in `Γ` |
| Theorem 3.2 | There is no stationary ε-equilibrium in `Γ` |
| Theorem 3.3 | The cyclic Markov equilibrium `κ = (½,0,0,½,0,0,…)`, `λ = (0,½,0,0,½,0,…)`, `μ = (0,0,½,0,0,½,…)` has limiting-average reward `(1,2,1)` |
| Theorem 3.4 | Every equilibrium has exactly **one** player randomizing per stage, cyclically in the order 1, 2, 3 |

⚠ **MANDATORY CORRECTION.** The abstract's "(ε > 0)" is **loose**. The
Theorem 3.2 proof is a limiting argument ("We take a discrete sequence of ε's
converging to 0…", p.306; "so `(xᵉ,yᵉ,zᵉ)` would not be an ε-equilibrium for
small ε", p.308). Payoffs lie in `[0,3]`, so every stationary profile is
trivially a 3-equilibrium and the literal universal reading is **false**.
Correct wording: **no stationary ε-equilibrium for all sufficiently small
ε > 0**. A sibling claim asserting the universal version was **refuted 1–2**.

⚠ **Second scope caveat.** "two-person games of a similar type" means two-person
**recursive** absorbing games. General two-person absorbing games do *not*
generally admit stationary ε-equilibria — FTV 1996
(DOI [`10.1287/moor.21.4.1016`](https://doi.org/10.1287/moor.21.4.1016)) says
so itself.

⚠ **Third caveat.** Do **not** read the example as "cyclic Markov suffices at
`n = 3`". Solan (1999) obtains uniform ε-equilibria for all three-player
absorbing games by a different and much more general route.

### Cross-check against this repository — the transcription is CORRECT

`docs/uniform-equilibrium/case-studies/FTVArchitectureAnalysis.md` encodes FTV in the repo's quitting-game
format (quit actions `B`/`R`/`F`). Mapping each cell to its quit-set:

| Cell | Quitters | Repo `r_S` | Published payoff | ✓ |
|---|---|---|---|---|
| `(B,L,N)` | {1} | `(1,3,0)` | `(1,3,0)*` | ✓ |
| `(T,R,N)` | {2} | `(0,1,3)` | `(0,1,3)*` | ✓ |
| `(T,L,F)` | {3} | `(3,0,1)` | `(3,0,1)*` | ✓ |
| `(B,R,N)` | {1,2} | `(1,0,1)` | `(1,0,1)*` | ✓ |
| `(B,L,F)` | {1,3} | `(0,1,1)` | `(0,1,1)*` | ✓ |
| `(T,R,F)` | {2,3} | `(1,1,0)` | `(1,1,0)*` | ✓ |
| `(B,R,F)` | {1,2,3} | `(0,0,0)` | `(0,0,0)*` | ✓ |
| `(T,L,N)` | ∅ | live, pays 0 | `(0,0,0)` non-absorbing | ✓ |

**All eight cells match the published table.** The analysis file's target
`v = (1,2,1)` matches Theorem 3.3's limiting-average reward exactly, and its
"phase `k`: only player `k` randomizes (half/half)" matches Theorem 3.4's
one-randomizer-per-stage cyclic structure and Theorem 3.3's `½` mixing.

This is a genuine external validation of the repo's transcription, and it
upgrades operative-queue item 6 ("transcribe the FTV cyclic game from the
published paper") from *to do* to *done and verified at the mathematical
level*. What remains is the Lean actual-data adapter.

**Repo status.** `L~`. The concrete FTV architecture and credibility checks,
the exact finite-horizon delivery constants `16/7`, `22/7`, `18/7` and common
modulus `22/(7T)`, the all-start semantic credibility bridge, and the exact
cyclic packet adapter are formalized in `FTVCyclicCredibility.lean`,
`FTVCyclicFiniteHorizon.lean`, `FTVCyclicSemanticBridge.lean`, and
`FTVCyclicMinimality.lean`. The remaining source-aligned target is the
published stationary-impossibility/approximate-boundary theorem; do not
describe the game or finite-horizon delivery as absent.

---

## SOLAN–VIEILLE 2002 — the consolation prizes collapse at n = 4

`[primary]` Solan--Vieille, *Quitting Games--An Example*, International
Journal of Game Theory **31**(3), 365--381 (2002), DOI
`10.1007/s001820200125`, exhibits an explicit **four-player quitting game**
(Figure 2) with:

- no stationary equilibrium (§3.2),
- no stationary ε-equilibrium,
- no perturbed ε-equilibrium (§3.3),
- no equilibrium payoff in the convex hull of the unilateral-quit payoffs
  `{(4,1,0,0), (1,4,0,0), (0,0,1,4), (0,0,4,1)}`.

The paper's own framing, pp.18–19:

> For two-player games, stationary ε-equilibria exist. For 3-player games,
> either a stationary ε-equilibrium exists, or there exists an ε-equilibrium in
> which the probability of termination in any given stage is arbitrarily small
> …, or both. The purpose of this section is to show on an example that this is
> no longer true for 4-player games. In that sense, our result is optimal.

This is the structural reason the `n ≥ 4` problem is hard: not merely that the
`n ≤ 3` *proofs* fail, but that the weaker *conclusions* they fall back on are
themselves false at `n = 4`.

⚠ **NUMERICAL DEFECT — attribute, do not assert.** The specific period-2
profile and payoffs printed in the paper (continue with probability `1/√2`;
`γ = (√2,1,√2,1)` and `(1,√2,1,√2)`) **do not check out numerically**. A
verifier transcribed Figure 2 cell by cell, validated the reading against three
formulas printed elsewhere in the paper (all reproduce exactly), and then found
the described profile yields `γ = (1, 1.414214, 0.942809, 1.299832)`, not
`(√2,1,√2,1)`; that it is not an equilibrium (player 3's quit payoff `1.000000`
vs continuation `0.919120`); and that structurally any player mixing at stage 1
must receive exactly his quit payoff `1`, so `γ¹ = √2` is impossible while
player 1 mixes. Numerically solving for `(12)(34)`-symmetric period-2
equilibria gives continuation probabilities `≈ 0.746097` and `≈ 0.734525` with
payoffs `≈ (1, 1.361424, 1, 1.340307)` and its swap.

**A period-2 cyclic equilibrium appears to exist, so the qualitative claim may
stand**, but the printed constants and the exact corrected certificate remain
under source-specific audit. The final 2002 paper is author-hosted, so the old
claim that only the 1998 discussion paper was readable is obsolete. Do not put
the disputed constants into Lean; see [`40-open-status.md`](40-open-status.md).

**Repo status.** `P1, not formalized`. This is the sharpest available fence on
stationary, perturbed, near-all-Continue/small-termination, and
solo-payoff-convex-hull fallback languages at `n = 4`. Formalize only the
source-stable qualitative propositions until the Figure-2 numerical packet is
reconciled.

---

## SORIN 1986 — a discounted endpoint that is not a uniform equilibrium payoff

**The program's central diagnosis, and now verified against the primary text.**
Two verifiers independently retrieved the author-hosted PDF (via a Wayback
snapshot — the live site refused connections) and read it cover to cover.

`[primary]` S. Sorin, *Asymptotic properties of a non-zero sum stochastic
game*, International Journal of Game Theory **15**(2), 101–107 (June 1986),
DOI [`10.1007/BF01770978`](https://doi.org/10.1007/BF01770978). Received June
1984, revised February 1985.

### The game (p.102)

One non-absorbing state, `2 × 2`, `*` marks absorbing cells:

```text
              L              R
   Top     (1,0)*         (0,2)*
   Bottom  (0,1)          (1,0)
```

Player 1's **Top row absorbs in both columns**; both Bottom cells are
non-absorbing and play stays put. Feasible set `C = Co{(1,0), (0,1), (0,2)}`.

The zero-sum reduction `[[1*, 0*], [0, 1]]` **is the Big Match**, giving
`v₁ = 1/2`; `v₂ = 2/3`. Threat point `V = (v₁, v₂) = (1/2, 2/3)` (p.103).

### Theorem 1 (p.103), verbatim

> `E(n) = E(λ) = {V}`, for all `n ≥ 1`, for all `λ ∈ (0,1]`.

The equilibrium payoff set of the `n`-stage game **and** of the `λ`-discounted
game is the *same singleton* `{(1/2, 2/3)}` for every horizon and every
discount factor. So both limits exist and both equal `V`. Only the strategies
move: in `G(λ)`, `s = λ/(λ+2)` and `t = 1/2` (stationary); in `G(n)`,
`s = 1/(2n+1)` and `t = 1/2` at stage one (p.105).

### Theorem 2 (p.103)

> `E(∞) = F`, where `F = {(a, 2(1−a)) : 1/2 ≤ a ≤ 2/3}`

is "the set of feasible individually rational and Pareto optimal payoffs".
Geometrically: the Pareto frontier of `C` (the segment `[(1,0),(0,2)]`)
intersected with the individually-rational region `{w₁ ≥ 1/2, w₂ ≥ 2/3}`.

⚠ **Cite the equation WITH its bounds.** `F` *is* algebraically
`2w₁ + w₂ = 2`, but only for `1/2 ≤ w₁ ≤ 2/3`. The bare equation **overstates**
the set — it would admit the non-individually-rational endpoints `(1,0)` and
`(0,2)`. Sorin never prints the equation; he prints the parametrization and
refers to "the line `[(1,0),(0,2)]`".

### The separation (p.107), verbatim

> The main feature of this example is the fact that `E(n)` and `E(λ)` are
> constant and disjoint from `E(∞)`. This implies that the difference between
> the infinite game and the two approximations cannot be reduced by taking a
> stronger concept of Equilibrium.

And: "the NEP in `G(∞)` are precisely the 'good' outcomes while `E(n)` and
`E(λ)` are reduced to the threat point." Numerically `2(1/2) + 2/3 = 5/3 ≠ 2`,
so `V ∉ E(∞)`.

⚠ **`E(∞)` is genuinely the UNIFORM equilibrium payoff set** — this was the
strongest refutation candidate both verifiers tried, and both killed it by
reading display (1) on p.102, which quantifies over **all `n ≥ N`**: the
standard uniform ε-equilibrium condition. A Banach limit appears in the paper
only in the definition of the feasible set `C(∞)`, never in the equilibrium
definition. So this is a **vanishing-discount-limit vs uniform** separation,
*not* a uniform vs limiting-average one. Sorin does not treat a Cesàro concept
at all.

⚠ **Convention.** Sorin uses `λ ∈ (0,1]` with
`X_λ = λ Σ (1−λ)^{m−1} x_m`, so the patient limit is `λ → 0`, not `δ → 1`.

### Cross-check against this repository — the transcription is CORRECT

`SorinAbsorbingGame.lean` states the game as

```text
              Left           Right
Top        (0, 2)*        (1, 0)*
Bottom     (1, 0)         (0, 1)
```

which is the paper's table with **player 2's two columns relabelled** — a
harmless renaming of that player's actions. Cell by cell, swapping the paper's
columns gives exactly the repo's table. Everything else matches:

| Item | Paper | Repo |
|---|---|---|
| Mixing probability | `s = λ/(λ+2)` | `topProb`, `λ/(2+λ)` with `λ := 1 − β` |
| Player 2's mixing | `t = 1/2` | `Pr₂(Left) = 1/2` |
| Discounted payoff | `V = (1/2, 2/3)`, constant in `λ` | `discountedPayoff_live`, `(1/2, 2/3)` for every `β` |
| Uniform payoff set | `2w₁ + w₂ = 2` | docstring states `2w₁ + w₂ = 2` |
| Separation | `5/3 ≠ 2` | docstring states `5/3 ≠ 2` |

**Repo status: `L~` as of 2026-08-02.** `SorinUniformSeparation.lean`
(untracked in the worktree, not yet in `GameTheory.lean`) machine-checks the
accounting identity `2·avg₁ + avg₂ = 2 − bottomRightOccupation`, the limit
passage to `2w₁ + w₂ = 2`, and the endpoint exclusion — all conditional on one
named hypothesis, `UniformEquilibriaForceBottomRightOccupationVanishing`.
Confirmed by this audit: it builds successfully and is free of `sorry`,
`admit`, and `native_decide`.

**One precision point.** That module proves `E(∞) ⊆ {2w₁ + w₂ = 2}` — the
necessary direction, which is exactly what the separation needs. Sorin's
Theorem 2 is stronger: a set *equality*
`E(∞) = {(a, 2(1−a)) : 1/2 ≤ a ≤ 2/3}`. The converse inclusion is unformalized,
and it is there that the bounds matter — the bare line admits `(1,0)` and
`(0,2)`, which are not individually rational and are not in `E(∞)`.

**Also worth recording:** the repo's docstring says the discounted equilibrium
is "constant in the discount". The paper says something stronger and more
useful — the *entire equilibrium payoff set* is the singleton `{V}`, for every
`n` **and** every `λ`. The finite-horizon half (`E(n) = {V}`, `s = 1/(2n+1)`)
is not mentioned in the repo at all and is independently interesting: it means
no finite-horizon approximation scheme can reach `E(∞)` either.

### Other separating examples — mostly not the same separation

`[primary]` Renault & Ziliotto give two examples (arXiv:1407.3028, published
GEB 2020, DOI `10.1016/j.geb.2020.08.001`; and *Limit Equilibrium Payoffs in
Stochastic Games*, MOR **45**(3), 889–895, DOI `10.1287/moor.2019.1015`). ⚠
**Neither reproduces Sorin's separation.** In the 7-state example `E_δ` and
`E'_δ` fail to converge at all while `E_∞ = {(1/2,0)}` is a singleton that
*coincides* with `E_δ` off `Δ₁`; the genuine separation there is that
`(1/2,1/2) ∈ E_δ` for `δ ∈ Δ₁` arbitrarily close to 1 yet is not a uniform
equilibrium payoff. In the 3-column example the limits of converging selections
of `E'_δ` **are exactly** the elements of `E_∞`; the separation is
stationary-limit vs uniform.

**Sorin 1986 remains the only verified instance of `lim E_δ` and `E_∞` both
being non-empty and disjoint.**

⚠ **Do not propagate Renault–Ziliotto's citation of Sorin.** Their
bibliography entry reads "International Journal of Game Theory, 98:296–303,
1984" — wrong year, impossible volume (IJGT was at vol. 13 in 1984), wrong
pages. The in-text citation consistently says "Sorin (1984)", so it is a
genuine bibliographic error. Their *other* Sorin 1986 reference (*On repeated
games with complete information*, MOR 11, 147–160) is correct and is a
different paper.

⚠ Renault–Ziliotto example/lemma **numbering differs** between the arXiv
preprint and the author's final MOR manuscript (HAL hal-04041893), and the
published INFORMS typesetting could not be opened. Cite by content, not by
number.

---

## Zero-sum boundary examples

See [`10-zero-sum-value.md`](10-zero-sum-value.md) for Ziliotto's 7-state
symmetric-information counterexample (Annals of Probability 2016) and Vigeral's
4-state compact-action counterexample (DGA 2013). Both sit strictly outside our
hypotheses (we assume perfect state observation and finite actions), which is
precisely their use: they mark where generalization stops being possible.
