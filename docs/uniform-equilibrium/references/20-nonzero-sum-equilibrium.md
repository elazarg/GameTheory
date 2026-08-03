# Non-zero-sum: uniform equilibrium existence

This is the literature the conjecture in `Uniform.lean` actually lives in.

**The one-sentence shape.** The frontier is a two-axis lattice. Along the
**player** axis: `n = 2` is fully settled, `n = 3` is settled for absorbing
games only, `n ≥ 4` is open even for quitting games. Along the
**solution-concept** axis, weakening Nash to *correlated* closes the problem at
every `n`.

Markers: see [README](README.md). Evidence from the 2026-08-02 research passes.

---

## Terminology hazard — three notions, routinely conflated

`[primary]` Keep these apart. The literature does not always.

| Notion | Definition |
|---|---|
| **Limiting-average** ε-equilibrium | Cesàro `liminf` of the stage payoffs |
| **Undiscounted** equilibrium payoff | `z = lim_k γ(σ^k)` for a sequence with `σ^k` a `1/k`-equilibrium (Solan–Vieille arXiv:2512.04306, Def. 2.3) |
| **Uniform** equilibrium payoff | for every `ε > 0` there is a profile `σ` that is an ε-equilibrium in **all** sufficiently long finite-horizon games, with payoff within `ε` of `z` (ibid., Remark 2.9) |

**Uniform is strictly stronger than undiscounted in general.** They coincide in
*positive recursive absorbing* games — verbatim from Remark 2.9:

> In positive recursive absorbing games, the expected average payoff `γₙ(σ)`
> over the first `n` stages is nondecreasing in `n`, and converges to the
> undiscounted payoff `γ(σ)`. This implies that the two concepts of equilibrium
> payoffs coincide for such games.

A verifier independently re-derived the monotonicity:
`γ_{i,n}(σ) = E[1_{θ≤n} · r_i(a^θ) · (n − θ + 1)/n]` is nondecreasing in `n`
*precisely because* `r_i ≥ 0`. The "positive" hypothesis does real work.

Our `IsUniformEquilibriumPayoff` / `HasUniformDeviationCapConstructor`
(`Uniform.lean`) is the **uniform** notion — the strongest of the three. Any
theorem imported from a paper whose abstract says "limiting average" needs its
upgrade sourced separately, not assumed.

---

## n = 2 — SETTLED (Vieille 2000)

**Statement.** `[primary, abstract-level]` Every two-player non-zero-sum finite
stochastic game (finite state and action sets) has a uniform/undiscounted
equilibrium payoff.

**The proof is three papers, not one.** All in Israel J. Math. **119** (2000):

| Part | Title | Pages | DOI | Role |
|---|---|---|---|---|
| I | *Two-player stochastic games I: A reduction* | 55–91 | [`10.1007/BF02810663`](https://doi.org/10.1007/BF02810663) | reduces the general problem to positive absorbing recursive games |
| II | *II: The case of recursive games* | 93–126 | [`10.1007/BF02810664`](https://doi.org/10.1007/BF02810664) | settles that class |
| III | *Small perturbations and stochastic games* | 127–142 | [`10.1007/BF02810665`](https://doi.org/10.1007/BF02810665) | auxiliary tools |

⚠ **Neither part alone proves existence.** Part I's abstract says so
explicitly: "It reduces the existence problem to the class of so-called
positive absorbing recursive games. The existence problem for this class is
solved in a subsequent paper." Vieille's own later texts always cite I and II
**jointly**. The repository's manuscript already cites
`\cite{Vieille2000I,Vieille2000II}` correctly; **Part III is missing from
`latex/references.bib` and from the manuscript bibliography** — see
[`ephemeral/MISSING.md`](../../../ephemeral/MISSING.md).

Also: **Vieille is the sole author.** Solan did not co-author the two-player
solution. (A stray gloss asserting otherwise was corrected in verification.)

**Source caveat.** All three full texts are paywalled (Springer 303-redirects
to `idp.springer.com`). Abstract text came from a Crossref-metadata mirror. The
two abstracts corroborate each other and match the authors' own 2015 and 2025
citation patterns, so the statements are safe; internal theorem numbering is
unknown to us.

**Repo status.** `—`. Not formalized, and the reduction structure (general →
positive absorbing recursive) is not represented as an interface either.

---

## n = 2, absorbing — the base case (Vrieze–Thuijsman 1989)

**Statement.** `[primary, abstract-level]` Verbatim from the publisher
abstract (idiosyncratic spelling preserved, which is itself evidence the text
is genuine publisher metadata):

> We prove the existence of ε-(Nash) equilibria in two-person non-zerosum
> limiting average repeated games with absorbing states.

Class: "These are stochastic games in which all states but one are absorbing."

**Citation.** O.J. Vrieze and F. Thuijsman, *On equilibria in repeated games
with absorbing states*, International Journal of Game Theory **18**(3),
293–310 (1989),
DOI [`10.1007/BF01254293`](https://doi.org/10.1007/BF01254293).

⚠ **The uniform upgrade is separately sourced, not inferred.** The 1989
abstract says *limiting average*, which is formally weaker. Later restatements
by Solan supply the uniform reading:

- Solan–Vohra (IJGT 31:91–121, 2002), introduction: "Vrieze and Thuijsman
  (1989) proved the existence of a uniform equilibrium payoff in two-player non
  zero-sum absorbing games."
- Munk–Solan (arXiv:2001.03094): "It follows from Vrieze and Thuijsman (1989)
  that every two-player non-zero sum absorbing game admits a uniform
  ε-equilibrium, for every ε > 0."

**Scope.** Does **not** cover several non-absorbing states — which is exactly
why Vieille (2000) was needed.

**Repo status.** `—` for the theorem. Our `Absorbing.lean` results are for an
absorbing *initial state* (the degenerate case), not for a live state with
absorbing surroundings.

---

## n = 3, absorbing — SETTLED (Solan 1999)

**Statement.** `[primary, abstract-level]` Verbatim from the INFORMS abstract:

> An `n`-player absorbing game is an `n`-player stochastic game where all the
> states but one are absorbing (a state is absorbing if once it is reached, the
> probability to leave it is zero, whatever the players play). We prove that
> every three-player absorbing game has an undiscounted equilibrium payoff.

**Citation.** E. Solan, *Three-Player Absorbing Games*, Mathematics of
Operations Research **24**(3), 669–698 (1999),
DOI [`10.1287/moor.24.3.669`](https://doi.org/10.1287/moor.24.3.669).

**Uniform reading, confirmed by Solan himself** (Munk–Solan arXiv:2001.03094):
"Solan (1999) proved the existence of a uniform ε-equilibrium in three-player
absorbing games… To date it is not known whether every four-player absorbing
game admits a uniform ε-equilibrium, for every ε > 0."

⚠ **The theorem is for `n = 3` only.** It defines the `n`-player class but
proves nothing for `n ≥ 4`. It has also resisted extension to general
three-player stochastic games with several non-absorbing states — Solan, in
December 2025: "Some results … have so far resisted extension to stochastic
games, e.g., the existence of an undiscounted equilibrium in three-player
absorbing games (Solan (1999)) and in absorbing team games (Solan (2000))."

**Still live machinery.** arXiv:2512.04306 Lemma 3.9 is "a special case of
Lemma 5.3 in Solan (1999)".

**Repo status.** `—`.

---

## Quitting games — CONDITIONAL (Solan–Vieille 2001)

**The model** `[primary]`, verbatim:

> A quitting game is a pair `(N, (r_S))` … At every stage each player chooses
> an action, either continue or quit. Let `S` be the subset of the players who
> chose to quit. If `S ≠ ∅`, then the game terminates, and each player `i`
> receives the payoff `r^i_S`. If `S = ∅`, the game continues… If the game
> never terminates, each player gets `0`.

And: "Quitting games form a class of stochastic games. More precisely, they are
both recursive games (in the sense of Everett) and repeated games with
absorbing states."

**Theorem 1.2** `[primary]`: every quitting game satisfying

- **A.1** — `r^i_{i} = 1` for every `i` (each player prefers unilateral
  termination to indefinite continuation), and
- **A.2** — `r^i_S ≤ 1` for every `S` containing `i` (a quitter cannot profit
  from others also quitting)

has a **cyclic subgame-perfect uniform ε-equilibrium**.

**Citation.** E. Solan and N. Vieille, *Quitting Games*, Mathematics of
Operations Research **26**(2), 265–285 (2001),
DOI [`10.1287/moor.26.2.265.10549`](https://doi.org/10.1287/moor.26.2.265.10549).

⚠ **This is conditional and payoff-restricted.** Quitting games are *not*
settled in general by this paper; the published abstract retains the qualifier
"under some assumptions on the payoff structure". An adversarial check
confirmed that Lemma 2.5's weakening does **not** effectively generalize the
theorem — it substitutes a different hypothesis keyed to the same A.1
normalization, and the Dynkin-game extension (Thm 2.8) re-assumes both A.1 and
A.2.

**Source note.** Verified against the Northwestern CMS-EMS DP 1227 (28 Sept
1998), the working-paper version; published MOR pages are paywalled.

**Repo status.** `L~` for the *model*: `QuittingGame.lean` builds quitting
games as stochastic games, general in the player type and terminal reward, and
`QuittingAsymptotic.lean` formalizes the translation from expected-terminal
equilibria to our finite-horizon-average `IsUniformEquilibriumPayoff`. The
Solan–Vieille **theorem** is `—`.

---

## Absorption paths — SOURCE ENDPOINT DEFECT UNDER REVIEW

Ashkenazi-Golan, Krasikov, Rainer, and Solan introduce absorption paths as
limits of approximate-equilibrium behavior in quitting games. Their printed
sequential-perfection definition tests a discrete jump only when the
**post-jump** absorption mass is strictly below one, while the path definition
and Remark 4.10 explicitly permit a sure terminal jump. The continuous clause
is empty for the sure-stage-one example. Proposition 4.14 and Theorem 4.15 do
not add a terminal optimality test, and no erratum was found in the arXiv or
published versions.

This omission cannot safely be repaired by testing the terminal product action
against continuation zero: a genuine first-stage equilibrium may rely on an
off-path punishment after a player prevents absorption. The two live repairs
are therefore:

1. restrict the hybrid path branch to jumps that remain nonterminal, carrying
   first-stage and all-continue equilibria as disjoint simple branches; or
2. augment terminal jumps with a credible continuation value and strategy
   witness.

The source theorem must not be used as a literal path/nonexistence equivalence
until one repaired bridge is proved. Exact source points, one false positive,
and one false negative for the naïve all-jumps repair are recorded in
[Review 07](../../../ephemeral/reviews/Review07-AbsorptionPathTerminalJumpConvention.md).

**Citation.** O. Ashkenazi-Golan, I. Krasikov, C. Rainer, and E. Solan,
*Absorption Paths and Equilibria in Quitting Games*, Mathematical Programming
(2022), DOI
[`10.1007/s10107-022-01807-6`](https://doi.org/10.1007/s10107-022-01807-6);
[arXiv:2012.04369](https://arxiv.org/abs/2012.04369).

**Repo status.** Mathematical bridge `R?`. No formal theorem should consume
the printed equivalence before the endpoint convention is repaired.

---

## Simon 2012 — an implication, not an existence theorem

`[primary, abstract-level]` R.S. Simon, *A Topological Approach to Quitting
Games*, Mathematics of Operations Research **37**(1), 180–195 (2012),
DOI [`10.1287/moor.1110.0524`](https://doi.org/10.1287/moor.1110.0524).
Abstract verbatim, from three independent DOI-keyed records:

> This paper presents a question of topological dynamics and demonstrates that
> its affirmation would establish the existence of approximate equilibria in
> all quitting games with only normal players.

"**Would establish**" is the paper's own word. Player `i` is *normal* if there
is `j ≠ i` with `r_i^{ij} ≤ r_i^{i}`. The machinery is a version of the
Kohlberg–Mertens structure theorem adapted to quitting games.

⚠ **Reading trap.** Solan–Solan write "This result was extended to a more
general class of quitting games by Simon (2012)", which reads as unconditional
in isolation. It cannot mean that — the same paper declares the four-player and
all-normal cases open.

---

## Correlated equilibrium — SETTLED FOR ALL n

This is the one place the problem is fully closed, and it is closed by
**weakening the solution concept**.

`[primary]` **Solan–Vieille 2002, Theorem 2.3**: "Every stochastic game
possesses an autonomous correlated equilibrium payoff." Every `n`-player finite
stochastic game (finite `N`, `S`, `A^i`, `|r| ≤ 1`). *Autonomous* = the device
conditions only on previous **signals**, never on previous states or actions.
Stronger for subclasses: Thm 2.4 for recursive games (min-max punishment,
correlation needed only on the equilibrium path); Thm 2.5 for positive
recursive games (a **stationary** device, independent of `ε`).

*Citation:* Games and Economic Behavior **38**(2), 362–399 (2002),
DOI [`10.1006/game.2001.0887`](https://doi.org/10.1006/game.2001.0887).

The notion is **uniform** — Def. 2.2, verbatim: for every `ε > 0` there exist
`D`, `σ ∈ G(D)` and `n₀` such that for every `n ≥ n₀`, every `i`, every
deviation `σ'_*` and every initial state `s`,
`γ^i_s + ε ≥ γ^i_n(D,s,σ) ≥ γ^i_s − ε ≥ γ^i_n(D,s,σ^{−i},σ'_*) − 2ε`, followed
by "Note that for every `ε > 0` a different correlation device may be used."

Three caveats carried from verification:

- the payoff notion is uniform-ε, not exact equilibrium, and the device is
  ε-dependent (except Thm 2.5);
- Thm 2.3's device is **not canonical** in the Forges (1988) sense: its
  on-path construction uses private current recommendations with delayed
  public disclosure of previous recommendations. After a detected unilateral
  deviation, however, the ordinary coalition-minmax punishment ignores the
  continuing device signals; it should not be described as correlated
  punishment;
- Solan–Vohra's normal-form device is a genuinely different object.

`[secondary]` **Solan–Vohra 2002**: every multiplayer **absorbing** game admits
a **normal-form** (one-shot pre-play) correlated equilibrium payoff. IJGT
**31**, 91–121 (2002),
DOI [`10.1007/s001820200109`](https://doi.org/10.1007/s001820200109).

**Why this matters to us.** `UniformEquilibriumProgram.md` records as a
standing constraint that a public lottery is **not** freely available and must
be synthesized endogenously with proved unilateral robustness, entry safety and
sublinear cost. The correlated results are exactly the theorems obtained when
that device is granted. They therefore isolate the remaining ordinary-Nash gap
as an **endogenous implementation problem for the autonomous device**. This is
strictly richer than manufacturing a public lottery from observed play: the
general construction uses current private recommendations and one-stage-
delayed disclosure. Fresh contingent tables are independent across dates,
and the ordinary coalition-minmax punishment ignores the continuing device
signals after a detected unilateral deviation. The
compiler must reproduce the needed information and obedience structure
through legal play, with robust sublinear payoff/state cost. This is a sharper
framing than the frontier's former "endogenous jointly controlled lotteries"
portfolio item, but it is not a theorem that robust public randomness alone
closes the gap.

**Repo status.** `—` for both theorems. `GameTheory/Concepts/Correlation/` and
`Repeated/MonitoringPublicRandomization.lean` exist but do not carry these.

---

## Post-2020 frontier

`[primary]` **Solan–Vieille, December 2025**, *Undiscounted Equilibrium in
Positive Recursive Absorbing Games with Non-Rectangular Absorption Structure*,
arXiv:2512.04306v1 (3 Dec 2025).

**Theorem 2.8**, verbatim: "Every positive recursive absorbing game that has no
rectangular connected component admits an undiscounted equilibrium payoff." By
Remark 2.9, a **uniform** equilibrium payoff.

Definitions (verified line by line against the PDF): *recursive* = payoff `0`
in the single nonabsorbing state; *positive* = `r_i(a) > 0` for every `i` and
every profile `a`; `B := {a ∈ A : p(a) = 0}`; a graph on `B` with edges between
profiles differing in at most one player's action; a connected component `B^l`
is **rectangular** if it is a product set `∏_i B^l_i`. Arbitrary finite player
set (contentful range `|I| ≥ 3`). Assumption 3.2 is explicitly WLOG.

Section 5 bounds the result honestly: combining with Solan–Solan (2021) to
cover a rectangular component is something the authors "do not know how to
prove"; non-positive, non-recursive, and multi-nonabsorbing-state extensions
are stated open.

⚠ Unrefereed preprint, no journal reference as of 2026-08-02. Cite as
"Solan–Vieille prove in a Dec-2025 preprint". Its companion, cited as
Solan & Vieille (2025) *Public correlated equilibrium in positive recursive
games*, is listed as **MIMEO (unpublished)** — do not cite it as available.

`[primary]` **Solan–Solan, sunspot equilibrium.** *Sunspot Equilibrium in
General Quitting Games*, arXiv:1803.00878 (v2, 5 Aug 2019, "Corrected
version"), Theorem 2.5: every **positive recursive general quitting game**
(each player may have more than one continue action) admits a sunspot
ε-equilibrium for every `ε > 0` — an ε-equilibrium in the extended game with a
public correlation device (a uniform `[0,1]` public signal each stage).

⚠ The uniform upgrade is an **authorial assertion, not a proof**: "By arguments
similar to those of Solan and Vieille (2001, Section 2.6), our results apply to
the stronger notion of uniform equilibrium." Not independently checked.

`[medium]` **Secondary catalogue** — identified only via citations inside
verified primary sources, not independently fetched:

- arXiv:2208.11425 — Ashkenazi-Golan, Flesch & Solan, *Absorbing Blackwell
  Games*
- arXiv:2012.04369 — Ashkenazi-Golan, Krasikov, Rainer & Solan, Math.
  Programming 2022, DOI `10.1007/s10107-022-01807-6`
- arXiv:1707.02598 — Solan & Solan, *Quitting Games and Linear Complementarity
  Problems*, Math. OR 45(2), DOI `10.1287/moor.2019.0996` (sunspot
  ε-equilibrium in the Q-matrix case)
- arXiv:2001.03094 — Munk & Solan
- arXiv:1803.00802 — *Jointly Controlled Lotteries with Biased Coins* —
  directly relevant to the frontier's endogenous-lottery item

⚠ arXiv:2201.05148 and arXiv:1301.1967 were **not identified** by any surviving
claim. Treat as unresearched.

**Bibliography hygiene note from verification:** an HTML-rendering fetch of
arXiv:2512.04306 *hallucinated* page numbers (Solan 1999 as 669–694, Solan 2000
as GEB 33:85–96) that the actual PDF contradicts (669–698; GEB 31:245–261).
Prefer `pdftotext` over HTML renderings for bibliographies.
