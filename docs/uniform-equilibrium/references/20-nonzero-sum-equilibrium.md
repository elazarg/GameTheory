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
`latex/references.bib` and from the manuscript bibliography** — see the
[bibliography maintenance queue](BibliographyMaintenance.md).

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

**Statement.** `[primary, abstract-level]` Verbatim from the INFORMS abstract,
independently re-fetched and cross-checked against Crossref metadata
2026-08-04 (both agree verbatim):

> An `n`-player absorbing game is an `n`-player stochastic game where all the
> states but one are absorbing (a state is absorbing if once it is reached, the
> probability to leave it is zero, whatever the players play). We prove that
> every three-player absorbing game has an undiscounted equilibrium payoff.

**Citation.** E. Solan, *Three-Player Absorbing Games*, Mathematics of
Operations Research **24**(3), 669–698 (1999),
DOI [`10.1287/moor.24.3.669`](https://doi.org/10.1287/moor.24.3.669). MOR full
text paywalled; not obtained.

### The undiscounted/uniform question — resolved, `PRIMARY_FULLTEXT` on the dissertation

The published abstract's headline word is **undiscounted**. Under this
document's own terminology table that is *a priori* the weaker notion, and
the equivalence proved elsewhere in this file (Remark 2.9 of
arXiv:2512.04306) is stated only for *positive recursive* absorbing games —
a class three-player **quitting** games with negative payoffs need not belong
to. That gap is real enough to require independent evidence, not an
assumption. Three converging sources, none of them the MOR text itself, close
it:

`[secondary]` **Solan's own contemporaneous exposition.** E. Solan, *Uniform
Equilibrium: More Than Two Players*, a lecture chapter dated 30 July 1999 —
the same year as the MOR paper — later published as *Uniform Equilibrium:
More than Two Players*, in Neyman & Sorin (eds.), *Stochastic Games and
Applications*, NATO Science Series C **570** (Kluwer, 2003), DOI
[`10.1007/978-94-010-0189-2_20`](https://doi.org/10.1007/978-94-010-0189-2_20)
— the same NATO ASI volume that contains Thuijsman 2003, already in this
bibliography. Author-hosted preprint fetched 2026-08-04:
`math.tau.ac.il/~eilons/natoasi4.pdf`. Its Section 2, verbatim:

> **Theorem 2.1 (Solan, 1999)** *Every three-player absorbing game admits a
> uniform equilibrium payoff.*

followed by a genuine proof sketch (Steps 1–3), not a bare citation: a
stationary `ε`-discounted equilibrium is chosen as a Puiseux function of the
discount rate `ε`, the limit `ε → 0` is taken algebraically, and the two
cases (limit strategy absorbing / non-absorbing) are each shown to yield an
"`(x,ε)`-perturbed" profile — Definition 2.4's statistical-test-plus-threat
construction, which is *by definition* an equilibrium simultaneously for all
sufficiently small `ε`, i.e. the **uniform** notion directly, not a weaker
notion later upgraded. This is the same "vanishing discount factor" technique
titling Ch. 10 of Solan's 2022 Cambridge textbook, *A Course in Stochastic
Game Theory* ("The vanishing discount factor approach and uniform equilibrium
in absorbing games") — corroborating that this is the field's standard route
to the *uniform*, not merely undiscounted, conclusion for absorbing games.
**No positivity or sign hypothesis appears anywhere in Theorem 2.1's
statement or proof** — payoffs `r_i(a)`, `r*_i(a)` are general reals throughout,
and Step 2 is explicitly titled "General non-absorbing payoffs". Section 3 of
the same chapter defines quitting games as the special case of absorbing
games where each player's two actions are continue/quit — so **Theorem 2.1
already covers every three-player quitting game, any sign of payoffs,
unconditionally**, with no need for Solan–Vieille's A.1/A.2-restricted
quitting-game theorem (recorded below), which exists to reach beyond `n = 3`,
not to cover it.

`[secondary]` **Munk–Solan (arXiv:2001.03094), confirmed verbatim by
downloading and re-extracting the PDF text 2026-08-04** (title: *Sunspot
Equilibrium in Positive Recursive Two-Dimensions Quitting Absorbing Games*;
the paper's own new contribution is restricted to that narrow class, but
these two citations of Solan 1999 are general background statements, not
scoped to it):

> "Solan (1999) proved the existence of a uniform `ε`-equilibrium in
> three-player absorbing games." (Introduction, p. 1)

> "It follows from Vrieze and Thuijsman (1989) that every two-player non-zero
> sum absorbing game admits a uniform `ε`-equilibrium, for every `ε` > 0.
> Solan (1999) extended this result to every three-player absorbing game. To
> date it is not known whether every four-player absorbing game admits a
> uniform `ε`-equilibrium, for every `ε` > 0." (§2, p. ~5)

**arXiv-trap check performed** (per this file's own standing caution about
`arxiv.org/pdf/<id>` serving stale/withdrawn content): the Atom API lists a
single version, v1, submitted 2020-01-07, comment "42 pages", no
withdrawal notice, no journal-ref; the PDF fetched under that URL contains
42 pages of ordinary mathematical content (not a withdrawal stub). Treat as a
live, unrefereed preprint — not disqualifying, but do not upgrade its status
past that.

`[primary, dissertation-text]` **The decisive source: Solan's own doctoral
dissertation.** A local copy already sat unread in the repository at
`ephemeral/old/_source_eilons_thesis.pdf` (97 pp., PDF `CreationDate`
10 Nov 1998, Center for the Study/Rationality and Interactive Decision
Theory, Hebrew University of Jerusalem, advisor Prof. Abraham Neyman). The
Acknowledgments name **three anonymous referees of Mathematics of Operations
Research, whose comments substantially improved the presentation of the
results in section 4** — i.e. this dissertation's Section 4 is, by its own
declaration, the material refereed into the MOR 1999 paper, not merely a
related document. Section 4.7, verbatim:

> **Theorem 4.23** *Every three-player repeated game with absorbing states has
> a perturbed equilibrium payoff.*

with a full formal proof (not a sketch) assembled from Lemmas 4.1, 4.2, 4.4,
4.8, 4.22 and 4.24, each independently proved earlier in the chapter.

**"Perturbed equilibrium payoff" is the dissertation's own name for the
uniform notion, stated as a blanket convention, not left implicit.**
Definition 3.9, verbatim: "The payoff vector `g` ... is a uniform
`x`-perturbed equilibrium payoff (**or a perturbed equilibrium payoff**) if it
is an `(x,ε)`-perturbed equilibrium payoff for every `ε > 0`" — the two names
are given as literal synonyms in the definition itself. And immediately
before Section 4 begins, the dissertation states its global reading
convention outright: "Since the results in this monograph refer to uniform
equilibria, **whenever we write equilibrium payoff**, `ε`-equilibrium
profiles and min-max value, **we mean the uniform equilibrium payoff**,
uniform `ε`-equilibrium profile and uniform min-max value respectively."
Applying that convention to Theorem 4.23 exactly as instructed yields: every
three-player absorbing game has a **uniform** equilibrium payoff — with no
sign or positivity hypothesis anywhere in the statement, the definitions
feeding it, or the five sufficient-condition lemmas section 4.2 lists.

**Verdict.** Effectively closed. The dissertation is `PRIMARY_FULLTEXT` on
the mathematical content — a complete, formally structured proof by the
paper's own author, tied to the MOR paper by the dissertation's own
acknowledgments — though it is not literally the MOR-typeset PDF itself
(that remains paywalled and unread; theorem/lemma numbering could differ
after copy-editing, though the referee acknowledgment makes wholesale
mathematical divergence very unlikely). Combined with the independent
contemporaneous conference exposition (Theorem 2.1 above) and the two
Munk–Solan restatements, three independent Solan-authored documents now
agree explicitly on the uniform reading, one of them with a complete formal
proof. The published abstract's "undiscounted" wording is best read as the
field's standard headline framing for this class of open problem (see the
Dec-2025 Solan–Vieille quote in [`40-open-status.md`](40-open-status.md):
"the main open problem... is whether every multiplayer stochastic game
admits an undiscounted equilibrium payoff") while the interior theorem proves
the strictly stronger uniform notion — the same pattern already recorded
above for Vrieze–Thuijsman 1989, whose abstract says "limiting average" yet
is uniformly re-cited as "uniform" by Solan–Vohra and by Munk–Solan, now
corroborated for Solan 1999 by an actual complete proof rather than by
pattern alone.

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

**Source note.** Theorem 1.2 above verified against the Northwestern CMS-EMS
DP 1227 (28 Sept 1998, `kellogg.northwestern.edu/research/math/papers/1227.pdf`),
the working-paper version. The **published** MOR text is not paywalled after
all: it is author-hosted at
`math.tau.ac.il/~eilons/quitting19.pdf` — a JSTOR-digitized scan whose header
confirms *Mathematics of Operations Research*, Vol. 26, No. 2 (May 2001),
pp. 265–285, DOI `10.1287/moor.26.2.265.10549`, matching the citation above
exactly. Both versions were read in full for this record.

**Repo status.** `L~` for the *model*: `Models/Quitting/Game.lean` builds quitting
games as stochastic games, general in the player type and terminal reward, and
`Models/Quitting/Asymptotic.lean` formalizes the translation from expected-terminal
equilibria to our finite-horizon-average `IsUniformEquilibriumPayoff`. The
Solan–Vieille **theorem** is `—`.

### Proposition 2.13 — the terminal-payoff / uniform-equilibrium bridge

`[primary]` No prior wing record existed for this proposition, despite it
being cited roughly 15 times across this program's literature notes as
"Solan–Vieille (2001), Proposition 2.13," with no title, journal, or quoted
statement anywhere. Read directly against the published text (see Source note
above — the JSTOR scan, not the 1998 working paper). Section 2.6,
"Equilibrium and uniformity," verbatim:

> PROPOSITION 2.13. *If x is an ε-equilibrium then it is a uniform
> ε′-equilibrium, provided ε′ > ε.*

where `γ_n(x) := E_x[1_{t≤n} r_{S_t}(n−t)/n]` is the expected payoff if
players receive `0` before termination and the termination payoff repeated at
every stage after, and a **uniform ε-equilibrium** is a profile that is an
ε-equilibrium for `γ_n` simultaneously, for every `n` large enough — this
program's own "uniform" reading, verbatim from the source. **This is a
bridge, not a structural result.** It says that in quitting games, the paper's
baseline notion of ε-equilibrium (Definition 1.1, built on the expected
terminal payoff `γ(x) = E_x[r_{S_t} 1_{t<∞}]`) automatically upgrades to a
genuine uniform ε′-equilibrium, with no extra construction needed. The proof
is an averaging argument the authors call routine ("Since the details are
standard, we only sketch the proof"), not new machinery.

**Numbering is confirmed NOT to match the 1998 working paper**, resolving the
question `40-open-status.md` and the audits flagged as open. DP 1227 has **no
Section 2.6 and nothing numbered past Theorem 2.8** — its highest label in
§2 is Lemma 2.7 (an independent-Bernoulli-race lemma), followed immediately
by Theorem 2.8 ("General payoff processes"). The entire "Equilibrium and
uniformity" section — and Proposition 2.13 with it — was added between the
1998 preprint and the 2001 publication. Any citation of "Prop. 2.13" checked
against the working paper is citing a section that is not there.

**For contrast, Proposition 2.4** (also widely re-cited, e.g. paired with
2.13 in AGKRS's Theorem 3.5 above): published Prop. 2.4 *is* present in the
working paper, as Lemma 2.2/Lemma 2.6 — "either **x** is a subgame-perfect
ε^{1/6}-equilibrium, or there is a stationary ε^{1/6}-equilibrium," proved in
the published §2.5 ("Proof of the main proposition," which explicitly restates
it as Proposition 2.6 for the write-up, exactly as
[`SourceCorrections-QuittingAbsorptionPaths.md`](SourceCorrections-QuittingAbsorptionPaths.md)
§3 already found). That finding is **unaffected** by today's read — Prop.
2.4's content was already read correctly there; only Prop. 2.13 was missing a
record.

**Confidence: `[primary]`**, full text of both the 1998 and 2001 documents,
JSTOR/DOI front matter confirmed. The 15 citing sites elsewhere in this repo
that invoke "Prop. 2.13" without further detail can now be checked against
the statement above rather than trusted on the strength of a number alone.

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
and one false negative for the naïve all-jumps repair were recorded in the
historical intake note
`ephemeral/reviews/Review07-AbsorptionPathTerminalJumpConvention.md`.

**Citation.** O. Ashkenazi-Golan, I. Krasikov, C. Rainer, and E. Solan,
*Absorption Paths and Equilibria in Quitting Games*, Mathematical Programming
(2022), DOI
[`10.1007/s10107-022-01807-6`](https://doi.org/10.1007/s10107-022-01807-6);
[arXiv:2012.04369](https://arxiv.org/abs/2012.04369).

**Repo status.** Mathematical bridge `R?`. No formal theorem should consume
the printed equivalence before the endpoint convention is repaired.

**Section 5 of the same paper is a separate and safe import**, and is recorded
on its own terms in
[`QBarMatrixQuittingGamesHaveContinuousEquilibria`](../../../ideas/UniformEquilibriumLiterature/QBarMatrixQuittingGamesHaveContinuousEquilibria.md):
the `Q̄`-matrix sufficient condition (Thm 5.4), the published
`S.1`/`S.2`/`S.3` characterization of `ε`-equilibrium existence (Thm 3.4,
Simon 2007 + Solan–Vieille 2001), the `ε^{1/6}` bound (Thm 3.5), the
identification of this program's canonical hard weight with the paper's own
`Γ_η`, and four printed defects in Remark 5.3 and Definition 5.1 that must not
be quoted as-is.

---

## Simon 2007 — Theorem 3, read in full (Theorem 3.4's other source)

R.S. Simon, *The Structure of Non-Zero-Sum Stochastic Games*, Advances in
Applied Mathematics **38**(1), 1–26 (2007), DOI
[`10.1016/j.aam.2006.07.002`](https://doi.org/10.1016/j.aam.2006.07.002).
Local copy now on disk:
`ephemeral/The-structure-of-non-zero-sum-stochastic-g_2007_Advances-in-Applied-Mathemat.pdf`
(the earlier "genuinely paywalled" note is retired).

**Confidence: `[primary]`.** Full text read — pp. 1, 5, 13–20, 24 — via
rendered page images (`pdftoppm -r 200`), not the `pdftotext` text layer: this
PDF's symbol fonts (`EPKMEM+Symbol`, `EPKMDL+MTMI`, …) carry no `ToUnicode`
map (`pdffonts` reports `uni: no` on the body-text fonts), so `pdftotext`
silently **drops every Greek glyph** — "for every positive ε there is…"
extracts as "for every positive there is…" with no visible gap, and can
misrender a stray glyph as an ASCII letter. All quotes below are transcribed
from the rendered images to avoid propagating that corruption.

### Abstract, verbatim (p. 1)

> Strategies in a stochastic game are δ-perfect if the induced one-stage games
> have certain δ-equilibrium properties. In special cases the existence of
> δ-perfect strategies for all positive δ implies the existence of
> ε-equilibria for every positive ε. Using this approach we prove the
> existence of ε-equilibria for every positive ε for a special class of
> quitting games. The proof reveals that more general proofs for the
> existence of ε-equilibria in stochastic games must involve the topological
> structure of how the equilibria of one-stage games are related to changes
> in the payoffs.

**The "special class" is escape games (§5, Theorem 4 below) — not Theorem 3.**
Theorem 3 lives in §4.4 ("Equivalences"), proved for **arbitrary** quitting
games from the machinery of §4.1–4.3, before §5's topological "spanning
property" is introduced at all. This resolves, in the direction favorable to
AGKRS, the question this wing record previously carried as unverified
inference ("Theorem 3 is plausibly the general principle rather than the
escape-game theorem itself"): **confirmed.** AGKRS's citation of "Theorem 3"
to source a fully general S.1/S.2/S.3 characterization is not reaching past a
narrower escape-game hypothesis than they use it for.

### The model Theorem 3 presupposes (§4.1, p. 14)

> In a quitting game each player has only two actions, c for continue and q
> for quit. As soon as one or more of the players at any stage chooses q, the
> game stops and the players receive their payoffs, which are determined by
> the subset of players that choose simultaneously the action q. If nobody
> chooses the action q throughout all stages of play, then all players
> receive 0.

Formally: player set `N`; for every non-empty `A ⊆ N` a payoff vector
`v(A) ∈ Rᴺ`, paid when `A` is exactly the set who first quit simultaneously;
`M ≥ 1` bounds the spread of all payoffs. Cast as a stochastic game: state
`x̂` (all-continue-so-far, payoff 0) plus `2^|N| − 1` absorbing states `s_A`.

### Definitions Theorem 3's statement uses

- **χⁿ, the min-max value** (§2.3, p. 5), verbatim: "For every player `n`
  define `χⁿ : S → R` so that `χⁿ(s)` is the min-max value for player `n` at
  the state `s`, the lowest upper bound for what player `n` can obtain from a
  start at `s` in response to all strategy choices of the other players.
  Formally `χⁿ(s)` equals `inf_σ sup_σ̃ⁿ 𝒱ₛⁿ(σ | σ̃ⁿ)`."
- **Feasible, ε-rational, normal player** (§4.3, p. 15–16), verbatim: "A
  vector `r ∈ Rᴺ` is *feasible* if it is in the convex hull of
  `{v(A) | ∅ ≠ A ⊆ N} ∪ {0}`. … A vector `r ∈ Rᴺ` is *ε-rational* for any
  positive `ε` if `rⁿ ≥ χⁿ − ε` for all `n ∈ N`. A player `n ∈ N` is *normal*
  if `v({n})ⁿ ≥ χⁿ`." (`v` abbreviates `v({i})ⁱ` per player.)
- **The correspondences `E_ε`, `F_ε`, and `q`** (§4.2, p. 15): for
  `r ∈ Rᴺ, p ∈ [0,1]ᴺ`, `aʲ(p)` is player `j`'s expected payoff from quitting
  simultaneously with the others' `p`, `bʲ(r,p)` her payoff from continuing
  (given continuation value `r`); `E_ε(r) := {p | pʲ>0 ⟹ aʲ(p) ≥ bʲ(p,r)−ε,
  pʲ<1 ⟹ bʲ(p,r) ≥ aʲ(p)−ε}` (a one-stage `ε`-equilibrium test — see the
  clause-map note below, it is pointwise identical to AGKRS's Definition 3.1);
  `F_ε(r) := {f(r,p) | p ∈ E_ε(r)}` where `f(r,p)` is the resulting expected
  payoff vector; `q(p) := 1 − ∏ⱼ(1−pʲ)`, the probability someone quits.
- **Stationary and instant approximate equilibria** (Definitions, p. 16),
  verbatim: "A quitting game has *stationary approximate equilibria* if for
  every `ε > 0` there is a `p ∈ [0,1]ᴺ` such that `(p, p, p, …)` is an
  `ε`-equilibrium. A quitting game has *instant approximate equilibria* if
  for every `ε > 0` there is a `p ∈ [0,1]ᴺ` with `pʲ = 1` for some player
  `j ∈ N` such that a `2ε`-equilibrium is described by the behavior `p` on
  the first stage followed by punishment of player `j` on the second stage
  (given that she did not quit) yielding to player `j` no more than `χʲ+ε`."
- **A quitting game has *approximate equilibria*** if for every `ε>0` an
  `ε`-equilibrium exists (general definition, §2.2, p. 5).
- **Cyclic strategy profile, orbit, extended orbit, total variation**
  (§4.2, p. 14–15): an orbit of a correspondence `F : X → X` is a sequence
  `(x₀,x₁,…)` with `(xₙ,xₙ₊₁) ∈ F`; a cyclic profile repeats a finite block
  `(p₀,…,p_{k-1})` forever; total variation is `Σ‖xᵢ−xᵢ₊₁‖`, and "unbounded"
  means the sum diverges.

### Theorem 3, verbatim (p. 18)

> **Theorem 3.** *For a quitting game with neither stationary approximate
> equilibria nor instant approximate equilibria the following are
> equivalent*:
>
> (i) *the game has approximate equilibria,*
> (ii) *for every positive `ε` there is a cyclic strategy profile
> `p = (p₀, …, p_{k−1}, p₀, …)` with `rᵢ(p) ∈ F_ε(rᵢ₊₁(p))` for all
> `i = 0, 1, …`, all the `rᵢ` are `ε`-rational, and `q(pᵢ)` is positive for
> some `0 ≤ i ≤ k − 1`,*
> (iii) *for every positive `ε` and every `B > 1` there is a finite orbit of
> `F_ε` of `ε`-rational vectors within a distance of `ε` of the feasible
> vectors with a total variation of at least `B`,*
> (iv) *for every positive `ε` there is an infinite orbit of `F_ε` of
> `ε`-rational vectors with unbounded total variation,*
> (v) *for every positive `ε` there is an infinite extended orbit of `F_ε` of
> `ε`-rational vectors with unbounded total variation.*

**The hypothesis is exactly "neither S.1-shaped nor S.2-shaped" (see below),
not any restriction to escape games, normal players, or a bounded player
count.** `N` is an arbitrary finite player set and `v(A)` arbitrary reals
throughout.

**Remark immediately following (p. 18), verbatim:** "That (iv) implies both
(i) and (ii) was proven by Solan and Vieille [22] in the context of `vʲ > 0`
for all players `j ∈ N`. Solan [20] showed that the minimal length of the
cycle in (ii) may depend on the size of `ε`." (`[22]` = Solan–Vieille,
*Quitting Games*, MOR 2001, already recorded above in this file.)

### Corollary 2 (p. 20) — the all-normal specialization

> **Corollary 2.** *If all players are normal and there are neither instant
> approximate equilibria nor stationary approximate equilibria then the
> quitting game has approximate equilibria if and only if for every positive
> `δ` there is an infinite orbit of `F_δ` of unbounded total variation.*

This simplifies Theorem 3's (i)⟺(iv) by dropping the "`ε`-rational" qualifier,
but needs the **extra** hypothesis "all players normal" that Theorem 3 itself
does not carry (Theorem 3 only gets, via Lemma 5 in its proof, that *some*
player is normal and *some* second player is normal — not that every player
is).

### Escape games (§5) — narrower than Theorem 3, not what it depends on

Definition (p. 20): a quitting game is an *escape game* if **(1)** every
player is normal, and there is a closed set `Q` and `ε̄ > 0` with three
further closure/existence properties (2)–(4) tying `Q` to the "spanning
property" — a Čech-homology condition (§5.2) borrowed from Kohlberg–Mertens-
style structure-theorem arguments. **Theorem 4** (p. 24), verbatim: "All
escape games have approximate equilibria." — proved by exhibiting condition
(v) of Theorem 3 via the topological spanning property, i.e. Theorem 4 is a
*downstream application* of Theorem 3, not a hypothesis it needs.

### Conjecture 1 (p. 14) — verbatim, and its status

Section 3.5 first proves (Lemma 2, verbatim): "If the Markov chain is time
homogeneous then the expected value of the function `w̄` is no more than
`|X|`." — where, for a finite-state Markov chain and `v : X×{0,1,…}→[0,1]`
with `v(x,i)` a martingale value, `w̄(p) := Σᵢ|v(xᵢ₊₁,i+1) − v(xᵢ,i)|` along a
path `p`. Then, verbatim:

> **Conjecture 1.** *Without the time homogeneous assumption the expected
> value of the function `w̄` is no more than `|X|`.*

followed by, verbatim: "The Markovian property is critical to Conjecture 1;
it is easy to find counter examples if the transitions and the function are
dependent on the past history. The main difficulty with Conjecture 1 lies
with the lack of a state identity that transcends the stages. We would be
satisfied if the expectation of `w̄` does not exceed `f(n)|X|` for any function
`f : {1,2,…} → R` that is independent of the choice of Markov chain."

**Why this is "the δ–ε relationship, stationary vs. Markovian."** Lemma 2's
time-homogeneous hypothesis is exactly what a *stationary* strategy profile
produces (the induced discrete decision process is a time-homogeneous Markov
chain); Theorem 2 (p. 13, the paper's chain-reduction sufficient condition
for approximate equilibria, feeding Theorem 4) consumes Lemma 2's bound.
Conjecture 1 asks whether the same bound survives for the time-inhomogeneous
chains a general **Markovian** (non-stationary) strategy profile induces —
exactly the "extending the δ-ε relationship from stationary to Markovian
processes" gloss this wing record carried at `[secondary]` from the 2016
survey, now confirmed against the primary text and located precisely.

**Status: open, unresolved in this paper.** The only two mentions of
"Conjecture 1" in the entire text are its statement (p. 14) and the
acknowledgment footnote (p. 1): "The author would like to thank Michael Voit
for helpful discussions on Conjecture 1." No resolution, partial result, or
restriction is claimed anywhere else in the paper (checked by full-text
search). **Conjecture 1 does not appear anywhere in Theorem 3's proof or
hypotheses** — Theorem 3 is proved directly from Lemmas 4–6 and Propositions
1–3, not through the Section 3.5 Markov-chain machinery Conjecture 1 belongs
to; it is Theorem 2 and (downstream) Theorem 4's escape-game route that
depend on that machinery, not Theorem 3.

---

## The clause map — AGKRS S.1/S.2/S.3 against the repository's three-branch disjunction (`MATH-P0-4`)

AGKRS Theorem 3.4 (`ephemeral/s10107-022-01807-6.pdf`, p. 739, `[primary]`),
verbatim: "A quitting game admits an `ε`-equilibrium for every `ε > 0`, if and
only if at least one of the following statements holds. **(S.1)** For every
`ε > 0` sufficiently small the game admits a stationary `ε`-equilibrium.
**(S.2)** For every `ε > 0` sufficiently small the game admits an
`ε`-equilibrium `x` that has the following structure: there is a player
`i ∈ I` who quits with probability 1 at the first stage; from the second
stage and on, all players punish player `i` with a payoff `ε`-close to her
min-max level. **(S.3)** For every `ε > 0` sufficiently small there is an
absorbing strategy profile `x` such that all players `i ∈ I` are sequentially
`ε`-perfect at `x`." ("Absorbing" is AGKRS's Def., p. 738: `P_x(θ<∞)=1`;
"sequentially `ε`-perfect," Definition 3.2, tests `ε`-perfectness — Definition
3.1, borrowed explicitly from Solan–Vieille — at every stage against the
continuation payoff.)

The repository's disjunction (`quittingCycle_zeroSolo_or_admissible_or_isolatedNegative`,
`GameTheory/Concepts/Stochastic/UniformEquilibrium/Quitting/Cycles/ThreeBranchDisjunction.lean`) is a
**different, weight-algebraic** trichotomy: `IsQuittingZeroSolo reward`
(every solo-quit reward `r_i({i}) ≤ 0`) `∨ HasAdmissibleAbsorbingQuittingCycle
reward` (some finite cyclic block has, at every coordinate, either a
deleted-opponent-survival product `< 1` around the cycle or a nonnegative solo
weight) `∨ HasIsolatedNegativeAbsorbingQuittingCycle reward` (some absorbing
cyclic block isolates a coordinate — every opponent silent at every phase —
whose solo weight is negative). It is exhaustive **only over weights that
admit some absorbing cyclic continuation block at all**; that residual
hypothesis is itself open (`UniformEquilibrium/Quitting/Cycles/ThreeBranchDisjunction.lean`, module
docstring: "this repository does not prove that every weight admits an
absorbing complementary cycle").

**Cell S.1 ↔ zero-solo: `PROVED`, one direction only.** Zero-solo makes
all-continue (`p = 0`) an *exact* (`0`-)equilibrium
(`quittingGame_isUniformEquilibriumPayoff_zero_of_zeroSolo`), which is a
literal witness of S.1 (a stationary `ε`-equilibrium for every `ε`, indeed
for `ε=0`). So **zero-solo ⟹ S.1**. The converse is open and almost
certainly false in general: S.1 only demands *some* stationary `p`, not
`p = 0`; nothing in the repository shows every S.1-weight is zero-solo, and
no counterexample search was run here to refute it either — left `open`.

**Cell S.3 ↔ admissible cycle: `PROVED`, one direction only, and only the
exact/periodic special case.** Simon's `E_ε(r)` (p. 15: `pʲ>0 ⟹ aʲ(p) ≥
bʲ(p,r)−ε`, `pʲ<1 ⟹ bʲ(p,r) ≥ aʲ(p)−ε`) is, coordinate for coordinate, the
same two inequalities as AGKRS's Definition 3.1 `ε`-perfectness applied to the
one-shot game `G(r)` (their Eqs. (2)–(3), p. 738: `rⁱ(aⁱ,σ⁻ⁱ) ≤ rⁱ(σ)+ε`,
`σⁱ(aⁱ)>0 ⟹ rⁱ(aⁱ,σ⁻ⁱ) ≥ rⁱ(σ)−ε`). So Theorem 3 condition (ii) — a cyclic
`p` with `rᵢ(p) ∈ F_ε(rᵢ₊₁(p))` for every `i` — says exactly that every player
is sequentially `ε`-perfect at the (periodic, hence absorbing whenever
`q(pᵢ)>0` somewhere in the period — repeated indefinitely, quit probability
`→ 1`) profile `p`: literally an S.3-witness, restricted to periodic profiles.
The repository's admissible-cycle branch builds the same object but *exactly*
(`0`-perfect at every phase, not merely `ε`-perfect for each `ε`) — strictly
stronger. So **admissible cycle ⟹ S.3** (via an exact witness, hence an
`ε`-witness for every `ε`). The converse — every S.3-weight admitting a
witness the repository's finite algebraic admissibility test can certify —
is **not** established: general S.3 witnesses need not be periodic, and
Theorem 3's (i)⟺(ii)⟺(iv)⟺(v) equivalence (which does let AGKRS pass between
periodic and general orbits) is Simon's, not re-proved or consumed here.
Left `open`.

**Cell S.2 ↔ (none): `OPEN`, no repository counterpart found.** S.2 is
witnessed by punishing the quitting player down to her **min-max value `χⁱ`**
of the full stochastic game — an `inf sup` over *all* strategies of the
opponents, not merely quitting-game solo-quit rewards `r_i({i})`. No file
under `GameTheory/Concepts/Stochastic/` computes or represents a min-max /
punishment-level quantity for quitting games (checked: no `Instant`,
`MinMax`, or "min-max value" construction exists there). The three-branch
disjunction's vocabulary (solo rewards, cyclic products, isolation) simply
has no object to compare S.2 against. This is a **gap in the map**, not a
mismatch: it says the repository's current machinery cannot even *state* the
S.2 case, let alone decide whether it lines up with anything.

**Cell isolated-negative ↔ (none): `OPEN`, no counterpart in AGKRS's
trichotomy.** The isolated-negative branch is the specific *failure mode* of
the admissible-cycle construction at one candidate block (mismatch
`= −r_who({who}) > 0`, a genuine profitable deviation for `who` away from
that cycle — `quittingIsolatedNegativeCycle_mismatch_eq`), not a residual
class that AGKRS's own proof leaves over. A weight landing here is not shown
to fail S.1, S.2, or S.3 for the *weight as a whole* — only that *this one
block* fails to certify S.3. Two things keep this genuinely open rather than
refuted: (a) the branches are exhaustive-but-not-exclusive, so an
isolated-negative weight can simultaneously be zero-solo and already satisfy
S.1 by the other route (`quittingThreeBranch_not_mutually_exclusive` exhibits
exactly this overlap); (b) S.2's min-max punishment is a plausible rescue for
an isolated negative coordinate that the repository has no machinery to test
(see the cell above). The repository's own docstring already says as much:
"The isolated-negative branch has no sufficiency theorem."

### Does the trichotomy alignment give "internal completeness ⟺ the quitting conjecture"?

**No — the map as it stands does not support that consequence, and it should
not be asserted.** The mechanism `PIPELINE.md` flags (`MATH-P0-4`) requires a
clause-by-clause *equivalence*, not a one-directional implication in two of
three cells and a blank in the third. Concretely: even a proof that the
repository's disjunction is exhaustive (every weight is zero-solo, or admits
an admissible cycle, or lands in isolated-negative for every candidate block)
would only show — via the two proved implications — that every such weight
satisfies **S.1, or S.3, or *neither is known***. The isolated-negative case
supplies no witness for S.1 ∨ S.2 ∨ S.3, so exhaustiveness of the internal
trichotomy would not, by this map, establish AGKRS's disjunction for every
weight, and therefore would not establish that every quitting game has
`ε`-equilibria for every `ε`. What blocks the consequence, precisely: (1) the
zero-solo/S.1 and admissible-cycle/S.3 correspondences are proved in one
direction only; (2) S.2 has no located counterpart at all in the
repository's vocabulary; (3) the isolated-negative branch is a per-block
failure diagnostic internal to one specific construction, not a case Simon's
or AGKRS's proofs leave open. A genuine equivalence would need, at minimum, a
formalized min-max/punishment value to even attempt cell S.2, and a
converse argument (general S.3 witness ⟹ some admissible cyclic block) for
cell S.3 that this pass did not find and did not attempt to construct.

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

**Why this matters to us.** [`Program.md`](../Program.md) records as a
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
  ε-equilibria for all multiplayer quitting games; ordinary uniform
  ε-equilibria when the source's derived matrix is **not** a Q-matrix; the
  exact matrix adapter still requires a full-text audit)
- arXiv:2001.03094 — Munk & Solan
- arXiv:1803.00802 — *Jointly Controlled Lotteries with Biased Coins* —
  directly relevant to the frontier's endogenous-lottery item

⚠ arXiv:2201.05148 and arXiv:1301.1967 were **not identified** by any surviving
claim. Treat as unresearched.

**Bibliography hygiene note from verification:** an HTML-rendering fetch of
arXiv:2512.04306 *hallucinated* page numbers (Solan 1999 as 669–694, Solan 2000
as GEB 33:85–96) that the actual PDF contradicts (669–698; GEB 31:245–261).
Prefer `pdftotext` over HTML renderings for bibliographies.
