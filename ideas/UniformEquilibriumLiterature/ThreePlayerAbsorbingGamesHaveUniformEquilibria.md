# Three-player absorbing games have uniform equilibria

| Field | Value |
| --- | --- |
| Citation of record | Solan, *Three-Player Absorbing Games*, MOR 24(3):669–698 (1999), DOI `10.1287/moor.24.3.669` |
| Source confidence | `PRIMARY_FULLTEXT` on the author's doctoral dissertation (Section 4, refereed by MOR's own referees per its Acknowledgments — see below); the MOR-typeset journal PDF itself remains unread (paywalled). Upgraded 2026-08-04 from `SECONDARY_VERIFIED` with primary text unread. |
| Mathematical status | `PROVED` externally |
| Repository / Lean status | `RECORDED / NONE` |
| Exact scope and quantifiers | Every three-player absorbing game (general-sign non-absorbing and absorbing payoffs, no positivity/recursive restriction) admits a **uniform** equilibrium payoff. Quitting games are a literal special case (continue/quit action sets), so this covers three-player quitting games with negative payoffs unconditionally. |
| Adapter | Source states/actions/evaluation and any perturbation/reduction hypotheses require adapter work before a Lean import; the dissertation's exact definitions (Section 3, "perturbed equilibrium payoff") are now available for that adapter. |
| Lean destination | none nominated before source/interface decomposition |
| Consumer | Sharp positive island below the four-player fallback-collapse fence; LCP `C1`'s induction base case; `InvertedCounterexampleSearch`'s `K1`; the case-2 carrier's non-vacuity argument |

The theorem does not settle three-player stochastic games with several live
states. Its role is a literature boundary and possible architecture source,
not a current formalization priority.

## The undiscounted/uniform question — resolved

The published INFORMS/Crossref abstract says the paper proves an
**undiscounted** equilibrium payoff exists — the *a priori* weaker of the two
notions in this program's terminology table, and the general equivalence
recorded elsewhere in this wing (arXiv:2512.04306, Remark 2.9) holds only for
*positive recursive* absorbing games, a class three-player quitting games
with negative payoffs need not fall into. This file previously carried the
gap unresolved. It is now closed by three independent Solan-authored
sources, fetched, quoted, and cross-checked 2026-08-04 — full text at
[`20-nonzero-sum-equilibrium.md`](../../docs/uniform-equilibrium/references/20-nonzero-sum-equilibrium.md#n--3-absorbing--settled-solan-1999):

1. **The decisive source: Solan's own doctoral dissertation**
   (`ephemeral/old/_source_eilons_thesis.pdf`, 97 pp., Center for the Study
   of Rationality, Hebrew University of Jerusalem, advisor A. Neyman,
   Nov 1998). Its Acknowledgments name three anonymous MOR referees whose
   comments "substantially improved the presentation of the results in
   section 4" — i.e. Section 4 *is* the material that became the MOR 1999
   paper. Section 4.7's **Theorem 4.23**: "Every three-player repeated game
   with absorbing states has a perturbed equilibrium payoff," proved in full
   (not sketched) from six earlier lemmas. Definition 3.9 gives "uniform
   `x`-perturbed equilibrium payoff" and "perturbed equilibrium payoff" as
   literal synonyms, and the chapter's own stated global convention reads:
   "whenever we write equilibrium payoff... we mean the uniform equilibrium
   payoff." Applying that convention to Theorem 4.23 verbatim gives: every
   three-player absorbing game has a **uniform** equilibrium payoff — no sign
   or positivity hypothesis anywhere.
2. **Solan's own 1999 conference exposition** (*Uniform Equilibrium: More
   Than Two Players*, dated the same year, published NATO Sci. Ser. C 570,
   2003) states "**Theorem 2.1 (Solan, 1999)** Every three-player absorbing
   game admits a **uniform** equilibrium payoff" and gives an actual proof
   sketch using the vanishing-discount-factor / Puiseux technique — the
   technique that *produces* the uniform notion directly, not one that proves
   undiscounted and upgrades it afterward. No sign or positivity hypothesis
   appears anywhere in the statement or the sketch.
3. **Munk–Solan (arXiv:2001.03094)**, verified live (not withdrawn; single
   version v1) and re-extracted from the PDF, restates twice, as an
   unqualified general background fact: "Solan (1999) proved the existence of
   a uniform ε-equilibrium in three-player absorbing games."

Given all three, the `n ≤ 3` claim as this repository uses it (uniform, not
merely undiscounted) is **supported**, at `PRIMARY_FULLTEXT` confidence on
the dissertation. The Munk–Solan bridge that earlier revisions of this file
leaned on was never actually load-bearing on its own — Solan's own
contemporaneous proof (sketch in the 1999 conference chapter, full in the
dissertation) is the direct evidence, and neither requires a "positive
recursive" restriction.
