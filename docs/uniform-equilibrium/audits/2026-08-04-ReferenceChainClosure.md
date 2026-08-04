# Audit, 2026-08-04 — reference-chain closure

> **Standing.** Dated audit record, not a live ledger. Triggered by the Solan
> 2003 case (`3533938` → `371e58d`): two topic-vocabulary literature sweeps
> declared a load-bearing citation "not locatable"; it was found only because
> it is reference [16] of Ashkenazi-Golan–Krasikov–Rainer–Solan (AGKRS). This
> audit runs reference-chain closure — reading the actual reference list of
> every source paper this program leans on — for the first time. It is a
> **first round**: coverage is uneven (below), and a second round is
> recommended, not optional.

## Method

Topic search (keyword sweeps over "quitting", "absorption", "uniform
equilibrium") fails when a relevant paper's title uses none of those words.
Reference-chain search does not: it reads what the papers *this program
already trusts* themselves cite, regardless of vocabulary. For each source
paper: prefer a local PDF (`ephemeral/`, `docs/`), else an arXiv id via the
Atom API or Semantic Scholar's reference-graph endpoint, else a targeted web
search for the published reference list. Every reference recovered this way
was cross-checked against `docs/uniform-equilibrium/references/00-bibliography.md`
and the rest of the wing (`10`–`50`, `SourceCorrections-*`,
`BibliographyMaintenance.md`) plus `ideas/` and `docs/uniform-equilibrium/`
generally, via full-text grep, before being called "unrecorded."

**Trap re-verified, not re-litigated.** `simon-noeq-v1.pdf`
(arXiv:2310.04217, "A Stochastic Game without Approximate Equilibria") is
already correctly handled by
[`2026-08-04-SimonMousetrapRetraction.md`](2026-08-04-SimonMousetrapRetraction.md),
written the same day: withdrawn 14 days after posting, author's comment "The
proof is flawed," and the `arxiv.org/pdf/...` trap is already documented
there. This audit used the paper only as a reference-chain node (its own
citations are real regardless of its retraction) and did not redo that work.

## Scope decision

The wing's ~65 bibliography entries span several sub-programs: zero-sum
uniform value, POMDP/PFA complexity (Q98–Q100), algorithmic
finite-memory equilibrium, proof-assistant formalization, and surveys. The
Solan-2003 case belongs to one cluster — **non-zero-sum existence for
absorbing/quitting games** — and that is where the census's "~20 distinct
results consumed" figure comes from. This audit's closure target is that
cluster: the "Non-zero-sum: existence" and "Non-zero-sum: post-2020" sections
of `00-bibliography.md`, plus Sorin 1986 and Bewley–Kohlberg 1976 (both
named as directly load-bearing in
[`2026-08-04-BorrowedPremiseCensus.md`](2026-08-04-BorrowedPremiseCensus.md)).
That is **25 source papers**. The zero-sum-value, algorithmic-complexity, and
formalization clusters were **not** swept — they are a different program with
their own citation trail, and closing them is future work, not part of this
pass.

## Closure results

| # | Source paper | Reference list obtained? | Method | Refs read |
|---|---|---|---|---|
| 1 | Vrieze & Thuijsman 1989 | No | — | — |
| 2 | Flesch, Thuijsman & Vrieze 1996 | No | — | — |
| 3 | Flesch, Thuijsman & Vrieze 1997 | No | — | — |
| 4 | Solan 1999 | **Yes** | Local PDF — Solan's PhD thesis (`ephemeral/old/_source_eilons_thesis.pdf`), the monograph containing this result | 38 |
| 5 | Vieille 2000a | No | — | — |
| 6 | Vieille 2000b | No | — | — |
| 7 | Vieille 2000c | No | — | — |
| 8 | Solan 2000 (*Absorbing Team Games*) | No | — | — |
| 9 | Solan & Vieille 2001 (*Quitting Games*) | **Yes** | Semantic Scholar reference-graph, DOI `10.1287/moor.26.2.265.10549` | 17 |
| 10 | Solan & Vieille 2002a (*Quitting Games — An Example*) | **Yes** | Local PDF (`ephemeral/old/counterexample-research/sources/quitting-example.pdf`) | 9 |
| 11 | Solan & Vieille 2002b (GEB, correlated equilibrium) | No | — | — |
| 12 | Solan & Vohra 2002 | No | — | — |
| 13 | Simon 2012 | **Yes** | Semantic Scholar reference-graph, DOI `10.1287/moor.1110.0524` | 19 |
| 14 | Solan & Solan 2018/19 (Sunspot) | No | arXiv id known (1803.00878), not fetched — see gaps | — |
| 15 | Solan & Solan 2020 (LCP) | **Yes** | Local PDF (`ephemeral/old/counterexample-research/sources/solan-solan-qmatrix.pdf`, arXiv:1707.02598) | 26 |
| 16 | Munk & Solan 2020 | **Yes** | Semantic Scholar reference-graph, arXiv:2001.03094 | 18 |
| 17 | AGKRS 2022 (*Absorption Paths and Equilibria in Quitting Games*) | **Yes** | Local PDFs — preprint (`absorption-paths.pdf`, arXiv:2012.04369) and published version (`ephemeral/s10107-022-01807-6.pdf`) | 23 |
| 18 | Ashkenazi-Golan, Flesch & Solan (*Absorbing Blackwell Games*) | **Yes** | Semantic Scholar reference-graph, arXiv:2208.11425 | 46 |
| 19 | Hansen, Ibsen-Jensen & Neyman 2023 | No | — | — |
| 20 | Flesch & Solan 2023 | **Yes** (with a caveat — see discrepancies) | Semantic Scholar reference-graph, DOI `10.1016/j.matpur.2023.09.002` | 38 |
| 21 | Solan & Vieille 2025 (arXiv:2512.04306) | **Yes** | Semantic Scholar reference-graph, arXiv:2512.04306 | 24 |
| 22 | Solan & Vieille 2025b (MIMEO, unpublished) | No — cannot be, per the wing's own note | — | — |
| 23 | Jointly Controlled Lotteries (arXiv:1803.00802) | No | arXiv id known, not fetched — see gaps | — |
| 24 | Sorin 1986 | No | — | — |
| 25 | Bewley & Kohlberg 1976 | No | — | — |

**10 of 25 closed (40%), 258 individual references read.** In addition,
three local PDFs adjacent to the program but not themselves wing entries were
fully mined as extra corroborating nodes: Solan 2003's own IGTR paper
(`solan-nash-correspondence-dynamics-value4.pdf`, the Question147 source
itself — 8 refs), Simon's 2016/17 survey *The challenge of non-zero-sum
stochastic games* (`simon-challenge.pdf` — ~28 refs), and Laraki–Solan–Vieille
*Continuous-time Games of Timing* (`continuous-timing.pdf` — 26 refs). Solan
2003's own reference list independently re-confirmed the AGKRS-side finding:
it cites Vrieze & Thuijsman 1989, Mertens–Neyman 1981, Mertens–Sorin–Zamir
1994 (CORE DP 9421, precursor to the 2015 book), Solan 1999, Solan 2000,
Solan & Vieille 1998 (the *Quitting Games* working paper), and Vieille 2000
II — nothing beyond the wing's existing coverage.

## Flagged and unrecorded, ranked

Ranked by strength of relevance signal: directness to this program, and how
many independent closed reference lists corroborate the same citation.
"Corroborated Nx" means N of the 13 closed/mined lists cite it independently.

### Tier 1 — high confidence, directly on-topic

1. **Ashkenazi-Golan, Krasikov, Rainer & Solan, "The APS approach for
   undiscounted quitting games," International Journal of Game Theory 55(1),
   2026. DOI `10.1007/s00182-026-00982-6`.** Not a reference *of* a closed
   paper — it is the apparent publication of AGKRS 2022's own reference [1],
   "Algorithms for Continuous Equilibria in Quitting Games (in preparation)"
   (same four authors, same absorption-path apparatus). Adapts the
   Abreu–Pearce–Stacchetti recursive method to characterize a subset of
   subgame-perfect ε-equilibrium payoffs in **undiscounted** quitting games —
   this is the same author team, the same absorption-path device the LCP wing
   already treats as its hard weight, and the word "undiscounted" verbatim.
   No arXiv preprint found; full text not obtained (paywalled).

2. **Simon, R.S., "The Structure of Non-Zero-Sum Stochastic Games," Advances
   in Applied Mathematics 38(1), 1–26, 2007.** Corroborated 7×: AGKRS
   (preprint and published), Solan & Vieille 2001's own descendant chain via
   Simon 2012, Simon 2012 itself, *Absorbing Blackwell Games*, Munk & Solan
   2020, Solan & Vieille 2025, and both Flesch–Solan 2022 papers. The wing
   already half-knows this: `00-bibliography.md`'s Simon 2012 entry has the
   aside "Simon (2007) is also cited by Solan–Vieille 2025 but was not
   located in this research" — but that is a footnote, not a bibliography
   block, and this audit shows it is the single most cross-cited unrecorded
   paper in the whole closure.

3. **Neyman, A., "Real Algebraic Tools in Stochastic Games," ch. 6 in
   *Stochastic Games and Applications* (NATO Science Series C, vol. 570),
   A. Neyman & S. Sorin (eds.), Kluwer, 2003.** Cited by Flesch & Solan,
   *Equilibrium in Two-Player Stochastic Games with Shift-Invariant Payoffs*
   (arXiv:2203.14492, see discrepancy note below). This is a primary source
   for exactly the gap `BibliographyMaintenance.md` §3.2(e) names — "mathlib
   has no Tarski–Seidenberg and no semialgebraic sets" — in the **same**
   volume the repo already cites one chapter of (Thuijsman's "The Big Match
   and the Paris Match," already `M`).

4. **Takahashi, M., "Equilibrium points of stochastic non-cooperative
   n-person games," J. Sci. Hiroshima Univ. Ser. A-I 28, 95–99, 1964.**
   Corroborated 5×: Solan's PhD thesis, *Absorbing Blackwell Games*, Munk &
   Solan 2020, Solan & Vieille 2025, both Flesch–Solan papers. Always cited
   paired with Fink 1964 (same volume, pages 89–93 immediately before it) —
   Fink is already `M` in the wing as the foundational discounted-equilibrium
   existence citation; Takahashi is its co-published companion and currently
   has zero bibliography presence, only one informal mention
   ("Fink/Takahashi", `50-formalization-status.md:222`) with no citation.

5. **Thuijsman, F. & Raghavan, T.E.S., "Perfect information stochastic games
   and related classes," International Journal of Game Theory 26, 403–408,
   1997.** Corroborated 5×: Solan & Vieille 2002a, Solan's thesis, Solan &
   Vieille 2001, Simon 2012, Flesch & Solan (shift-invariant). Cited by
   *both* Solan–Vieille papers this program treats as central; defines the
   perfect-information subclass that is a natural structural restriction for
   existence arguments.

6. **Solan, E., "Stochastic games with two non-absorbing states," Israel
   Journal of Mathematics 119, 29–54, 2000.** Corroborated 3×: Solan &
   Vieille 2002a, *Absorbing Blackwell Games*, Munk & Solan 2020. **This is a
   different paper from the one already recorded as "Solan 2000"** in
   `00-bibliography.md` (*Absorbing Team Games*, GEB 31:245–261) — confirmed
   distinct by Solan & Vieille 2025's own reference list, which cites
   *Absorbing Team Games* by that title separately. Published in the same
   Israel J. Math. vol. 119 as the Vieille I/II/III trilogy that already
   anchors this program.

### Tier 2 — clearly relevant, less densely corroborated

7. **Mertens, J.-F. & Parthasarathy, T., "Equilibria for Discounted
   Stochastic Games," ch. 10, same NATO 570 volume.** Existence of
   equilibria in discounted stochastic games, by one half of Mertens–Neyman,
   in the volume the repo already partially cites.
8. **Neyman, A., "Existence of the Value and the Minmax," ch. 11, same
   volume.** Cited (as "Stochastic games: Existence of the MinMax") by both
   Munk & Solan 2020 and Solan & Vieille 2025.
9. **Thuijsman, F., "Repeated Games with Absorbing States," ch. 13, same
   volume.** Cited identically by both Munk & Solan 2020 and Solan & Vieille
   2025. **Distinct from ch. 12**, "The Big Match and the Paris Match,"
   which is the repo's existing Thuijsman-2003 record — same author, same
   book, different chapter, easy to conflate with what is already `M`.
10. **Ashkenazi-Golan, Flesch, Predtetchinski & Solan, "Existence of
    equilibria in repeated games with long-run payoffs," PNAS 119(11), 2022.
    DOI `10.1073/pnas.2105867119`.** Corroborated 3×. Nash existence for
    infinitely repeated games with countably many players and long-run
    payoffs — general existence machinery from the same author cluster as
    *Absorbing Blackwell Games*.
11. **Ragel, T., "Weak Approachability of Convex Sets in Absorbing Games,"
    Mathematics of Operations Research 49(3), 1372–1402, 2023. DOI
    `10.1287/moor.2021.0160`.** Cited by Solan & Vieille 2025. Recent,
    directly "absorbing games," extends Flesch–Laraki–Perchet weak
    approachability.
12. **Solan, E. & Vieille, N., "Deterministic multi-player Dynkin games,"
    Journal of Mathematical Economics 39(8), 911–929, 2003. DOI
    `10.1016/s0304-4068(03)00021-1`.** Cited by Solan & Vieille 2001's own
    reference list. Dynkin games are the stopping-game generalization of
    quitting games, same authors as the wing's central *Quitting Games*
    paper.
13. **Shmaya, E., Solan, E. & Vieille, N., "An application of Ramsey's
    theorem to stopping games," Games and Economic Behavior 42, 300–306,
    2003.** Cited by Solan & Vieille 2001. A genuinely different proof
    technique (Ramsey theory) applied to the stopping-game existence
    question.
14. **Flesch, J., Kuipers, J., Mashiah-Yaakovi, A., Schoenmakers, G., Shmaya,
    E., Solan, E. & Vrieze, K., "Non-existence of subgame-perfect
    ε-equilibrium in perfect information games with infinite horizon,"
    International Journal of Game Theory 43(4), 945–951, 2014.** Cited by
    Flesch & Solan (shift-invariant, 2022 preprint). A **negative** result —
    belongs next to `30-counterexamples.md`'s territory — with Solan among
    seven authors.
15. **Flesch, J. & Solan, E., "Equilibrium in Two-Player Stochastic Games
    with Shift-Invariant Payoffs," arXiv:2203.14492 (28 Mar 2022).** See the
    discrepancy note below — this is a **distinct paper** from the already-
    recorded Flesch & Solan 2023 (arXiv:2208.12096, *Stochastic Games with
    General Payoff Functions*), five months apart, two-player vs. multiplayer
    scope.
16. **Ashkenazi-Golan, Flesch, Predtetchinski & Solan, "Regularity of the
    minmax value and equilibria in multiplayer Blackwell games," Israel
    Journal of Mathematics, DOI `10.1007/s11856-024-2679-9` (2022 preprint /
    2024 journal issue).** Companion to the already-tracked *Absorbing
    Blackwell Games* (arXiv:2208.11425), same author cluster.
17. **Attia, L. & Oliu-Barton, M., "A formula for the value of a stochastic
    game," PNAS 2018.** Corroborated 3×. Oliu-Barton is already `—` in the
    wing for the 2014 elementary Bewley–Kohlberg reproof; this is a
    zero-sum-value follow-on by the same author.

### Tier 3 — plausibly relevant, single-source or more tangential

18. Flesch, Schoenmakers & Vrieze, "Stochastic Games on a Product State
    Space," Mathematics of Operations Research 33, 403–420, 2008, and its
    companion "…the Periodic Case," International Journal of Game Theory 38,
    263–289, 2009 — corroborated 4× combined (AGKRS, *Absorbing Blackwell
    Games*, Flesch & Solan 2022×2).
19. Sorin, S. & Vigeral, G., "Limit optimal trajectories in zero-sum
    stochastic games," Dynamic Games and Applications 10, 555–572, 2020 —
    cited by AGKRS's own published reference list; "limit optimal
    trajectories" is a zero-sum analogue of "absorption paths."
20. Vieille, N., "Weak approachability," Mathematics of Operations Research
    17, 781–791, 1992 — cited by AGKRS's published reference list.
21. Sobel, M.J., "Noncooperative Stochastic Games," Annals of Mathematical
    Statistics 42(6), 1930–1935, 1971 — cited in Solan's thesis; early
    existence-adjacent foundational paper predating Vrieze–Thuijsman.
22. Vieille, N., "On Equilibria in Undiscounted Stochastic Games," Discussion
    Paper 9446, CEREMADE, 1994 — cited in Solan's thesis. Title is exactly
    on-topic and this is very likely a direct precursor to the Vieille 2000
    a/b/c trilogy; probably hard to obtain (unpublished DP).
23. Vieille, N., "Solvable States in Stochastic Games," International
    Journal of Game Theory 21, 395–404, 1993 — cited in Solan's thesis.
24. Thuijsman, F., "Optimality and Equilibria in Stochastic Games," CWI Tract
    82, Center for Mathematics and Computer Science, Amsterdam, 1992 —
    Thuijsman's own PhD monograph, the structural analogue of Solan's thesis;
    cited in Solan's thesis.
25. Simon, R., Spiez, S. & Toruńczyk, H., "Equilibrium existence and topology
    in some repeated games with incomplete information," 2002 — cited by
    Simon 2012's own reference list; topological existence methodology
    directly analogous to Simon's own approach.
26. Solan, E. & Vohra, R., "Correlated Equilibrium in Quitting Games,"
    Mathematics of Operations Research, 2001 — appears as a citation
    **distinct** from the already-recorded Solan & Vohra 2002 (IJGT) in two
    independent Semantic Scholar extractions (*Absorbing Blackwell Games*
    and Munk & Solan 2020). Flagged with an explicit caution: this could be
    a genuine early/working-paper version, or a Semantic Scholar database
    duplicate of the 2002 paper — **not primary-verified either way**.
27. Flesch, J., Herings, J.-J., Maes, J. & Predtetchinski, A., "Subgame
    Maxmin Strategies in Zero-Sum Stochastic Games with Tolerance Levels,"
    Dynamic Games and Applications, 2018 — cited by Flesch & Solan
    (shift-invariant).
28. Mashiah-Yaakovi, A., "Correlated Equilibria in Stochastic Games with
    Borel Measurable Payoffs," Dynamic Games and Applications, 2015 — cited
    by Flesch & Solan (shift-invariant).
29. Laraki, R., Maitra, A. & Sudderth, W., "Two-Person Zero-Sum Stochastic
    Games with Semicontinuous Payoff," Dynamic Games and Applications, 2012
    — cited by Flesch & Solan (shift-invariant).
30. Rogers, P.D., "Non-Zerosum Stochastic Games," PhD thesis, Operations
    Research Center report ORC 69-8, University of California, Berkeley,
    1969 — cited in Solan's thesis; earliest non-zero-sum stochastic-game
    existence attempt found in this sweep, likely hard to obtain.
31. Laraki, R., Solan, E. & Vieille, N., "Continuous-time Games of Timing,"
    Journal of Economic Theory 120(2), 206–238, 2005 — local PDF present
    (`ephemeral/old/counterexample-research/sources/continuous-timing.pdf`),
    never processed into the wing. Same author trio as *Quitting Games*;
    adjacent timing/Dynkin-game research cluster, not itself about quitting
    games.
32. Simon, R.S., "The challenge of non-zero-sum stochastic games,"
    International Journal of Game Theory 46(1), 191–204 (year given as both
    2016 and 2017 across sources — see discrepancy note), 2016/17 — local
    PDF present (`ephemeral/old/counterexample-research/sources/simon-challenge.pdf`),
    never processed. A survey/open-problems paper directly on this program's
    subject; its own reference list supplied several of the items above.
33. Maitra, A. & Sudderth, W. — cluster of Borel/general-state-space
    stochastic-game papers (1991 "Borel Stochastic Games with Lim Sup
    Payoff"; 1993 "Borel Stochastic Games with Lim Sup Payoff" [sic,
    corroborated 2×]; 1998 "Finitely additive stochastic games with Borel
    measurable payoffs," IJGT 27, 257–267; 2003 "Stochastic Games with Borel
    Payoffs," NATO 570 ch. 24) — corroborated 4× combined across the
    withdrawn-paper's own references, Simon's challenge paper, *Absorbing
    Blackwell Games*, and Flesch & Solan. General-state-space theory is
    somewhat tangential to this repo's finite-state model, hence Tier 3
    despite the corroboration count.
34. Gobbino, M. & Simon, R.S., "How many times can a function be iterated?"
    — technical tool paper underlying "Discrete Viability Theory" (itself
    cited by AGKRS as "in preparation," never independently verified as
    published). Year discrepancy across sources: Simon 2012's own list gives
    2009 (likely the arXiv/working-paper date); Simon's challenge paper
    gives 2013 (likely Journal of Difference Equations and Applications,
    the eventual venue) — see discrepancy note.

## Citation discrepancies found in passing

Per the task's own trap warning (the repo's census already flags the IGTR
volume/year issue), here is what independent sources actually say, without
normalizing:

- **Solan 2003 IGTR year and end page.** The repo's own bibliography says
  "3, 291–300." AGKRS's own published reference list [16] says "3, 291–300
  **(2003)**." Simon's 2016/17 challenge paper's reference list says
  "International Game Theory Review 3(4), pp. 291–**299**," dated
  "**(2001)**." Simon 2012's Semantic-Scholar-extracted reference list also
  gives "(2001)," venue "IGTR." The primary preprint held locally
  (`solan-nash-correspondence-dynamics-value4.pdf`) is itself dated "January
  25, 2001" on its title page. **Majority of independent evidence — the
  repo's own prior finding, Simon 2016/17, Simon 2012's citation, and the
  primary preprint's own dateline — points to 2001; AGKRS 2022's "(2003)" is
  the outlier**, not the repo.
- **Solan & Vieille 2002a's year.** Cited as 2002 everywhere checked
  (matching the published header "Int J Game Theory (2002) 31:365–381," read
  directly from the local PDF) **except** Simon's 2016/17 challenge paper,
  whose reference list gives "(2003)." This looks like an error in Simon's
  paper, not in this repository's records.
- **Flesch & Solan 2023 / "shift-invariant payoffs" title conflict.**
  `00-bibliography.md` records DOI `10.1016/j.matpur.2023.09.002` under the
  title "Stochastic games with general payoff functions." A Semantic
  Scholar reference-graph query against that exact DOI returned the paper's
  title as "Equilibrium in Two-Player Stochastic Games with Shift-Invariant
  Payoffs." A direct arXiv Atom API check resolved this: **these are two
  distinct papers** — arXiv:2208.12096 (25 Aug 2022, "Stochastic Games with
  General Payoff Functions," multiplayer, matches the repo's title and is
  almost certainly the paper behind the JMPA DOI) and arXiv:2203.14492 (28
  Mar 2022, "Equilibrium in Two-Player Stochastic Games with Shift-Invariant
  Payoffs," two-player only, unrecorded — Tier 2 item 15 above). Semantic
  Scholar's DOI-keyed metadata appears to have merged or mis-attributed the
  two records; the repo's own bibliography title is correct, but this is
  worth knowing before trusting that DOI lookup again.
- **Gobbino–Simon "How many times can a function be iterated?" year.** 2009
  per Simon 2012's own reference list, 2013 per Simon's challenge paper's
  reference list. Not resolved in this pass — flagged as Tier 3 item 34.

## What could not be checked, and why

- **15 of the 25 core source papers (60%) have no reference list obtained**
  in this pass: Vrieze & Thuijsman 1989, FTV 1996, FTV 1997, Vieille
  2000a/b/c, Solan 2000 (*Absorbing Team Games*), Solan & Vieille 2002b
  (GEB), Solan & Vohra 2002, Solan & Solan 2018/19, Hansen–Ibsen-Jensen–Neyman
  2023, Solan & Vieille 2025b, Jointly Controlled Lotteries, Sorin 1986,
  Bewley & Kohlberg 1976. Reason in each case: pre-2000s MOR/IJGT/GEB/Annals
  papers predate the arXiv-common era for this literature and are paywalled
  with no local copy in the repository; a few (Solan & Solan 2018/19,
  Jointly Controlled Lotteries) **do** have known arXiv ids but were not
  fetched in this pass purely on time/tool-call budget, not unavailability —
  these are the cheapest continuation points for a second round.
- **Semantic Scholar's reference-graph endpoint began returning HTTP 429**
  partway through this session, capping how many additional DOI/arXiv
  lookups were attempted. This is why the above 12 gaps were not closed by
  the same method that worked for the 10 that were.
- **The NATO 570 volume's other chapters** (2, 3, 4, 5, 7, 8, 9, 14 — Neyman,
  Sorin, Vrieze, Nowak, Mertens contributions on Markov-chain methods,
  classification, discounted finite-case theory, Borel state spaces,
  measurable selection, and the orderfield property) were identified by
  title only, via one secondary web-search summary of the table of contents,
  and not read. Chapters 6, 10, 11, 13 (Tier 1/2 above) are the ones with a
  title specific enough to judge directly relevant; the rest are left
  unjudged rather than guessed at.
- **AGKRS's own 2026 sequel** (Tier 1, item 1) is paywalled; only its
  abstract was obtained (via a publisher metadata fetch), not its reference
  list or body. If it turns out to bear on the LCP wing's open questions,
  that is a follow-up in its own right, separate from this citation-closure
  pass.
- **The zero-sum-value, algorithmic-complexity (Q98–Q100), and
  formalization-landscape clusters of the wing were not swept at all** — see
  Scope decision above. Their citation graphs are unexamined by this audit.

## Bottom line

Reference-chain closure surfaced **34 flagged items** across three
confidence tiers from **258 references read across 13 reference lists**
(10 wing source papers plus 3 adjacent local-PDF papers). The single
strongest, most-corroborated finding is Simon 2007's *Structure of
Non-Zero-Sum Stochastic Games* (cited by 7 of 13 closed lists and already
half-acknowledged in the wing as "not located"). The single most
program-relevant finding is the apparent 2026 publication of AGKRS's own
promised follow-up algorithm paper, on undiscounted quitting games, by the
same four authors. Closure is **not complete**: 60% of the scoped source
papers' own reference lists remain unread, for reasons that are mostly
budget (arXiv ids already in hand) rather than unavailability, so a second
round is recommended before treating this cluster's citation graph as
closed.
