# What is actually open

The precise status of the problem stated in
`GameTheory/Concepts/Stochastic/UniformExistenceConjecture.lean` (`exists_uniformDeviationCapConstructor`), as of 2026-08-02.

---

## The headline

`[primary]` **Still open.** The most recent authoritative statement is by Solan
and Vieille themselves, December 2025 — verified verbatim from the arXiv PDF
via `pdftotext` (not a summarizer), arXiv:2512.04306v1, line 10:

> One of the main open problems in game theory to date is whether every
> multiplayer stochastic game admits an undiscounted equilibrium payoff. This
> open problem was answered affirmatively for two-player zero-sum games
> (Mertens and Neyman (1981)), for two-player non-zero-sum games (Vieille
> (2000a,b)), and for various classes of stochastic games with more than two
> players (see, e.g., Solan (1999); Solan and Vieille (2001), Simon (2007,
> 2012), Flesch et al. (2007, 2008, 2009), and Solan et al. (2020)).

Note "**various classes**", not "all games".

## The lattice

| Players | Absorbing | General stochastic |
|---|---|---|
| `n = 2`, zero-sum | ✔ Kohlberg 1974 | ✔ Mertens–Neyman 1981 |
| `n = 2`, non-zero-sum | ✔ Vrieze–Thuijsman 1989 | ✔ Vieille 2000 (I + II) |
| `n = 3` | ✔ Solan 1999 | **OPEN** |
| `n ≥ 4` | **OPEN** — open even for *quitting* games | **OPEN** |

Independent confirmations at four levels of the hierarchy, all `[primary]`:

- **PNAS 2015** (Solan–Vieille survey): "The question in its most generality
  remains open."
- **arXiv:2208.11425** (Ashkenazi-Golan, Flesch & Solan): four-plus-player
  average-payoff absorbing games are "a major open problem in game theory to
  date". Verbatim: "The existence of an ε-equilibrium, for every ε > 0, in
  two-player and three-player average-payoff absorbing games was proven by
  Vrieze and Thuijsman (1989) and Solan (1999), respectively. The question
  whether average-payoff absorbing games with at least four players always
  admit an ε-equilibrium … is a major open problem in game theory to date."
- **arXiv:2001.03094** (Munk–Solan): "To date it is not known whether every
  four-player absorbing game admits a uniform ε-equilibrium, for every ε > 0."
- **arXiv:2012.04369** (Ashkenazi-Golan, Krasikov, Rainer & Solan): "Whether
  every quitting game admits an ε-equilibrium for every ε > 0 is an open
  problem." Same in Solan–Solan arXiv:1707.02598: "To date it is not known
  whether four-player quitting games admit ε-equilibria for every ε > 0."

The absorption-path paper does not currently remove this open cell. Its
printed discrete sequential-perfection clause omits sure terminal jumps,
although its path class permits them; the theorem proof does not visibly
repair the omission. A naïve all-jumps test against continuation zero is also
wrong because it erases credible off-path punishment. The exact source audit
and two candidate repairs were recorded in the historical intake note
`ephemeral/reviews/Review07-AbsorptionPathTerminalJumpConvention.md`.
Accordingly, the four-player path-or-barrier search remains a discriminant,
not an imported equivalence theorem.

**Even `n = 3` general stochastic games are open.** Solan (2025) records that
his own 1999 three-player absorbing theorem "has so far resisted extension to
stochastic games". So the gap between the two right-hand cells at `n = 3` is
real and acknowledged.

## What closed, and at what price

The problem *is* solved at every `n` if you weaken the solution concept:

| Relaxation | Result | Citation |
|---|---|---|
| Autonomous correlated equilibrium | **all** `n`-player finite stochastic games | Solan–Vieille, GEB 38(2):362–399, DOI `10.1006/game.2001.0887` |
| Normal-form correlated equilibrium | **all** multiplayer absorbing games | Solan–Vohra, IJGT 31:91–121, DOI `10.1007/s001820200109` |
| Sunspot ε-equilibrium | positive recursive **general quitting** games | Solan–Solan, arXiv:1803.00878 |

**This is the sharpest available statement of what the open problem costs.**
The entire `n ≥ 3` difficulty is the cost of manufacturing correlation from
observed play rather than being handed a device. [`Program.md`](../Program.md)
already forbids a free public lottery as a modelling decision; the correlated
theorems say exactly what that decision is worth. The frontier's "endogenous
jointly controlled lotteries" portfolio item is therefore not one idea among
many — it is, in a precise sense, *the* difference between a solved and an open
problem. This framing is stronger than what the frontier currently states.

## Post-2020 movement

`[primary]` **Solan–Vieille, arXiv:2512.04306v1 (3 Dec 2025)**, Theorem 2.8:
every **positive recursive absorbing** game with an arbitrary finite player set
and **no rectangular connected component** of nonabsorbing action profiles
admits an undiscounted (hence, by Remark 2.9, uniform) equilibrium payoff. Full
definitions in [`20-nonzero-sum-equilibrium.md`](20-nonzero-sum-equilibrium.md).

The authors' own positioning: "our result delineates where the main difficulty
in establishing [existence in] recursive absorbing games lies. The
non-rectangularity condition identifies a large, easily checkable class of
games for which the equilibrium problem is now resolved."

**Section 5 bounds it honestly.** Combining with Solan–Solan (2021) to cover a
rectangular component is something the authors "do not know how to prove";
non-positive, non-recursive, and multi-nonabsorbing-state extensions are stated
open.

⚠ Unrefereed preprint as of 2026-08-02.

**Relevance to this program.** Rectangularity of the nonabsorbing component is
a *combinatorial* condition on the action-profile graph — cheap to state,
cheap to check, and of exactly the shape this program keeps looking for in its
gate layer. It is a live candidate for a Lean predicate, independent of whether
the theorem is formalized. That it is the boundary of the newest published
progress makes it worth understanding before designing further gates.

---

## Internal Q96--Q100 status — not external literature

This subsection is a repository ledger, not a claim that the following
question answers are published results. The evidence markers above do not
transfer from a cited ingredient to our derived theorem.

- **Q96: corrected theorem answered; counterexample Lean-formalized.** The
  unconditional four-test occupation formulation is false because a
  prescribed recurrent class can lie outside a particular player's unilateral
  arena. Commit `68149dd` checks the two-player/two-node escaped-class example,
  including its linear delivery failure and Poisson impossibility. The exact
  split-domain gain--bias converse, recurrent-coverage alternative, and fifth
  obstruction extraction remain open formalization work.

- **Q97: answered and internally checked; partially Lean-formalized.** The exact
  finite Flesch--Thuijsman--Vrieze calculation proves that every reduced live
  architecture delivering `(1,2,1)` has at least three phases, and that the
  named three-phase architecture is unique at the fixed phase origin. It also
  separates supportwise approximate complementarity (qualitative stability)
  from probability-weighted regret (an explicit instability family). This
  closes the question-corpus item, but it is our symbolic argument, not a
  theorem extracted from the 1997 paper. The actual FTV game, ten-node cyclic
  architecture, four sufficient-condition checks, and ledger/punishment/
  adaptive consumers are landed in Lean at `8090347`; the sharp modulus,
  necessity, period-three lower bound, and rigidity are not.

- **Q98: answered source-conditionally; not Lean-formalized.** The answer
  concludes that the unbounded finite-public gain--bias synthesis language is
  recursively enumerable complete, so no total computable per-input node
  bound exists. Its external premise is Ummels's thesis Theorem 4.13, whose
  14-player `FinNE`/`FinSPE` halting reduction is stated with an explicit
  **proof sketch**. The graph trimming, all-node completion, terminal-reward
  gain--bias/finite-state-SPE bridge, gate reduction, and exact-target
  compensation gadget are repository arguments. They have not been
  externally sourced, independently reconstructed down to every reduction
  gadget, or formalized in Lean. Until that audit lands, Q98 is a
  source-conditional internal result, not a new `[primary]` literature fact.

- **Q99: core threshold/certificate boundary audited; appended
  historywise/clock answer awaits review.** It asks only for verification of one supplied
  rational homogeneous private-controller profile; it does not ask for
  synthesis or strategy-class completeness. Under its independent-memory and
  complete-public-action semantics, the posterior filter stays a product of
  marginal memory beliefs, but those beliefs may range over a continuum.
  Rosenberg--Solan--Vieille (2002), Theorem 1, gives convergence and one
  behavior strategy uniformly near-optimal at all sufficiently long horizons;
  Chatterjee--Saona--Ziliotto (2022), Theorem 2.9, gives arbitrarily good
  deterministic finite-memory strategies.

  A separately audited repository reduction embeds a rational PFA in one
  opponent's hidden controller memory using one public state and an absorbing
  public acceptance bit. It respects simultaneous-action timing, and with one
  opponent the product-filter restriction is vacuous. Hence the finite-memory
  upper bounds are sharp: \(L>c\) is \(\Sigma^0_1\)-complete,
  \(L\le c\) is \(\Pi^0_1\)-complete, \(L\ge c\) and equality are
  \(\Pi^0_2\)-complete, and \(L<c\) is \(\Sigma^0_2\)-complete. The
  combined delivery-and-cap predicate is already \(\Pi^0_1\)-complete at a
  fixed positive tolerance, and an exact-delivery Safe-action variant gives
  the exact-cap lower bound. Rote (2025), Theorem 1(a), supplies a seven-state,
  four-letter PFA calibration at cutpoint \(1/7\); the conversion to two
  players, one public state, nine opponent memories, five deviator actions,
  and two opponent actions is an audited upper bound, not a minimality result.

  Strict rejection has a finite deterministic-transducer plus rational
  recurrent-class certificate. Since cap acceptance is co-r.e.-complete, it
  cannot have a sound-and-complete recursively enumerable family of finite
  rational or algebraic acceptance certificates. The fully observed gain--bias
  problem remains a sound but necessarily incomplete acceptance relaxation.
  The PFA embedding and these derived classifications are internal, not
  external literature theorems and not Lean-formalized.

  The appended answer further claims a \(\Pi^0_1\)-complete repaired
  historywise predicate, preservation for explicitly ultimately periodic
  clocks, and \(\Pi^0_3\)-complete verification for a fixed total
  primitive-recursive clock language. Those additions are not yet independently
  sealed: Review 01 checks the core bridge and hierarchy, while Review 02 checks
  the common-modulus and clock quantifiers. The exact DFA-on-`bin(t)` boundary
  remains open. Exact attainment; finite-memory attainment; the requested
  observation-stationary and represented belief-stationary distinctions; tight
  delivery complexity; sharp decidable subclasses; and computable
  \(\eta\)-optimal memory bounds in the restricted product-filter class remain
  unanswered or insufficiently justified. General-POMDP no-memory-bound results
  do not by themselves settle that restricted-class memory question. No
  conclusion from Q98's existential public-controller synthesis language
  settles any of these supplied-profile questions.

- **Q100: posed; correlated existence is external, endogenous implementation
  is open.** Solan--Vieille (2002), Theorem 2.3, gives every finite
  multiplayer stochastic game a uniform autonomous correlated-equilibrium
  payoff. Q100 isolates the gap to ordinary Nash play as implementation of
  the device through the original game's public actions and independent
  private randomization. The device is richer than a public coin: the general
  construction uses private current recommendations and one-stage-delayed
  disclosure. Fresh contingent tables are independent across dates, and the
  ordinary punishment ignores the continuing device signals. No universal
  compiler or selectorwise nonimplementation theorem is claimed. Q100 gives a
  finite witnesswise target separator, with its scalar core partially
  Lean-formalized, but that does not rule out retargeting. A universal
  compiler would settle the general finite-player ordinary uniform-equilibrium
  existence problem.

---

## Loose ends — things this research could NOT resolve

These are honest gaps in the citation record, not settled negatives.

1. **The textbook statements of open status were never reached.** Solan, *A
   Course in Stochastic Game Theory* (Cambridge 2022), the Laraki–Sorin
   handbook chapter, and the Jaśkiewicz–Nowak survey were all commissioned and
   none was reached by a surviving claim. The open-status finding above rests
   on primary preprints and PNAS 2015 rather than on a textbook. Worth fixing:
   a textbook citation is the right thing for the manuscript's introduction.

2. **arXiv:2201.05148 and arXiv:1301.1967 were never identified.** Both were
   commissioned; no surviving claim covers them. Treat as unresearched.

3. **The Solan–Vieille (2002) Figure 2 numerical discrepancy is unresolved.**
   The relevant source is *Quitting Games--An Example*, IJGT **31**(3),
   365--381, DOI `10.1007/s001820200125`, not the 2001 MOR paper. The final
   article is author-hosted; source availability is no longer the blocker.
   The printed `√2` period-2 packet in the final IJGT text fails the current
   independent recomputation. Resolving whether this is a source typo, a
   transcription error, or a convention mismatch requires another direct
   audit of the author-hosted final PDF and the exact table—not a MOR source.
   The source-stable qualitative `n = 4` propositions do not require those
   constants.

4. **Definable/o-minimal and Blackwell-game routes to `n ≥ 3` were requested
   but never surfaced** beyond the bare mention of *Absorbing Blackwell Games*
   (arXiv:2208.11425). Given that Bewley–Kohlberg's zero-sum proof *is* a
   semi-algebraic definability argument, and that this repository has built a
   large curve-selection apparatus, whether anyone is pursuing an o-minimality
   route for non-zero-sum `n`-player existence is a question worth a dedicated
   pass.

5. **Full texts never read** (paywalled): Vieille 2000 a/b/c, Vrieze–Thuijsman
   1989, Solan 1999, Simon 2012. Abstract-level statements only. For
   the 2001 MOR *Quitting Games* and 2002 GEB correlated-equilibrium papers,
   the verified text is the 1998 Northwestern CMS-EMS working papers (DP 1227
   and DP 1226), not the published articles—theorem numbering could have
   shifted in copy-editing, though published
   abstracts match in substance.

6. **Verification ran out of search budget.** Sessions repeatedly exhausted
   their WebSearch quota, so adversarial contradiction-hunting was done by
   targeted fetches of Crossref/OpenAlex/Semantic Scholar/Unpaywall/author PDFs
   rather than open web search. A broad "is this disputed" sweep was never run
   for any result.
