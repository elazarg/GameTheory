# Known results: the external literature of record

This directory is the project's **citation of record** for results that already
exist in the published literature. It answers one question: *what is known, by
whom, in exactly what form, and how does this repository relate to it?*

It is deliberately separate from mutable working state:

- `ephemeral/UniformEquilibriumCurrentFrontier.md` records **our** theorem boundary and
  working hypotheses;
- `questions/` records **our** self-contained mathematical questions;
- this directory records **other people's theorems**, with durable citations,
  so that no route is re-derived by accident and no known obstruction is
  rediscovered the hard way.

Companion file: [`ephemeral/MISSING.md`](../../../ephemeral/MISSING.md) — the gap list, i.e. known
results that this repository does *not* yet record, formalize, or consume.

## Files

| File | Contents |
|---|---|
| [`00-bibliography.md`](00-bibliography.md) | Durable citations (author, year, venue, DOI/arXiv), one block per work |
| [`10-zero-sum-value.md`](10-zero-sum-value.md) | Zero-sum uniform **value** results and their exact hypotheses |
| [`20-nonzero-sum-equilibrium.md`](20-nonzero-sum-equilibrium.md) | Non-zero-sum uniform **equilibrium** existence results |
| [`30-counterexamples.md`](30-counterexamples.md) | Counterexamples and benchmarks that constrain any proof |
| [`40-open-status.md`](40-open-status.md) | What is actually open, and post-2020 movement |
| [`50-formalization-status.md`](50-formalization-status.md) | This repo's Lean coverage, plus the external proof-assistant landscape |

## Evidence conventions

Every statement carries one of these markers. They are about **our confidence
in the citation**, not about the quality of the result.

| Marker | Meaning |
|---|---|
| `[primary]` | The theorem statement was read in the paper itself (arXiv/PDF/published text) |
| `[abstract]` | Only the published abstract was readable (paywall or scan without a text layer); in-paper theorem numbers unknown |
| `[secondary]` | Verified via a survey/tutorial restatement, not the original |
| `[unverified]` | Recorded from memory or a search summary; **not** checked against a source. Treat as a lead, not a fact |

Where a claim was checked and found wrong, it is recorded under a `REFUTED`
heading rather than deleted. Same discipline as the no-go files in
`GameTheory/Concepts/Stochastic/`: a killed claim is a permanent result.

## Repository-status markers

Each result also carries how this repository currently stands with respect to
it:

| Marker | Meaning |
|---|---|
| `L` | A checked Lean declaration exists here (file and name given) |
| `L~` | A **conditional** or partial Lean declaration exists (named hypotheses, or a restricted instance) |
| `T` | Tracked in a planning file (frontier, manuscript, question corpus, README) but not formalized |
| `—` | Not recorded anywhere in this repository |

These are the same seals as `UniformEquilibriumProgram.md` uses (`M`/`L`/`A`/`C`)
restricted to what is relevant here: whether *someone else's* theorem is
represented in our tree.

## Provenance

Assembled 2026-08-02 from three adversarially-verified deep-research passes
(claims fetched from primary sources, then killed unless they survived a 2-of-3
refutation vote), reconciled against `latex/references.bib`, the manuscript
bibliography in `UniformEquilibriumFrontierManuscript.tex`, and a direct
inspection of the Lean tree and the vendored mathlib checkout.

Pass 1 covered the zero-sum uniform value; pass 2 the non-zero-sum existence
results, open status, and post-2020 frontier; pass 3 Sorin's 1986 example and
the proof-assistant landscape. Roughly 13M subagent tokens across 316 agents;
9 claims were refuted in verification and are recorded as such rather than
dropped.

Where the research could not reach a source, the file says so. Notably: the
Mertens–Neyman and Kohlberg full texts were never read, Sorin's numbers were
never cross-checked against a textbook, and the Lean-side formalization sweep
did not survive verification (the mathlib facts in
[`50-formalization-status.md`](50-formalization-status.md) come from direct
inspection instead, which is stronger). The complete list of such gaps is in
[`ephemeral/MISSING.md`](../../../ephemeral/MISSING.md) §5.

**Targeted addendum, 2026-08-02.** The Q98 audit directly read the
Ummels--Wojtczak LMCS paper (arXiv:1109.4017) and Ummels's thesis around
Theorem 4.13. The bibliography records the exact split: the peer-reviewed
paper states 14-player `FinNE`/`PureFinNE`, the thesis also states
`FinSPE`/`PureFinSPE`, and both presentations label the decisive reduction a
proof sketch. Repository bridges built on that source retain a separate
internal, non-formalized status.

The Q99 audit directly read Rosenberg--Solan--Vieille (2002), Theorem 1,
resolving the previously missing DOI as `10.1214/aos/1031689022`, and
Chatterjee--Saona--Ziliotto (2022), Theorem 2.9 and Remarks 2.1--2.2. Together
they give the common expected-average value and deterministic finite-memory
approximation, not an exact optimizer or effective approximation threshold.
The audit also read Rote (2025), Theorem 1(a), and the PFA complexity
restatement in Chadha--Sistla--Viswanathan (2018). A separate elementary
repository embedding now transfers those PFA threshold facts while respecting
Q99's simultaneous-action and full-public-action semantics. It yields
\(L>c\) as \(\Sigma^0_1\)-complete, \(L\le c\) as
\(\Pi^0_1\)-complete, \(L\ge c\) and \(L=c\) as
  \(\Pi^0_2\)-complete, and \(L<c\) as \(\Sigma^0_2\)-complete, together
  with the finite-rejection/no-complete-enumerable-acceptance-certificate split.
  The embedding and hierarchy transfer are internal and not Lean-formalized.
  Q99's appended answer adds candidate repaired-historywise and effective-clock
  classifications; `ephemeral/reviews/Review01-*` and `Review02-*` are the
  designated independent checks before those additions inherit the core
  audit's status. Exact attainment, stationary distinctions, tight complexity,
  useful decidable subclasses, restricted product-filter memory bounds, and the
  exact automatic-clock boundary remain open or omitted; the general-POMDP
  no-memory-bound result is not silently transferred to them.

The Q100 reframing uses the primary Solan--Vieille working paper and published
record for *Correlated Equilibrium in Stochastic Games*, Theorem 2.3 and
Definition 2.2. It settles uniform autonomous correlated-equilibrium payoff
existence for every finite player number. The repository deliberately records
the mediator boundary: the general device supplies temporally correlated
private recommendations and remains relevant during punishment, so this is
not an ordinary Nash theorem or a public-coin implementation result. The
endogenous compiler/obstruction is internal open work.
