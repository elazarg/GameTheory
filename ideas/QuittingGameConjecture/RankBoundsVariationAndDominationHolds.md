# Rank bounds variation, and domination holds unrestricted

| Status | Provenance | Consumer | Falsifier |
| --- | --- | --- | --- |
| `OPEN`, maturity `M [reported]`, P0 | Q161 | `MATH-P0-8` — discharges `hdominate` and the Case-1 reach bound; the folding lemma | an error in the excursion decomposition or the performance-difference identity |

## The four results

**(1) The maximal inequality, with the coupling emerging rather than
imposed.** For a δ-balanced decision process,
`P(sup_m |S_m| ≥ ε) ≤ δ·E[w̄]/ε²` — the published hypothesis `δ ≤ ε²ρ/B`
is the special case, and the proof (finite-horizon stopped-square + pricing
the quadratic variation by the decision variation + the overshoot paying one
`δ`) yields the clean product form directly.

**(2) Rank bounds variation — with a definition correction.** Rank `≤ n`
gives `E[w̄] ≤ 2nM`, by excursion decomposition per class with last-visit
bookkeeping — and **action-independence is required only for actions of
positive return probability**. Zero-return actions impose no genuine
condition; the published definition, read literally, would let adversarial
assignment of the irrelevant `r_y` values inflate the numerical rank. The
corrected rank is the right object, and Proposition 2 itself is the proof.

**(3) The rank-one corollary, strengthened.**
`P(sup_m S_m ≥ ε) ≤ 2Mδ/ε²`, and more strongly `≤ 2Mδ/(ε² + 2Mδ)`.

**(4) Domination with the unrestricted quantifier — sharper than the
published assertion.** In the live-chain plan application, **every**
unilateral behavioural deviation satisfies `Adv(α) ≤ max{A_C, ε + δ}` (plus
explicit trigger-cost additions), where `A_C` is the always-continue
deviation's advantage. Proved by an exact performance-difference
decomposition and summation by parts over survival probabilities — the
answer is explicit that this is **not** a consequence of the crossing
estimate alone, and it is stronger than the published "only repetitive
continuing matters", which asserted the reduction informally. The
architecture guard's warning about exactly this step is discharged by proof,
not by citation.

## The K2 correction — my supplied explanation was wrong

The rank-one reading I supplied said Quit and Continue "give the same
distribution over the next visit to the live chain". False: Quit has zero
return mass, Continue may have positive. Rank one holds for the right
reason — with the corrected definition, at most one action per live state
has positive return probability, so the action-independence condition is
automatic; rank is exactly one when some live state is varied, and **no
recurrence of the live chain is needed**.

## What this closes

With the ledger, the clocks, the ceiling-IR attainment, and the Case-2
wiring already landed, this answer supplies the last two compiler
components on paper: the Case-1 reach bound (rank-one corollary at the
combined clock) and `hdominate` (result 4). The relaxed compiler —
per-tolerance chains with divergent quit mass into approximate equilibria —
is now **complete at `M [reported]`**; what remains is formalization
(dispatched), the folding lemma riding the reach bounds, and the
min-max-band attainment for targets below the ceiling (Q162).

## Open

- Formalize (1)–(4). The Abel/performance-difference shape of (4) matches
  the ledger file's cash-out identities — the formalization should reuse
  them, and the corrected rank definition is the one to encode.
- Whether the strengthened denominator form `2Mδ/(ε² + 2Mδ)` improves any
  downstream constant enough to matter.
