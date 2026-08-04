# Anchored shortening has unbounded reachable depth under determined anchors

## Lifecycle

| Field | Value |
| --- | --- |
| Lifecycle | `ACTIVE` |
| Verdict | `OPEN` (reported proof, not audited or formalized here) |
| Objective priority | `P2` (per `MATH-P2-5`; promotable to `P1` only if a repair decoder consumes a surviving weak form) |
| Last audited | 2026-08-05, extraction from `PIPELINE.md`'s `MATH-P2-5` row and `FRONTIER.md`'s "Exact open hinge" section; no independent re-derivation performed |
| Central live claim | For the exact-`D` anchor system (anchors computed from the letter via `out=F_y(in)`, not free labels), bounded loop erasure fails in two senses: exact-endpoint fibres can have unbounded depth already at `n=2` for one fixed weight, and no length bound `L(ε)` depending only on `n`, `‖r‖_∞`, `ε` exists even approximately, already at `n=3`. The mechanism is that a determined anchor pins the **common** continue factor `c(y)` but not an individual **deleted** factor `c_{-i}(y)`: at `y_i=1`, `c(y)=0` while `c_{-i}(y)≈1` is possible, letting unbounded observable depth hide behind a constant-reset anchor. |
| Next discriminant | Independent re-derivation of the reset-clock counterexample (Question 141 §3, three coordinates), or a bounded-deletion theorem over the actual exact-`D` anchor digraph if one of the surviving weak forms (nonuniform fixed-weight bound, or the `O(1/ε)` prefix approximation of a distinguished orbit) is shown to be consumable by a repair decoder |
| Production destination | none yet; feeds `MATH-P2-5`'s decision on whether bounded loop erasure over exact-`D` anchors is worth pursuing at `P1` |
| Supersedes / superseded by | none |

## Provenance and seal caveat, load-bearing

This claim is **an independent solver's answer** to
[`questions/Question141-BoundedReachabilityDepthUnderDeterminedAnchors.md`](../../questions/Question141-BoundedReachabilityDepthUnderDeterminedAnchors.md).
**It has not been audited in this repository, and none of it is
formalized.** It carries seal `M [reported]` throughout, following the
convention in
[`UniformDefectToGainConversionIsFalse.md`](../AbsorbingCycleCarrier/UniformDefectToGainConversionIsFalse.md).
The question itself is unusually self-contained (full proofs supplied
in-line, no external citations), which lowers but does not eliminate the
audit cost — an unaudited proof of this length is exactly where a subtle
sign or quantifier error is most likely to survive.

## Exact claim, scope, and non-claims

**Setting (from the source, restated).** Letters `ℓ=(y,z)` pair a row
`y∈[0,1]^I` with an anchor `z∈E=[-1,1]^I` satisfying complementarity (6);
`in(ℓ)=z`, `out(ℓ)=F_y(z)` where `F_y(z)=b(y)+c(y)z` is the affine row map.
A word is admissible if consecutive letters' `out`/`in` agree exactly. The
**observable** of a word retains both endpoint anchors and every deleted
product `Π_{-i}(w)=∏_k c_{-i}(y_k)`, but not the middle anchors.

**A1 (exact endpoint fibres): false already at `n=2`.** For the weight
`r({1})=(a,0)`, `r({2})=(1,-1)`, `r({1,2})=(0,1)` (the same weight as
`AnchoredRepairOrUniformDebtDescent.md`'s surgery witness), the admissible
words starting at anchor `0` are **unique at every length** `m`, ending at
distinct anchors `(a-e_m,0)` with `e_m = a^{m+1}(1-a)/(1-a^{m+1})`. Since the
`e_m` are pairwise distinct, the endpoint fibre for `(a-e_m,0)` contains only
the length-`m` word: no uniform length bound `L(n,‖r‖_∞)` can exist.

**A2 (uniform approximate shortening): false already at `n=3`.** A
"reset-clock" weight on three coordinates —
`r_1(S) = 1` if `1∈S` else `-1`; `r_2(S) = 1_{2∈S}(1_{3∈S}-θ)`;
`r_3(S) = 1_{3∈S}(θ-1_{2∈S})`, for `θ∈(0,1)` — has a letter `ℓ* = (y*,z*)`
with `y*=(1,θ,θ)`, `z*=(1,0,0)`, satisfying `F_{y*}(z) = z*` for **every**
input anchor `z`. So the word `(ℓ*)^N` is admissible for every `N`, with
anchor **exactly reset** at every step, yet `Π_{-1}((ℓ*)^N) = ((1-θ)^2)^N`
decays as slowly as `θ` is chosen small. For any proposed length bound `L`,
choosing `θ` small enough makes every word of length `≤L` have
`Π_{-1} > 3/4` while a length-`N` word has `Π_{-1} ≤ 1/2`: no `L(n,‖r‖_∞,ε)`
works uniformly in the weight.

**A2 for one fixed weight: true, but only nonuniformly**, by total
boundedness of the compact observable space — the bound depends on the whole
weight `r`, not merely `n` and `‖r‖_∞`.

**The mechanism.** `F_y(z)=b(y)+c(y)z` is affine with linear part `c(y)·Id`,
giving a genuine contraction `|z_m-z̃_m| = (∏c(y_k))|z_0-z̃_0|` **when the same
row sequence is reused** — but complementarity may force a different row
after any anchor perturbation, so this contraction cannot be transported
across a repair. Separately: `c(y)=0 ⟺ y_i=1` for some `i`, and at such a
row `c_{-i}(y)` is unconstrained by `c(y)` — it can be arbitrarily close to
`1` even as the common factor vanishes. The reset-clock construction stores
unbounded depth exactly there: every anchor is reset to the identical point
`z*`, but the coordinate-`1`-deleted product `c_{-1}(y*)=(1-θ)^2` barely
moves per step.

**Excision fails twice, independently.** Pairwise-separated-anchor packing
bounds the number of *distinct* anchors a word can visit (`N_E(ε) ≤
(⌊2/ε⌋+1)^n`), but an anchor may be revisited arbitrarily often (as in the
reset-clock word), so packing alone does not bound length. And even when two
positions have **exactly** equal anchors (`z_p=z_q`), deleting the segment
between them changes `Π_{-i}` by up to `1-S_i` for the deleted segment's own
product `S_i` — unboundedly, since nothing bounds `1-S_i` in terms of
`|z_p-z_q|=0`.

**The join is separately unstable.** For an interior row (`0<y_i<1`,
`g_i=0`), any nonzero anchor perturbation with `c_{-i}(y)>0` breaks
complementarity outright; the required row-repair jump can be as large as
the full diameter `1` (explicit witness, `n=2`), with no modulus `ρ(η)→0`.
Under the K4 weight specifically, each letter is determined by its incoming
anchor, so repairing one letter forces recomputing every later letter,
which is compatible with a raw length bound but not with a uniform
observable estimate.

**What does survive.** The K4 weight's own distinguished orbit (started at
anchor `0`) **is** approximately shortenable, with an explicit `O(1/ε)`
prefix bound `L_{K4}(ε) = max{⌈1/ε⌉, ⌈log_2(1/ε)⌉}` — so A1's failure and
A2's approximate failure are genuinely separate phenomena on the same
weight, and the general uniform failure (A2) is driven by the *reset-clock*
construction, not by the K4 weight.

**Non-claims.** This does not claim every weight behaves like the
reset-clock construction, nor that no usable weaker form exists — the
source explicitly leaves open whether the nonuniform fixed-weight bound or
the distinguished-orbit `O(1/ε)` approximation can be consumed by an actual
repair decoder. It does not claim anything about the exact-`D` anchors'
digraph structure beyond what `F_y` already supplies; `MATH-P2-5`'s digraph
formalization is separately unbuilt.

## What is already machine-checked

Nothing in this claim is formalized in this repository. No Lean file
implements the letter/word/observable machinery of Question 141, the K4
weight's fibre analysis, or the reset-clock counterexample. The K4 weight
itself coincides with `AnchoredRepairOrUniformDebtDescent.md`'s surgery
witness and `QuittingBoundedSurgeryDescentCounterexample.lean`'s table, but
that file proves a **different** fact (the zero-pinned optimized-debt
plateau and its zero-pin-unpinned resolution), not the endpoint-fibre or
observable-shortening statements here. Citing that file as machine support
for this claim would be a scope error.

## Claim ledger

| ID | Exact claim | Verdict | Seals | Scope | Consumer |
| --- | --- | --- | --- | --- | --- |
| G1 | `ℒ` is compact, `in`/`out` are continuous, `F_y(E)⊆E`, and words of every length exist from every anchor | `PROVED` | `M [reported]` | general `I`, `r` | preliminary; needed for the rest to be well-posed |
| G2 | Exact-endpoint shortening (A1) is false already at `n=2` for one fixed weight (the K4/surgery weight) | `PROVED` | `M [reported]` | that weight | closes `MATH-P2-5`'s literal reachability question negatively |
| G3 | Approximate observable shortening uniform in the weight (A2, fixed `n`, `‖r‖_∞`) is false already at `n=3` (reset-clock weight) | `PROVED` | `M [reported]` | that weight family, `n=3` | rules out the natural repaired version of A1 |
| G4 | Approximate observable shortening for one fixed full weight holds, but only nonuniformly | `PROVED` | `M [reported]` | general, nonuniform | identifies the only unconditionally surviving positive statement |
| G5 | The K4 weight's distinguished orbit is approximately shortenable with an explicit `O(1/ε)` prefix bound | `PROVED` | `M [reported]` | that weight, that orbit | candidate surviving weak form for a repair decoder |
| G6 | Approximate internal excision is not generally valid: exact anchor equality does not bound the change in deleted products, and the join is separately unstable with no uniform row-repair modulus | `PROVED` | `M [reported]` | general | forecloses the natural repair strategy (pigeonhole + excision) |

## Falsifiers and wrong turns

- **The direct falsifier for G3.** Re-derive the reset-clock construction
  (source §3, "A three-coordinate reset-clock counterexample") by hand,
  checking `g_1,g_2,g_3` from (18)–(20) and the fixed-anchor identity
  `F_{y*}(z)=z*` for every `z`; an error there would collapse the uniform
  failure.
- **Do not conflate this claim's K4 weight with
  `AnchoredRepairOrUniformDebtDescent.md`'s or
  `FaithfulUnpinningLeavesASurvivingGap.md`'s use of the same table.** All
  three use `r({1})=(a,0)`, `r({2})=(1,-1)`, `r({1,2})=(0,1)`, but each asks
  a different question of it (optimized-debt plateau; faithful-unpinning
  gap; endpoint-fibre depth). A machine-checked fact about one does not
  transfer to another without a separate proof.
- **Do not read G2/G3 as refuting the surgery decoder's closure in
  `AnchoredRepairOrUniformDebtDescent.md`.** That file's descent refutation
  is a different, already machine-checked statement about bounded-length
  *debt decrement*, not about endpoint-fibre depth; the two are related in
  spirit (both driven by the seam/anchor mechanism) but not identical
  claims.
- **Do not assume the free-label case (K2 in the source) is relevant here.**
  It is supplied only as a contrast — the free-label failure is easy and
  uninteresting; every claim in this file is specifically about the
  *determined*-anchor case (`out=F_y(in)`), which is harder to fail and is
  why the failure is worth recording.

## Production map

```text
Question141 (external solver's answer) -> [MISSING: internal audit] -> MATH-P2-5 (not yet imported)
```

`MATH-P2-5` currently has no digraph structure over the exact-`D` anchors in
the repository; Mathlib's graph API is unused in the quitting tree. Missing
arrows, in order of value: (1) an independent hand-audit of the reset-clock
construction (G3), since it is the sharpest negative result and the one most
likely to hide an error; (2) a decision on whether G4 or G5's surviving weak
form is consumable by any actual repair decoder — `MATH-P2-5`'s stated
promotion condition; (3) a Lean formalization of the letter/word/observable
machinery if promotion is warranted.

## Exit conditions

- `MINED` if audited and no repair decoder is ever found to consume G4 or
  G5 — the row then documents a closed negative result with no further
  action.
- Promoted to `ACTIVE` at `P1` if a repair decoder is shown to consume the
  nonuniform fixed-weight bound (G4) or the distinguished-orbit
  approximation (G5), per `MATH-P2-5`'s stated acceptance condition.
- `WRONG` at the claim level if the reset-clock construction (G3) or the K4
  fibre argument (G2) fails to reproduce under audit.
