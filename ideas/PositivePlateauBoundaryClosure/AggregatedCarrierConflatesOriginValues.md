# The aggregated carrier conflates origin values

## Lifecycle

| Field | Value |
| --- | --- |
| Lifecycle | `ACTIVE` |
| Verdict | `OPEN` (reported counterexample, not audited or formalized here) |
| Objective priority | `P0` |
| Last audited | 2026-08-05, extraction from `PIPELINE.md`/`FRONTIER.md`; no independent re-derivation performed |
| Central live claim | Retaining only the aggregated survival data — the full survival `S` and every deleted survival `S_{-i}`, without the ordered vector factorization `(P_j)_j` — is **not** a harmless simplification of the carrier in [`CompletedVectorFactorTraceIsCompactAndDetermining.md`](CompletedVectorFactorTraceIsCompactAndDetermining.md). Two one-row complementary arrays exist with **identical** aggregated survival data (and, in one variant, an identical stage-obstacle-gap trace) but **different** origin values. |
| Next discriminant | Independent re-derivation of the two explicit witness arrays, or a repaired aggregated coordinate that is shown to be fibre-constant for origin value |
| Production destination | none; this is a fence against a cheaper alternative to `MATH-P0-1`'s carrier |
| Supersedes / superseded by | none |

## Provenance and seal caveat

Same source and same caveat as
[`CompletedVectorFactorTraceIsCompactAndDetermining.md`](CompletedVectorFactorTraceIsCompactAndDetermining.md):
an **unaudited, unformalized solver's answer** to
[`questions/Question150-CompactAndDetermining.md`](../../questions/Question150-CompactAndDetermining.md)
(Part C, "Why C2 does not rescue the aggregated carrier"), restated with less
detail as fact (K4) of
[`questions/Question152-RepairFromARelaxedLimit.md`](../../questions/Question152-RepairFromARelaxedLimit.md)
and as settled prose in `PIPELINE.md`'s `MATH-P0-1` row and `FRONTIER.md`
item 9 ("The aggregated carrier is not an acceptable fallback..."). It has
not been checked in this repository and carries seal `M [reported]` only.

## Exact claim and witnesses

Fix `I = {1,2,3}`. For a one-row array `x = (x_1,x_2,x_3) ∈ [0,1]^3`, write
`p_j = 1-x_j` for the post-row survival factors.

**Witness pair.** Let `q ∈ (0,1)`, `h = 1-q`, and

- `x^A = (1, 0, h)`, giving post-row survival `p^A = (0, 1, q)`;
- `x^B = (1, h, 0)`, giving post-row survival `p^B = (0, q, 1)`.

Both have the **same** aggregated data: `c = 0`, `c_{-1} = q`,
`c_{-2} = c_{-3} = 0` (equation (40) of Question 150). So their completed
scalar graphs for `S` and every `S_{-i}` are identical.

Define the weight by `r_1({2}) = r_1({1,2}) = 1`, all other coordinates of
`r` zero, terminal continuation `0`. Both `x^A` and `x^B` are complementary
(their `g`-gaps are zero at every coordinate). But:

- `V_1^A(0) = 0` — under `x^A` player 1's only reachable nonempty coalitions
  are `{1}` and `{1,3}`, both paying `0`;
- `V_1^B(0) = h` — under `x^B`, coalition `{1,2}` occurs with weight `h`,
  paying `1`.

So `V_1^A(0) ≠ V_1^B(0)` despite identical aggregated survival traces:
**aggregation loses payoff information.**

**Sharper variant.** If instead only `r_1({1,2}) = 1` (with `r_1({2}) = 0`),
the same two arrays give stage-obstacle gaps `g_1^A = 0` but `g_1^B = h`:
even the standard obstacle-gap trace built on top of the aggregated survival
data is not fibre-constant. So neither the raw aggregated survival data nor
the aggregated-plus-obstacle-gap data suffices; the ordered vector
factorization `(P_j)_j` is genuinely necessary, not merely convenient.

## What is already machine-checked

Nothing in this specific claim (the two witness arrays and the inequality of
origin values) is machine-checked. A related but **distinct** fact is: the
unilateral stopping obstacle is not a function of accumulated mass alone,
`QuittingObstacleMassDescentCounterexample.not_exists_obstacle_as_function_of_accumulatedMass`.
That theorem is about scalar mass `τ` failing to determine the obstacle at a
single coordinate; the claim here is about the richer aggregated
`(S, S_{-i})` data failing to determine the *origin value* across three
coordinates. Do not conflate the two when citing machine-checked support.

## Claim ledger

| ID | Exact claim | Verdict | Seals | Scope | Consumer |
| --- | --- | --- | --- | --- | --- |
| D1 | `x^A`, `x^B` above are both complementary with identical aggregated survival data `(c, c_{-1}, c_{-2}, c_{-3})` but `V_1^A(0) ≠ V_1^B(0)` | `PROVED` | `M [reported]` | `n=3`, the exhibited weight | rules out the aggregated carrier as a fallback for `MATH-P0-1` |
| D2 | The sharper variant (`r_1({1,2})=1` alone) also separates the standard obstacle-gap trace, not merely the origin value | `PROVED` | `M [reported]` | same | rules out "obstacle-gap trace repairs aggregation" as a fix |

## Falsifiers and wrong turns

- **The direct falsifier.** Re-derive `V_1^A(0)` and `V_1^B(0)` by hand from
  the stated weight and rows; a single arithmetic slip would collapse the
  separation.
- **Do not read this as a fence against `CompletedVectorFactorTraceIsCompactAndDetermining.md`.**
  That claim retains the vector factorization precisely to avoid this failure;
  this file documents why the *cheaper* alternative (aggregated data only)
  cannot be substituted for it.
- **Do not assume a repaired scalar summary exists.** The witnesses show
  failure already at `n=3`, one row; nothing here searches for or rules out
  every possible alternative aggregated coordinate, only the natural one
  (full and deleted survivals, with or without the obstacle-gap trace).

## Production map

```text
Question150 Part C (external solver's answer) -> [MISSING: internal audit] -> no production surface
```

This claim is purely a negative fence; it has no positive production target
of its own. It protects `MATH-P0-1`'s acceptance criterion ("do not fall back
on the aggregated carrier") from being quietly relaxed.

## Exit conditions

- `MINED` once the two witness computations are independently re-derived (by
  hand or in Lean), converting this fence into `M` at the strict sense used
  elsewhere in this program.
- `WRONG` if the arithmetic in D1 or D2 fails to reproduce under audit.
