# The completed vector-factor trace carrier is compact and determining

## Lifecycle

| Field | Value |
| --- | --- |
| Lifecycle | `ACTIVE` |
| Verdict | `OPEN` (reported proof, not audited or formalized here) |
| Objective priority | `P0` |
| Last audited | 2026-08-05, extraction from `PIPELINE.md`/`FRONTIER.md`; no independent re-derivation performed |
| Central live claim | Let `𝔗_r` be the closure, in the joint Hausdorff metric, of the completed **vector-factor** trace `t ↦ (τ(t), (P_j(t))_j)` together with the joint completed obstacle hypographs, over finite complementary arrays. `𝔗_r` is compact; the vector trace determines `S`, every `S_{-i}`, and the value at the origin *continuously*; the hypograph determines the cap continuously; finite complementary arrays are dense in `𝔗_r`; and every element of `𝔗_r` pulls back simultaneously in trace, cap, and origin value. |
| Next discriminant | Independent re-derivation of Part A (Hausdorff compactness of the completed chain order) and Part B3 (pullback), or a Lean formalization of `𝔗_r` and its continuity theorems |
| Production destination | `MATH-P0-1`'s exact finite adapter against `𝔗_r`; none built yet |
| Supersedes / superseded by | Sharpens [`RealizedAnchoredHolonomyClosedness.md`](RealizedAnchoredHolonomyClosedness.md)'s open "next discriminant" and the compactification candidate surveyed in [`EnrichedAbsorptionPathsMayCompactifyTheEscapingMiddle.md`](EnrichedAbsorptionPathsMayCompactifyTheEscapingMiddle.md); neither file is marked superseded here, since neither has been re-audited against this claim |

## Provenance and seal caveat, load-bearing

This claim is **an independent solver's answer** to
[`questions/Question150-CompactAndDetermining.md`](../../questions/Question150-CompactAndDetermining.md),
reproduced as settled prose in `docs/uniform-equilibrium/PIPELINE.md`'s
`MATH-P0-1` row and `FRONTIER.md` item 9 before this extraction. **It has not
been audited in this repository, and none of it is formalized.** Per
[`ideas/README.md`](../README.md), a rigorous audit is what establishes `M`;
an unaudited solver answer does not qualify, however confident the prose. The
ledger below marks every row `M [reported]`, following the convention already
used in
[`UniformDefectToGainConversionIsFalse.md`](../AbsorbingCycleCarrier/UniformDefectToGainConversionIsFalse.md):
`[reported]` means supplied externally and checked neither by hand nor by
Lean in this repository.

This is exactly the situation the extraction task exists to guard against: a
sibling reported result in this same investigative thread
(`QuittingRelaxedCycleGainIsolatedCoordinate.lean`, on a different but
related question) was dispatched for formalization and found **false**. Treat
every unaudited claim below as carrying that risk until independently
re-derived.

## Exact claim, scope, and non-claims

The construction (definitions reproduced from Question 150 §1–§1b, matching
`FRONTIER.md` item 9's vocabulary):

- for a finite complementary array `x`, the **trace** is the completed graph
  of `t ↦ (τ(t), (P_j(t))_j) ∈ [0,1] × [0,1]^I`, with consecutive cumulative
  points joined by straight chords;
- the **obstacle hypograph** `H_i(x)` is the closure of the sub-graph of the
  stage obstacle `O_i(t)` against `τ(t)`;
- `𝔗_r` is the Hausdorff closure of `{(trace(x), (H_i(x))_i) : x complementary}`.

**What is claimed proved (all `M [reported]`):**

1. `𝔗_r` is compact (Part A1: Helly-type compactness of completed monotone
   chains under the coordinatewise order `(τ,p) ⪯ (σ,q) ⟺ τ≤σ, p_j≥q_j`).
2. The vector trace determines `S = 1-τ`, every `S_{-i} = ∏_{j≠i}P_j`, and the
   backward value at the origin continuously (Part A2); the hypograph
   determines the cap continuously via a uniform-continuity argument on the
   compact marked base.
3. Finite complementary traces are **not** closed in `𝔗_r` — an explicit
   `r=0` family converges to a genuinely nonlinear parabolic arc that is not
   the trace of any finite array (Part B1, "strict nonclosedness").
4. Literal rowwise complementarity does not survive on the unmarked limit; it
   is replaced by exact complementarity on retained atoms, a closed
   differential condition `supp α_i ⊆ {V_i = r_i({i})}` on diffuse interior
   pieces, and an existential closed chronological-profile lift on zero-mass
   pieces (Part B2). Adding that profile mark is itself a compact enrichment.
5. **Pullback (Part B3):** every `z ∈ 𝔗_r` is simultaneously approximable — in
   trace, in every cap, and in origin value — by a finite complementary array.
6. **No forced trade-off (Part C):** compactness and continuous determination
   hold together; what is lost is only finiteness of the realized set and
   literal rowwise complementarity, not compactness or determination.

**Two load-bearing conventions, explicitly not optional:**

- **The piecewise-affine completion convention is load-bearing.** Segments
  must be straight chords between cumulative points. Forcing them onto the
  product manifold `{∏_j P_j = 1-τ}` erases stage atoms, and the factor path
  then no longer determines coalition payoffs (this is proved, not asserted,
  via the convexity-defect argument `δ(τ,p) = 1-τ-∏_j p_j ≥ 0` and its strict
  positivity on genuine multi-coordinate stage atoms).
- **The terminal vector is assumed fixed.** If it varies, it must be retained
  as one further compact coordinate; this is stated but not separately
  proved here.

**Non-claims.** The exact finite adapter from `𝔗_r` back to production
`QuittingBoundaryHolonomy`/`QuittingAnchoredBoundaryBlock` machinery is
**not** built (`MATH-P0-1`'s acceptance criterion remains open). Nothing here
says the relaxed package on `𝔗_r` certifies small deviation *gain* — that is
a separate, negatively answered question; see
[`RelaxedLimitPackageDoesNotCertifySmallGain.md`](RelaxedLimitPackageDoesNotCertifySmallGain.md).
Nor does anything here rescue the cheaper *aggregated* carrier (survival data
alone, without the ordered vector factorization); see
[`AggregatedCarrierConflatesOriginValues.md`](AggregatedCarrierConflatesOriginValues.md).

## What is already machine-checked

Part of the *motivation* for needing the vector factorization (rather than a
scalar accumulated-mass clock) is independently machine-checked, and is cited
as background fact (K2) in the source question. The unilateral stopping
obstacle is not a function of accumulated mass alone:
`QuittingObstacleMassDescentCounterexample.not_exists_obstacle_as_function_of_accumulatedMass`
in `GameTheory/Concepts/Stochastic/QuittingObstacleMassDescentCounterexample.lean`
proves `¬ ∃ f : ℝ → ℝ, ∀ t, f (accumulatedMass t) = obstacleValue t` on an
explicit two-row table. This machine-checked fact supports the *design
choice* of retaining the ordered vector factor `(P_j)_j` rather than only
`τ`; it does **not** establish the compactness or determination theorems
above, which remain entirely `[reported]`.

## Claim ledger

| ID | Exact claim | Verdict | Seals | Scope | Consumer |
| --- | --- | --- | --- | --- | --- |
| A1 | `𝔗_r`, the closure of the joint completed vector-factor trace plus obstacle hypographs, is compact in the Hausdorff metric | `PROVED` | `M [reported]` | general finite index set `I`, general weight `r` | `MATH-P0-1` acceptance |
| A2 | The vector trace determines `S`, every `S_{-i}`, and the origin value continuously; the hypograph determines the cap continuously | `PROVED` | `M [reported]` | same | makes the limit usable rather than decorative |
| A3 | The finite complementary image is strictly smaller than `𝔗_r` (nonclosed), witnessed by an explicit nonlinear parabolic limit at `r=0` | `PROVED` | `M [reported]` | the exhibited `r=0` family | rules out "the carrier is just the finite set" readings |
| B1 | Literal rowwise complementarity is replaced, on the closure, by exact complementarity on atoms + a closed differential condition on diffuse pieces + an existential chronological-profile lift on zero-mass pieces | `PROVED` | `M [reported]` | general | defines the "relaxed package" consumed by `MATH-P0-2` |
| B2 | Pullback: every element of `𝔗_r` is simultaneously approximable in trace, cap, and origin value by a finite complementary array | `PROVED` | `M [reported]` | general | the usability claim; without it the carrier is decorative |
| C | No compactness-vs-determination trade-off; the only casualty is finiteness and literal rowwise complementarity | `PROVED` | `M [reported]` | general | licenses treating `𝔗_r` as the target carrier for `MATH-P0-1` |

The obstacle-not-a-function-of-mass motivation (K2 in the source) is
`M`, machine-checked — see "What is already machine-checked" above. It
supports the design but is not itself A1/A2/A3/B1/B2/C.

## Falsifiers and wrong turns

- **The direct falsifier for A1.** Exhibit a sequence of finite complementary
  traces with no Hausdorff-convergent subsequence in the claimed ambient
  space, or show the completed-chain-order argument fails to be closed under
  limits.
- **The direct falsifier for A2.** Exhibit two sequences of finite
  complementary arrays whose traces converge to the same point of `𝔗_r` but
  whose origin values (or some `S_{-i}`) converge to different limits.
- **The direct falsifier for B2 (pullback).** Exhibit `z ∈ 𝔗_r` with no
  sequence of finite complementary arrays approximating it simultaneously in
  trace, cap, *and* origin value — i.e. a genuine failure of usability, as
  opposed to mere non-finiteness.
- **Do not read this claim as licensing the aggregated (survival-only)
  carrier.** `AggregatedCarrierConflatesOriginValues.md` is the fence: dropping
  the ordered vector factorization for the aggregated `(S, S_{-i})` data loses
  origin-value information even conditional on the obstacle trace.
- **Do not read compactness+determination here as certifying small deviation
  gain.** That is a separate question, answered negatively; see
  `RelaxedLimitPackageDoesNotCertifySmallGain.md`.
- **Do not substitute the product-manifold completion for the piecewise-affine
  one.** The claim is proved only under chords between cumulative points;
  projecting onto `{∏_j P_j = 1-τ}` is shown (not merely asserted) to destroy
  determination.

## Production map

```text
Question150 (external solver's answer) -> [MISSING: internal audit] -> no production surface
                                        -> MATH-P0-1's exact finite adapter (open)
```

Nothing here is formalized and nothing should be until the audit lands or a
Lean construction of `𝔗_r` is attempted directly. The one piece of adjacent
machine truth is
`QuittingObstacleMassDescentCounterexample.not_exists_obstacle_as_function_of_accumulatedMass`,
cited above, which is untouched by anything in this file and remains valid
regardless of this claim's fate.

Missing arrows, in order of value: (1) an independent hand-audit of Part A1's
compactness argument and Part B3's pullback argument, since those are the two
load-bearing steps the rest depends on; (2) a Lean definition of `𝔗_r` and
its continuity theorems; (3) `MATH-P0-1`'s exact finite adapter.

## Exit conditions

- `MINED` at the claim level when A1/A2/B2 are independently re-derived (by
  hand or in Lean) and the exact finite adapter is built, closing
  `MATH-P0-1`.
- Any row becomes `WRONG` if a counterexample of the kind listed under
  "Falsifiers" is found; the file then survives as the regression recording
  why the carrier construction was attempted.
- `BLOCKED` if re-derivation stalls on an unstated step in the source answer
  (e.g. the exact modulus in the origin-value continuity estimate, equation
  (20) of Question 150), in which case the prerequisite is recovering that
  step independently.
