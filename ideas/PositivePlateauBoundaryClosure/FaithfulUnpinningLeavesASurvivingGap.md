# A gap can survive faithful terminal unpinning

## Lifecycle

| Field | Value |
| --- | --- |
| Lifecycle | `ACTIVE` |
| Verdict | `MIXED` — see per-row seals; the qualitative "unpinning kills both known plateau witnesses" sub-claim has independent machine-checked support, the new faithful-formulation content does not |
| Objective priority | `P1` (per `PC-008`'s deprioritization, pending `MATH-P1-4`'s formalization) |
| Last audited | 2026-08-05, extraction from `PIPELINE.md`'s `PC-008` and `MATH-P1-4` rows; no independent re-derivation performed |
| Central live claim | Two candidate ways to "free the terminal continuation" of the zero-pinned optimized-debt quantity are both rejected: a constant offset `w=v+Λ` measures terminal-shift sensitivity, not deviation gain, and is nonzero even on a genuine zero-gain array; freeing only the deviating continuation makes the free-terminal optimum identically zero on **every** weight. The faithful formulation selects **both** the prescribed and the deviating terminal values by zero-seeded repeated-period iteration of the same array. Under it, the known surgery-witness weight collapses to gap `0` at every length, but the weight `r({1})=r({2})=(-1,1)`, `r({1,2})=(1,-1)` has gap exactly `1` at every length — a negative singleton value carried by its unique active coordinate. |
| Next discriminant | `MATH-P1-4`: machine-check both computations, with the faithful free-terminal formulation itself defined in Lean rather than assumed |
| Production destination | `MATH-P1-4`; feeds the `PC-008`/`PC-009` priority decision for escaping-middle compactification |
| Supersedes / superseded by | Extends [`AnchoredRepairOrUniformDebtDescent.md`](AnchoredRepairOrUniformDebtDescent.md), which posed exactly this test ("The decisive next test is to define the optimized debt over chains with a free admissible terminal continuation...") without answering it |

## Provenance and seal caveat, load-bearing

The **faithful-formulation content** — the rejection of the two naive
unpinning conventions, the zero-seeded repeated-period selector, and the new
weight `r({1})=r({2})=(-1,1)`, `r({1,2})=(1,-1)` — is **an independent
solver's answer** to
[`questions/Question151-TheFreeTerminalCalibration.md`](../../questions/Question151-TheFreeTerminalCalibration.md).
**It has not been audited in this repository, and none of it is
formalized.** It carries seal `M [reported]`, following the convention in
[`UniformDefectToGainConversionIsFalse.md`](../AbsorbingCycleCarrier/UniformDefectToGainConversionIsFalse.md).

The **qualitative sub-claim** that both previously known plateau witnesses
have exact zero-debt equilibria once their terminal continuation is unpinned
is, separately, machine-checked — see below. Do not let the machine-checked
status of that narrower fact lend unearned confidence to the faithful
formulation's new content, which is a different, larger claim built on top
of it.

## Exact claim, scope, and non-claims

**Setting.** `D^{v,w}(x) = Σ_i max{0, W_i(0)-V_i(0)}`, where `V` is the
prescribed backward recursion with terminal value `v` and `W` is the
deviating (max-affine) recursion with terminal value `w`. A matched pair
`v=w` gives `D≡0` on every weight — a fact used only as a trap to avoid, not
as evidence (Question 151's own warning, `(K1)`).

**Rejected convention 1: constant offset `w=v+Λ`.** This offset enters the
transport only through `Π_{-i}(m)(w_i-v_i)`, so it transports as a constant
shift. On the known surgery-witness weight `r({1})=(a,0)`, `r({2})=(1,-1)`,
`r({1,2})=(0,1)`, the constant row `(1/2,0)` is a genuine zero-gain array
(§`(K4)` of the source: every coordinate is exactly indifferent), yet
`D^{v,v+Λ}` evaluates to `a > 0` on it. So this convention measures
terminal-shift sensitivity, not repeated deviation gain, and is a poor proxy
even after the prescribed value is made self-consistent.

**Rejected convention 2: free only the deviating continuation.** Selecting
`w` by the zero-seeded companion-map limit while leaving `v` pinned makes the
resulting infimum **identically zero on every weight**: the always-available
zero array with `v = 1` (entrywise) suppresses every positive difference,
since complementarity at the zero array only requires `r_i({i}) ≤ v_i`.

**The faithful formulation.** Select both `v` and `w` as zero-seeded
repeated-period limits of the *same* array's own one-period Bellman maps:
`v°(x) = lim_k P_x^k(0)`, `w°(x) = lim_k Φ_x^k(0)`, restricting to arrays
`x` with `v°(x)` self-consistent (`x ∈ 𝒜_m(v°(x))`). The resulting quantity
`D^{v°(x),w°(x)}(x)`, minimized over such `x`, measures exactly one
phenomenon: a negative singleton value at the unique active coordinate when
exactly one coordinate is ever active over the period, and `0` whenever two
or more coordinates are simultaneously active (because then every relevant
deleted survival product is `<1`, making the deviation map's fixed point
coincide with the prescribed one).

**Result on the surgery witness.** The constant row `x_{t,1}=1/2, x_{t,2}=0`
gives `v° = (a,0)` and, since `Φ_1(z)=max{a,z}`, `Φ_2(z)=max{0,z/2}`,
`w° = (a,0) = v°`. So the faithful gap is `0` at every length — the plateau
genuinely was an artifact of the zero pin for **this** weight.

**Result on the new weight.** For `r({1})=r({2})=(-1,1)`, `r({1,2})=(1,-1)`,
every selected-complementary period is shown (by a case analysis on the row
types, source §6) to have exactly coordinate `1` active — coordinate `2`'s
singleton value `1` blocks the all-zero array, and no period can keep both
coordinates simultaneously active without violating complementarity. This
forces `v° = (-1,1)`, and coordinate `1`'s deviation map `Φ_1(z)=max{-1,z}`
zero-seeds to `w°_1 = 0`, while coordinate `2`'s deviation map contracts to
its already-matching fixed point `1`. So `D^{v°,w°} = max{0, 0-(-1)} = 1`,
realized e.g. by the constant row `(1/2, 0)` at every length `m`.

**Non-claims.** This does not claim the new weight is a plateau of the
*zero-pinned* chain family in the sense of `AnchoredRepairOrUniformDebtDescent.md`
— it is a plateau of the *faithfully unpinned* quantity, a different object.
It does not claim completeness — whether every weight with a faithful gap
looks like this one, or whether the faithful gap is itself the right proxy
for uniform-equilibrium difficulty, is not addressed. It does not resolve
`PC-008`'s "canonical boundary selection" caveat: "algebraic self-consistency
is a closed condition, but the canonical boundary selection is not" — the
zero-seeded selector `v°`/`w°` is discontinuous at `S(x)=1` (an explicit
witness in the source shows the selected graph `{(x,v°(x))}` is not closed).

## What is already machine-checked

**Both known plateau witnesses' unpinned equilibria are machine-checked**,
independently of the faithful-formulation content above:

- **Surgery witness** `r({1})=(a,0)`, `r({2})=(1,-1)`, `r({1,2})=(0,1)`:
  `stationaryRoot_isEndpointNash` and `quittingConstantDynamicDebt_eq_zero`
  in
  `GameTheory/Concepts/Stochastic/QuittingBoundedSurgeryDescentCounterexample.lean`
  prove the constant `1/2`-mixing row is exact endpoint Nash against its own
  self-consistent continuation `(a,0)`, and that the dynamic-debt recursion
  against that continuation (rather than the zero pin) is identically zero
  at every fuel and start.
- **`1/8`-plateau table** `r({1})=(1/4,0)`, `r({2})=(1,-1/4)`,
  `r({1,2})=(3/4,1/4)`: the identically-named `stationaryRoot_isEndpointNash`
  and `quittingConstantDynamicDebt_eq_zero` in
  `GameTheory/Concepts/Stochastic/QuittingPositiveDebtPlateauTable.lean`
  prove the same pair of facts against continuation `(1/4,0)`.

These machine-checked facts establish that **the zero pin, not the game, is
responsible for both known plateaus** — exactly the qualitative content
`AnchoredRepairOrUniformDebtDescent.md` already asserts as `M` in its own
prose. They do **not** formalize the faithful `v°`/`w°` selector, the
rejection of the two naive conventions, or the new weight's gap-`1` result;
those are `MATH-P1-4`'s open acceptance criterion.

## Claim ledger

| ID | Exact claim | Verdict | Seals | Scope | Consumer |
| --- | --- | --- | --- | --- | --- |
| F1 | Constant-offset unpinning (`w=v+Λ`) is a poor proxy: nonzero on a genuine zero-gain array | `PROVED` | `M [reported]` | the surgery-witness weight | rules out the cheapest unpinning convention |
| F2 | Deviating-continuation-only unpinning gives an infimum identically `0` on every weight | `PROVED` | `M [reported]` | all weights, all lengths | rules out the second cheapest convention |
| F3 | The faithful (both-sides, zero-seeded, repeated-period) formulation is well-defined and measures a negative singleton value at a lone active coordinate | `PROVED` | `M [reported]` | general (case analysis by number of simultaneously active coordinates) | defines the target quantity `MATH-P1-4` must formalize |
| F4 | Surgery-witness weight has faithful gap `0` at every length | `PROVED` (qualitatively, via machine-checked equilibrium) | `M [reported]` for the specific faithful-formalism computation; the underlying zero-debt-under-unpinning fact is `M+L` (`stationaryRoot_isEndpointNash`, `quittingConstantDynamicDebt_eq_zero` in `QuittingBoundedSurgeryDescentCounterexample.lean`) | that weight | shows compactification work is not categorically wasted on this witness |
| F5 | `r({1})=r({2})=(-1,1)`, `r({1,2})=(1,-1)` has faithful gap exactly `1` at every length | `PROVED` | `M [reported]` | that weight | first honest instance of a gap surviving faithful unpinning; `MATH-P1-4`'s primary target |

## Falsifiers and wrong turns

- **The direct falsifier for F5.** Re-derive the row-type classification of
  source §6 (every selected-complementary period has exactly coordinate `1`
  active) by hand; an error there would collapse the claimed gap.
- **Do not restate F4 as "the terminal pair `v=w=(a,0)` gives `D=0`."** That
  is the vacuous matched-pair case `(K1)` warns against; F4's content is that
  the *independently selected* `v°` and `w°` happen to coincide, not that
  they were matched by fiat.
- **Do not infer `F5`'s gap from `F1`'s zero-gain array by analogy.** The
  surgery witness and the new weight are different weights with different
  active-coordinate structure; `F5`'s classification is a separate case
  analysis, not a corollary of `F1`.
- **Do not treat `PC-008`'s "canonical boundary selection is not closed"
  caveat as resolved.** The selector `v°(x)` is discontinuous exactly where
  `S(x)=1`, with an explicit witness in the source; any downstream use must
  carry this caveat.

## Production map

```text
Question151 (external solver's answer) -> [MISSING: internal audit] -> MATH-P1-4 (formalization, READY)
                                                                      -> feeds PC-008/PC-009 priority
```

The two machine-checked equilibrium facts
(`QuittingBoundedSurgeryDescentCounterexample.stationaryRoot_isEndpointNash`,
`.quittingConstantDynamicDebt_eq_zero`;
`QuittingPositiveDebtPlateauTable.stationaryRoot_isEndpointNash`,
`.quittingConstantDynamicDebt_eq_zero`) are untouched by anything in this
file and remain valid regardless of the faithful-formulation content's fate.

Missing arrows, in order of value: (1) an independent hand-audit of F3's
selector definition and F5's case analysis; (2) `MATH-P1-4`'s Lean
formalization of the faithful selector and both computations; (3) deciding
whether F5's weight is representative or idiosyncratic — i.e. whether a
faithful gap correlates with anything already tracked (e.g. isolated
negative solo weight, as in `AbsorbingCycleCarrier`'s mismatch
characterization).

## Exit conditions

- `MINED` once `MATH-P1-4` lands: both computations machine-checked with the
  faithful selector itself defined in Lean.
- Any row becomes `WRONG` if the corresponding hand-audit or formalization
  attempt fails to reproduce the claimed value.
- `BLOCKED` if the faithful selector cannot be stated in Lean without first
  resolving the discontinuity noted in "Non-claims" (the selected graph
  `{(x,v°(x))}` is not closed at `S(x)=1`).
