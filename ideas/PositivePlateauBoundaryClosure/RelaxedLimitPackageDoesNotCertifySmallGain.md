# The relaxed limit package does not certify small gain

## Lifecycle

| Field | Value |
| --- | --- |
| Lifecycle | `ACTIVE` |
| Verdict | `OPEN` (reported counterexample, not audited or formalized here) |
| Objective priority | `P0` |
| Last audited | 2026-08-05, extraction from `PIPELINE.md`'s `MATH-P0-2` row; no independent re-derivation performed |
| Central live claim | The relaxed package that survives at the closure `𝔗_r` of [`CompletedVectorFactorTraceIsCompactAndDetermining.md`](CompletedVectorFactorTraceIsCompactAndDetermining.md) — exact complementarity on atoms, a closed differential condition on diffuse pieces, an existential chronological-profile lift on zero-mass pieces — is **not** a sufficient certificate for small deviation gain nearby. There is an explicit `z_* ∈ 𝔗_r`, itself the trace of a finite complementary array, with a robust gain floor: every finite array within a fixed positive distance of `z_*` in the trace has maximum deviation gain bounded away from zero. Adding the chronological-profile mark does not repair this. |
| Next discriminant | Independent re-derivation of the witness computation (Question 152 Parts A–D), or a repaired certificate combining the relaxed package with an explicit terminal-debt condition |
| Production destination | `MATH-P0-2`'s "robust pointwise alternative"; the limit-object route to it is closed **as posed** by this claim, redirecting `MATH-P0-2` to the repair ladder instead |
| Supersedes / superseded by | none |

## Provenance and seal caveat, load-bearing

This claim is **an independent solver's answer** to
[`questions/Question152-RepairFromARelaxedLimit.md`](../../questions/Question152-RepairFromARelaxedLimit.md),
which itself takes the carrier `𝔗_r` of
[`CompletedVectorFactorTraceIsCompactAndDetermining.md`](CompletedVectorFactorTraceIsCompactAndDetermining.md)
as a *granted, unaudited assumption* (its own (K1)–(K5)). **Nothing here has
been audited in this repository, and none of it is formalized.** It carries
seal `M [reported]` throughout, following the convention in
[`UniformDefectToGainConversionIsFalse.md`](../AbsorbingCycleCarrier/UniformDefectToGainConversionIsFalse.md).
Because this claim's soundness is inherited from the carrier claim it
assumes, any refutation of `CompletedVectorFactorTraceIsCompactAndDetermining.md`
would require re-examining this file as well.

## Exact claim, scope, and non-claims

**The core distinction: value-approximation vs. gain-approximation.** The
pullback property already established for `𝔗_r` (`B2`/`B3` in the carrier
claim) controls the *prescribed* origin value, `S`, every `S_{-i}`, and each
obstacle cap continuously. It says nothing about `gain_i(x) = sup_w u_i(x[i→w])
- u_i(x)`, the supremum over unilateral deviations, because that supremum is
evaluated by a *different* recursion — the companion/deviation map with
terminal value `Λ_i = max{0, r_i({i})}` — not the prescribed recursion with
terminal value `0`. Trace-nearness controls the first; it does not control
the second.

**The witness (`I = {1,2,3}`).** `r_2 = r_3 = 0`; `r_1(J) = 0` if
`J ∩ {1,2} = ∅`, `r_1(J) = 1` if exactly one of `1,2` is in `J`, `r_1(J) = -1`
if both are in `J`. Take the one-row array `x* = ((0, 1/2, 0))`. It is
complementary (`g_1(0) = -1/2 ≤ 0` since `x*_{0,1}=0`; `g_2=g_3=0`). Its
prescribed value is `u_1(x*) = 1/2`. Deviating by `w_0=0, w_1=1` (waiting one
step past the array's end) achieves value `1`, so `gain_1(x*) = 1/2` — exactly
the transported terminal term `S_{-1}(1)·Λ_1 = (1/2)·1`.

**The robust floor.** Let `z_* = F(x*) ∈ 𝔗_r`. Using an upper bound on the
prescribed value in terms of terminal survivals and a lower bound from one
fixed deviation, the source derives: for `α = 1/12`, every finite trace
within a computed radius `η` of `z_*` has `gain_1(x) ≥ 1/2 - 3α = 1/4`. Taking
`ε_0 = min{η/2, 1/8}` gives `max_i gain_i(x) ≥ 1/4 > ε_0` for **every** finite
array (complementary or not) within `ε_0` of `z_*` in the trace.

**Density and usability come apart.** `z_*` is not a non-finite closure
artifact — it is literally `F(x*)` for a finite complementary array. So the
carrier contains an actual finite object satisfying every relaxed condition,
arbitrarily close to which no array (finite, complementary, or otherwise) has
small gain.

**Why the chronological-profile mark does not help.** `z_*` already has a
fully known, single-row chronology with no unresolved zero-mass pieces or
competing lifts. Marking it changes nothing about `gain_1(x*) = 1/2`, and the
whole marked neighborhood remains subject to the same lower bound. What is
missing is not chronological information but an explicit condition that the
*transported terminal debt* at the origin — computed by the deviation
recursion with terminal value `Λ_i`, not the prescribed recursion — vanish.

**Also established (Part A):** the relaxed package is a **genuine**
weakening, not a cosmetic one — an explicit non-finite element of `𝔗_r` (a
parabolic-arc limit) satisfies the relaxed conditions without being the trace
of any finite array — and the relaxed package is **closed** under limits
within `𝔗_r`.

**Non-claims.** This does not refute equilibrium existence, nor does it
refute the carrier claim itself; it refutes only that the *relaxed package
alone* certifies small gain. It does not attempt a repaired certificate
(e.g. a deviation-envelope condition with terminal value `Λ_i` added to the
package); that is left as the next discriminant.

## What is already machine-checked

The general machinery the witness computation leans on — but not the
witness computation itself — has machine-checked precedent:

- **The exact transport law.**
  `quittingFiniteDynamicDebt_eq_max_zero_sub_accumulatedStageGaps` in
  `GameTheory/Concepts/Stochastic/QuittingDynamicDebtTransportLaw.lean`
  proves the closed form `debt = max 0 (survivalWeight·terminalDebt -
  Σ survivalWeight·max 0 stageGap)`, establishing that the deviation
  transport is a contraction with truncation, never an amplification. This is
  the production-Lean analogue of the "transported terminal term" identity
  the source cites as standing machinery (its §1b, "Tools already
  available").
- The signed-phasewise-accumulation-equals-relaxed-cycle-gain identity is
  also cited as standing machinery in the source, but its own general
  statement remains `OPEN`/unformalized per
  [`TheSignedAccumulationIsTheGain.md`](../AbsorbingCycleCarrier/TheSignedAccumulationIsTheGain.md),
  and its `P_who = 1` (isolated) specialization was recently found to compute
  the **wrong** value in `QuittingRelaxedCycleGainIsolatedCoordinate.lean`.
  Treat any citation of that identity in this claim's ancestry as carrying
  that specific, now-known caveat, even though the witness above does not use
  the isolated case.

The witness array `x*`, the weight, and the gain-floor inequality (the actual
content of this claim) are **not** formalized anywhere in this repository.

## Claim ledger

| ID | Exact claim | Verdict | Seals | Scope | Consumer |
| --- | --- | --- | --- | --- | --- |
| E1 | The relaxed package is a strict weakening of literal rowwise complementarity (non-finite witness `z_A`) | `PROVED` | `M [reported]` | general | shows `𝔗_r`'s relaxation is not cosmetic |
| E2 | The relaxed package is closed under limits in `𝔗_r` | `PROVED` | `M [reported]` | general | needed for the package to be a well-posed target |
| E3 | The relaxed package does **not** certify small gain: `z_*` above has a robust gain floor `1/4` on its whole `ε_0`-neighborhood | `PROVED` | `M [reported]` | the exhibited 3-coordinate weight | closes `MATH-P0-2`'s limit-object route as posed |
| E4 | The chronological-profile mark does not repair E3 | `PROVED` | `M [reported]` | same | rules out the cheapest proposed fix |
| E5 | `z_*` is itself a finite complementary trace, not merely a closure artifact, so density and usability come apart inside the carrier | `PROVED` | `M [reported]` | same | sharpens E3: the failure is not confined to non-finite limits |

## Falsifiers and wrong turns

- **The direct falsifier.** Re-derive the bound `gain_1(x) ≥ 1/4` on the
  stated `ε_0`-neighborhood of `z_*` by hand; a slip in the upper/lower bound
  derivation (source equations (18)–(23)) would collapse the floor.
- **Do not read `MATH-P0-1`'s pullback (value/cap/trace approximation) as
  gain control.** That confusion is exactly what this claim exists to
  foreclose; see `CompletedVectorFactorTraceIsCompactAndDetermining.md`'s
  B2/B3 for what pullback *does* control.
- **Do not treat this as a refutation of the carrier itself.** `𝔗_r`'s
  compactness/determination claim is untouched; what fails is a specific
  proposed use of it (certifying gain directly from the relaxed package).
- **Do not assume every `z ∈ 𝔗_r` has a gain floor.** Only `z_*` is exhibited;
  the claim is existential ("there is a `z` for which...").

## Production map

```text
Question152 (external solver's answer, assumes Question150 unaudited) -> [MISSING: internal audit] -> no production surface
```

This closes the limit-object route to `MATH-P0-2` **as posed**; per
`PIPELINE.md`, the surviving route is the repair ladder
(`MATH-P0-3`/[`StationaryRepairExhaustion`](../StationaryRepairExhaustion/README.md))
and the anchored-repair capstone
([`AnchoredRepairOrUniformDebtDescent.md`](AnchoredRepairOrUniformDebtDescent.md)).
Nothing here is formalized; missing arrows in order of value: (1) an
independent hand-audit of the gain-floor inequality; (2) a repaired
certificate (deviation-envelope condition with terminal value `Λ_i`) that the
source suggests but does not supply; (3) a Lean regression for `x*`'s gain
computation, which would be cheap given the existing `QuittingDynamicDebtTransportLaw`
machinery.

## Exit conditions

- `MINED` once the gain-floor witness is independently re-derived and either
  a repaired certificate is found or the repair ladder supersedes this route
  entirely.
- `WRONG` if the witness computation fails to reproduce under audit.
- `BLOCKED` if the repaired-certificate direction (a deviation-envelope
  condition added to the relaxed package) cannot be stated without importing
  unstated assumptions from the source.
