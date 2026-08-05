# The min-max is a stationary stopping value

| Status | Provenance | Consumer | Falsifier |
| --- | --- | --- | --- |
| `OPEN`, maturity `M [reported]` (with one instantiation refuted, see below), P0 | Q162 | phase-switch punishment attainment; circulation floors; branch-three mismatch; Q163's reservation bridge | an error in the stationarity proof, or a weight where a nonstationary plan punishes strictly better |

## The theorem

For player `j` of a quitting weight, with `S_j(y)` the stop payoff and
`H_j(y)` the opponent-absorption contribution of a constant opponent row `y`:

> `χ_j = inf_y Φ_j(y)`, where `Φ_j(y) = max{ S_j(y), H_j(y)/(1−c(y)) }`
> for `y ≠ 0` and `Φ_j(0) = max{d_j, 0}`.

**Stationary opponent plans suffice in value** — no phased or nonstationary
plan punishes below the best constant row — and for every `ε > 0` a constant
row repeated forever is `ε`-optimal (rational rows for rational tables).
Exact attainment can fail. The reply side rides pure stopping times (the
payoff is affine in each own hazard), which is what makes `Φ` a two-branch
maximum.

## The computed tables

- **Hostile two-coordinate table**: `χ = −1000` exactly, attained by the
  opponent quitting surely; the machine-checked horizon-two value `−500` is
  pure averaging dilution. The band `χ = −1000 < 0 = ceiling` is maximal.
- **Scaled cyclic weight**: `χ = 1/6` at every coordinate — the recorded
  `1/3` bound (one neighbour quits surely) is **not tight**; the minimizer
  mixes the zero-paying neighbour surely with the other at rate `1/2`,
  equalizing stop and continue at `1/6`. Both directions of the bound are
  by short explicit inequalities. Note for consumers: the circulation floor
  there used `max{d, χ} = 1/3` via `d = 1/3`, so the sharpened `χ` changes
  no landed certificate.
- **The repaired four-player family — the answer's C3 is REFUTED.** It
  asserts every coalition omitting `j` pays `1` and concludes `χ ≡ 1`. The
  premise is false: **solo** coalitions pay the cyclic `(1, 3, x, 0)`
  pattern — the repair gave `1` to outsiders of coalitions of size `≥ 2`
  only. The contradiction with the Q160-followup's two-punisher formula
  (`χ(2,1) = 2/3`, boundaries `x = 1/2`, `x₊(λ)`) therefore resolves in the
  **followup's favour**; the cross-check fence in the question predicted
  exactly this adjudication. The general formula stands; only this
  instantiation was botched. Downstream: certificates using floor `1` are
  unaffected (`χ ≤ max{0,d} = 1` always, so floor `1` is conservative).

## Consumer forms

The answer's D-sections restate the results in the three consumed shapes
(phase-switch punishment for the band, circulation floors, the
isolated-negative mismatch with true `χ`); to be wired when the punishment
attainment lands. The formula makes `χ` a finite-dimensional optimization —
certifiable brackets for rational tables — which is what the certsearch
floor needed.

## Open

- Formalize the stationarity theorem and the formula (the reply-side
  stopping structure plus the two-branch `Φ`).
- The corrected `F′` min-max: the followup's two-punisher derivation is the
  standing account; a re-derivation through this formula (with the solo
  pattern handled correctly) would confirm both.
- Exact attainment characterization (when is the inf attained).
