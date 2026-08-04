# The carrier needs the zero-solo disjunct

## Lifecycle

| Field | Value |
| --- | --- |
| Lifecycle | `ACTIVE` |
| Verdict | `WRONG` as stated without the disjunct; `OPEN` in the corrected form |
| Objective priority | `P0` |
| Last audited | 2026-08-04, `7cc6f77` |
| Central live claim | "Every weight admits an admissible absorbing cycle" is **false**. The corrected statement is: every weight either has `Λ = 0`, in which case the landed zero branch already applies, or admits an admissible absorbing cycle. |
| Next discriminant | Decide the corrected statement on weights with some `r_i({i}) > 0`. |
| Production destination | none yet |
| Supersedes / superseded by | corrects the reduction recorded in this group's README |

## The counterexample

For `I = {1,2}`,

    r({1}) = (0, -1),   r({2}) = (1, -1),   r({1,2}) = (0, 0).

**Every discounted complementary row vanishes.** All coordinate-`1` entries are
nonnegative, so `Z_1^β ≥ 0`, `Σ_1 = 0`, `A_1 = y_2`, and
`g_1^β = -y_2 - β(1-y_2)Z_1^β ≤ 0`; hence `y_1 > 0` forces `y_2 = 0`. With
`y_1 = 0` and `y_2 > 0`, `Z_2^β = -y_2/(δ+βy_2)` and
`g_2^β = -δ/(δ+βy_2) < 0`, contradicting complementarity. So every discounted
row is `(p_δ, 0)`, and letting `δ → 0` forces `p_δ → 0`. This weight is in the
vanishing branch, and all three scale regimes `ρ = 0`, `ρ ∈ (0,∞)`, `ρ = ∞` are
realizable along it.

**No admissible absorbing cycle exists.** Coordinate-`1` values lie in `[0,1]`,
so `Γ_1 ≥ 0` and the max form gives `z_{k,1} = y_{k,2} + (1-y_{k,2})z_{k+1,1}`.
If any phase has `y_{k,2} > 0`, composing around the cycle is an affine map of
slope `∏(1-y_{k,2}) < 1` fixing `1`, so `z_{k,1} = 1` everywhere — but
`y_{k,1} > 0` would force `Γ_1 = 0`, hence `z_{k,1} = 0`. So `y_{k,1} = 0` at
every phase, coordinate `2` is isolated, and since `r_2({2}) = -1 < 0` its
mismatch is `1`. If instead `y_{k,2} = 0` at every phase, absorption forces some
`y_{k,1} = p > 0`, the cyclic value is `z_{k,2} = -1`, and there
`Σ_2 = -1+p` against `Γ_2 = -1`, so `g_2 = p > 0`, contradicting `g_2 ≤ 0` at
`y_{k,2} = 0`.

I verified every step of this by hand. It is correct.

## Why it does not break the program

`Λ_1 = max{0, 0} = 0` and `Λ_2 = max{0, -1} = 0`, so **`Λ = 0`**.

When `Λ = 0` the two recursions have *matched* terminal data, the optimized
zero-boundary debt is identically zero at every cutoff, and the landed zero
branch already delivers terminal approximate equilibria and hence a uniform
payoff. So this weight was never in the hard class; the exact equilibrium is
the all-continue profile, with payoff `(0,0)`, which no player can improve on
since `r_i({i}) ≤ 0` for both.

That is the whole content of the counterexample: **the absorption fence, which
is required to keep the cycle notion from being vacuous, also excludes the
genuinely non-absorbing equilibria.** Those are exactly the weights with
`Λ = 0`, and exactly the ones the zero branch already covers.

## The corrected reduction

> For every weight, either `Λ = 0` — and the landed zero branch applies — or
> the weight admits an admissible absorbing cycle.

The first disjunct is landed (`M+L+C`). The second is the open statement. The
conditional from an admissible absorbing cycle to a uniform equilibrium payoff
is machine-checked and unaffected.

The counterexample cannot be perturbed into the open class without work: it
relies on `Σ_1 ≡ 0`, which needs `r_1({1}) = 0` exactly. Setting
`r_1({1}) = ε > 0` breaks the first step of the argument and puts the weight
outside the `Λ = 0` disjunct simultaneously. Whether some *other* weight with
`Λ ≠ 0` sits in the vanishing branch with no admissible cycle is the live
question.

## Correction to a supplied fact

The vacuity witness for the absorption fence was stated with `z = (1,…,1)`.
That is wrong in detail: with all rows zero the companion map is
`T_i(w) = max{r_i({i}), w}`, so the anchored limit is `Λ_i` and the mismatch is
`Λ_i - z_i`, generally nonzero at `z = 1`. **The correct trivial witness is
`z = Λ`**, where `F_0(Λ) = Λ`, complementarity holds since
`g_i = r_i({i}) - Λ_i ≤ 0` always, and the mismatch is exactly zero. The
conclusion — that absorption cannot be dropped — is unaffected, and is if
anything strengthened: the degenerate witness exists for *every* weight, not
just for large `z`.

## Falsifiers and wrong turns

- Do not read the counterexample as refuting the carrier. It refutes the
  unqualified claim; the disjunctive form survives and is what should be
  quoted.
- Do not attempt to repair it by weakening absorption. The all-continue
  configuration is a genuine equilibrium here, so any notion admitting it is
  correct about this weight and vacuous about every other.
- The zero-solo disjunct is not a special case to be tidied away later. It is
  where the non-absorbing equilibria live, and it is already solved.

## Exit conditions

`MINED` when the corrected statement is decided on weights with some
`r_i({i}) > 0`.
