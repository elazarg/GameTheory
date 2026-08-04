# Mismatch vanishes except on isolated negative coordinates

## Lifecycle

| Field | Value |
| --- | --- |
| Lifecycle | `ACTIVE` |
| Verdict | `PROVED` |
| Objective priority | `P0` |
| Last audited | 2026-08-04, `7af7acc` |
| Central live claim | An absorbing complementary cycle has positive deviation mismatch at a coordinate `i` if and only if every opponent of `i` is silent at every phase and `r_i({i}) < 0`; the mismatch is then exactly `-r_i({i})`. |
| Next discriminant | Formalize against the cycle-pinned debt definition; the transport law it rests on is already production. |
| Production destination | `QuittingCyclePinnedDebt.lean` (in flight) |
| Supersedes / superseded by | none |

## Claim ledger

| Claim | Verdict | Seals | Scope | Consumer |
| --- | --- | --- | --- | --- |
| The cyclic composite `T_i` is `P_i`-Lipschitz and fixes `z_{1,i}` | `PROVED` | `M` | any cycle, **any sign** of terminal mismatch | everything below |
| The mismatch is `0` whenever `P_i < 1` | `PROVED` | `M` | as above | reduces existence of zero-mismatch cycles to existence of cycles |
| `P_i = 1` forces the isolated configuration, and then the mismatch is `[-r_i({i})]₊` | `PROVED` | `M` | absorbing cycles | the admissibility condition in the carrier |
| At most one coordinate is isolated in an absorbing cycle | `PROVED` | `M` | absorbing cycles | makes the mismatch value unambiguous |
| Unrolling the transport law gives `δ_i^{(N)} = [P_i^N μ_i - C_i(1 + P_i + … + P_i^{N-1})]₊` | `PROVED` | `M` | **only when `μ_i ≥ 0`** | superseded as the main route; see below |

Notation: `P_i = ∏_k c_{-i}(y_k)` is the deleted survival product around the
cycle, `C_i = Σ_k (∏_{k'<k} c_{-i}(y_{k'})) · g_i(y_k, z_{k+1})⁺` the
accumulated credit, `μ_i` the terminal mismatch, `Λ_i = max{0, r_i({i})}`.

## The anchor

The mismatch must be defined against an anchor, because in the isolated case the
cycle map has a continuum of fixed points. Let `T_i` be the composite of the
phase maps `w ↦ max{Σ_i(y_k), A_i(y_k) + c_{-i}(y_k)·w}` around the cycle, and
define

    ẑ_i := lim_N T_i^N(Λ_i),        mismatch := ẑ_i - z_{1,i}.

The anchor `Λ_i` carries the entire content: anchoring at `z_{1,i}` instead
would make the mismatch identically zero. `Λ_i` is the right anchor because
against permanently silent opponents the deviating coordinate's achievable
payoffs are exactly `{r_i({i}), 0}`, with supremum `Λ_i`.

## Statement and proof

**The route is a contraction estimate, not the unrolled transport law.** Each
phase map is `c_{-i}(y_k)`-Lipschitz, so `T_i` is `P_i`-Lipschitz; and
complementarity at every `(y_k, z_{k+1})` makes `z_{1,i}` a fixed point of
`T_i`, since the value recursion has exactly the same max form. Hence

    |T_i^N(Λ_i) - z_{1,i}| ≤ P_i^N · |μ_i|,     μ_i := Λ_i - z_{1,i},

**for either sign of `μ_i`**. So `P_i < 1` gives mismatch `0` outright.

**Why not the unrolled law.** The production transport law
`δ_i(t) = [c_{-i}(x_t)·δ_i(t+1) - g_i(t)⁺]₊` and its geometric unrolling require
a **nonnegative** terminal debt, and `μ_i ≥ 0` is *not* automatic for absorbing
complementary cycles. Witness, which lies inside this program's own
solo-quitter family: `n = 2`, `r_1({1}) = 0`, `r_1({2}) = 1`,
`r_1({1,2}) = 0`, `r_2({2}) = 1/2`, all other entries `0`; the length-one cycle
`y = (0, 1/2)`, `z = (1, 1/2)` is complementary and absorbing, and
`μ_1 = Λ_1 - z_1 = 0 - 1 = -1 < 0`. There the geometric formula predicts
`δ^{(N)} = 0` while the truth is `-2^{-N}`. The unrolled law is therefore an
upper bound only, off the nonnegative-mismatch regime, and must not be used as
the general route. It remains correct and useful whenever `μ_i ≥ 0`.

`P_i = 1` means `c_{-i}(y_k) = 1` at every phase — every factor of a product of
`[0,1]`-numbers equalling one — i.e. every opponent `j ≠ i` has `y_{k,j} = 0` at
every `k`, the **isolated** configuration. In it,
`Σ_i(y_k) = r_i({i})` and `A_i(y_k) = 0`, so `g_i = r_i({i}) - z_{k+1,i}`, and
the value recursion collapses to the cyclic convex combination

    z_{k,i} = y_{k,i}·r_i({i}) + (1 - y_{k,i})·z_{k+1,i}.

Absorption forces `y_{k,i} > 0` for some `k` (only `i` can supply absorbing
mass), so the unique cyclic solution is `z_{k,i} = r_i({i})` at every phase.
Hence `g_i ≡ 0`, `C_i = 0` automatically, and

    μ_i = Λ_i - r_i({i}) = [-r_i({i})]₊.

So the mismatch is positive exactly when `r_i({i}) < 0`, with value `-r_i({i})`.

**Reading.** The deviating coordinate gains only when it is alone in a cycle
that forces it to absorb at a loss, and waiting forever escapes that loss. Any
opponent quitting with positive probability anywhere in the cycle destroys the
gain.

**At most one coordinate is isolated.** Two isolated coordinates would silence
every coordinate at every phase, giving `∏_k c(y_k) = 1` and contradicting
absorption. So the exceptional case involves a single coordinate and the
mismatch value is unambiguous, independent of the norm chosen on `ℝ^I`.

**The credit term is not load-bearing.** Under complementarity `P_i = 1` forces
isolation, which forces `g_i ≡ 0` and hence `C_i = 0`. So the branch
"`P_i = 1` and `C_i > 0`" is vacuous, and for `P_i < 1` the contraction estimate
alone suffices. `C_i` can be dropped from the statement entirely; it is retained
above only because the unrolled law is the production route for the
nonnegative-mismatch case.

## Falsifiers and wrong turns

- If some cycle with `P_i < 1` is exhibited with positive mismatch, the
  contraction estimate is wrong; check that `z_{1,i}` really is a fixed point of
  `T_i`, which is where complementarity at *every* phase is consumed.
- **Wrong turn already taken and corrected:** proving the `P_i < 1` case from
  the unrolled transport law. That law needs `μ_i ≥ 0`, which fails on
  absorbing complementary cycles — including ones produced by this program's own
  solo-quitter construction, where the non-isolated coordinates can have
  `μ_j = Λ_j - r_j({i}) < 0`. An adversarial audit caught this; the contraction
  route replaces it and is sign-free.
- **Wrong turn already taken:** stating the cycle notion without the absorption
  requirement. The all-continue list then reproduces every value vector and is
  complementary whenever `z_i ≥ r_i({i})`, so "every weight admits a
  zero-mismatch cycle" would be true and vacuous. Absorption is what makes `z`
  a function of the rows.
- The claim is about the deviation mismatch of a cycle, not about the optimized
  debt of a zero-pinned chain. Those differ precisely by the pin.

## Production map

Rests on the production transport law
`quittingFiniteDynamicDebt_eq_max_zero_sub_accumulatedStageGaps` and its
corollaries (fence-free equality; zero terminal debt gives zero debt; the stage
gap ignores its own coordinate). Destination is the cycle-pinned debt module.
Missing arrow: the cycle iteration itself, which needs the cyclic composite and
its contraction estimate.

## Exit conditions

`MINED` once formalized and consumed by the existence claim. `WRONG` if a
counterexample cycle with `P_i < 1` and positive mismatch is exhibited.
