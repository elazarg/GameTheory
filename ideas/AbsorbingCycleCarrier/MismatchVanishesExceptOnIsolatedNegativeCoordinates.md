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
| Unrolling the transport law over `N` repetitions of a cycle gives `δ_i^{(N)} = [P_i^N μ_i - C_i(1 + P_i + … + P_i^{N-1})]₊` | `PROVED` | `M` | any cycle, any nonnegative terminal mismatch | the two below |
| The mismatch is `0` whenever `P_i < 1` or `C_i > 0` | `PROVED` | `M` | as above | reduces existence of zero-mismatch cycles to existence of cycles |
| Positive mismatch forces the isolated configuration, and then equals `[-r_i({i})]₊` | `PROVED` | `M` | absorbing cycles | the admissibility condition in the carrier |

Notation: `P_i = ∏_k c_{-i}(y_k)` is the deleted survival product around the
cycle, `C_i = Σ_k (∏_{k'<k} c_{-i}(y_{k'})) · g_i(y_k, z_{k+1})⁺` the
accumulated credit, `μ_i` the terminal mismatch, `Λ_i = max{0, r_i({i})}`.

## Statement and proof

The production transport law gives, for a finite window,

    δ_i(t) = [c_{-i}(x_t)·δ_i(t+1) - g_i(t)⁺]₊

and its unrolled closed form. Applying it to `N` repetitions of a cycle and
using `[q[w]₊ - s]₊ = [qw - s]₊` for `q, s ≥ 0` gives the displayed geometric
form. Then:

- if `P_i < 1`, the transported term `P_i^N μ_i → 0` while the subtracted sum
  increases to `C_i/(1 - P_i) ≥ 0`, so the limit is `0`;
- if `P_i = 1` and `C_i > 0`, the subtracted sum is `N·C_i → ∞`, so the limit
  is `0`;
- if `P_i = 1` and `C_i = 0`, the expression is constantly `μ_i`.

`P_i = 1` means `c_{-i}(y_k) = 1` at every phase, i.e. every opponent `j ≠ i`
has `y_{k,j} = 0` at every `k` — the **isolated** configuration. In it,
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
opponent quitting with positive probability anywhere in the cycle, or any stage
at which `i` quits with probability one at a strict gain, destroys the gain.

## Falsifiers and wrong turns

- If some cycle with `P_i < 1` is exhibited with positive mismatch, the
  geometric unrolling is wrong; check the `[q[w]₊ - s]₊` step, which needs
  `q, s ≥ 0` and fails for a negative terminal mismatch.
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
