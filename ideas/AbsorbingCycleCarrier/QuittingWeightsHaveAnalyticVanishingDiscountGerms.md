# Quitting weights have analytic vanishing-discount germs

## Lifecycle

| Field | Value |
| --- | --- |
| Lifecycle | `ACTIVE` |
| Verdict | `PROVED` for germ existence and for convergence of the normalized quit direction; `OPEN` for the matching scaling case and for nondegeneracy |
| Objective priority | `P1` |
| Last audited | 2026-08-04, `c1d77fb` (module landed); tree at `67ad767` |
| Central live claim | Every quitting weight admits a real-analytic vanishing-discount Bellman germ, and along it the normalized quit direction **converges** — not merely along subsequences. |
| Next discriminant | Expand the absorption product to first order to *pin* the matching scaling case `q = m`, which is currently only squeezed; and decide whether the nondegeneracy hypothesis is available on the vanishing-absorption branch or is vacuous exactly there. |
| Production destination | `GameTheory/Concepts/Stochastic/QuittingAnalyticGerm.lean` (landed), over `Math/AnalyticOrderComparison.lean` (landed) |
| Supersedes / superseded by | none; supplies a producer for the hard branch of [`VanishingAbsorptionIsTheOnlyRemainingCase.md`](VanishingAbsorptionIsTheOnlyRemainingCase.md) |

Priority is `P1` rather than `P0` deliberately: this is a load-bearing
*producer*, not a step on the shortest path. It regularizes the discounted
family that the dichotomy already relies on, but it does not by itself decide
the vanishing-absorption branch, and two of its clauses (the matching case,
nondegeneracy) are not closed.

## Claim ledger

| ID | Exact claim | Verdict | Seals | Scope | Consumer |
| --- | --- | --- | --- | --- | --- |
| G1 | Every quitting weight has a real-analytic vanishing-discount Bellman germ | `PROVED` | `M+L` | all finite quitting weights | everything below |
| G2 | The decoded quit mass **is** the germ's `mix none i true` coordinate | `PROVED` | `M+L` | along any germ, `0 < t < radius` | makes the quit family an analytic object |
| G3 | The active-state value satisfies `V · (1 − β · c) = β · R`, with `c` the all-continue mass and `R` the one-stage absorbing contribution | `PROVED` | `M+L` | same | the discounted analogue of the stationary balance law |
| G4 | The endpoint difference is the discounted gap `Σ_i(y) − (A_i(y) + c_{−i}(y) · V_i)` in the quitting layer's deleted coordinates | `PROVED` | `M+L` | same | connects the germ to the quitting layer's own complementarity |
| G5 | Exact endpoint Nash is **equivalent** to the two pure best-response inequalities *together with* the active-state Bellman equality, at strictly positive discount | `PROVED` | `M+L` | any `W`, `root`, `β > 0`; stated germ-free | the dictionary capstone |
| G6 | The quit rates are analytic at `0`, and the discount complement is exactly `t ^ q` for the germ's ramification `q` | `PROVED` | `M+L` | along any germ | input to the order machinery |
| G7 | Feeding `Math.AnalyticOrderComparison` gives a **converging** normalized quit direction and reduces the scaling regime to the comparison of two naturals `q` versus `m` | `PROVED` | `M+L` | germs satisfying nondegeneracy — see `F4` | the point of the file |
| G8 | Total absorption `1 − ∏_j (1 − y_j)` is analytic and squeezed between the total quit mass and its `n`-fold multiple; the negligible and dominant scaling cases transfer verbatim to absorption | `PROVED` | `M+L` | same | turns a statement about quit rates into one about absorption |
| G9 | The matching case `q = m` transfers only as a squeeze, between `1/(n · Σa)` and `1/Σa` | `PROVED` as a squeeze; `OPEN` as a limit | `M+L` | same | the gap `F5` names |

Every `L` here is a declaration of
`GameTheory/Concepts/Stochastic/QuittingAnalyticGerm.lean`, which is imported by
`GameTheory.lean` and contains no `sorry`; `Math/AnalyticOrderComparison.lean`
is imported by `Math.lean` and likewise contains no `sorry`. **Axiom-cleanliness
is reported by the module's author and was not re-checked by a build in this
audit**; the textual `sorry` check was.

Declaration map for the ledger: `G1` is
`nonempty_analyticBellmanGerm_quittingGame`; `G2` is
`quittingGermRoot_apply_true_toReal`; `G3` is `quittingGermValue_mul_one_sub`,
with `quittingGermValue_eq_smul_rootSuccessorPayoff` as the recursion it comes
from; `G4` is `quittingGerm_endpointDifference_eq`; `G5` is
`isεQuittingRootEndpointNash_zero_iff_of_rootRecursion`, applied at the germ by
`isεQuittingRootEndpointNash_quittingGermRoot`; `G6` is
`analyticAt_quittingGermQuitRate` and `quittingGerm_discountComplement`; `G7` is
`exists_quittingGermQuitRate_leadingOrder_normalization`; `G8` is
`quittingGermAbsorption_bounds`, `analyticAt_quittingGermAbsorption`,
`tendsto_pow_div_quittingGermAbsorption_nhds_zero` and
`..._atTop`; the whole dictionary is packaged as `quittingGerm_dictionary`.
Absorbed states being pinned to the weight —
`quittingGerm_assignment_val_some` — is what makes the dictionary a statement
about the quitting weight rather than about an arbitrary value assignment.

## Germ data from the endgame probe (2026-08-05, `X`)

Numerical germ extractions, discovery-grade, recorded here so the symbolic
ledger and the probe do not drift apart:

- **The disjunction witness has ramification `q = 2`** — both quit rates
  scale as `√t`, and the germ's natural parameter for that weight is
  `√(1−β)`. Not previously stated anywhere in the symbolic record; a direct
  target for `G6`'s machinery (extract `q` symbolically and confirm).
- **`ρ` is a germ invariant, not a weight invariant — fence confirmed on
  data.** The probe's `ρ̂ ≈ 1/3` for the FTV table against the hand-computed
  `ρ = 0` traces to *different germs*: the symmetric stationary branch versus
  the nonstationary period-3 cycle. Not a contradiction — the fence firing
  exactly as written. Any future use of a numerically extracted `ρ` must name
  which germ it rode.
- All three tested paths tracked a **single support pattern over twenty
  orders of magnitude** of `t` — the pattern-redetection machinery is built
  but unstressed; a weight with a genuine support switch is still wanted as a
  test article.

## What this buys

The dichotomy of
[`VanishingAbsorptionIsTheOnlyRemainingCase.md`](VanishingAbsorptionIsTheOnlyRemainingCase.md)
runs on a family of discounted complementary rows and a *convergent
subsequence*. Two things are unsatisfying about that: the subsequence is chosen
non-canonically, and the resulting limit carries no regularity.

The germ replaces both. Along it every coordinate is an analytic function of a
single curve parameter, so:

- the vanishing direction is a genuine limit, not a subsequential cluster
  point — `G7`;
- the comparison of the vanishing discount against the vanishing absorption,
  which is the entire content of the "scale regime" language used elsewhere in
  this program, becomes a comparison of two natural numbers, the ramification
  `q` against the family's leading order `m` — `G7`, transferred to absorption
  by `G8`.

Before this module no file in the repository imported both the quitting layer
and the analytic Bellman-germ layer. `G5` is the join: the germ's polynomial
best-response inequalities and the quitting layer's own zero-regret root
complementarity are the same condition, given the Bellman equality at positive
discount.

## Falsifiers and wrong turns — all five are load-bearing

- **`F1` Positivity of the discount is not free.** The germ's radius is
  unbounded, so the curve parameter `t` can exceed `1` and the discount factor
  `1 − t^q` can be negative or zero. Every statement that consumes `β > 0` —
  in particular `G5` and hence exact endpoint Nash — carries the extra
  hypothesis `t < 1` (`quittingGerm_discountFactor_pos`). A downstream proof
  that drops it is unsound, not merely imprecise. **Falsifier for any such
  proof:** instantiate it at a germ of radius above `1` and a parameter above
  `1`.
- **`F2` The germ discards the sign pattern.** `AnalyticBellmanGerm` retains
  only `IsPolynomialBellmanSolution` and throws away the sign cell's pattern
  `τ`. So **nothing here freezes which best-response inequalities are slack**
  along the germ; complementarity is re-derived pointwise at each `t`. Any
  argument that assumes a fixed slack pattern — "the same coordinates are
  indifferent all along the curve" — does not follow from this module and needs
  `exists_analyticBellmanGerm_of_positiveCoordinateArc` directly. **Falsifier:**
  exhibit a germ whose active set changes along the curve; the module permits
  it.
- **`F3` The endpoint is prescribed, not regularized.** `analyticBellmanGermExistence`
  prescribes the endpoint of the germ it produces. It does **not** take a given
  sequence of discounted complementary rows and produce an analytic curve
  through it. Putting a prescribed point in the closure of a sign cell is extra
  work not done here. **Falsifier for the over-reading:** any use of the form
  "let `(y_δ)` be the discounted family of the dichotomy; by `G1` it is
  analytic" is invalid.
- **`F4` Nondegeneracy is a hypothesis and is not discharged.** `G7` needs some
  player to quit with positive probability arbitrarily close to `t = 0`
  (`hne` in `exists_quittingGermQuitRate_leadingOrder_normalization`). A germ
  along which everybody continues forever has the identically-zero quit family
  and no normalized direction at all. **This is the sharpest falsifier
  available**, and it points at the case that matters: the hard branch of the
  dichotomy is precisely the one where absorption degenerates. If the germs of
  the vanishing-absorption weights all have identically-zero quit rates near
  `0`, then `G7` is vacuous exactly where it was wanted. Deciding this is the
  named next discriminant.
- **`F5` The matching case is squeezed, not pinned.** For `q = m` the transfer
  to absorption bounds the limit between `1/(n · Σa)` and `1/Σa` rather than
  determining it (`G9`). Pinning it requires expanding the absorption product
  `1 − ∏_j(1 − y_j t)` to first order, i.e. showing the higher-order terms of
  the product do not contribute at the leading order. **Falsifier for a
  downstream argument:** any consumer needing the exact constant in the
  matching regime is currently unsupported.

Two further reading errors worth naming:

- the `discount := 0` field of `quittingGame` plays no role anywhere in this
  development; `IsDiscountedStationaryBellmanEq` carries the discount factor as
  an explicit argument, so a reader concluding "the game is undiscounted, hence
  this says nothing about discounted play" is wrong;
- absorbed states are pinned to the weight with no residual discount
  dependence, so a proof looking for a discount correction at absorbed states is
  looking for something that is provably zero.

## Production map

```text
analyticBellmanGermExistence  (AnalyticBellmanExistence.lean)
        |
        v
nonempty_analyticBellmanGerm_quittingGame        [G1, landed]
        |
        +--> quittingGerm_dictionary             [G2-G5, landed]
        |
        +--> analyticAt_quittingGermQuitRate     [G6, landed]
                |
                v
        Math.exists_leadingOrder_normalization   (AnalyticOrderComparison.lean)
                |
                v
        exists_..._leadingOrder_normalization    [G7, landed, needs `hne`]
                |
                v
        tendsto_pow_div_quittingGermAbsorption_* [G8, landed; matching case G9 squeezed]
                |
                v
        [MISSING] the vanishing-absorption branch of the dichotomy
```

Missing arrows, in order of value:

1. discharge or refute `hne` on the weights in the vanishing-absorption branch
   (`F4`) — without this the chain is conditional at its most important link;
2. pin the matching case by the first-order expansion (`F5`);
3. connect the converging normalized direction to an actual cycle or mass-path
   statement. The germ regularizes the family; it does not yet build the
   carrier.

There is currently **no consumer** in the repository: no production theorem
takes `G7` or `G8` as a hypothesis. By the promotion gate of
[`../README.md`](../README.md), that makes this landed infrastructure rather
than closure progress, and the file says so rather than implying otherwise.

## Exit conditions

- `MINED` when the vanishing-absorption branch either consumes the germ or is
  shown not to need it.
- `BLOCKED` if `F4` turns out to require a separate existence theorem —
  a germ with nonvanishing quit rates for the hard weights — which would then
  be the named prerequisite.
- Claim `G7` becomes `WRONG` if a quitting weight is exhibited whose germ has a
  normalized quit direction with two distinct subsequential limits; that would
  refute the order comparison it rests on.
- Claim `G9` is promoted from squeeze to limit, or the file records that the
  squeeze is all that is true.
