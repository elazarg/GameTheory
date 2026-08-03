# Finite-group Reynolds sums for invariant welfare weights

## Lifecycle

| Field | Value |
| --- | --- |
| Lifecycle | `PENDING` |
| Verdict | `MIXED` |
| Objective priority | `P2` |
| Last audited | 2026-08-03, isolated experiment `FiniteGroupInvariantWeights.lean` |
| Central live claim | Orbit-summing a positive welfare weight produces a positive invariant weight, and summing transported welfare caps produces the cap for that invariant weight. |
| Next discriminant | Supply or refute the game-automorphism transport of one non-invariant all-profile welfare cap. |
| Production destination | Possible producer for the invariant-weight hypothesis of coalition security--welfare assembly; none without an actual cap-transport adapter. |
| Supersedes / superseded by | Independent Reynolds component used by `ideas/CoalitionSplittingGroupActions/README.md`; distinct from cyclic clock averaging. |

### Claim ledger

| ID | Exact claim | Verdict | Seals | Scope / consumer |
| --- | --- | --- | --- | --- |
| GIR1 | The orbit sum of a strictly positive weight under a finite group action is strictly positive and invariant. | `PROVED` | `X` | `FiniteGroupInvariantWeights.lean`. |
| GIR2 | Weighted evaluation at the orbit-summed weight is the sum of evaluations at all translated weights. | `PROVED` | `X` | Finite double-sum identity. |
| GIR3 | If every translated weight has a cap with error `epsilon`, the orbit-summed weight has the summed cap with error `|Gamma|*epsilon`. | `PROVED` | `X` | Pointwise finite algebra. |
| GIR4 | Uniform welfare caps for all translated weights combine into the production cap for the invariant orbit weight. | `PROVED` | `X` | Divide the error by `|Gamma|` and take the finite supremum of horizons. |
| GIR5 | One stochastic-game welfare cap transports to every translated weight under a supplied game automorphism. | `OPEN` | `I` | Actual states/actions/kernel/payoff adapter. |

### Falsifiers and wrong turns

- Averaging weights does not create a welfare cap from no cap; GIR3 needs the
  inequality for every translated weight.
- A player permutation that is not a game automorphism does not transport the
  all-profile payoff inequality.
- Positivity of the original weight is essential for the assembly theorem;
  orbit-summing a signed separator can leave zero coordinates.
- This Reynolds sum acts on player coordinates.  It is unrelated to removing
  zero-frequency oscillations from a cyclic time signal.

### Production map

```text
positive weight ----------------orbit sum--> positive invariant weight [X]
one welfare cap --game automorphisms-------> all translated caps       [?]
all translated caps --------------sum------> invariant welfare cap     [X]
invariant cap + transported singleton floors -> uniform payoff         [L]
```

### Exit conditions

- Upgrade GIR1--GIR3 to `M` only after independent mathematical audit.
- Mark `MINED` after independent audit and either a named actual-data adapter
  or a proof that the constant-one weight already covers every intended use.
- Mark GIR5 `WRONG` for a proposed symmetry if payoff or profile transport
  changes the cap statement.
- Mark `PARKED` when no live coalition split yields a non-invariant cap worth
  symmetrizing.

## 1. Orbit-summed weights

Let a finite group `Gamma` act on the finite player set `I`, and let
`alpha : I -> R`.  Define the unnormalized Reynolds sum

```text
barAlpha(i) = sum_(g in Gamma) alpha(g.i).       (1.1)
```

Normalization by `|Gamma|` is unnecessary for security--welfare assembly,
because multiplying every positive weight and its cap by one positive scalar
does not change saturation.

### Theorem 1

If `alpha(i) > 0` for every player, then `barAlpha(i) > 0` for every player.
Moreover,

```text
barAlpha(h.i) = barAlpha(i)
```

for every `h : Gamma`.

### Proof

The sum in (1.1) is nonempty and every summand is positive.  For invariance,

```text
barAlpha(h.i)
  = sum_g alpha(g.(h.i))
  = sum_g alpha((g*h).i)
  = sum_k alpha(k.i),
```

because right multiplication by `h` permutes the finite group.  QED.

For a transitive action, every invariant weight is constant on players, so
`barAlpha` is a positive constant weight.  For several player orbits it may
take a different positive value on each orbit.

## 2. Summing translated caps

For a payoff vector `x`, write

```text
W_alpha(x) = sum_i alpha(i) * x(i).
```

Finite sum interchange gives

```text
W_barAlpha(x)
  = sum_g W_(g.alpha)(x),
```

where `(g.alpha)(i) = alpha(g.i)` under the convention (1.1).

Suppose for every `g` one has

```text
W_(g.alpha)(x) <= W_(g.alpha)(v) + epsilon.
```

Summing over `g` yields

```text
W_barAlpha(x)
  <= W_barAlpha(v) + |Gamma| * epsilon.          (2.1)
```

For a uniform cap requested at error `delta`, apply each transported cap at
`epsilon = delta / |Gamma|` and take the maximum of the finitely many horizon
thresholds.  The experiment proves this directly for the production
`HasUniformWeightedWelfareCap` predicate.  Thus a game automorphism transport
theorem for one cap would produce a positive invariant cap.

## 3. Coalition-splitting use

The coalition assembly theorem needs positive weights but not invariance.
Invariance becomes useful when symmetry is used to reduce all singleton split
certificates to player-orbit representatives: the aggregate ceiling should
respect the same relabeling.  GIR1--GIR3 show that this requirement need not be
assumed at the level of the original separator.  It can be manufactured from
the full orbit of any transported positive cap.

The hard step remains GIR5.  It requires an automorphism of the actual game,
not merely a permutation of `I`, and it must quantify over transported
behavior profiles so that the cap remains valid for **every** profile.
