# Exact cycles are not limits of relaxed ones

| Status | Provenance | Consumer | Falsifier |
| --- | --- | --- | --- |
| `OPEN`, maturity `M [reported]`, P1 | Q154, Solan 2001 Thm 2.2 | any route producing an exact cycle by limiting relaxed ones | an exact cycle on the witness weight, or a rate bounding the period |

## What this does **not** show

The witness weight below is **zero-solo**: every solo value is `-1/2 ≤ 0`, so
`IsQuittingZeroSolo` holds and the weight lands in the reduction's **first,
already-settled** disjunct, which delivers payoff `0` outright. It needs no
cycle and it **does not bear on completeness of the disjunction**.

The published family likewise has a uniform equilibrium payoff, so its lack of
an exact *equilibrium* contradicts nothing here: an admissible absorbing cycle
is a different object from an exact equilibrium, and the compiler turns the
former into the latter's uniform payoff, not conversely. Whether that family
admits an admissible absorbing cycle is **open**, and is the question that would
actually bear on completeness.

## What it does show

`M [reported]`, Q154. An explicit rational three-coordinate cyclic weight has
`ε`-complementary cycles at every tolerance, of period `3m`, and **no exactly
complementary cycle of any finite period**. The argument is finite: centered
values `zᵢ = Vᵢ + 1/2` are nonnegative because every reward to `i` from an
outcome containing `i` is at least `-1/2`; the local gain identity forces at
most one positive coordinate per exact row; singleton rows pin the active
coordinate's centered value to zero while forcing the predecessor's strictly
positive; the coordinate sum is `1/2` at every phase, which the block-endpoint
vertices cannot meet.

So **exactness is not recoverable from relaxed solutions by any limiting
argument.** Any route that manufactures an exact cycle as a limit of
`ε`-cycles is closed in general — not because the objects fail to converge, but
because the exact object need not exist even when relaxed ones exist at every
tolerance. This closes a proof strategy, which is the whole of its value.

The published theorem is the same phenomenon in a game of independent standing:
the minimal period of a periodic `δ`-equilibrium satisfies
`liminf_{δ→0} d(ε,δ) = +∞` for all small `ε`, with no rate — the proof is a
compactness sketch, and a bounded period would yield an exact limit cycle that
the companion theorem forbids.

## The divergence is not the mass-poor-block artifact

Along Q154's cycles the absorbed mass is constantly `7/8`. The period diverges
with absorption bounded away from zero, so this is not a block too mass-poor to
pay for its own closure. The published mechanism agrees and is sharper: a
handoff seam priced at `ε`, where exact equilibrium caps the incoming player's
whole-phase quit mass below `ε` so handoffs never complete, and under
`δ`-tolerance the handoff trickles at about `δ/ε` per stage against order-one
mass.

## When absorption *can* vanish is a finite check

`M [reported]`, Q154's general lemma, and the part of this most likely to be
reusable. With `dᵢ = rᵢ({i})` and `Bᵢⱼ = rᵢ({j}) - dᵢ`, consider the normalized
singleton LCP

```
λ ∈ Δ(I),   q = Bλ ≥ 0,   λᵢqᵢ = 0.
```

Every `ε`-cycle at small `ε` has absorption bounded below **iff** that LCP is
infeasible; and when it is feasible, period **one** already suffices, so
diverging period is then impossible. Vanishing absorption and diverging period
are mutually exclusive regimes, separated by a decidable property of the table.

This is the same singleton LCP the residual-class group studies, which makes
"can absorption vanish here" a finite feasibility question rather than a limit
to be estimated.

## Open

- Machine-check the no-exact-cycle claim. Dispatched.
- **The question that would bear on completeness:** does the published cyclic
  three-player family — which sits in the `S₊ ≠ ∅, S₋ = ∅` case, where
  admissibility is automatic and only absorption can fail — admit an admissible
  absorbing cycle? Its uniform equilibrium payoff exists, so a negative answer
  would falsify the disjunction without touching existence.
- No rate is known for the divergence in either source.
