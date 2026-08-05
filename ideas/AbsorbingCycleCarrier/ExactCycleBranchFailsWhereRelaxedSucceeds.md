# The exact-cycle branch fails where the relaxed one succeeds

| Status | Provenance | Consumer | Falsifier |
| --- | --- | --- | --- |
| `OPEN`, maturity `M [reported]`, P0 | Q154, Solan 2001 Thm 2.2 | the second disjunct and its periodic compiler | an exact cycle on either witness weight, or a rate bounding the period |

## What the second disjunct actually asserts

`L`, read off the definitions. The reduction's second branch is

```
IsQuittingCycleAdmissible reward cycle := ∀ who, IsQuittingCycleZeroDeviationMismatchAt reward cycle who
```

— **zero** deviation mismatch at every coordinate. This is the *exact* cycle
notion, not the `ε`-relaxed one used by the external equivalence that the
branch was modelled on. The distinction was never load-bearing before; it is
now.

The periodic compiler inherits the same commitment. Its accuracy form takes
**one** block of **fixed** period and returns `IsεAsymptoticNash` at *every*
`ε`, by proving the `ε = 0` statement and weakening. So the consumer is not
merely stated exactly — it is structurally incapable of consuming a family of
blocks whose period grows as `ε` shrinks.

## Two independent sources say the exact object can be absent

**(1) `M [reported]`, Q154.** An explicit rational three-coordinate weight with
cyclic successor structure has `ε`-cycles at every tolerance, of period `3m`,
with **no exact cycle of any finite period**. The argument is finite: centered
values are nonnegative because every reward to `i` from an outcome containing
`i` is at least `-1/2`; the local gain identity forces at most one positive
coordinate per exact row; singleton rows then pin the active coordinate's
centered value to zero while forcing the predecessor's strictly positive, and
the coordinate sum is `1/2` at every phase, which the block-endpoint vertices
cannot satisfy.

**(2) `M [reported]`, published.** For a two-parameter family the minimal period
of a periodic `δ`-equilibrium satisfies `liminf_{δ→0} d(ε,δ) = +∞` for all small
`ε`, and the same game admits **no exact equilibrium at all** while having a
uniform equilibrium payoff. The divergence proof is a compactness sketch with
**no rate** — a bounded period would produce an exact limit cycle, which the
companion theorem forbids. A finite exact cycle takes finitely many values,
hence is bounded, so the machine-checked bounded form of that companion theorem
already excludes every exact finite cycle: the boundedness loophole is closed.

## This is not the vanishing-absorption artifact

Along Q154's `ε`-cycles the absorbed mass is constantly `7/8`. The period
diverges with absorption bounded away from zero, so the failure is not an
instance of a block too mass-poor to pay for its own closure.

The published mechanism agrees and is sharper: a handoff seam priced at `ε`.
Exact equilibrium caps the incoming player's whole-phase quit mass below `ε`,
so handoffs never complete; under `δ`-tolerance the handoff trickles at about
`δ/ε` per stage against order-one mass, and the period stretches **because the
exact object is forbidden**, not because per-period absorption shrinks.

## When absorption *can* vanish is a finite check

`M [reported]`, Q154's general lemma. With `dᵢ = rᵢ({i})` and
`Bᵢⱼ = rᵢ({j}) - dᵢ`, consider the normalized singleton LCP

```
λ ∈ Δ(I),   q = Bλ ≥ 0,   λᵢqᵢ = 0.
```

Then: every `ε`-cycle at small `ε` has absorption bounded below **iff** that LCP
is infeasible; and when it is feasible, period **one** already suffices, so
diverging period is impossible. Vanishing absorption and diverging period are
therefore mutually exclusive regimes, decided by a finite linear-complementarity
feasibility question on the weight alone.

This is the same singleton LCP the residual-class group studies. The connection
is not decorative: it makes "can absorption vanish here" a decidable property of
the table rather than a limit to be estimated.

## Consequence

The branch must be restated over relaxed cycles, with the period allowed to grow
as the tolerance shrinks, and the compiler resigned to accept a per-tolerance
family rather than a single block. That is a change of signature, not a change
of proof.

Two things this does **not** do. It does not refute existence — both witnesses
have uniform equilibrium payoffs. And it does not make the reduction useless: it
identifies exactly which of its two branches carries the weight, and the already
machine-checked repair for the neither-branch weight shows the relaxed route
delivers the real payoff predicate.

## Open

- Machine-check Q154's weight. Dispatched; until it lands this file is reported,
  not audited.
- No rate is known for the divergence, in either source. A seam heuristic
  suggests `defect × period ≈ η·ln 2`, matching a family already recorded here,
  and a ramp argument suggests period `~ c(η)·log(1/δ)` might beat it. Both are
  inference, not results.
- Decide whether the two witnesses are the same phenomenon. Q154's is a
  three-coordinate cyclic weight and the published one is a rotating solo-quitter
  role; the cyclic successor structure is common to both, which is suggestive and
  unproven.
