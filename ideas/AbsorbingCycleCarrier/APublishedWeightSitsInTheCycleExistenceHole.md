# A published weight sits in the cycle-existence hole

| Status | Provenance | Consumer | Falsifier |
| --- | --- | --- | --- |
| `OPEN`, maturity `M [reported]`, P0 | Solan 2001 Thm 2.1, notion audit | the trichotomy's hypothesis | an absorbing cyclic continuation for this weight at some period |

## The compiler's output is not a surrogate

`L`, traced through the definitions. This had to be settled before anything
below could mean anything, and it settles favourably.

`IsεAsymptoticNash (quittingTerminalPayoff reward) 0 profile` is exact Nash
against the terminal payoff over **all** behavior-strategy deviations, with no
restricted class. And `tendsto_finiteAveragePayoff_quittingGame` proves,
**unconditionally for every profile — including off-path deviations** — that the
finite-average payoff converges to `quittingTerminalPayoff`. So exact terminal
Nash *is* exact `0`-equilibrium of the actual asymptotic-payoff game; the
terminal payoff is not a stand-in for it.

Per stage the same holds: the Nash–Bellman edge condition is proved equivalent
to full one-shot mixed Nash. So `IsQuittingCyclicContinuationBlock` — value
recursion, exact edges, positive absorption somewhere — is the *same object* as
the published notion of a finite-period completely absorbing admissible
sequence. The bridge onward to `IsUniformEquilibriumPayoff` is a further and
weaker consequence, not the load-bearing step.

This closes, in the affirmative, the standing worry that our cycle machinery
might be certifying a weaker object than the literature's.

## The weight

`M [reported]`. The published three-player family, with the `ε`-bonus on
two-quitter entries:

```
r({1}) = (1, 3, 0)        r({1,2}) = (1+ε, 0, 1)
r({2}) = (0, 1, 3)        r({2,3}) = (1, 1+ε, 0)
r({3}) = (3, 0, 1)        r({1,3}) = (0, 1, 1+ε)
                          r({1,2,3}) = (0, 0, 0)
```

Solo values are all `1 > 0`, so it is **not zero-solo**: the trichotomy's first
branch fails outright.

**No period-one *solo-quitter* cycle (`L`).** The affine no-join condition —
the repository's `QuittingSoloQuitterCriterion` — asks, for some coordinate `i`
with positive solo value, a rate `p ∈ (0,1]` with
`(1-p)·r_j({j}) + p·r_j({i,j}) ≤ r_j({i})` for every `j ≠ i`. At `i = 1, j = 3`
it reads `(1-p)·1 + p·(1+ε) ≤ 0`, i.e. `1 + pε ≤ 0`, false for every `p`. It
fails at **every** coordinate and every rate, and that lifts to the block level:
no period-one block whose row isolates a single coordinate as the sole possible
quitter is admissible, for any owner, hazard, or terminal.

Rows in which **two or three coordinates mix simultaneously are not covered**,
and no machinery for them exists. So period one is excluded for the solo-quitter
family only, not outright.

Note this already fails at `ε = 0`, where an admissible cycle nonetheless
**exists** at period three. So no-join failing is not by itself evidence of
non-existence — period three is where the unperturbed table lives, and the fence
only rules out period one.

**The period-three block breaks (`L`).** The unperturbed phase-rotation block,
machine-checked for `ε = 0`, stops being admissible under the perturbation: at
the phase where the silent creditor coordinate is promised value `1`, quitting
pays `½·1 + ½·(1+ε) = 1 + ε/2` while continuing pays `½·0 + ½·2 = 1`, an
endpoint difference of exactly `ε/2`. Computed from the repository's own quit
and continue payoff lemmas, not postulated — this is the published preemption
mechanism reproduced internally.

This covers **that one block**. Other period-three blocks are not examined.

**No cycle at any period is machine-checked (`L`,
`PerturbedCyclicWeightNoExactCycle.lean`) — in the real-hazard encoding.** For
every `ε ∈ (0, 2]`, period-uniform over `ZMod m`, with the `ε = 0` rotation
constructed in the same encoding as the in-file correctness witness, and the
dependence on `ε > 0` verified mechanically (the nonnegative weakening is
rejected; both consumers of the predecessor inequality need `ε` times a
positive rate). Scaling invariance is checked and transports to the normalized
table.

**The encoding boundary is closed
(`PerturbedCyclicWeightCycleExistenceHoleOccupied.lean`).** The cycle-level
transport exists — a cyclic continuation block maps to a real-encoding
`ExactCycle` of the same period, with the weight alignment machine-checked
entry-for-entry — and the occupancy is now stated against the trichotomy's
own predicate: `¬∃ terminal, IsQuittingCyclicContinuation (ftvRewardEps ε)
terminal` for every `ε ∈ (0, 2]`. **The hole occupancy is `L` end-to-end**,
fully internal; the published theorem is independent confirmation only.

The proof, substantially simpler than the published six-lemma route:

- a global-minimum argument over the finitely many phase values gives the
  floor: every phase value is at least `1`;
- the row dichotomy holds for this weight too — at most one positive
  coordinate per exact row, for every `ε ∈ [0, 2]`;
- **the label lock**: at a nonzero singleton row the active coordinate's value
  is pinned to exactly `1`, while the silent predecessor is forced to
  `≥ 1 + εh > 1` — the single point where `ε > 0` enters — and the silent
  successor to `1 + 2h > 1`. So "value `= 1`" uniquely identifies the active
  coordinate, zero rows leave values unchanged, and the active label can never
  hand off: every nonzero row is supported on one fixed coordinate `k`. Then
  coordinate `k−1` earns `0` at every phase (`r_{k−1}({k}) = 0`), so its value
  contracts to `0`, contradicting the floor.

At `ε = 0` the predecessor's value is exactly `1` and the handoff is possible
— which is the published rotation — so the argument fails at `ε = 0` exactly
as it must. The published Theorem 2.1 remains as independent confirmation but
is no longer load-bearing for this weight.

Two structural corollaries from the same answer, both `M [reported]`:

- **`n = 3` is minimal — corrected form**: every two-coordinate weight
  **with some `r_i({i}) > 0`** admits a period-one exact cycle. The
  unqualified form is false: a zero-solo two-coordinate weight can have
  all-continue as its only exact structure, which has survival `1` and is no
  cycle. The hole (which requires a positive solo value to escape branch
  one) still cannot occur at two players, but the minimality statement must
  carry the positivity hypothesis.
- **Cycle sets are affine-invariant; branch membership is not.** Coordinatewise
  payoff translation and positive scaling preserve exactly-complementary
  sequences. So the zero-solo three-coordinate weight with no exact cycle
  (Q154's) translates to a **positive-diagonal second occupant of the hole**
  with its own self-contained proof — and the zero-solo branch of the
  trichotomy is revealed as a normalization artifact relative to the cycle
  object it gates.

One authoring correction: the table as posed violates the corpus's
`‖r‖_∞ ≤ 1` convention (entries `3`); rescaling by `1/3` fixes it and changes
nothing, by the same affine invariance.

## What it exhibits

The trichotomy is exhaustive only under the hypothesis that the weight admits an
absorbing cyclic continuation at all. This weight has positive solo values and —
modulo the unformalized theorem — admits none at any period. So the
cycle-existence hole is **not hypothetical**: a published game sits in it, and
it is the same game the program already treats as its leading hard candidate.

It does **not** refute existence. The family has a uniform equilibrium payoff.
What it refutes is the adequacy of the cycle route as a *complete* method.

## What must be formalized

`¬∃ terminal, IsQuittingCyclicContinuation reward terminal` for this weight, at
every period — a port of the published Theorem 2.1 in its bounded form. That is
the paper's actual contribution and is substantial: the argument runs through
its own `ρ`-argument and a chain of six lemmas. Nothing weaker will do, since
the two negative computations above cover periods one and three only.

## Open

- The port itself.
- Whether a **rational** weight with positive solo values and no cycle of any
  period exists, provable self-containedly. This family is rational for rational
  `ε`, but its non-existence proof is not self-contained here.
- Whether the isolated-negative branch's missing sufficiency theorem and this
  hole are independent, or two faces of the same gap.
