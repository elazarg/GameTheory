# Marked absorption cylinder and generalized traces

Design record for the boundary object of `MATH-P0-1` / `LEAN-P1-4`: the finite
encoding of a calibrated exact-`D` block, and the limit space it sits densely
inside.

Evidence discipline: `L` is production Lean; `M` is audited mathematics, not
formalized; `O` is an open obligation. Nothing here is landed Lean.

## 1. Notation for a finite block

Let `ι` be the finite player set and `𝒥` the nonempty subsets of `ι`, with
reward `r : 𝒥 → Payoff ι`. A block of length `m` is a family of live product
roots `x_t : ι → PMF Bool`, `t < m`, from one actual common zero-boundary
Nash–Bellman chain. For a single root `x`:

| Quantity | Definition |
| --- | --- |
| continue mass | `c(x) = ∏_i x_i(false)` |
| absorption into `J ∈ 𝒥` | `a(x)(J) = ∏_{i∈J} x_i(true) · ∏_{i∉J} x_i(false)` |
| opponent-only continue mass | `c_{-i}(x) = ∏_{j≠i} x_j(false)` |

so `Σ_{J∈𝒥} a(x)(J) = 1 - c(x)`. The two survival products are

\[
 S(t)=\prod_{u<t}c(x_u),
 \qquad
 S_{-i}(t)=\prod_{u<t}c_{-i}(x_u),
\]

with accumulated mass `τ(t) = 1 - S(t)`.

## 2. The cylinder carries `|ι|+1` clocks

`L` The landed holonomy coordinates already separate two survival factors: the
prescribed slope is full survival `P = S(m)`, while the unilateral max-affine
slope is opponent-only survival `χ_i = S_{-i}(m)`.

`M` This is not presentational duplication. Player `i`'s quit-at-`t` value is

\[
 Q_i(t)=S_{-i}(t)\cdot
 \sum_{J\subseteq\iota\setminus\{i\}}
 \Bigl[\textstyle\prod_{j\in J}x_{t,j}(\mathrm{true})
       \prod_{j\notin J\cup\{i\}}x_{t,j}(\mathrm{false})\Bigr]
 \, r_i\bigl(J\cup\{i\}\bigr),
\]

because a deviator quitting at `t` has obeyed only up to `t`, so its weight is
opponent-only survival. Total mass advances whenever player `i` alone quits,
while `S_{-i}` does not move: the clocks differ by exactly `i`'s own
contribution, and `S_{-i}` is not recoverable from the aggregate absorption
path. Collapsing stages destroys the per-stage product structure relating them.

The playerwise clocks are therefore load-bearing for **every** player's cap,
not only for bookkeeping the debt owner.

**Carrier.** The absorption and clock coordinates are paths in the mass
parameter `τ ∈ [0, 1 - s_exit]`, not block totals and not endpoint scalars.
Build the path by setting it at the stage masses `τ(t)` to
`Σ_{u<t} S(u) a(x_u)(J)`, then extending affinely on each `[τ(t), τ(t+1)]`,
splitting the increment across coalitions in proportion to `a(x_t)(·)`. This
makes `τ` an honest arclength, so `Σ_J` of the path is exactly `τ` and the path
is `1`-Lipschitz in `ℓ¹` — the bound the compactness argument consumes.
Snapping `τ` to the nearest completed stage does **not** satisfy the identity:
between stage masses the snapped value is a jump value.

`τ` is mass, not calendar time, so paths do not reintroduce the length fence. A
finite list of absorption atoms is rejected for the opposite reason: its atom
count is a natural-number coordinate that diverges exactly as calendar length
does, re-importing the `14d75ff` obstruction.

Every mass and survival coordinate is bounded in `[0,1]`: in particular
`0 ≤ s_exit ≤ 1` and `0 ≤ χ_i ≤ 1` are both required as fields. The upper
bounds are not decoration — without `s_exit ≤ 1` the domain `[0, 1 - s_exit]`
can be empty and the "recorded points lie in the mass domain" obligations are
unprovable, in the encoding and again in every composition.

**Endpoint scalars are stored and pinned, not derived.** Keep `s_exit`, `χ_i`,
and the cap as fields, each carrying a hypothesis pinning it to its path. `ℝ`'s
order is classical and not kernel-reducible, so a cap defined by `sSup` and a
defect defined by a sum over a *spliced* path both fail to reduce
definitionally, and `forgetful_compose` stops being `rfl`. That `rfl` is the
only line machine-checking the encoding against the landed holonomy law; it is
worth more than eliminating five fields.

## 3. The obstacle is not a function of mass

`M` The stopping obstacle does **not** descend to accumulated mass, and neither
do the deleted clocks after full absorption.

The tempting argument — a stretch with no mass advance has `c(x_u) = 1`, so all
coordinates continue, so the bracket is `r_i({i})` and `Q_i` is constant — is
true but irrelevant. `τ(t)` is the mass absorbed **strictly before** `t`, so
`τ(t) = τ(t')` constrains the preceding rows and says nothing about the row the
obstacle reads at `t'`. That row is unconstrained.

Minimal counterexample, `I = {1,2}`, `i = 1`, `r_1({1}) = 0`,
`r_1({1,2}) = 1`, so `Q_1(p,t) = S_{-1}(t)·p_{t,2}`:

```
p_0 = (0,0),  p_1 = (0,1)
τ(0) = τ(1) = 0        (row 0 absorbs nothing)
Q_1(p,0) = 0,  Q_1(p,1) = 1
```

Same accumulated mass, different obstacle. The missing datum is the current
row. The failure is not confined to zero rows; the universal all-scheme descent
property holds only in the degenerate case `r_i(K) = 0` for every `K ∋ i`.
Separately, after total mass reaches `1` a deleted clock can still change, and
under uniform convergence the family of deleted clocks is not compact — it can
converge pointwise to a terminal jump.

**Consequence.** The obstacle and clock coordinates are completed graphs, not
functions:

```
G_i = completed chronological graph of  t ↦ (τ(t), S_{-i}(t))
H_i = closed completed hypograph of the stage obstacle trace,
      including values at zero-mass stages
```

`H_i` must retain zero-mass stages, since that is where the counterexample
lives. In this topology the results are favourable: the graph-completed ambient
space is compact, the cap `sup H_i` is **continuous** (not merely
semicontinuous), a maximizing witness is retained, and concatenation is
continuous. The uniform-clock topology delivers none of these.

## 4. Exit port and Never are different types

`M` For a finite block the defect `s_exit = S(m)` is survival to the exit port,
transported into the successor and evaluated at *its* continuation. Genuine
`Never` mass arises only for a completed infinite path, as the limit of
`s_exit` along a concatenation chain.

These are separated at the level of types:

- `MarkedAbsorptionCylinder` — finite. Subprobability with defect `s_exit`. No
  `Never` field.
- `MarkedAbsorptionPath` — completed. A `Never` atom `ν_∞`, no exit port.

A single type with an "is-final" flag is rejected: it reinstates the
wrong-composition risk at every concatenation lemma. Declaring a finite block's
remainder to be `Never` gives the wrong payoff and the wrong deviation values.

## 5. The mark is an independent coordinate

`L` The calibrated anchor separates preterminal opponent survival from the
final marked atom.

`M` The transported packet mass is `preterminalSurvival × terminalMass`, and
this may tend to zero along a family whose conditional kernel `κ_*` and
advantage stay bounded away from zero. So `κ_*` is not a continuous function of
the absorption path and cannot be reconstructed from it — nor from the other
enriched coordinates. It enters as an independent pointed coordinate: the raw
conditional kernel at the marked root, the owner `i_*`, the marked action
profile and quitter set `T_*`, and the advantage scalar, each stored separately
from the transported mass.

`(i_*, J_*)` must be globally fixed, or else carried as a finite discrete
coordinate. Allowing them to vary silently leaves the mark-composition law
undefined.

## 6. Anchors make splice legality closed

`M` Entry and exit anchors are exact-`D` root data valued in a compact space.
Concatenation is legal exactly when `e_out(z) = e_in(z')` — an equality in a
Hausdorff space, hence a **closed** condition whenever anchors are retained as
fields. This is why anchors are coordinates rather than side conditions: it
converts admissibility, which the scalar projection forgets, into a relation
surviving limits. Anchor-free spliceability is not even well-defined.

## 7. What the cylinder forgets

| Dropped | Reason |
| --- | --- |
| literal block length `m` | `L`: every compact subset of `ℕ × X` has bounded length, so retaining literal length forecloses the compactification the route exists to obtain. |
| the complete source word | It is what makes the fixed-cutoff lift compact at each cutoff and what cannot survive an escaping middle. |

The encoding map is intentionally non-injective. Proving the retained data
still determines all semantics is the content of P0-A.

## 8. The finite-encoding obligations

`O` For every calibrated exact-`D` block, prove:

1. **Payoff.** The cylinder's prescribed value equals the block's literal
   finite policy value, slope `P = s_exit`.
2. **Obstacle.** `H_i` equals the completed hypograph of the block's literal
   quit-at-`t` trace, and `sup H_i` equals the landed max-affine cap
   coordinate, slope `χ_i = S_{-i}(m)`.
3. **Clocks.** `G_i` and the absorption path agree with `S(·)`, `S_{-i}(·)`.
4. **Packet.** `preterminalSurvival`, `terminalMass`, `κ_*`, `T_*`, advantage
   agree with the calibrated anchor, the two mass factors kept separate.
5. **Debt.** Retained entry debt equals the block's dynamic debt at entry.
6. **Anchors.** `e_in`, `e_out` are the block's exact-`D` endpoints.
7. **Concatenation.** The cylinder of a concatenation equals the composition of
   cylinders, associatively, agreeing with the landed `(B,P)`/`(A,T,χ)` laws
   under the forgetful map.

Item 7 subsumes the test that matters most: the forgetful map to holonomy
coordinates must be a homomorphism. If it is not, the encoding is wrong
independently of any topology.

## 9. The limit space

`M` The finite realizable set is **not closed**. Finite `μ`-paths are finitely
piecewise affine while limits can be genuinely nonlinear. This is not a
missing-coordinate problem:

> No additional coordinate valued in a sequentially compact space can make the
> finite realizable image closed while the projection back to the enriched
> coordinates stays continuous.

So there is no "smallest compact coordinate that closes it". The alternatives
are a noncompact complexity coordinate, or admitting infinite/diffuse
generalized objects.

`O` The target is therefore a compactness theorem for **generalized completed
chronological traces**, in which finite blocks are dense, value and cap extend
continuously, and concatenation extends continuously once anchors are retained
and a mark-transport convention is fixed. Two facts make this route viable
rather than merely available: a uniform cap bound survives to the limit, and a
limit self-splice pulls back to a nearby finite self-splice under boundary-row
flexibility — the pullback that a surgery decoder needs.

## 10. Standing fences

- Do not pursue a compact added coordinate closing the finite realizable set.
  That shape is proved impossible.
- Do not state the obstacle or the deleted clocks as functions of `τ`.
- A cylinder is a semantic encoding, not a repair. It supplies neither decoder.
- The published sure-terminal-jump endpoint defect is unrepaired; the
  restricted and augmented adapters remain the two options.
- Exact identities for attainable data do not make the attainable set closed.
