# Marked Absorption Cylinder — finite semantics for P0-A

Dated design note, 2026-08-03. This fixes the **finite** object required by
`MATH-P0-1` / `LEAN-P1-4` before any infinite topology is scaffolded, per the
standing decision in [`PIPELINE.md`](../PIPELINE.md) (`PC-003`) and the ordered
agenda in the [frontier manuscript](../manuscript/UniformEquilibriumFrontierManuscript.tex).

Evidence discipline: statements marked `L` are production Lean at `14d75ff`;
statements marked `A` are derivations audited on paper **in this note only**
and are not machine-checked; statements marked `O` are the open obligations
this design is meant to make precise. Nothing here is landed mathematics.

## 0. What this note decides

The route selected at `cd1db11` encodes each calibrated exact-`D` block as a
marked subprobability absorption cylinder, schematically

\[
 z=\bigl(\pi,s_{\rm exit};e_{\rm in},e_{\rm out};
          i_*,T_*,\kappa_*;V,\mathcal O,D;\text{provenance}\bigr).
\]

That schema names the coordinates but does not settle their types, their
clocks, or which of them are independent. This note settles exactly that, and
records one finding that changes the schema.

## 1. Notation for an actual finite block

Let `ι` be the finite player set and `𝒥` the nonempty subsets of `ι`, with
reward `r : 𝒥 → Payoff ι`. A block of length `m` is a family of live product
roots `x_t : ι → PMF Bool`, `t < m`, taken from one actual common
zero-boundary Nash–Bellman chain. Write, for a single root `x`:

| Quantity | Definition |
| --- | --- |
| continue mass | `c(x) = ∏_{i} x_i(false)` |
| absorption into `J ∈ 𝒥` | `a(x)(J) = ∏_{i∈J} x_i(true) · ∏_{i∉J} x_i(false)` |
| opponent-only continue mass | `c_{-i}(x) = ∏_{j≠i} x_j(false)` |

so that `Σ_{J∈𝒥} a(x)(J) = 1 - c(x)`. Define the two survival products

\[
 S(t)=\prod_{u<t}c(x_u),
 \qquad
 S_{-i}(t)=\prod_{u<t}c_{-i}(x_u),
\]

and the corresponding absorbed masses `M(t) = 1 - S(t)`,
`M_{-i}(t) = 1 - S_{-i}(t)`.

## 2. The finding: the cylinder carries `|ι|+1` clocks, not one

`L` The landed holonomy coordinates already separate two survival factors:
the prescribed slope is full survival `P = S(m)`, while the unilateral
max-affine slope is opponent-only survival `χ_i = S_{-i}(m)`
(`QuittingBoundaryHolonomy.lean`, "the max-affine slope is actual
opponent-only survival"). This is not a presentational duplication.

`A` Player `i`'s quit-at-`t` value is

\[
 Q_i(t)=S_{-i}(t)\cdot
 \sum_{J\subseteq\iota\setminus\{i\}}
 \Bigl[\textstyle\prod_{j\in J}x_{t,j}(\mathrm{true})
       \prod_{j\notin J\cup\{i\}}x_{t,j}(\mathrm{false})\Bigr]
 \, r_i\bigl(J\cup\{i\}\bigr),
\]

because a deviator who quits at `t` has obeyed only up to `t`, so its
weight is opponent-only survival, and its absorption at `t` is certain.

Consequently a reparametrization by **total** absorption mass `τ = M(t)` is
the correct clock for the prescribed payoff and for `P`, but it is *not* the
clock of any player's stopping obstacle. Total mass advances whenever player
`i` alone quits with positive probability, while `S_{-i}` does not move at
all. The two clocks differ by exactly player `i`'s own contribution.

**Design consequence.** The cylinder must carry the total-absorption path
*and*, for each player, the opponent-only survival as a separate monotone
function of the same parameter. These are not recoverable from the aggregated
absorption path: collapsing calendar stages destroys the per-stage product
structure that relates them. The schema's single `π` is therefore
insufficient, and the "playerwise clocks" item is load-bearing for **every**
player's cap, not only for bookkeeping the debt owner.

## 3. The obstacle is a function at finite level and a closed graph at the limit

A natural fear is that reparametrizing by mass makes `Q_i` ill-defined,
because many calendar stages collapse to one mass time. `A` It does not, at
finite level:

- If `τ` does not advance across a stretch, then `c(x_u) = 1` there, hence
  every `x_{u,i}(false) = 1`, hence `c_{-i}(x_u) = 1` and the bracket above
  equals `r_i({i})`. So `S_{-i}` and `Q_i` are both constant on the stretch.
- If `τ` advances while `S_{-i}` does not, all opponents surely continue on
  that stretch, so the bracket again equals `r_i({i})` and `Q_i` is constant.

In both degenerate directions `Q_i` is constant, so **`Q_i` descends to a
well-defined function of `τ`**. This is a genuinely favourable finding: the
finite encoding theorem can state `Q_i` as a function, not a correspondence.

`O` The limit object is different. `Q_i(·)` is càdlàg in `τ` with jumps at
absorption atoms, and under convergence of blocks the atoms move. Pointwise
limits therefore fail. The limiting obstacle must be the **closed completed
hypograph** of `Q_i` — the graph with its jump segments filled in — and the
cap `sup_τ Q_i(τ)` must be shown upper semicontinuous with a retained
approximately-optimal location. Neither is proved. This replaces the
manuscript's hedged "might be a closed hypo/epigraph" with a specific claim:
a function finitely, a closed completed hypograph in the limit.

## 4. Exit port and Never are different types, not different values

`L`/`A` For a finite block the defect `s_exit = S(m)` is survival to the exit
port. It is transported into the successor block and evaluated at *its*
continuation. Genuine `Never` mass arises only for a completed infinite path,
as the limit of `s_exit` along a concatenation chain.

**Design consequence.** These must be separated at the level of types, not by
a boolean field on one type:

- `MarkedAbsorptionCylinder` — the finite object. Its total mass is a
  subprobability on `𝒥` with defect `s_exit`. It has **no** `Never` field.
- `MarkedAbsorptionPath` — the completed object. It has a `Never` atom
  `ν_∞`, and no exit port.

Conflating them is the specific error the manuscript flags as producing wrong
block composition and wrong deviation values. A single type with an
"is-final" flag reintroduces exactly that risk at every concatenation lemma,
so it is rejected.

## 5. The mark is an independent coordinate, by construction

`L` The calibrated anchor already separates preterminal opponent survival
from the final marked atom (`QuittingCalibratedTerminalAnchor`:
`preterminalSurvival`, `terminalMass`, `terminalAdvantage`, and the marked
`action`/`terminalQuitters`).

`A` The transported mass of the marked packet is
`preterminalSurvival × terminalMass`, and this product may tend to zero along
a family whose conditional kernel `κ_*` and advantage stay bounded away from
zero. Hence `κ_*` is **not** a continuous function of the absorption path
`π`, and cannot be reconstructed from it.

**Design consequence.** `κ_*` enters as an independent (pointed / blown-up)
coordinate: the raw conditional kernel at the marked root, the owner `i_*`,
the full marked action profile and its quitter set `T_*`, and the advantage
scalar — each stored separately from the transported mass. Storing only the
jump size of `π` loses the packet.

This is also where the route is most likely to fail, and the failure is
exactly the `P0-B` falsifier: two families with the same limiting `π` but
different limiting `κ_*` would show the enriched relation is not closed. The
independence established here does not by itself decide closedness.

## 6. Anchors make splice legality a closed condition

`O`→`A` Entry and exit anchors `e_in, e_out` are exact-`D` root data, valued
in a compact space (product roots lie in `[0,1]^ι`; the debt point lies in a
fixed compact box, `L` at `14d75ff`). Concatenation is legal exactly when
`e_out(z) = e_in(z')`.

Because that is an equality in a Hausdorff space, **splice legality is a
closed condition** whenever the anchors are retained as fields. This is the
positive reason anchors must be coordinates rather than side conditions: it
converts admissibility, which the scalar-coefficient projection forgets, into
a relation that can survive a limit. It is also the precise sense in which
this design does not repeat the projection error of the coefficient box.

## 7. What the cylinder deliberately forgets

Retained by the fixed-cutoff lift but **excluded** here:

| Dropped | Reason |
| --- | --- |
| literal block length `m` | `L` at `14d75ff`: every compact subset of `ℕ × X` has bounded length, so retaining literal length forecloses the compactification the route exists to obtain. |
| the complete source word | It is what makes the fixed-cutoff lift compact at each cutoff and what cannot survive an escaping middle. The encoding must recover semantics without it. |

The encoding map is therefore intentionally non-injective. Proving that the
retained data still determines all semantics is the content of P0-A, not an
incidental check.

## 8. The P0-A obligation list

`O` Define the finite type of §4 with the coordinates fixed in §§2–6, and
prove, for every calibrated exact-`D` block:

1. **Payoff identity.** The cylinder's prescribed value equals the block's
   literal finite policy value, with slope `P = s_exit`.
2. **Obstacle identity.** For each player, the cylinder's `Q_i(·)` equals the
   block's literal quit-at-`t` values under the reparametrization of §3, and
   its supremum equals the landed max-affine cap coordinate, with slope
   `χ_i = S_{-i}(m)`.
3. **Clock identity.** The retained total and opponent-only clocks agree with
   `S(·)` and `S_{-i}(·)`.
4. **Packet identity.** `preterminalSurvival`, `terminalMass`, `κ_*`, `T_*`,
   and the advantage agree with the calibrated anchor's fields, with the two
   mass factors kept separate.
5. **Debt identity.** The retained entry debt equals the block's dynamic debt
   at its entry root.
6. **Anchor identity.** `e_in`, `e_out` are the block's exact-`D` endpoints.
7. **Concatenation.** For chronologically adjacent blocks, the cylinder of the
   concatenation equals the composition of the cylinders, and this composition
   is associative and agrees with the landed `(B,P)` / `(A,T,χ)` composition
   laws under the forgetful map to holonomy coordinates.

Item 7 subsumes the correctness test that matters most: the forgetful map from
cylinders to landed holonomy coordinates must be a homomorphism. If it is not,
the encoding is wrong, independently of any topology.

## 9. Non-goals and standing fences

- This note defines no topology on cylinders and claims no compactness. `P0-B`
  remains open and may be false; §5 identifies where.
- It supplies neither decoder (`P0-C`, `P0-D`). A cylinder is a semantic
  encoding, not a repair.
- It does not repair the published sure-terminal-jump endpoint defect; the
  restricted and augmented adapters remain the two open options.
- Q132's nonattainment fence still applies: exact identities for attainable
  data do not make the attainable set closed.

## 10. Status

`O` Nothing in this note is formalized. §§2–3 and §5 are paper derivations
made here and should be re-derived by the implementer rather than cited; §§4,
6, 7 are design decisions with stated rationale. The immediate consumer is
`LEAN-P1-4`, which should not begin before §8's list is accepted or amended.
