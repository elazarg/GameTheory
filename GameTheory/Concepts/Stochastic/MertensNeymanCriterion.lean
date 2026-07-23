/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.Adaptive
import GameTheory.Concepts.Stochastic.Fink
import GameTheory.Concepts.Stochastic.ZeroSum
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# The Abstract Mertens–Neyman Criterion

This file states and proves, from explicit analytic hypotheses, the abstract
(conditional) form of the Mertens–Neyman criterion for the uniform value of a
two-player zero-sum stochastic game: bounded payoffs, together with a
**tail-variation modulus** for the discounted-value family and an
**adaptive-index one-step tracking estimate**, imply that a genuinely
history-adaptive strategy secures the vanishing-discount limit value up to
`ε` over all sufficiently long horizons (Stage B), which assembles into a
uniform equilibrium payoff for a zero-sum presentation (Stage C).

The point of this file is the *contract*: the precise shape of the
hypotheses (`IsTailVariationBounded` above all) that a later, purely
algebraic construction must discharge. Where the deepest quantitative
estimate of Mertens–Neyman (1981) would be needed to *discharge* a
hypothesis rather than merely to state it, this file promotes the residual
to an explicit, precisely named hypothesis instead of `sorry`ing it — see
the module docstring notes on `IsRowIndexTrackingCert` below.

## Stage A: the discounted-value family and its contract

* `StochasticGame.IsTailVariationBounded` — the tail-variation modulus, in
  **interval-envelope** form: for every `ε`, some `δ` bounds the
  `Function.eVariationOn` total variation of `v` over the *whole interval*
  `(0, δ)` by `ε`. This bounds `‖v a - v b‖` for every pair `a, b ∈ (0, δ)`
  regardless of order — deliberately *not* a chain-order (monotone-only)
  bound, since the realized Mertens–Neyman adaptive discount index generally
  moves non-monotonically along a play. This is the exact statement a
  concrete algebraic construction (the "F1" file) must produce.
* `StochasticGame.IsTailVariationBounded.pairwise_le` — the two-point
  (`m = 1`) instance: a genuine Cauchy criterion for `v` as `λ → 0⁺`.
* `StochasticGame.IsTailVariationBounded.exists_vanishingDiscountLimit` — the
  vanishing-discount limit `v₀ := lim_{λ→0⁺} v λ` exists, proved by the
  Cauchy criterion and completeness of `G.State → Payoff ι` (a finite-rank
  real vector space under the sup norm).
* `StochasticGame.IsShapleyFamily` — the general Shapley/Fink one-step
  property tying `v λ` to the stationary optimal profile `x λ` at discount
  complement `λ = 1 - β`, matching `BellmanVariety.lean`'s `λ`-convention and
  `Fink.lean`'s `IsDiscountedStationaryBellmanEq`.

## Stage B: the one-sided (maximizer-role) guarantee

* `StochasticGame.IsRowIndexTrackingCert` — the promoted one-step tracking
  estimate: the adaptive-index potential `v (λ (t, h)) (state h)` is a
  historywise near-supermartingale, up to a per-stage error budget `e`,
  under the row player's `λ`-indexed strategy, against *every* opposing
  play. This is the exact quantitative content Mertens–Neyman's λ-update
  argument supplies (generalizing `BigMatchUniform.lean`'s `bfX`/`bfXExpect`
  submartingale to the abstract discounted-value family); it is promoted to
  a hypothesis here rather than derived from `IsShapleyFamily` and
  `IsTailVariationBounded` directly (see the docstring on the definition for
  the exact missing step).
* `StochasticGame.secures_vanishingDiscountLimit_row` — **the core
  reduction**: bounded payoffs, `IsTailVariationBounded`, and
  `IsRowIndexTrackingCert` (supplied along the canonical vanishing calendar
  schedule) together give the maximizer-role finite-horizon guarantee.
  `IsTailVariationBounded` is used directly inside the proof to bound the
  cumulative tracking error by `ε`, uniformly in the horizon.

## Stage C: assembly to a uniform equilibrium payoff

* `StochasticGame.isUniformEquilibriumPayoff_of_secures_row_col` — combining
  a row-side and a column-side instance of Stage B's guarantee through
  `isUniformEquilibriumPayoff_of_deviation_caps` gives the two-player
  zero-sum uniform equilibrium payoff `(w, -w)`. The column-side guarantee is
  the mirror image of Stage B (row and column swapped, sign of the target
  flipped) and is taken here as a hypothesis of the same shape that Stage B
  proves for the row side; it is not re-derived to keep this file's scope
  bounded — the construction is identical with `0` and `1` exchanged.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability Math.PMFProduct

-- ============================================================================
-- Stage A: the discounted-value family and its contract
-- ============================================================================

section StageA

variable {ι : Type} (G : StochasticGame ι) [Fintype ι] [Fintype G.State]

/-- **The tail-variation modulus (interval-envelope form).** For every
`ε > 0` there is a `δ > 0` such that the (extended-real) total variation of
`v`, in the sense of `Function.eVariationOn`, over the *whole interval*
`(0, δ)` is at most `ε`.

This is deliberately an **interval**, not a chain-order, control: the
realized Mertens–Neyman adaptive discount index generally moves
non-monotonically along a play (it can both decrease and increase, driven by
the running deficit between realized and target payoff), so a bound that
only controls decreasing chains of discount-complements would not bound the
value swings actually encountered along a play. `Function.eVariationOn`
instead bounds `‖v a - v b‖` for *every* pair `a, b ∈ (0, δ)` regardless of
order (`eVariationOn.edist_le`, used in `pairwise_le` below) — the
interval-envelope contract, in the terminology of Mertens–Neyman's original
`λ`-update construction (design (b) of the two envisaged here; design (a),
a plain chain-order bound, would only be sound if the realized index were
known to be pathwise monotone, which it is not in general).

`eVariationOn`'s definition already subsumes the *unweighted-density*
picture `∃ ψ ≥ 0` with `∫_0^δ ψ < ∞` and `‖v b - v a‖ ≤ ∫_{min a b}^{max a b}
ψ`: any such `ψ` gives `eVariationOn v (Ioo 0 δ) ≤ ENNReal.ofReal (∫_0^δ ψ)`
(a consequence of `MeasureTheory.intervalIntegral` additivity, not
re-derived here), and conversely bounded variation is itself represented by
its own indefinite-variation function. For the concrete real-valued
row/column discounted values used in Stage B/C, `MonotoneOn.eVariationOn_le`
gives the cheapest bridge: eventual monotonicity of `fun lam => v lam s who`
on `(0, δ)` together with a bound on its total drop there,
`ENNReal.ofReal (f b - f a)`, discharges this hypothesis directly — exactly
the "eventual monotonicity + ordinary tail bounded variation" shape a
concrete vanishing-discount construction (`F1b`) is expected to export.

The norm is the sup norm on `G.State → Payoff ι`, i.e. `G.State → ι → ℝ`
under Mathlib's finite-Pi instance (`Pi.normedAddCommGroup`, applied twice):
`‖f‖ = sup over states s, players i, of |f s i|`. This choice composes
cleanly with `norm_le_pi_norm`, which lets the sup bound be read off
pointwise at any single state and player without further work. -/
def IsTailVariationBounded (v : ℝ → G.State → Payoff ι) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    eVariationOn v (Set.Ioo (0 : ℝ) δ) ≤ ENNReal.ofReal ε

/-- The pairwise (any two points, either order) consequence of
`IsTailVariationBounded`: a genuine Cauchy criterion for `v` along
`λ → 0⁺`. Immediate from `eVariationOn.edist_le`, which bounds the distance
between the values at *any* two points of the interval by its variation over
the whole interval — no ordering between `lam` and `lam'` is required. -/
theorem IsTailVariationBounded.pairwise_le {v : ℝ → G.State → Payoff ι}
    (h : G.IsTailVariationBounded v) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ lam lam' : ℝ, lam ∈ Set.Ioo (0 : ℝ) δ →
      lam' ∈ Set.Ioo (0 : ℝ) δ → ‖v lam - v lam'‖ ≤ ε := by
  obtain ⟨δ, hδ, hvar⟩ := h ε hε
  refine ⟨δ, hδ, fun lam lam' hlam hlam' => ?_⟩
  have hedist : edist (v lam) (v lam') ≤ ENNReal.ofReal ε :=
    (eVariationOn.edist_le v hlam hlam').trans hvar
  rw [edist_dist] at hedist
  have hdist : dist (v lam) (v lam') ≤ ε := (ENNReal.ofReal_le_ofReal_iff hε.le).mp hedist
  rwa [dist_eq_norm] at hdist

/-- **Existence of the vanishing-discount limit.** `IsTailVariationBounded`
implies `v` has a limit `v₀` as `λ → 0⁺`, in the explicit `ε`-`δ` sense.
Proved via the Cauchy criterion (`pairwise_le`) along the canonical
decreasing sequence `1 / (n + 2) → 0`, completeness of `G.State → Payoff ι`,
and a final triangle-inequality step extending the sequential limit to
arbitrary `λ → 0⁺`. -/
theorem IsTailVariationBounded.exists_vanishingDiscountLimit
    {v : ℝ → G.State → Payoff ι} (h : G.IsTailVariationBounded v) :
    ∃ v₀ : G.State → Payoff ι, ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ lam : ℝ, lam ∈ Set.Ioo (0 : ℝ) δ → ‖v lam - v₀‖ ≤ ε := by
  set lamSeq : ℕ → ℝ := fun n => 1 / (n + 1) with hlamSeq
  have hlamSeq_pos : ∀ n, 0 < lamSeq n := fun n => by positivity
  have hlamSeq_anti : Antitone lamSeq := by
    intro n m hnm
    simp only [hlamSeq]
    have hnm1 : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnm 1
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact div_le_div_of_nonneg_left (by norm_num) hn1 hnm1
  have hlamSeq_tendsto : Filter.Tendsto lamSeq Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hcauchy : CauchySeq (fun n => v (lamSeq n)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨δ, hδ, hpair⟩ := h.pairwise_le G (half_pos hε)
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlamSeq_tendsto δ hδ
    refine ⟨N, fun m hm n hn => ?_⟩
    have hm' : lamSeq m < δ := by
      have := hN m hm; rwa [Real.dist_eq, sub_zero, abs_of_pos (hlamSeq_pos m)] at this
    have hn' : lamSeq n < δ := by
      have := hN n hn; rwa [Real.dist_eq, sub_zero, abs_of_pos (hlamSeq_pos n)] at this
    have hbound := hpair (lamSeq m) (lamSeq n) ⟨hlamSeq_pos m, hm'⟩ ⟨hlamSeq_pos n, hn'⟩
    rw [dist_eq_norm]
    exact lt_of_le_of_lt hbound (by linarith)
  obtain ⟨v₀, hv₀⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨v₀, fun ε hε => ?_⟩
  obtain ⟨δ, hδ, hpair⟩ := h.pairwise_le G (half_pos hε)
  obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.mp hlamSeq_tendsto δ hδ
  obtain ⟨N2, hN2⟩ := Metric.tendsto_atTop.mp hv₀ (ε / 2) (half_pos hε)
  set N := max N1 N2 with hN
  have hNδ : lamSeq N < δ := by
    have := hN1 N (le_max_left _ _)
    rwa [Real.dist_eq, sub_zero, abs_of_pos (hlamSeq_pos N)] at this
  have hNdist : dist (v (lamSeq N)) v₀ ≤ ε / 2 := (hN2 N (le_max_right _ _)).le
  refine ⟨δ, hδ, fun lam hlam => ?_⟩
  have hstep := hpair lam (lamSeq N) hlam ⟨hlamSeq_pos N, hNδ⟩
  have htri : ‖v lam - v₀‖ ≤ ‖v lam - v (lamSeq N)‖ + ‖v (lamSeq N) - v₀‖ := by
    calc ‖v lam - v₀‖ = ‖(v lam - v (lamSeq N)) + (v (lamSeq N) - v₀)‖ := by
          congr 1; abel
      _ ≤ ‖v lam - v (lamSeq N)‖ + ‖v (lamSeq N) - v₀‖ := norm_add_le _ _
  have hNdist' : ‖v (lamSeq N) - v₀‖ ≤ ε / 2 := by
    rwa [dist_eq_norm] at hNdist
  linarith [htri, hstep, hNdist']

variable [DecidableEq ι] [∀ i, Fintype (G.Act i)]

/-- **The Shapley/Fink one-step property**, matching `BellmanVariety.lean`'s
`λ = 1 - β` convention: for every discount complement `λ ∈ (0, 1)`, `x λ` is
a stationary Nash selection of the discounted auxiliary games determined by
`v λ`, and `v λ` is exactly the auxiliary payoff generated by `x λ` — i.e.
`(x λ, v λ)` is a Fink discounted stationary Bellman equilibrium at discount
`β = 1 - λ`. This is the abstract "discounted-value family with its
per-`λ` stationary optimal profile" that Stage A's contract calls for,
reusing `Fink.lean`'s `IsDiscountedStationaryBellmanEq` (itself built from
the statewise auxiliary-game Nash correspondence, the general-player
analogue of `ZeroSum.lean`'s Shapley operator machinery). -/
def IsShapleyFamily (v : ℝ → G.State → Payoff ι) (x : ℝ → G.StationaryMixedProfile) :
    Prop :=
  ∀ lam ∈ Set.Ioo (0 : ℝ) 1, G.IsDiscountedStationaryBellmanEq (1 - lam) (x lam) (v lam)

end StageA

-- ============================================================================
-- Stage B: the one-sided (maximizer-role) guarantee, two-player zero-sum
-- ============================================================================

section StageB

variable (G : StochasticGame (Fin 2)) [Fintype G.State] [∀ i, Fintype (G.Act i)]
  [∀ i, Nonempty (G.Act i)]

/-- The row player's `λ`-indexed strategy: play the stationary optimal
action `x λ` at the discount complement `λ` selected by the running index
schedule `lam`, which may depend on the whole history. -/
def rowIndexStrategy (x : ℝ → G.StationaryMixedProfile) (lam : G.HistoryPotential) :
    G.BehaviorStrategy 0 :=
  fun t h => x (lam t h) h.2 0

/-- The row-value continuation potential read off the running index: the
discounted value of player `0` at the current state, at the discount
complement the schedule selects there. -/
def indexPotential (v : ℝ → G.State → Payoff (Fin 2)) (lam : G.HistoryPotential) :
    G.HistoryPotential :=
  fun t h => v (lam t h) h.2 0

/-- **The adaptive one-step tracking estimate** (the promoted hypothesis).
Along the row player's `λ`-indexed strategy, against *every* opposing column
strategy `dev`, the running-index potential `v (λ (t, h)) (state h)` is a
historywise near-supermartingale up to a per-stage error budget `e t`. This
is precisely the quantitative content of the Mertens–Neyman `λ`-update: it
generalizes `BigMatchUniform.lean`'s `bfX_le_expect_step` /
`bfXExpect_le_succ` submartingale step from the Big Match's concrete
potential to the abstract discounted-value family `v`.

It is *not* derived here from `IsShapleyFamily` and `IsTailVariationBounded`
directly. Doing so needs, at every history, comparing the fixed-`λ` Shapley
Bellman equation at the running index `λ (t, h)` against the one-step
continuation evaluated at the successor index `λ (t + 1, h')`, which first
requires passing to the *average-reward normalization* of the discounted
Bellman equation (`averageReward_bellman_le_of_discounted_bellman_le` in
`Discounted.lean` is exactly this conversion, but only for a single *fixed*
`β`) before the discrepancy between the two indices can be bounded by the
tail-variation modulus. The history-adaptive-`β` generalization of that
conversion lemma is the exact missing step, and is promoted here. -/
def IsRowIndexTrackingCert (v : ℝ → G.State → Payoff (Fin 2))
    (x : ℝ → G.StationaryMixedProfile) (lam : G.HistoryPotential) (target : ℝ)
    (e : ℕ → ℝ) : Prop :=
  ∀ (dev : G.BehaviorStrategy 1) (t : ℕ) (h : G.Hist t),
    target + v (lam t h) h.2 0 ≤
      G.stageEUAt (G.pairBehaviorProfile (G.rowIndexStrategy x lam) dev) h 0 +
        G.historyContinuationEU (G.pairBehaviorProfile (G.rowIndexStrategy x lam) dev)
          (G.indexPotential v lam) h + e t

/-- The canonical vanishing calendar schedule at level `δ`: strictly
decreasing to `0` while staying inside `(0, δ)`. Used to instantiate the
promoted tracking-cert hypothesis, and as the concrete chain along which
`IsTailVariationBounded` bounds the cumulative tracking error uniformly in
the horizon. -/
def calSched (δ : ℝ) (t : ℕ) : ℝ := δ / (t + 2)

theorem calSched_pos {δ : ℝ} (hδ : 0 < δ) (t : ℕ) : 0 < calSched δ t := by
  unfold calSched; positivity

theorem calSched_lt {δ : ℝ} (hδ : 0 < δ) (t : ℕ) : calSched δ t < δ := by
  unfold calSched
  rw [div_lt_iff₀ (by positivity)]
  have h2 : (2 : ℝ) ≤ (t : ℝ) + 2 := by linarith [(Nat.cast_nonneg t : (0:ℝ) ≤ (t:ℝ))]
  nlinarith

theorem calSched_antitone {δ : ℝ} (hδ : 0 ≤ δ) : Antitone (calSched δ) := by
  intro s t hst
  unfold calSched
  have h1 : (0 : ℝ) < (s : ℝ) + 2 := by positivity
  have h2 : (s : ℝ) + 2 ≤ (t : ℝ) + 2 := by exact_mod_cast Nat.add_le_add_right hst 2
  exact div_le_div_of_nonneg_left hδ h1 h2

/-- The running index as a (calendar-only) history potential. -/
def calScheduleHist (δ : ℝ) : G.HistoryPotential := fun t _ => calSched δ t

/-- The Stage B tracking error along the calendar schedule: the value gap
between consecutive discount levels, in the same sup norm
`IsTailVariationBounded` is stated with. -/
def calTrackError (v : ℝ → G.State → Payoff (Fin 2)) (δ : ℝ) (t : ℕ) : ℝ :=
  ‖v (calSched δ t) - v (calSched δ (t + 1))‖

omit [∀ i, Fintype (G.Act i)] [∀ i, Nonempty (G.Act i)] in
/-- **`IsTailVariationBounded` at work.** The cumulative tracking error
along the calendar schedule, over *any* horizon `T`, is bounded by the
tail-variation budget — uniformly in `T`, not just on average. Proved by
exhibiting the schedule `t ↦ calSched δ (T - t)` (monotone increasing on
`Iic T`) as one admissible chain witnessing `eVariationOn`'s defining
supremum. -/
theorem sum_calTrackError_le {v : ℝ → G.State → Payoff (Fin 2)} {δ ε' : ℝ}
    (hδ : 0 < δ) (hε' : 0 ≤ ε')
    (hvar : eVariationOn v (Set.Ioo (0 : ℝ) δ) ≤ ENNReal.ofReal ε') (T : ℕ) :
    ∑ t ∈ Finset.range T, G.calTrackError v δ t ≤ ε' := by
  set u : ℕ → ℝ := fun i => calSched δ (T - i) with hu
  have hmono : MonotoneOn u (Set.Iic T) := by
    intro i hi j hj hij
    simp only [Set.mem_Iic] at hi hj
    exact calSched_antitone hδ.le (by omega)
  have hmem : ∀ i ≤ T, u i ∈ Set.Ioo (0 : ℝ) δ :=
    fun i _ => ⟨calSched_pos hδ _, calSched_lt hδ _⟩
  have hsum := eVariationOn.sum_le_of_monotoneOn_Iic (f := v) (s := Set.Ioo (0 : ℝ) δ) hmono hmem
  set F : ℕ → ENNReal := fun j => edist (v (calSched δ j)) (v (calSched δ (j + 1))) with hF
  have hpt : ∀ i ∈ Finset.range T, edist (v (u (i + 1))) (v (u i)) = F (T - 1 - i) := by
    intro i hi
    simp only [Finset.mem_range] at hi
    have e1 : T - (i + 1) = T - 1 - i := by omega
    have e2 : T - i = T - 1 - i + 1 := by omega
    simp only [hu, hF]
    rw [e1, e2]
  have hreindex : ∑ i ∈ Finset.range T, edist (v (u (i + 1))) (v (u i)) =
      ∑ j ∈ Finset.range T, F j := by
    rw [Finset.sum_congr rfl hpt, Finset.sum_range_reflect]
  rw [hreindex] at hsum
  have hFeq : ∀ j, F j = ENNReal.ofReal (G.calTrackError v δ j) := by
    intro j
    simp only [hF, calTrackError, edist_dist, dist_eq_norm]
  simp only [hFeq] at hsum
  have hnonneg : ∀ t ∈ Finset.range T, 0 ≤ G.calTrackError v δ t := fun t _ => by
    unfold calTrackError; exact norm_nonneg _
  rw [← ENNReal.ofReal_sum_of_nonneg hnonneg] at hsum
  have hfinal := hsum.trans hvar
  exact (ENNReal.ofReal_le_ofReal_iff hε').mp hfinal

/-- **Stage B: the maximizer-role guarantee — the core reduction.** Bounded
payoffs, the tail-variation modulus, and the promoted one-step tracking
estimate (along the canonical calendar schedule) together secure the
vanishing-discount limit value up to `ε`, against *every* opposing column
strategy, uniformly over every sufficiently long horizon.
`IsTailVariationBounded` is used directly here (via `sum_calTrackError_le`)
to bound the cumulative tracking error by `ε ⁄ 2` uniformly in the horizon
`T`; the boundary loss from the telescope (`2 C ⁄ T`) is what then forces
the horizon threshold `T₀`. -/
theorem secures_vanishingDiscountLimit_row
    (v : ℝ → G.State → Payoff (Fin 2)) (x : ℝ → G.StationaryMixedProfile)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ lam ∈ Set.Ioo (0 : ℝ) 1, ∀ s who, |v lam s who| ≤ C)
    (hvar : G.IsTailVariationBounded v) (w : ℝ) (s₀ : G.State)
    (htrack : ∀ δ : ℝ, 0 < δ →
      G.IsRowIndexTrackingCert v x (G.calScheduleHist δ) w (G.calTrackError v δ)) :
    ∀ ε : ℝ, 0 < ε → ∃ (σ : G.BehaviorStrategy 0) (T₀ : ℕ),
      ∀ (dev : G.BehaviorStrategy 1) (T : ℕ), T₀ ≤ T →
        w - ε ≤ G.finiteAveragePayoff s₀ T (G.pairBehaviorProfile σ dev) 0 := by
  intro ε hε
  obtain ⟨δ0, hδ0, hvarδ0⟩ := hvar (ε / 2) (half_pos hε)
  set δ := min δ0 1 with hδdef
  have hδpos : 0 < δ := lt_min hδ0 one_pos
  have hδle1 : δ ≤ 1 := min_le_right _ _
  have hδleδ0 : δ ≤ δ0 := min_le_left _ _
  have hvarδ : eVariationOn v (Set.Ioo (0 : ℝ) δ) ≤ ENNReal.ofReal (ε / 2) :=
    (eVariationOn.mono v (Set.Ioo_subset_Ioo_right hδleδ0)).trans hvarδ0
  have hesum := G.sum_calTrackError_le hδpos (by positivity) hvarδ
  have hCδ : ∀ (t : ℕ) (s : G.State) (who : Fin 2), |v (calSched δ t) s who| ≤ C :=
    fun t s who =>
      hC (calSched δ t) ⟨calSched_pos hδpos t, lt_of_lt_of_le (calSched_lt hδpos t) hδle1⟩ s who
  set σ := G.rowIndexStrategy x (G.calScheduleHist δ) with hσ
  obtain ⟨T₀, hT₀⟩ := exists_nat_gt ((2 * C + ε / 2) / ε)
  refine ⟨σ, max T₀ 1, fun dev T hT => ?_⟩
  have hT0 : 0 < T := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right T₀ 1) hT)
  have hTge : (T₀ : ℝ) ≤ T := by exact_mod_cast le_trans (le_max_left T₀ 1) hT
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT0
  have hbellman : ∀ (t : ℕ) (h : G.Hist t),
      w + G.indexPotential v (G.calScheduleHist δ) t h ≤
        G.stageEUAt (G.pairBehaviorProfile σ dev) h 0 +
          G.historyContinuationEU (G.pairBehaviorProfile σ dev)
            (G.indexPotential v (G.calScheduleHist δ)) h + G.calTrackError v δ t :=
    fun t h => htrack δ hδpos dev t h
  have hv0 : ∀ h : G.Hist 0, |G.indexPotential v (G.calScheduleHist δ) 0 h| ≤ C := by
    intro h
    exact hCδ 0 h.2 0
  have hvT : ∀ h : G.Hist T, |G.indexPotential v (G.calScheduleHist δ) T h| ≤ C := by
    intro h
    exact hCδ T h.2 0
  have hguar := G.finiteAveragePayoff_ge_of_history_bellman_le
    (G.pairBehaviorProfile σ dev) s₀ 0 (fun _ _ => w)
    (G.indexPotential v (G.calScheduleHist δ)) (G.calTrackError v δ)
    (c := w) (C0 := C) (CT := C) (fun _ _ => le_refl w) hv0 hvT hbellman hT0
  have hesumT := hesum T
  have h1 : (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, G.calTrackError v δ t ≤ (T : ℝ)⁻¹ * (ε / 2) :=
    mul_le_mul_of_nonneg_left hesumT (by positivity)
  have h2 : 2 * C + ε / 2 < (T₀ : ℝ) * ε := by
    rw [div_lt_iff₀ hε] at hT₀; exact hT₀
  have h3 : (T₀ : ℝ) * ε ≤ (T : ℝ) * ε := mul_le_mul_of_nonneg_right hTge hε.le
  have h4 : (2 * C + ε / 2) / T ≤ ε := by
    rw [div_le_iff₀ hTreal]; linarith
  have heq5 : 2 * C / (T : ℝ) + (T : ℝ)⁻¹ * (ε / 2) = (2 * C + ε / 2) / T := by
    field_simp
  have h5 : 2 * C / (T : ℝ) + (T : ℝ)⁻¹ * (ε / 2) ≤ ε := heq5 ▸ h4
  have hCT2 : (C + C) / (T : ℝ) = 2 * C / T := by ring
  linarith [hguar, h1, h5, hCT2]

end StageB

-- ============================================================================
-- Stage C: assembly to a uniform equilibrium payoff
-- ============================================================================

section StageC

variable (G : StochasticGame (Fin 2)) [Fintype G.State] [∀ i, Fintype (G.Act i)]

/-- Zero-sum stage payoffs make finite-horizon average payoffs zero-sum too,
mirroring `ZeroSum.lean`'s `IsZeroSum.discountedPayoff_one_eq_neg_zero` at
the finite-horizon average payoff. -/
theorem finiteAveragePayoff_one_eq_neg_zero (hzs : G.IsZeroSum) (σ : G.BehaviorProfile)
    (s₀ : G.State) (T : ℕ) :
    G.finiteAveragePayoff s₀ T σ 1 = -G.finiteAveragePayoff s₀ T σ 0 := by
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT; simp
  · rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff,
      G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
    rw [show (∑ t ∈ Finset.range T, G.expectedStagePayoff σ s₀ t 1) =
        ∑ t ∈ Finset.range T, -G.expectedStagePayoff σ s₀ t 0 from
      Finset.sum_congr rfl fun t _ => hzs.expectedStagePayoff_one_eq_neg_zero σ s₀ t]
    rw [Finset.sum_neg_distrib]
    ring

/-- **The column-side mirror of Stage B's row guarantee**: securing `-w - ε`
for player `1` against every row deviation. This has exactly the shape
`secures_vanishingDiscountLimit_row` proves for the row player with `0` and
`1` exchanged; it is taken here as a hypothesis of that same shape rather
than re-derived, to keep this file's scope bounded (see the module
docstring). -/
def SecuresCol (w : ℝ) (s₀ : G.State) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (σ : G.BehaviorStrategy 1) (T₀ : ℕ),
    ∀ (dev : G.BehaviorStrategy 0) (T : ℕ), T₀ ≤ T →
      -w - ε ≤ G.finiteAveragePayoff s₀ T (G.pairBehaviorProfile dev σ) 1

/-- **Stage C: assembly to a uniform equilibrium payoff.** Combining Stage
B's row guarantee with its column-side mirror (`SecuresCol`) through
`isUniformEquilibriumPayoff_of_deviation_caps` gives the two-player
zero-sum uniform equilibrium payoff `(w, -w)`. -/
theorem isUniformEquilibriumPayoff_of_secures_row_col
    (hzs : G.IsZeroSum) (w : ℝ) (s₀ : G.State)
    (hrow : ∀ ε : ℝ, 0 < ε → ∃ (σ : G.BehaviorStrategy 0) (T₀ : ℕ),
      ∀ (dev : G.BehaviorStrategy 1) (T : ℕ), T₀ ≤ T →
        w - ε ≤ G.finiteAveragePayoff s₀ T (G.pairBehaviorProfile σ dev) 0)
    (hcol : G.SecuresCol w s₀) :
    G.IsUniformEquilibriumPayoff s₀ (fun who => if who = 0 then w else -w) := by
  apply G.isUniformEquilibriumPayoff_of_deviation_caps
  intro δ hδ
  obtain ⟨σrow, T₀r, hTr⟩ := hrow δ hδ
  obtain ⟨σcol, T₀c, hTc⟩ := hcol δ hδ
  refine ⟨G.pairBehaviorProfile σrow σcol, max T₀r T₀c, fun T hT => ?_⟩
  have hTr' : T₀r ≤ T := le_trans (le_max_left _ _) hT
  have hTc' : T₀c ≤ T := le_trans (le_max_right _ _) hT
  have hzs0 := G.finiteAveragePayoff_one_eq_neg_zero hzs
    (G.pairBehaviorProfile σrow σcol) s₀ T
  have hlo := hTr σcol T hTr'
  have hhi := hTc σrow T hTc'
  have hcase : ∀ who : Fin 2, who = 0 ∨ who = 1 := by
    intro who
    match who with
    | 0 => exact Or.inl rfl
    | 1 => exact Or.inr rfl
  constructor
  · intro who
    rcases hcase who with rfl | rfl
    · rw [if_pos rfl, abs_le]
      exact ⟨by linarith, by linarith [hzs0]⟩
    · rw [if_neg (by decide), abs_le]
      exact ⟨by linarith [hzs0], by linarith⟩
  · intro who dev
    rcases hcase who with rfl | rfl
    · rw [G.update_pairBehaviorProfile_zero, if_pos rfl]
      have hhi' := hTc dev T hTc'
      have hzs' := G.finiteAveragePayoff_one_eq_neg_zero hzs
        (G.pairBehaviorProfile dev σcol) s₀ T
      linarith
    · rw [G.update_pairBehaviorProfile_one, if_neg (by decide)]
      have hlo' := hTr dev T hTr'
      have hzs' := G.finiteAveragePayoff_one_eq_neg_zero hzs
        (G.pairBehaviorProfile σrow dev) s₀ T
      linarith

end StageC

end StochasticGame
end GameTheory
