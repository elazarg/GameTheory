/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.Adaptive
import GameTheory.Concepts.Stochastic.Fink
import GameTheory.Concepts.Stochastic.FinkSchedule
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

### The zero-sum row/column protection bridge (`StageAB`) and its limits (`StageBSchedule`)

`IsRowIndexTrackingCert` is **not** discharged in this file; it remains a
promoted hypothesis, exactly as before. Two sorry-free pieces of genuine
progress towards it are added instead, sharpening the residual:

* `StochasticGame.IsShapleyFamily.le_row_discountedPayoff` (and its column
  mirror `le_col_discountedPayoff`) — the missing zero-sum bridge: at a
  *single, fixed* discount level `lam`, `IsShapleyFamily` plus `IsZeroSum`
  plus the natural "value is itself zero-sum" side condition together give
  row's actual `lam`-discounted Shapley-style security guarantee against
  *every* history-dependent column deviation (built from
  `IsDiscountedStationaryBellmanEq.row_bellman_ge`, the zero-sum companion to
  Fink's own `deviation_bellman_ge`, which only caps the *deviator's own*
  payoff and says nothing about the non-deviating player without zero-sum).
* `StochasticGame.IsShapleyFamily.isDiscountedStationaryBellmanSchedule_calSched`
  connects `IsShapleyFamily` along the canonical calendar to
  `FinkSchedule.lean`'s `IsDiscountedStationaryBellmanSchedule` — the
  *correctly discount-scaled* (`β/(1-β)`) time-varying verification layer
  that a genuine history-adaptive argument needs. `tendsto_atTop_calSched_ratio`
  then makes precise **why this still does not discharge
  `IsRowIndexTrackingCert`**: `IsTailVariationBounded` controls the
  *unscaled* jump `‖v lam - v lam'‖`, but the scaling factor `(1-lam)/lam`
  that a correct average-reward Bellman conversion needs diverges as
  `lam → 0⁺`, so it does not control the *scaled* bias jump
  `FinkSchedule.lean`'s `IsScheduledFinkSwitchBound` requires.
  `FinkSchedule.lean`'s own docstring already flags this as an "unresolved
  selection theorem"; closing it needs Mertens–Neyman's actual λ-update rule
  (moving `λ` by the *realized running deficit*, not by calendar time alone)
  — genuinely new mathematical content beyond algebraic reshuffling of the
  existing Stage A data, and the true remaining content of
  `IsRowIndexTrackingCert`.

## The Mertens–Neyman adaptive index (`AdaptiveIndex`)

The λ-update rule the previous section's remark calls for — genuinely new
content, not algebraic reshuffling — is defined here, with its elementary
properties proved and its own one-step tracking attempt carried as far as it
goes without `sorry`:

* `StochasticGame.rowRunningSurplus` / `rowIndexDenom` / `rowDeficitIndex` —
  the adaptive index itself: the row player's *realized* running surplus
  over a target `w` (the real-valued generalization of
  `BigMatchUniform.lean`'s `netRightExcess`), its clamped denominator
  (generalizing `bfDenom`), and the resulting discount-complement index
  `δ / rowIndexDenom`. `rowIndexDenom_snoc_of_le` gives the one-step update
  law; `rowDeficitIndex_pos`/`_le`/`_mem_Ioc`/`_lt_one` give its range facts;
  `rowDeficitIndex_eq_of_surplus_zero` / `_two_eq_calSched_of_surplus_zero`
  confirm it is a strict generalization of `calSched`, recovered exactly
  when the realized surplus stays at `0`.
* `StochasticGame.IsShapleyFamily.rowDeficitIndex_bellman_le` — the one-step
  tracking attempt, generalizing `BigMatchUniform.lean`'s `bfX_le_expect_step`
  to the abstract discounted-value family along `rowDeficitIndex`. It
  succeeds at a *weaker* shape than `IsRowIndexTrackingCert` (the adaptive
  potential's own one-step drift, with no external scalar target and no
  `stageEUAt` term) — see its docstring for the exact algebraic point where
  strengthening it further re-encounters the `β / (1 - β)` divergence, now
  fully explicit rather than a qualitative remark.
* `StochasticGame.IsRowDeficitIndexSecuring` — the sharpened residual:
  `IsRowIndexTrackingCert`'s abstract, opaque hypothesis, replaced by the
  concrete statement that row's `rowDeficitIndex`-indexed strategy secures
  the target `w` up to `ε` over long horizons. Strictly sharper than
  `IsRowIndexTrackingCert` (no remaining freedom in `lam` or the per-step
  budget `e`), it is **not proved** here; its docstring identifies exactly
  the crossing/occupation argument — bounding how often `rowIndexDenom` is
  pushed against its floor by a sustained shortfall, weighted by
  `IsTailVariationBounded`'s modulus at each level visited — that a proof
  would need.

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
-- Stage A→B bridge: the zero-sum row/column protection guarantee
-- ============================================================================

section StageAB

/-!
### The zero-sum row/column protection bridge

`IsShapleyFamily` only records that `(x lam, v lam)` is a **Nash**
equilibrium of the discounted auxiliary games (`IsDiscountedStationaryBellmanEq`,
via `IsDiscountedAuxNash`): no *unilateral deviation* by either player
improves their own payoff. On its own, in a general (non-zero-sum) `n`-player
game this says nothing about what a *non*-deviating player is guaranteed
against an opponent's deviation — Fink's own corollaries
(`IsDiscountedStationaryBellmanEq.deviation_finiteAveragePayoff_le`) only cap
the *deviator's own* payoff.

In a two-player **zero-sum** game this gap closes: column having no incentive
to deviate, transported through the zero-sum identity, is *exactly* row's
security-level guarantee against every column response (the classical fact
that Nash equilibria of zero-sum games are saddle points). The theorems below
formalize this transport, both for the row and the column player, from
`IsDiscountedStationaryBellmanEq`/`IsShapleyFamily` plus `IsZeroSum` plus the
**value zero-sum** side condition `v lam s 1 = -v lam s 0`.

The value zero-sum condition is not re-derived here: it is the standard fact
that the (unique, by contraction) value of a zero-sum discounted stochastic
game is itself zero-sum, but establishing it from `IsShapleyFamily` alone
would need a value-uniqueness argument bridging Fink's general `n`-player
fixed-point construction with the separate Shapley-operator/minimax value
machinery of `ZeroSum.lean` (`discountedShapleyValue`) — out of scope here,
and stated as an explicit hypothesis instead. -/

/-- Zero-sum linearity of `discountedAuxEU`: if the underlying game is
zero-sum and the continuation value `V` is itself zero-sum, the auxiliary
payoff is zero-sum at *every* joint mixed action, not just at an equilibrium
profile. Pure algebra, no Nash property used. -/
theorem discountedAuxEU_one_eq_neg_zero_of_zeroSum
    {G : StochasticGame (Fin 2)} [Fintype G.State] [∀ i, Fintype (G.Act i)]
    (hzs : G.IsZeroSum) (β : ℝ) (V : G.State → Payoff (Fin 2))
    (hVzs : ∀ s, V s 1 = -V s 0) (s : G.State) (m : ∀ i, PMF (G.Act i)) :
    G.discountedAuxEU β V s m 1 = -G.discountedAuxEU β V s m 0 := by
  rw [G.discountedAuxEU_eq, G.discountedAuxEU_eq]
  have hstage : expect (pmfPi m) (fun a => G.stagePayoff s a 1) =
      -expect (pmfPi m) (fun a => G.stagePayoff s a 0) := by
    rw [show (fun a => G.stagePayoff s a 1) = fun a => (-1 : ℝ) * G.stagePayoff s a 0 by
      funext a; rw [hzs s a]; ring]
    rw [expect_const_mul]; ring
  have hcont : expect (pmfPi m) (fun a =>
      expect (G.transition s a) (fun s' => V s' 1)) =
      -expect (pmfPi m) (fun a => expect (G.transition s a) (fun s' => V s' 0)) := by
    rw [show (fun a => expect (G.transition s a) (fun s' => V s' 1)) =
        fun a => (-1 : ℝ) * expect (G.transition s a) (fun s' => V s' 0) by
      funext a
      rw [show (fun s' => V s' 1) = fun s' => (-1 : ℝ) * V s' 0 by
        funext s'; rw [hVzs s']; ring]
      rw [expect_const_mul]]
    rw [expect_const_mul]; ring
  rw [hstage, hcont]; ring

/-- **Row protection at the auxiliary-game level.** Column's own no-incentive-
to-deviate property (`IsDiscountedAuxNash` at `who = 1`), transported through
zero-sum linearity, bounds row's payoff *below* by `V s 0` against every
column mixed deviation `d` — even though `d` need not be column's equilibrium
action. -/
theorem IsDiscountedStationaryBellmanEq.row_discountedAuxEU_ge
    {G : StochasticGame (Fin 2)} [Fintype G.State] [∀ i, Fintype (G.Act i)]
    {β : ℝ} {x : G.StationaryMixedProfile} {V : G.State → Payoff (Fin 2)}
    (hF : G.IsDiscountedStationaryBellmanEq β x V)
    (hzs : G.IsZeroSum) (hVzs : ∀ s, V s 1 = -V s 0)
    (s : G.State) (d : PMF (G.Act 1)) :
    V s 0 ≤ G.discountedAuxEU β V s (Function.update (x s) 1 d) 0 := by
  have hnash := hF.1 s 1 d
  rw [hF.2 s 1,
    G.discountedAuxEU_one_eq_neg_zero_of_zeroSum hzs β V hVzs s
      (Function.update (x s) 1 d),
    hVzs s] at hnash
  linarith

/-- **Column protection at the auxiliary-game level**, the mirror of
`row_discountedAuxEU_ge`: row's own no-incentive-to-deviate property, via
zero-sum linearity, bounds column's payoff below by `V s 1` against every row
mixed deviation. -/
theorem IsDiscountedStationaryBellmanEq.col_discountedAuxEU_ge
    {G : StochasticGame (Fin 2)} [Fintype G.State] [∀ i, Fintype (G.Act i)]
    {β : ℝ} {x : G.StationaryMixedProfile} {V : G.State → Payoff (Fin 2)}
    (hF : G.IsDiscountedStationaryBellmanEq β x V)
    (hzs : G.IsZeroSum) (hVzs : ∀ s, V s 1 = -V s 0)
    (s : G.State) (d : PMF (G.Act 0)) :
    V s 1 ≤ G.discountedAuxEU β V s (Function.update (x s) 0 d) 1 := by
  have hnash := hF.1 s 0 d
  rw [hF.2 s 0] at hnash
  have hz := G.discountedAuxEU_one_eq_neg_zero_of_zeroSum hzs β V hVzs s
    (Function.update (x s) 0 d)
  have hVs : V s 0 = -V s 1 := by rw [hVzs s]; ring
  linarith [hz, hnash, hVs]

variable {G : StochasticGame (Fin 2)} [Fintype G.State] [∀ i, Fintype (G.Act i)]

/-- **Row protection, history level.** The zero-sum companion to
`IsDiscountedStationaryBellmanEq.deviation_bellman_ge`: with row fixed at its
`lam`-optimal stationary action and column playing an *arbitrary*
history-dependent deviation, row's continuation satisfies the discounted
Bellman *lower* inequality — the exact quantitative content
`IsRowIndexTrackingCert`'s docstring calls for at a single, fixed discount
level (see the remark after `secures_vanishingDiscountLimit_row` for why a
*single fixed* level does not yet assemble into that certificate's genuinely
history-adaptive, index-tracking form). -/
theorem IsDiscountedStationaryBellmanEq.row_bellman_ge
    {β : ℝ} {x : G.StationaryMixedProfile} {V : G.State → Payoff (Fin 2)}
    (hF : G.IsDiscountedStationaryBellmanEq β x V)
    (hzs : G.IsZeroSum) (hVzs : ∀ s, V s 1 = -V s 0)
    (dev : G.BehaviorStrategy 1) (t : ℕ) (h : G.Hist t) :
    V h.2 0 ≤ (1 - β) * G.stageEUAt
        (Function.update (G.markovBehaviorProfile x) 1 dev) h 0 +
      β * expect
        (G.stageActionDist (Function.update (G.markovBehaviorProfile x) 1 dev) h)
        (fun a => expect (G.transition h.2 a) (fun s' => V s' 0)) := by
  have hrow := hF.row_discountedAuxEU_ge hzs hVzs h.2 (dev t h)
  unfold stageEUAt
  rw [G.stageActionDist_update_markovBehaviorProfile, ← G.discountedAuxEU_eq]
  exact hrow

/-- **Column protection, history level**, the mirror of `row_bellman_ge`. -/
theorem IsDiscountedStationaryBellmanEq.col_bellman_ge
    {β : ℝ} {x : G.StationaryMixedProfile} {V : G.State → Payoff (Fin 2)}
    (hF : G.IsDiscountedStationaryBellmanEq β x V)
    (hzs : G.IsZeroSum) (hVzs : ∀ s, V s 1 = -V s 0)
    (dev : G.BehaviorStrategy 0) (t : ℕ) (h : G.Hist t) :
    V h.2 1 ≤ (1 - β) * G.stageEUAt
        (Function.update (G.markovBehaviorProfile x) 0 dev) h 1 +
      β * expect
        (G.stageActionDist (Function.update (G.markovBehaviorProfile x) 0 dev) h)
        (fun a => expect (G.transition h.2 a) (fun s' => V s' 1)) := by
  have hcol := hF.col_discountedAuxEU_ge hzs hVzs h.2 (dev t h)
  unfold stageEUAt
  rw [G.stageActionDist_update_markovBehaviorProfile, ← G.discountedAuxEU_eq]
  exact hcol

/-- **Row protection, discounted-payoff level.** `IsShapleyFamily` at a
genuine discount complement `lam`, plus zero-sum (game and value), gives row's
`lam`-discounted Shapley-style security guarantee against every
history-dependent column deviation — the Fink/Nash-style analogue of
`ZeroSum.lean`'s `discountedShapleyValue_le_row_discountedPayoff` (which uses
the separate Shapley-operator/minimax formalization instead). -/
theorem IsShapleyFamily.le_row_discountedPayoff
    {v : ℝ → G.State → Payoff (Fin 2)} {x : ℝ → G.StationaryMixedProfile}
    (hSF : G.IsShapleyFamily v x) (hzs : G.IsZeroSum)
    {lam : ℝ} (hlam : lam ∈ Set.Ioo (0 : ℝ) 1) (hVzs : ∀ s, v lam s 1 = -v lam s 0)
    (dev : G.BehaviorStrategy 1) (s₀ : G.State) :
    v lam s₀ 0 ≤ G.discountedPayoff (1 - lam)
        (Function.update (G.markovBehaviorProfile (x lam)) 1 dev) s₀ 0 := by
  have hF := hSF lam hlam
  obtain ⟨C, hC⟩ := exists_abs_bound_of_finite
    (fun p : G.State × G.JointAct => G.stagePayoff p.1 p.2 0)
  exact G.le_discountedPayoff_of_bellman_le (C := C) (fun s a => hC (s, a))
    (Function.update (G.markovBehaviorProfile (x lam)) 1 dev) s₀ (fun s => v lam s 0)
    (by linarith [hlam.2]) (by linarith [hlam.1])
    (fun t h => hF.row_bellman_ge hzs hVzs dev t h)

/-- **Column protection, discounted-payoff level**, the mirror of
`IsShapleyFamily.le_row_discountedPayoff`. -/
theorem IsShapleyFamily.le_col_discountedPayoff
    {v : ℝ → G.State → Payoff (Fin 2)} {x : ℝ → G.StationaryMixedProfile}
    (hSF : G.IsShapleyFamily v x) (hzs : G.IsZeroSum)
    {lam : ℝ} (hlam : lam ∈ Set.Ioo (0 : ℝ) 1) (hVzs : ∀ s, v lam s 1 = -v lam s 0)
    (dev : G.BehaviorStrategy 0) (s₀ : G.State) :
    v lam s₀ 1 ≤ G.discountedPayoff (1 - lam)
        (Function.update (G.markovBehaviorProfile (x lam)) 0 dev) s₀ 1 := by
  have hF := hSF lam hlam
  obtain ⟨C, hC⟩ := exists_abs_bound_of_finite
    (fun p : G.State × G.JointAct => G.stagePayoff p.1 p.2 1)
  exact G.le_discountedPayoff_of_bellman_le (C := C) (fun s a => hC (s, a))
    (Function.update (G.markovBehaviorProfile (x lam)) 0 dev) s₀ (fun s => v lam s 1)
    (by linarith [hlam.2]) (by linarith [hlam.1])
    (fun t h => hF.col_bellman_ge hzs hVzs dev t h)

end StageAB

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
-- Stage B discharge attempt: the calendar-schedule connection and its limits
-- ============================================================================

section StageBSchedule

variable (G : StochasticGame (Fin 2)) [Fintype G.State] [∀ i, Fintype (G.Act i)]

/-- Along the canonical calendar schedule, `IsShapleyFamily` gives a genuine
`FinkSchedule.lean`-style `IsDiscountedStationaryBellmanSchedule`: statewise
Nash consistency at every calendar stage `t`, with discount complement
`calSched δ t`. This is the honest connection from Stage A's abstract
per-`λ` data to the *existing*, correctly-scaled time-varying verification
layer of `FinkSchedule.lean` — see the remark below for why this connection,
by itself, still does not discharge `IsRowIndexTrackingCert`. -/
theorem IsShapleyFamily.isDiscountedStationaryBellmanSchedule_calSched
    {v : ℝ → G.State → Payoff (Fin 2)} {x : ℝ → G.StationaryMixedProfile}
    (hSF : G.IsShapleyFamily v x) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    G.IsDiscountedStationaryBellmanSchedule (fun t => 1 - calSched δ t)
      (fun t => x (calSched δ t)) (fun t => v (calSched δ t)) :=
  fun t => hSF (calSched δ t) ⟨calSched_pos hδ t, lt_of_lt_of_le (calSched_lt hδ t) hδ1⟩

/-- **Why the discharge stops here — the sharpened residual.**
`FinkSchedule.lean`'s
`IsDiscountedStationaryBellmanSchedule.finiteAveragePayoff_ge_targetAverage`
would (via `isDiscountedStationaryBellmanSchedule_calSched` above, plus the
zero-sum row-protection bridge of `IsDiscountedStationaryBellmanEq.row_bellman_ge`
generalized calendar-wise as `FinkSchedule.lean` already does for the
non-zero-sum deviation bound) finish a derivation of an
`IsRowIndexTrackingCert`-strength guarantee — *if* it were fed an
`IsScheduledFinkSwitchBound` for the induced schedule: a bound on the jump of
the *scaled* bias `scheduledFinkBias β V t s who = (β t / (1 - β t)) * V t s
who` between consecutive calendar stages.

`IsTailVariationBounded` only controls the *unscaled* jump `‖v lam - v
lam'‖`; it does **not** control the scaled one, because the scaling factor
`(1 - lam) / lam` itself diverges as `lam → 0⁺` — along the canonical
calendar it grows like `t / δ`, unboundedly, as `tendsto_atTop_calSched_ratio`
below makes precise. So even a `v` that is genuinely Cauchy (hence bounded)
in the *unscaled* sup norm can have an unbounded, non-summable *scaled* bias
jump, and `IsScheduledFinkSwitchBound` (equivalently, the genuinely
history-adaptive λ-index-tracking accounting `IsRowIndexTrackingCert`
promotes) is **not** implied by `IsShapleyFamily` and `IsTailVariationBounded`
alone. `FinkSchedule.lean`'s own module docstring already flags exactly this
gap: "It does not assume the unresolved selection theorem needed to
construct such a schedule in a general multiplayer stochastic game."
Closing it needs Mertens–Neyman's actual λ-update rule — moving `λ` as a
function of the *realized running deficit* between accumulated payoff and
target, rather than of calendar time alone — which is not encoded anywhere
in this file's or `FinkSchedule.lean`'s existing machinery, and is the
genuine remaining content of `IsRowIndexTrackingCert`. -/
theorem tendsto_atTop_calSched_ratio {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto (fun t : ℕ => (1 - calSched δ t) / calSched δ t)
      Filter.atTop Filter.atTop := by
  have hEq : ∀ t : ℕ, (1 - calSched δ t) / calSched δ t = ((t : ℝ) + 2) / δ - 1 := by
    intro t
    have hne : calSched δ t ≠ 0 := ne_of_gt (calSched_pos hδ t)
    unfold calSched at hne ⊢
    field_simp
  simp_rw [hEq]
  apply Filter.tendsto_atTop_add_const_right
  apply Filter.Tendsto.atTop_div_const hδ
  exact Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop

end StageBSchedule

-- ============================================================================
-- The Mertens–Neyman adaptive index: the realized running-deficit λ-update
-- ============================================================================

section AdaptiveIndex

/-!
### The adaptive index (constructive partial progress towards `IsRowIndexTrackingCert`)

`calSched`/`calScheduleHist` above is a **calendar** schedule: it depends only
on elapsed time `t`, never on how play has actually gone. Mertens–Neyman's
own λ-update instead moves the discount complement by the *realized* running
deficit between accumulated payoff and a target — a genuinely
history-adaptive index. This section defines that index as a Lean object,
`rowDeficitIndex`, and proves its elementary properties: the one-step update
law of its denominator, positivity/range bounds, and the fact that it is a
strict generalization of `calSched` (recovered exactly when the realized
surplus stays at `0`).

The concrete template is `BigMatchUniform.lean`'s `netRightExcess`/`bfDenom`:
there the denominator `bfDenom N k := max (k + N + 1) 1` is the clamped,
shifted excess of the minimizer's realized `±1` actions. Here the excess is
replaced by the row player's own *realized* running surplus over an
arbitrary real target `w` — `rowRunningSurplus` — giving `rowIndexDenom`
exactly the same clamped-additive shape, and `rowDeficitIndex := δ /
rowIndexDenom` the corresponding index in the discount-complement domain
(rather than `bfDenom`'s value-potential domain).

`rowDeficitIndex_bellman_le` below then attempts the one-step tracking
estimate against arbitrary opposing play, generalizing
`BigMatchUniform.lean`'s `bfX_le_expect_step`. It succeeds at a *weaker*
shape than `IsRowIndexTrackingCert` (no external scalar target, only the
potential's own one-step drift) — see its docstring and the sharpened
residual `IsRowDeficitIndexCrossingBound` at the end of this section for
exactly where and why the stronger, target-based shape still resists proof
from this file's existing hypotheses alone.
-/

variable (G : StochasticGame (Fin 2)) [Fintype G.State] [∀ i, Fintype (G.Act i)]
  [∀ i, Nonempty (G.Act i)]

/-! #### Step 1–2: the realized running surplus and the index denominator -/

/-- The row player's **realized running surplus** over a target `w`: the
actual accumulated stage payoff recorded along the history `h` (via
`totalPayoff`, read off the history's own recorded `(state, action)` pairs —
*not* an expectation), in excess of `w` charged once per elapsed stage.
Positive means row has actually earned above the target `w` so far along
this specific play; negative means row is running a realized deficit below
`w`. The exact real-valued generalization of `BigMatchUniform.lean`'s
`netRightExcess` (there a `±1`-per-stage integer walk driven by the
opponent's realized action; here a real-valued walk driven by row's own
realized stage payoff against an arbitrary target `w`). -/
def rowRunningSurplus (w : ℝ) {t : ℕ} (h : G.Hist t) : ℝ :=
  G.totalPayoff 0 h - t * w

@[simp] theorem rowRunningSurplus_zero (w : ℝ) (h : G.Hist 0) :
    G.rowRunningSurplus w h = 0 := by
  simp [rowRunningSurplus]

/-- **One-step update of the running surplus** — the realized-stage analogue
of `BigMatchUniform.lean`'s `netRightExcess_snoc`: extending the history by
one realized stage adds that stage's realized payoff deficit `stagePayoff
h.2 a 0 - w` to the surplus. -/
theorem rowRunningSurplus_snoc (w : ℝ) {t : ℕ} (h : G.Hist t) (a : G.JointAct)
    (s' : G.State) :
    G.rowRunningSurplus w ((Fin.snoc h.1 (h.2, a), s') : G.Hist (t + 1)) =
      G.rowRunningSurplus w h + (G.stagePayoff h.2 a 0 - w) := by
  unfold rowRunningSurplus
  rw [totalPayoff_snoc]
  push_cast
  ring

/-- **The Mertens–Neyman index denominator.** The calendar clock `t + N`,
shifted by the realized running surplus and clamped below by the floor `N` —
the exact real-valued analogue of `BigMatchUniform.lean`'s `bfDenom N k :=
max (k + N + 1) 1`. A realized surplus (row doing well) pushes the
denominator *up* (so the index `δ / denom` below shrinks — more patient,
closer to the vanishing-discount limit); a realized deficit pushes it back
*down* towards the floor `N` (more aggressive, reacting faster to the
shortfall), exactly the "moved by the realized running deficit" update law
the task calls for. -/
def rowIndexDenom (N : ℕ) (w : ℝ) {t : ℕ} (h : G.Hist t) : ℝ :=
  max (N : ℝ) ((t : ℝ) + N + G.rowRunningSurplus w h)

theorem le_rowIndexDenom (N : ℕ) (w : ℝ) {t : ℕ} (h : G.Hist t) :
    (N : ℝ) ≤ G.rowIndexDenom N w h :=
  le_max_left _ _

theorem rowIndexDenom_pos {N : ℕ} (hN : 1 ≤ N) (w : ℝ) {t : ℕ} (h : G.Hist t) :
    0 < G.rowIndexDenom N w h :=
  lt_of_lt_of_le (by exact_mod_cast hN) (G.le_rowIndexDenom N w h)

/-- **The one-step update relation, off the clamp boundary.** Whenever both
the stage-`t` *and* the successor stage-`(t+1)` unclamped calendar-plus-
surplus values dominate the floor `N` (the real-valued step `stagePayoff h.2
a 0 - w` need not be `±1`-bounded as `BigMatchUniform.lean`'s excess step
is, so — unlike `bfDenom_succ_of_right`/`bfDenom_succ_of_left`, where the
predecessor being unclamped already forces the `±1`-step successor to be
unclamped too — both endpoints must be assumed off the clamp here), the
denominator updates *additively* by exactly `1` plus the realized
stage-payoff deficit `stagePayoff h.2 a 0 - w`. -/
theorem rowIndexDenom_snoc_of_le (N : ℕ) (w : ℝ) {t : ℕ} (h : G.Hist t)
    (hoff : (N : ℝ) ≤ (t : ℝ) + N + G.rowRunningSurplus w h)
    (a : G.JointAct) (s' : G.State)
    (hoff1 : (N : ℝ) ≤ (t : ℝ) + N + G.rowRunningSurplus w h + 1 +
      (G.stagePayoff h.2 a 0 - w)) :
    G.rowIndexDenom N w ((Fin.snoc h.1 (h.2, a), s') : G.Hist (t + 1)) =
      G.rowIndexDenom N w h + 1 + (G.stagePayoff h.2 a 0 - w) := by
  unfold rowIndexDenom
  rw [rowRunningSurplus_snoc, max_eq_right hoff]
  push_cast
  rw [max_eq_right (by linarith [hoff1])]
  ring

/-! #### Step 1–2: the adaptive index itself -/

/-- **The Mertens–Neyman adaptive index.** The row player's running discount
complement `λ`, moved by the realized running deficit between accumulated
payoff and a running target `w`: the base calendar rate `δ` divided by the
deficit-adjusted denominator `rowIndexDenom`. By construction a
`G.HistoryPotential` — a function of the history prefix `Hist t` alone, so
adapted to the natural filtration with no separate measurability proof
needed in this finite discrete setting — ready to be plugged into
`rowIndexStrategy`/`indexPotential`/`IsRowIndexTrackingCert` in place of
`calScheduleHist`. -/
def rowDeficitIndex (δ : ℝ) (N : ℕ) (w : ℝ) : G.HistoryPotential :=
  fun _ h => δ / G.rowIndexDenom N w h

theorem rowDeficitIndex_pos {δ : ℝ} (hδ : 0 < δ) {N : ℕ} (hN : 1 ≤ N) (w : ℝ)
    (t : ℕ) (h : G.Hist t) :
    0 < G.rowDeficitIndex δ N w t h :=
  div_pos hδ (G.rowIndexDenom_pos hN w h)

theorem rowDeficitIndex_le {δ : ℝ} (hδ : 0 ≤ δ) {N : ℕ} (hN : 1 ≤ N) (w : ℝ)
    (t : ℕ) (h : G.Hist t) :
    G.rowDeficitIndex δ N w t h ≤ δ / N :=
  div_le_div_of_nonneg_left hδ (by exact_mod_cast hN) (G.le_rowIndexDenom N w h)

/-- **Range fact.** `rowDeficitIndex` always lands in `(0, δ / N]`. -/
theorem rowDeficitIndex_mem_Ioc {δ : ℝ} (hδ : 0 < δ) {N : ℕ} (hN : 1 ≤ N) (w : ℝ)
    (t : ℕ) (h : G.Hist t) :
    G.rowDeficitIndex δ N w t h ∈ Set.Ioc (0 : ℝ) (δ / N) :=
  ⟨G.rowDeficitIndex_pos hδ hN w t h, G.rowDeficitIndex_le hδ.le hN w t h⟩

/-- **Range fact.** With `δ < N`, `rowDeficitIndex` lands strictly inside
`Ioo 0 1`, the domain `IsShapleyFamily` requires. -/
theorem rowDeficitIndex_lt_one {δ : ℝ} (hδ : 0 < δ) {N : ℕ} (hN : 1 ≤ N)
    (hδN : δ < N) (w : ℝ) (t : ℕ) (h : G.Hist t) :
    G.rowDeficitIndex δ N w t h < 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le Nat.one_pos hN
  calc G.rowDeficitIndex δ N w t h ≤ δ / N := G.rowDeficitIndex_le hδ.le hN w t h
    _ < 1 := (div_lt_one hNpos).mpr hδN

theorem rowDeficitIndex_zero {δ : ℝ} (N : ℕ) (w : ℝ) (h : G.Hist 0) :
    G.rowDeficitIndex δ N w 0 h = δ / N := by
  unfold rowDeficitIndex rowIndexDenom
  rw [rowRunningSurplus_zero]
  norm_num

/-- **Recovery of the calendar schedule.** When the realized running surplus
is exactly `0` — in particular whenever row's realized stage payoff has
equalled the target `w` at every past stage — `rowDeficitIndex` collapses
*exactly* to a calendar-style schedule `δ / (t + N)`, confirming
`rowDeficitIndex` is a strict generalization of `calSched`, not a
replacement construction. -/
theorem rowDeficitIndex_eq_of_surplus_zero {δ : ℝ} (N : ℕ) (w : ℝ)
    {t : ℕ} (h : G.Hist t) (hsurplus : G.rowRunningSurplus w h = 0) :
    G.rowDeficitIndex δ N w t h = δ / ((t : ℝ) + N) := by
  unfold rowDeficitIndex rowIndexDenom
  rw [hsurplus, add_zero, max_eq_right (by linarith [Nat.cast_nonneg (α := ℝ) t])]

/-- At base level `N = 2`, the zero-surplus collapse recovers `calSched`
*verbatim*. -/
theorem rowDeficitIndex_two_eq_calSched_of_surplus_zero {δ : ℝ} (w : ℝ)
    {t : ℕ} (h : G.Hist t) (hsurplus : G.rowRunningSurplus w h = 0) :
    G.rowDeficitIndex δ 2 w t h = calSched δ t := by
  rw [G.rowDeficitIndex_eq_of_surplus_zero 2 w h hsurplus, calSched]
  norm_num

/-! #### Step 3: the one-step tracking attempt -/

/-- General pointwise bound extracted from the sup-norm difference bound
`IsTailVariationBounded` (via `IsTailVariationBounded.pairwise_le`) supplies:
the value difference at any single state/player is bounded by the sup-norm
difference of the two value functions. -/
theorem abs_sub_apply_le_norm (V W : G.State → Payoff (Fin 2)) (s : G.State)
    (who : Fin 2) : |V s who - W s who| ≤ ‖V - W‖ := by
  have h1 : ‖(V - W) s who‖ ≤ ‖(V - W) s‖ := norm_le_pi_norm ((V - W) s) who
  have h2 : ‖(V - W) s‖ ≤ ‖V - W‖ := norm_le_pi_norm (V - W) s
  rw [Pi.sub_apply, Pi.sub_apply, Real.norm_eq_abs] at h1
  exact h1.trans h2

/-- At a single fixed history, the row-index strategy paired with an
arbitrary column deviation induces exactly the same stage mixed action as
row's stationary Markov play at the index's *current* value there, paired
with the same deviation — the bridge letting `row_bellman_ge`'s fixed-`β`
Bellman inequality (stated for `markovBehaviorProfile`) apply to
`rowIndexStrategy`. -/
theorem stageActionDist_pairBehaviorProfile_rowIndexStrategy
    (x : ℝ → G.StationaryMixedProfile) (lam : G.HistoryPotential)
    (dev : G.BehaviorStrategy 1) {t : ℕ} (h : G.Hist t) :
    G.stageActionDist (G.pairBehaviorProfile (G.rowIndexStrategy x lam) dev) h =
      G.stageActionDist
        (Function.update (G.markovBehaviorProfile (x (lam t h))) 1 dev) h := by
  rw [stageActionDist_pairBehaviorProfile, stageActionDist_update_markovBehaviorProfile]
  congr 1
  funext i
  fin_cases i
  · rfl
  · simp [Function.update]

/-- **The one-step adaptive-index tracking attempt** — generalizing
`BigMatchUniform.lean`'s `bfX_le_expect_step` from the Big Match's concrete
`bfX` potential to the abstract discounted-value family `v`, along the
concrete `rowDeficitIndex` update law.

The bound splits into exactly the two pieces the module docstring's
`StageBSchedule` remark identifies: (1) a fixed-`λ₀ := rowDeficitIndex …  t
h` discounted-to-average conversion slack, from `row_bellman_ge` applied at
the *single* discount level `λ₀`, bounded by `λ₀ * (C + Cv)` (`C` bounds
stage payoffs, `Cv` bounds `v`); and (2) the *index-jump* slack from
evaluating the continuation at the *adaptive* successor index `λ (t+1) h'`
instead of the fixed `λ₀`, bounded by `ε` via the unscaled tail-variation
pairwise bound `hpair` (an instance of `IsTailVariationBounded.pairwise_le`).

This succeeds at a *weaker* shape than `IsRowIndexTrackingCert`: the
conclusion bounds the adaptive potential's own one-step drift (matching
`bfXExpect_le_succ`'s role exactly), but carries **no external scalar
target** `w` and **no `stageEUAt` term** on the right — `IsRowIndexTrackingCert`
additionally needs `target + v(λ₀) ≤ stageEU + E[v(λ')] + e`, i.e. needs the
*fixed-λ₀* slack `λ₀ * (stageEU - E_fixed[v(λ₀)])` (not just its absolute
bound `λ₀ * (C + Cv)`) to be dominated by `stageEU - w` for *every* possible
opposing deviation. `IsRowDeficitIndexCrossingBound` below states precisely
why that further step is exactly where the `β / (1 - β)` divergence bites
even at this fully explicit, concrete index. -/
theorem IsShapleyFamily.rowDeficitIndex_bellman_le
    {v : ℝ → G.State → Payoff (Fin 2)} {x : ℝ → G.StationaryMixedProfile}
    (hSF : G.IsShapleyFamily v x) (hzs : G.IsZeroSum)
    (hVzs : ∀ lam ∈ Set.Ioo (0 : ℝ) 1, ∀ s, v lam s 1 = -v lam s 0)
    {C Cv : ℝ} (hC : ∀ s a who, |G.stagePayoff s a who| ≤ C)
    (hCv : ∀ lam ∈ Set.Ioo (0 : ℝ) 1, ∀ s who, |v lam s who| ≤ Cv)
    {δ' ε : ℝ}
    (hpair : ∀ lam ∈ Set.Ioo (0 : ℝ) δ', ∀ lam' ∈ Set.Ioo (0 : ℝ) δ',
      ‖v lam - v lam'‖ ≤ ε)
    {N : ℕ} {δ w : ℝ} (hδ0 : 0 < δ) (hN1 : 1 ≤ N)
    (hδN : δ / N < δ') (hδ'1 : δ' ≤ 1)
    (dev : G.BehaviorStrategy 1) (t : ℕ) (h : G.Hist t) :
    v (G.rowDeficitIndex δ N w t h) h.2 0 ≤
      G.historyContinuationEU
        (G.pairBehaviorProfile (G.rowIndexStrategy x (G.rowDeficitIndex δ N w)) dev)
        (G.indexPotential v (G.rowDeficitIndex δ N w)) h +
      ((δ / N) * (C + Cv) + ε) := by
  set lam := G.rowDeficitIndex δ N w with hlamdef
  have hlam0_pos : 0 < lam t h := G.rowDeficitIndex_pos hδ0 hN1 w t h
  have hlam0_le : lam t h ≤ δ / N := G.rowDeficitIndex_le hδ0.le hN1 w t h
  have hlam0_lt1 : lam t h < 1 := lt_of_le_of_lt hlam0_le hδN |>.trans_le hδ'1
  have hlam0mem : lam t h ∈ Set.Ioo (0 : ℝ) 1 := ⟨hlam0_pos, hlam0_lt1⟩
  have hF := hSF (lam t h) hlam0mem
  have hbell := hF.row_bellman_ge hzs (hVzs (lam t h) hlam0mem) dev t h
  set SE := G.stageEUAt (Function.update (G.markovBehaviorProfile (x (lam t h))) 1 dev) h 0
    with hSEdef
  set EF := expect
      (G.stageActionDist (Function.update (G.markovBehaviorProfile (x (lam t h))) 1 dev) h)
      (fun a => expect (G.transition h.2 a) (fun s' => v (lam t h) s' 0))
    with hEFdef
  have hbell' : v (lam t h) h.2 0 ≤ (lam t h) * SE + (1 - lam t h) * EF := by
    have hring : (1 - (1 - lam t h)) = lam t h := by ring
    rw [hring] at hbell
    exact hbell
  have hSEle : SE ≤ C := by
    rw [hSEdef]
    unfold stageEUAt
    have := abs_expect_le_of_abs_le
      (G.stageActionDist (Function.update (G.markovBehaviorProfile (x (lam t h))) 1 dev) h)
      (fun a => G.stagePayoff h.2 a 0) (fun a => hC h.2 a 0)
    exact le_of_abs_le this
  have hEFge : -Cv ≤ EF := by
    rw [hEFdef]
    have hin : ∀ a, |expect (G.transition h.2 a) (fun s' => v (lam t h) s' 0)| ≤ Cv := by
      intro a
      exact abs_expect_le_of_abs_le (G.transition h.2 a) (fun s' => v (lam t h) s' 0)
        (fun s' => hCv (lam t h) hlam0mem s' 0)
    have := abs_expect_le_of_abs_le
      (G.stageActionDist (Function.update (G.markovBehaviorProfile (x (lam t h))) 1 dev) h)
      (fun a => expect (G.transition h.2 a) (fun s' => v (lam t h) s' 0)) hin
    exact neg_le_of_abs_le this
  have hlam0nonneg : 0 ≤ lam t h := hlam0_pos.le
  have hkey : v (lam t h) h.2 0 ≤ EF + (lam t h) * (C + Cv) := by
    have heq : (lam t h) * SE + (1 - lam t h) * EF = EF + (lam t h) * (SE - EF) := by ring
    have hSECEF : SE - EF ≤ C + Cv := by linarith [hSEle, hEFge]
    have hmul : (lam t h) * (SE - EF) ≤ (lam t h) * (C + Cv) :=
      mul_le_mul_of_nonneg_left hSECEF hlam0nonneg
    calc v (lam t h) h.2 0 ≤ (lam t h) * SE + (1 - lam t h) * EF := hbell'
      _ = EF + (lam t h) * (SE - EF) := heq
      _ ≤ EF + (lam t h) * (C + Cv) := by linarith [hmul]
  set σ := G.pairBehaviorProfile (G.rowIndexStrategy x lam) dev with hσdef
  set EA := G.historyContinuationEU σ (G.indexPotential v lam) h with hEAdef
  have hEA_unfold : EA = expect (G.stageActionDist σ h) (fun a => expect (G.transition h.2 a)
      (fun s' => v (lam (t + 1) (Fin.snoc h.1 (h.2, a), s')) s' 0)) := by
    rw [hEAdef]
    unfold historyContinuationEU indexPotential
    rfl
  have hEF_eq : EF = expect (G.stageActionDist σ h)
      (fun a => expect (G.transition h.2 a) (fun s' => v (lam t h) s' 0)) := by
    rw [hEFdef, hσdef, G.stageActionDist_pairBehaviorProfile_rowIndexStrategy x lam dev h]
  have hpt : ∀ a, expect (G.transition h.2 a) (fun s' => v (lam t h) s' 0) ≤
      expect (G.transition h.2 a)
        (fun s' => v (lam (t + 1) (Fin.snoc h.1 (h.2, a), s')) s' 0) + ε := by
    intro a
    have hpt2 : ∀ s', v (lam t h) s' 0 ≤
        v (lam (t + 1) (Fin.snoc h.1 (h.2, a), s')) s' 0 + ε := by
      intro s'
      have hmemL : lam (t + 1) (Fin.snoc h.1 (h.2, a), s') ∈ Set.Ioo (0 : ℝ) δ' :=
        ⟨G.rowDeficitIndex_pos hδ0 hN1 w (t + 1) _,
          lt_of_le_of_lt (G.rowDeficitIndex_le hδ0.le hN1 w (t + 1) _) hδN⟩
      have hmemR : lam t h ∈ Set.Ioo (0 : ℝ) δ' :=
        ⟨hlam0_pos, lt_of_le_of_lt hlam0_le hδN⟩
      have hb := G.abs_sub_apply_le_norm (v (lam t h))
        (v (lam (t + 1) (Fin.snoc h.1 (h.2, a), s'))) s' 0
      have hv := hpair (lam t h) hmemR (lam (t + 1) (Fin.snoc h.1 (h.2, a), s')) hmemL
      have habs := hb.trans hv
      rw [abs_le] at habs
      linarith [habs.1]
    have hmono := expect_mono (G.transition h.2 a) (fun s' => v (lam t h) s' 0)
      (fun s' => v (lam (t + 1) (Fin.snoc h.1 (h.2, a), s')) s' 0 + ε) hpt2
    rwa [expect_add, expect_const] at hmono
  have hjump : EF ≤ EA + ε := by
    rw [hEF_eq, hEA_unfold]
    have hmono := expect_mono (G.stageActionDist σ h)
      (fun a => expect (G.transition h.2 a) (fun s' => v (lam t h) s' 0))
      (fun a => expect (G.transition h.2 a)
        (fun s' => v (lam (t + 1) (Fin.snoc h.1 (h.2, a), s')) s' 0) + ε)
      hpt
    rwa [expect_add, expect_const] at hmono
  have hCCv : 0 ≤ C + Cv := by
    have h1 : 0 ≤ C := le_trans (abs_nonneg _) (hC h.2 (Classical.arbitrary G.JointAct) 0)
    have h2 : 0 ≤ Cv := le_trans (abs_nonneg _) (hCv (lam t h) hlam0mem h.2 0)
    linarith
  have hlamCCv : (lam t h) * (C + Cv) ≤ (δ / N) * (C + Cv) :=
    mul_le_mul_of_nonneg_right hlam0_le hCCv
  linarith [hkey, hjump, hlamCCv]

/-! #### Step 4: the sharpened residual -/

/-- **The sharpened residual.** The precise remaining content of
`IsRowIndexTrackingCert`, once `lam` is fixed to the *concrete*
`rowDeficitIndex δ N w` construction above: row's `λ`-indexed strategy along
`rowDeficitIndex` secures the target `w` up to `ε`, over every sufficiently
long horizon, against every column deviation. Literally
`secures_vanishingDiscountLimit_row`'s conclusion, specialized to
`σ := rowIndexStrategy x (rowDeficitIndex δ N w)`.

This is **strictly sharper** than the abstract `IsRowIndexTrackingCert`: all
the freedom in choosing an arbitrary history-dependent `lam` and an
arbitrary per-step budget `e` is gone — only `δ, N, w` remain free, and
through them the fully explicit update law `rowIndexDenom_snoc_of_le`.
`rowDeficitIndex_bellman_le` above proves *part* of what a derivation would
need — the adaptive potential's own near-drift bound `v (lam t h) h.2 0 ≤ EA
+ (δ / N) * (C + Cv) + ε` — but, as that theorem's docstring explains, this
bound discards the *sign* of the fixed-`λ₀` conversion slack `λ₀ *
(stageEU - E_fixed[v λ₀])`. Recovering `IsRowDeficitIndexSecuring` from it
needs that *signed* slack's **Cesàro average along the realized play** to
vanish, not merely each term to be individually bounded in absolute value.

Concretely: writing out the per-step gap `w + v (lam t h) - stageEU - EA`
that a target-based telescope (`finiteAveragePayoff_ge_of_history_bellman_le`)
would need small, `rowDeficitIndex_bellman_le`'s own algebra gives it the
form `-(1 - λ₀) * stageEU - λ₀ * E_fixed[v λ₀] + w`, which is **not** itself
small — the `(1 - λ₀) ≈ 1` coefficient on `stageEU` is exactly the `β / (1 -
β)`-type divergence the module docstring already flags, now made fully
explicit and concrete. Closing the gap needs exactly the coupling
`rowIndexDenom_snoc_of_le` already exposes: `rowIndexDenom`'s *only* driver
is the same realized deficit `stagePayoff - w` that this per-step gap is
built from, so a run of play that inflates the gap's negative contribution
*simultaneously* drives `rowIndexDenom` down towards its floor `N` (raising
`λ`, making the index react faster to the shortfall) — a genuine
**crossing/occupation** argument, bounding how often and how far
`rowIndexDenom` can be pushed against its floor by a sustained shortfall,
weighted at each level it visits by `IsTailVariationBounded`'s modulus
there. Formalizing that coupling — rather than merely naming it, as here —
is the true remaining mathematical content of `IsRowIndexTrackingCert`, and
is not attempted in this file. -/
def IsRowDeficitIndexSecuring
    (x : ℝ → G.StationaryMixedProfile) (δ : ℝ) (N : ℕ) (w : ℝ) (s₀ : G.State) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℕ, ∀ (dev : G.BehaviorStrategy 1) (T : ℕ), T₀ ≤ T →
    w - ε ≤ G.finiteAveragePayoff s₀ T
      (G.pairBehaviorProfile (G.rowIndexStrategy x (G.rowDeficitIndex δ N w)) dev) 0

end AdaptiveIndex

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
