/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Order.LiminfLimsup
import GameTheory.Concepts.Stochastic.Uniform
import GameTheory.Concepts.Stochastic.InfinitePlayMeasure

/-!
# Bridging finite-horizon-average payoffs to the liminf- and limsup-average games

`GameTheory.Concepts.Stochastic.Uniform` states `IsUniformEquilibriumPayoff`
entirely in terms of **finite-horizon averages** `finiteAveragePayoff s₀ T σ`
for `T ≥ T₀`.  The non-existence literature (e.g. Simon's Mousetrap preprint,
whose claimed counterexample was later retracted; what survives is the
order-of-limits distinction between expected-liminf payoffs and limits of
finite averages, which is what this file bridges) is stated for the
**liminf-average** game instead: the payoff of an infinite
play `ω` is `liminf_T A_T ω`, where `A_T ω` is the average of the first `T`
stage payoffs realized along `ω`, and the game-theoretic payoff is the
expectation `E[liminf_T A_T]` of that pathwise quantity under the measure
induced by a fixed profile. The **limsup-average** game replaces `liminf_T`
by `limsup_T` in that same payoff functional; nothing else about the setup
changes.

This file supplies the bridge between `finiteAveragePayoff` and both
tail-average notions, in two layers. The abstract lemmas
(`integral_liminf_le_of_bounded_of_eventually_le`,
`le_integral_liminf_of_bounded_of_tendsto_ae_of_eventually_le`, and their
limsup duals `le_integral_limsup_of_bounded_of_eventually_le`,
`integral_limsup_le_of_bounded_of_tendsto_ae_of_eventually_le`) work at the
level of generality the bridge actually needs: an arbitrary probability
space `(Ω, μ)` carrying a uniformly bounded family `A : ℕ → Ω → ℝ` of the
finite-horizon averages of one fixed profile, realized pathwise. They stay
fully general and do not mention `StochasticGame` at all.

The game-facing corollaries specialize `(Ω, μ)` to `G.Play` and
`G.infinitePlayMeasure` (`GameTheory.Concepts.Stochastic.InfinitePlayMeasure`)
— the measure built by the Ionescu-Tulcea theorem from `G`'s transition
kernel and a fixed behavior profile — and `A` to `G.pathwiseAveragePayoff`,
the finite-horizon average payoff realized pathwise along an infinite play.
`StochasticGame.integral_pathwiseAveragePayoff` (via the projection property
`StochasticGame.map_histOfPlay_infinitePlayMeasure`) proves this process's
expectation at every horizon is exactly `finiteAveragePayoff`, so both
corollaries below are unconditional in their realization: neither assumes a
process representing the finite-horizon averages.

## Two directions, two different stories

* **Deviation direction (closed).**
  `integral_liminf_le_of_bounded_of_eventually_le` is real Fatou for a
  uniformly bounded family, composed with the trivial fact that `liminf` of
  an eventually-bounded sequence respects the bound. Applied to a fixed
  unilateral deviation, this gives `E[liminf_T A_T] ≤ v_i + 2ε` directly from
  `IsUniformEquilibriumPayoff`
  (`StochasticGame.deviation_liminf_le_of_isUniformEquilibriumPayoff`) once
  the deviation profile's pathwise realization is supplied.

* **On-path direction (conditional).** The reverse bound
  `E_σ[liminf_T A_T] ≥ v_i - ε` does **not** follow from pinned expectations
  alone: a uniformly bounded sequence of expectations converging to `L` can
  have `liminf_T A_T ω = 0` pathwise almost everywhere (the standard "moving
  bump"/typewriter-sequence construction: a sequence of events of constant
  positive probability that slides across the sample space, so every point
  is eventually excluded infinitely often, while also being covered
  infinitely often). Boundedness already gives uniform integrability for
  free on a probability space, so **uniform integrability is not the missing
  hypothesis**. What suffices is **almost-sure convergence** of `A_T` to a
  limit: then `liminf_T A_T = lim_T A_T` a.e., and the dominated convergence
  theorem (using the same uniform bound) upgrades convergence of
  expectations to convergence of the integral of the a.e. limit, which is
  the integral of the liminf.
  `le_integral_liminf_of_bounded_of_tendsto_ae_of_eventually_le` states and
  proves this conditional form;
  `StochasticGame.onPath_le_liminf_integral_of_isUniformEquilibriumPayoff`
  instantiates it against `IsUniformEquilibriumPayoff`.

## What the pair does and does not give

Together the two directions do **not** make the finite-horizon-average
notion and the liminf-average notion interchangeable. Without the on-path
direction's extra hypothesis:

* a non-existence theorem for the liminf-average game does **not** formally
  refute `IsUniformEquilibriumPayoff` — the deviation direction alone only
  shows our notion's deviation payoffs cannot *exceed* the liminf-average
  deviation cap, which is the wrong direction for a refutation to bite; and
* `exists_uniformEquilibriumPayoff` does **not** formally deliver a
  liminf-average equilibrium payoff — the on-path lower bound is exactly the
  missing half, and it costs a genuine extra hypothesis (a.s. convergence)
  that a bare uniform equilibrium payoff does not supply.

## The limsup dual, and the asymmetry it makes explicit

Negation exchanges `liminf` and `limsup` pointwise
(`liminf_neg_eq_neg_limsup`), unconditionally: no boundedness or convergence
hypothesis is needed for that identity by itself, since `Real.sSup`/
`Real.sInf` already return the junk value `0` on unbounded or empty sets,
consistently with negation. Applying each of the two abstract lemmas above
to `-A` therefore produces a dual pair, stated for `limsup` instead of
`liminf`, with **no change to the ENNReal/`ofReal` machinery inside either
proof** — the sign flip is absorbed entirely by
`liminf_neg_eq_neg_limsup` and `MeasureTheory.integral_neg`, applied once
each, from the outside:

* `le_integral_limsup_of_bounded_of_eventually_le` is the dual of
  `integral_liminf_le_of_bounded_of_eventually_le`. It is **unconditional**:
  negation turns "eventually `∫ A_n ≤ bound`" into "eventually
  `bound ≤ ∫ A_n`", and Fatou dualizes to reverse Fatou
  (`limsup E[A_n] ≤ E[limsup A_n]`) without picking up any new hypothesis.
* `integral_limsup_le_of_bounded_of_tendsto_ae_of_eventually_le` is the dual
  of `le_integral_liminf_of_bounded_of_tendsto_ae_of_eventually_le`, and it
  stays **conditional** on the same a.s.-convergence hypothesis: negation
  relabels which sign of inequality needs the hypothesis, it does not
  remove it. The moving-bump construction refutes the unconditional form
  here too, by the same negation: a constant sequence of expectations
  `1/2` with `limsup_T A_T ω = 1` and `liminf_T A_T ω = 0` at every `ω`
  satisfies "eventually `E[A_T] ≤ bound`" at `bound = 1/2`, while
  `E[limsup_T A_T] = 1 > bound`.

So the two liminf-side game corollaries have exact limsup-side twins with
the **same** free/conditional split, mirrored rather than doubled:
`onPath_le_limsup_integral_of_isUniformEquilibriumPayoff` is unconditional
— it is the *on-path* bound, not the deviation bound — and
`deviation_limsup_le_of_isUniformEquilibriumPayoff` is conditional on
`hconv` — it is the *deviation* bound, not the on-path bound. This is the
opposite pairing from the liminf game, not an extra free direction:

| Notion   | Deviation (upper bound on `E[·]`)  | On-path/delivery (lower bound)     |
|----------|-------------------------------------|-------------------------------------|
| liminf   | unconditional (Fatou)               | conditional on a.s. convergence     |
| limsup   | conditional on a.s. convergence     | unconditional (reverse Fatou)       |

Consequently `IsUniformEquilibriumPayoff` does **not** transfer to the
limsup-average notion in both directions for free: swapping the aggregation
from liminf to limsup only swaps *which* of the two directions is free: it
does not make both free at once. Each notion gets exactly one unconditional
half and one conditional half, and the two notions' free halves are duals
of each other under `A ↦ -A`.

## Main definitions and results

* `integral_liminf_le_of_bounded_of_eventually_le` — real Fatou for a
  uniformly bounded family, composed with an eventual expectation bound
* `le_integral_liminf_of_bounded_of_tendsto_ae_of_eventually_le` — the
  on-path converse, conditional on almost-sure convergence
* `liminf_neg_eq_neg_limsup` — negation exchanges `liminf` and `limsup`
  pointwise, unconditionally
* `le_integral_limsup_of_bounded_of_eventually_le` — the unconditional
  limsup dual of the deviation-direction Fatou lemma; the on-path bound in
  the limsup game
* `integral_limsup_le_of_bounded_of_tendsto_ae_of_eventually_le` — the
  limsup dual of the on-path lemma, conditional on almost-sure convergence;
  the deviation bound in the limsup game
* `StochasticGame.pathwiseAveragePayoff` — the finite-horizon average payoff
  realized pathwise along an infinite play
* `StochasticGame.integral_pathwiseAveragePayoff` — its expectation against
  `infinitePlayMeasure` is exactly `finiteAveragePayoff`
* `StochasticGame.deviation_liminf_le_of_isUniformEquilibriumPayoff` — the
  deviation direction instantiated against `IsUniformEquilibriumPayoff`,
  unconditionally (given a bound on stage payoffs)
* `StochasticGame.onPath_le_liminf_integral_of_isUniformEquilibriumPayoff` —
  the on-path direction instantiated against `IsUniformEquilibriumPayoff`,
  conditional on the same almost-sure convergence hypothesis as before
* `StochasticGame.onPath_le_limsup_integral_of_isUniformEquilibriumPayoff` —
  the on-path direction in the limsup game, unconditionally
* `StochasticGame.deviation_limsup_le_of_isUniformEquilibriumPayoff` — the
  deviation direction in the limsup game, conditional on almost-sure
  convergence of the deviation profile's own pathwise realization
-/

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace GameTheory

/-- **Negation exchanges `liminf` and `limsup` pointwise, unconditionally.**
No boundedness or convergence hypothesis is needed: `Real.sSup`/`Real.sInf`
already return the junk value `0` on unbounded or empty sets, consistently
with negation, so the identity holds for every `u` and every filter `f`.
This is the single fact that lets the limsup lemmas below be obtained from
the liminf ones by applying them to `-A`, rather than by re-deriving the
Fatou argument for the opposite sign. -/
theorem liminf_neg_eq_neg_limsup {β : Type*} (u : β → ℝ) (f : Filter β) :
    liminf (fun n => -u n) f = -limsup u f := by
  rw [liminf_eq, limsup_eq, ← Real.sSup_neg]
  congr 1
  ext a
  simp only [Set.mem_neg, Set.mem_setOf_eq, le_neg]

/-- **Real Fatou for a uniformly bounded family, composed with an eventual
expectation bound.** If `A : ℕ → Ω → ℝ` is uniformly bounded by `C` and its
expectation is eventually at most `bound`, then the expectation of its
pathwise `liminf` is at most `bound` too.

This is the deviation direction of the finite-horizon/liminf-average bridge:
Fatou gives `E[liminf A] ≤ liminf E[A]`, and `liminf E[A] ≤ bound` is
immediate from the eventual bound. -/
theorem integral_liminf_le_of_bounded_of_eventually_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A : ℕ → Ω → ℝ} {C bound : ℝ}
    (hmeas : ∀ n, Measurable (A n))
    (hbound : ∀ n ω, |A n ω| ≤ C)
    (hle : ∀ᶠ n in atTop, ∫ ω, A n ω ∂μ ≤ bound) :
    ∫ ω, liminf (fun n => A n ω) atTop ∂μ ≤ bound := by
  set L : Ω → ℝ := fun ω => liminf (fun n => A n ω) atTop with hLdef
  have hboundedBelow : ∀ ω, IsBoundedUnder (· ≥ ·) atTop (fun n => A n ω) :=
    fun ω => Filter.isBoundedUnder_of ⟨-C, fun n => (abs_le.mp (hbound n ω)).1⟩
  have hboundedAbove : ∀ ω, IsBoundedUnder (· ≤ ·) atTop (fun n => A n ω) :=
    fun ω => Filter.isBoundedUnder_of ⟨C, fun n => (abs_le.mp (hbound n ω)).2⟩
  have hcobddBelow : ∀ ω, IsCoboundedUnder (· ≥ ·) atTop (fun n => A n ω) :=
    fun ω => (hboundedAbove ω).isCoboundedUnder_flip
  have hLlow : ∀ ω, -C ≤ L ω := fun ω =>
    Filter.le_liminf_of_le (hcobddBelow ω)
      (Filter.Eventually.of_forall (fun n => (abs_le.mp (hbound n ω)).1))
  have hLup : ∀ ω, L ω ≤ C := fun ω =>
    Filter.liminf_le_of_frequently_le
      ((Filter.Eventually.of_forall (fun n => (abs_le.mp (hbound n ω)).2)).frequently)
      (hboundedBelow ω)
  have hLmeas : Measurable L := Measurable.liminf hmeas
  -- Pointwise: `ENNReal.ofReal ∘ (· + C)` commutes with `liminf`.
  have hpt : ∀ ω, ENNReal.ofReal (L ω + C) =
      liminf (fun n => ENNReal.ofReal (A n ω + C)) atTop := fun ω =>
    Monotone.map_liminf_of_continuousAt
      (f := fun x : ℝ => ENNReal.ofReal (x + C))
      (fun x y hxy => ENNReal.ofReal_le_ofReal (by linarith : x + C ≤ y + C))
      (fun n => A n ω)
      ((ENNReal.continuous_ofReal.comp (continuous_id.add continuous_const)).continuousAt)
      (hcobddBelow ω) (hboundedBelow ω)
  have hmeas_ofReal : ∀ n, Measurable (fun ω => ENNReal.ofReal (A n ω + C)) :=
    fun n => ENNReal.measurable_ofReal.comp ((hmeas n).add_const C)
  have hfatou :
      ∫⁻ ω, liminf (fun n => ENNReal.ofReal (A n ω + C)) atTop ∂μ ≤
        liminf (fun n => ∫⁻ ω, ENNReal.ofReal (A n ω + C) ∂μ) atTop :=
    lintegral_liminf_le hmeas_ofReal
  rw [← MeasureTheory.lintegral_congr hpt] at hfatou
  -- Convert the shifted `liminf`'s `lintegral` to a Bochner integral.
  have hLint : Integrable L μ :=
    MeasureTheory.Integrable.of_mem_Icc (-C) C hLmeas.aemeasurable
      (ae_of_all _ fun ω => ⟨hLlow ω, hLup ω⟩)
  have hLeq : ∫ ω, (L ω + C) ∂μ = (∫⁻ ω, ENNReal.ofReal (L ω + C) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun ω => show (0 : ℝ) ≤ L ω + C by linarith [hLlow ω])
      (hLmeas.add_const C).aestronglyMeasurable
  -- Convert each stage integral the same way.
  have hAn_int : ∀ n, Integrable (A n) μ := fun n =>
    MeasureTheory.Integrable.of_mem_Icc (-C) C (hmeas n).aemeasurable
      (ae_of_all _ fun ω => abs_le.mp (hbound n ω))
  have hstage : ∀ n, ∫⁻ ω, ENNReal.ofReal (A n ω + C) ∂μ =
      ENNReal.ofReal (∫ ω, A n ω ∂μ + C) := by
    intro n
    have hsum : ∫ ω, (A n ω + C) ∂μ = ∫ ω, A n ω ∂μ + C := by
      rw [integral_add (hAn_int n) (integrable_const C), integral_const]
      simp
    rw [← hsum]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      ((hAn_int n).add (integrable_const C))
      (ae_of_all _ fun ω => show (0 : ℝ) ≤ A n ω + C by
        have h := (abs_le.mp (hbound n ω)).1
        linarith)).symm
  obtain ⟨n₀, hn₀⟩ := hle.exists
  have hnorm : ‖∫ ω, A n₀ ω ∂μ‖ ≤ C := by
    have h := MeasureTheory.norm_integral_le_of_norm_le_const
      (μ := μ) (f := A n₀) (C := C)
      (ae_of_all μ fun ω => show ‖A n₀ ω‖ ≤ C by
        rw [Real.norm_eq_abs]; exact hbound n₀ ω)
    simpa using h
  have hlow0 : -C ≤ ∫ ω, A n₀ ω ∂μ := by
    have h := (abs_le.mp (by rwa [Real.norm_eq_abs] at hnorm)).1
    linarith
  have hboundC : 0 ≤ bound + C := by linarith [hlow0.trans hn₀]
  have hle' : ∀ᶠ n in atTop, ENNReal.ofReal (∫ ω, A n ω ∂μ + C) ≤
      ENNReal.ofReal (bound + C) := by
    filter_upwards [hle] with n hn
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hliminf_le :
      liminf (fun n => ∫⁻ ω, ENNReal.ofReal (A n ω + C) ∂μ) atTop ≤
        ENNReal.ofReal (bound + C) := by
    rw [show (fun n => ∫⁻ ω, ENNReal.ofReal (A n ω + C) ∂μ) =
        (fun n => ENNReal.ofReal (∫ ω, A n ω ∂μ + C)) from funext hstage]
    exact Filter.liminf_le_of_frequently_le hle'.frequently
  have hchain : ∫⁻ ω, ENNReal.ofReal (L ω + C) ∂μ ≤ ENNReal.ofReal (bound + C) :=
    hfatou.trans hliminf_le
  have hrealchain :
      (∫⁻ ω, ENNReal.ofReal (L ω + C) ∂μ).toReal ≤
        (ENNReal.ofReal (bound + C)).toReal :=
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hchain
  rw [ENNReal.toReal_ofReal hboundC, ← hLeq, integral_add hLint (integrable_const C),
    integral_const] at hrealchain
  simp only [MeasureTheory.probReal_univ, smul_eq_mul, one_mul] at hrealchain
  linarith

/-- **Reverse Fatou for a uniformly bounded family, composed with an eventual
expectation bound.** The dual of `integral_liminf_le_of_bounded_of_eventually_le`
under `A ↦ -A`. If `A : ℕ → Ω → ℝ` is uniformly bounded by `C` and its
expectation is eventually at least `bound`, then the expectation of its
pathwise `limsup` is at least `bound` too.

This is the on-path/delivery direction of the finite-horizon/limsup-average
bridge, and it is **unconditional**: no almost-sure-convergence hypothesis is
needed, unlike the liminf on-path direction
(`le_integral_liminf_of_bounded_of_tendsto_ae_of_eventually_le`). The proof is
exactly `integral_liminf_le_of_bounded_of_eventually_le` applied to `-A`,
translated by `liminf_neg_eq_neg_limsup` and `MeasureTheory.integral_neg`: the
`ENNReal.ofReal`/Fatou route inside that lemma is not touched. -/
theorem le_integral_limsup_of_bounded_of_eventually_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A : ℕ → Ω → ℝ} {C bound : ℝ}
    (hmeas : ∀ n, Measurable (A n))
    (hbound : ∀ n ω, |A n ω| ≤ C)
    (hle : ∀ᶠ n in atTop, bound ≤ ∫ ω, A n ω ∂μ) :
    bound ≤ ∫ ω, limsup (fun n => A n ω) atTop ∂μ := by
  have hkey := integral_liminf_le_of_bounded_of_eventually_le
    (A := fun n ω => -A n ω) (C := C) (bound := -bound)
    (fun n => (hmeas n).neg)
    (fun n ω => by simpa using hbound n ω)
    (by
      filter_upwards [hle] with n hn
      rw [MeasureTheory.integral_neg]
      linarith)
  have hfun : (fun ω => liminf (fun n => -A n ω) atTop) =
      fun ω => -limsup (fun n => A n ω) atTop :=
    funext fun ω => liminf_neg_eq_neg_limsup (fun n => A n ω) atTop
  rw [hfun, MeasureTheory.integral_neg] at hkey
  linarith

/-- **On-path direction, conditional on almost-sure convergence.** If
`A : ℕ → Ω → ℝ` is uniformly bounded, converges almost everywhere to `f`, and
its expectation is eventually at least `bound`, then the expectation of its
pathwise `liminf` is at least `bound` too.

The a.s.-convergence hypothesis is not free: without it the conclusion is
false (see the module docstring for the standard counterexample). It is
exactly what upgrades convergence of expectations, via dominated
convergence, to convergence of the integral of the a.e. limit — which
equals the integral of the `liminf` because a.e.-convergent sequences have
`liminf = lim` almost everywhere. -/
theorem le_integral_liminf_of_bounded_of_tendsto_ae_of_eventually_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A : ℕ → Ω → ℝ} {f : Ω → ℝ} {C bound : ℝ}
    (hmeas : ∀ n, Measurable (A n))
    (hbound : ∀ n ω, |A n ω| ≤ C)
    (hconv : ∀ᵐ ω ∂μ, Tendsto (fun n => A n ω) atTop (𝓝 (f ω)))
    (hle : ∀ᶠ n in atTop, bound ≤ ∫ ω, A n ω ∂μ) :
    bound ≤ ∫ ω, liminf (fun n => A n ω) atTop ∂μ := by
  have hliminf_eq : (fun ω => liminf (fun n => A n ω) atTop) =ᵐ[μ] f := by
    filter_upwards [hconv] with ω hω
    exact hω.liminf_eq
  have hdomconv : Tendsto (fun n => ∫ ω, A n ω ∂μ) atTop (𝓝 (∫ ω, f ω ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => C)
    · exact fun n => (hmeas n).aestronglyMeasurable
    · exact integrable_const C
    · exact fun n => ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]; exact hbound n ω
    · exact hconv
  have hle' : bound ≤ ∫ ω, f ω ∂μ := ge_of_tendsto hdomconv hle
  calc bound ≤ ∫ ω, f ω ∂μ := hle'
    _ = ∫ ω, liminf (fun n => A n ω) atTop ∂μ := (integral_congr_ae hliminf_eq).symm

/-- **Limsup bound, conditional on almost-sure convergence.** The dual of
`le_integral_liminf_of_bounded_of_tendsto_ae_of_eventually_le` under `A ↦ -A`.
If `A : ℕ → Ω → ℝ` is uniformly bounded, converges almost everywhere to `f`,
and its expectation is eventually at most `bound`, then the expectation of
its pathwise `limsup` is at most `bound` too.

Unlike `le_integral_limsup_of_bounded_of_eventually_le`, this direction is
**not** free: the a.s.-convergence hypothesis is not removed by the sign
flip, only relabeled to the opposite inequality (see the module docstring
for the dualized moving-bump counterexample). -/
theorem integral_limsup_le_of_bounded_of_tendsto_ae_of_eventually_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A : ℕ → Ω → ℝ} {f : Ω → ℝ} {C bound : ℝ}
    (hmeas : ∀ n, Measurable (A n))
    (hbound : ∀ n ω, |A n ω| ≤ C)
    (hconv : ∀ᵐ ω ∂μ, Tendsto (fun n => A n ω) atTop (𝓝 (f ω)))
    (hle : ∀ᶠ n in atTop, ∫ ω, A n ω ∂μ ≤ bound) :
    ∫ ω, limsup (fun n => A n ω) atTop ∂μ ≤ bound := by
  have hconv' : ∀ᵐ ω ∂μ, Tendsto (fun n => -A n ω) atTop (𝓝 (-f ω)) := by
    filter_upwards [hconv] with ω hω using hω.neg
  have hkey := le_integral_liminf_of_bounded_of_tendsto_ae_of_eventually_le
    (A := fun n ω => -A n ω) (f := fun ω => -f ω) (C := C) (bound := -bound)
    (fun n => (hmeas n).neg)
    (fun n ω => by simpa using hbound n ω)
    hconv'
    (by
      filter_upwards [hle] with n hn
      rw [MeasureTheory.integral_neg]
      linarith)
  have hfun : (fun ω => liminf (fun n => -A n ω) atTop) =
      fun ω => -limsup (fun n => A n ω) atTop :=
    funext fun ω => liminf_neg_eq_neg_limsup (fun n => A n ω) atTop
  rw [hfun, MeasureTheory.integral_neg] at hkey
  linarith

namespace StochasticGame

variable {ι : Type} (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [Fintype G.State]
  [DecidableEq G.State] [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

/-- **The finite-horizon average payoff, realized pathwise.** The same average
`finiteAveragePayoff` computes in expectation, evaluated along one realized
infinite play instead: this is the concrete process `A` that the abstract
bridge lemmas above are instantiated against, once `(Ω, μ)` is specialized to
`(G.Play, G.infinitePlayMeasure σ s₀)`. -/
noncomputable def pathwiseAveragePayoff (who : ι) (n : ℕ) (p : G.Play) : ℝ :=
  (n : ℝ)⁻¹ * G.totalPayoff who (G.histOfPlay n p)

omit [DecidableEq ι] [DecidableEq G.State] [∀ i, DecidableEq (G.Act i)] [Fintype ι]
  [Fintype G.State] [∀ i, Fintype (G.Act i)] in
/-- `pathwiseAveragePayoff` is measurable at every horizon: it factors through
the measurable map `histOfPlay n` into the finite (hence discrete-measurable)
type `Hist n`. Only finiteness (not the concrete `Fintype` data the
surrounding section otherwise needs) is required here. -/
theorem measurable_pathwiseAveragePayoff [Finite ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] (who : ι) (n : ℕ) :
    Measurable (G.pathwiseAveragePayoff who n) := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  haveI : Fintype G.State := Fintype.ofFinite G.State
  haveI : ∀ i, Fintype (G.Act i) := fun i => Fintype.ofFinite (G.Act i)
  have hg : Measurable (fun h : G.Hist n => (n : ℝ)⁻¹ * G.totalPayoff who h) :=
    Measurable.of_discrete
  exact hg.comp (G.measurable_histOfPlay n)

omit [Fintype ι] [DecidableEq ι] [Fintype G.State] [DecidableEq G.State]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)] in
/-- A bound on stage payoffs bounds `pathwiseAveragePayoff` uniformly, exactly
as it bounds `finiteAveragePayoff` (`abs_finiteAveragePayoff_le`) — the same
argument, applied pathwise instead of in expectation. -/
theorem abs_pathwiseAveragePayoff_le (who : ι) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ s a, |G.stagePayoff s a who| ≤ C) (n : ℕ) (p : G.Play) :
    |G.pathwiseAveragePayoff who n p| ≤ C := by
  unfold pathwiseAveragePayoff
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simpa using hC0
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hbd := G.abs_totalPayoff_le hC (G.histOfPlay n p)
    calc |(n : ℝ)⁻¹ * G.totalPayoff who (G.histOfPlay n p)|
        = (n : ℝ)⁻¹ * |G.totalPayoff who (G.histOfPlay n p)| := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ (n : ℝ)⁻¹ * (n * C) := mul_le_mul_of_nonneg_left hbd (by positivity)
      _ = C := by field_simp

omit [DecidableEq ι] [DecidableEq G.State] [∀ i, DecidableEq (G.Act i)] in
/-- **`pathwiseAveragePayoff` realizes `finiteAveragePayoff`.** Its expectation
against `infinitePlayMeasure` is exactly the finite-horizon average payoff,
at every horizon — this is the projection property
(`map_histOfPlay_infinitePlayMeasure`) transported through integration
(`integral_histOfPlay_infinitePlayMeasure`) and unfolded against
`finiteAveragePayoff`'s own definition. It is what makes the game-facing
corollaries below unconditional in their realization. -/
theorem integral_pathwiseAveragePayoff (σ : G.BehaviorProfile) (s₀ : G.State) (who : ι)
    (n : ℕ) :
    ∫ p, G.pathwiseAveragePayoff who n p ∂(G.infinitePlayMeasure σ s₀) =
      G.finiteAveragePayoff s₀ n σ who := by
  unfold pathwiseAveragePayoff
  rw [G.integral_histOfPlay_infinitePlayMeasure σ s₀ n
    (fun h => (n : ℝ)⁻¹ * G.totalPayoff who h), Math.Probability.expect_const_mul]
  rfl

omit [DecidableEq G.State] [∀ i, DecidableEq (G.Act i)] in
/-- The deviation direction of the finite-horizon/liminf-average bridge,
instantiated against `IsUniformEquilibriumPayoff`. `σ`, `T₀`, `hσ` are the
witnesses `IsUniformEquilibriumPayoff` supplies at accuracy `ε` (typically
obtained by the caller via `hv ε hε`). Given a uniform bound on stage
payoffs to `who` (`hC0`, `hC`), the liminf-average payoff of the deviation
profile `Function.update σ who dev`, realized pathwise on
`infinitePlayMeasure`, is capped by `v who + 2 * ε` — exactly as its
finite-horizon average is, and unconditionally: `infinitePlayMeasure`
supplies the pathwise realization. -/
theorem deviation_liminf_le_of_isUniformEquilibriumPayoff
    (s₀ : G.State) (v : Payoff ι) {ε : ℝ} {who : ι} (dev : G.BehaviorStrategy who)
    {σ : G.BehaviorProfile} {T₀ : ℕ}
    (hσ : ∀ T, T₀ ≤ T → G.IsεHorizonNash s₀ T ε σ ∧
      ∀ who', |G.finiteAveragePayoff s₀ T σ who' - v who'| ≤ ε)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ s a, |G.stagePayoff s a who| ≤ C) :
    ∫ p, liminf (fun n => G.pathwiseAveragePayoff who n p) atTop
      ∂(G.infinitePlayMeasure (Function.update σ who dev) s₀) ≤ v who + 2 * ε := by
  apply integral_liminf_le_of_bounded_of_eventually_le
    (G.measurable_pathwiseAveragePayoff who) (G.abs_pathwiseAveragePayoff_le who hC0 hC)
  filter_upwards [eventually_ge_atTop T₀] with T hT
  rw [G.integral_pathwiseAveragePayoff (Function.update σ who dev) s₀ who T]
  obtain ⟨hNash, hpin⟩ := hσ T hT
  have hdev := hNash who dev
  have hupper := (abs_le.mp (hpin who)).2
  linarith

omit [DecidableEq G.State] [∀ i, DecidableEq (G.Act i)] in
/-- The on-path direction of the finite-horizon/liminf-average bridge,
instantiated against `IsUniformEquilibriumPayoff`, conditional on the same
almost-sure convergence hypothesis as
`le_integral_liminf_of_bounded_of_tendsto_ae_of_eventually_le`. `σ`, `T₀`,
`hσ` are the witnesses `IsUniformEquilibriumPayoff` supplies at accuracy
`ε`. Given a uniform bound on stage payoffs (`hC0`, `hC`) and that `σ`'s own
pathwise averages on `infinitePlayMeasure` converge almost surely (`hconv`),
the liminf-average payoff of `σ` is at least `v who - ε`.

Unlike the deviation direction, `hconv` is a genuine extra mathematical
hypothesis, not just an infrastructure gap: `IsUniformEquilibriumPayoff`
alone pins expectations, and pinned expectations do not force a.s.
convergence (see the module docstring). The pathwise realization itself is
unconditional; `hconv` is not. -/
theorem onPath_le_liminf_integral_of_isUniformEquilibriumPayoff
    (s₀ : G.State) (v : Payoff ι) {ε : ℝ} (who : ι)
    {σ : G.BehaviorProfile} {T₀ : ℕ}
    (hσ : ∀ T, T₀ ≤ T → G.IsεHorizonNash s₀ T ε σ ∧
      ∀ who', |G.finiteAveragePayoff s₀ T σ who' - v who'| ≤ ε)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ s a, |G.stagePayoff s a who| ≤ C)
    {f : G.Play → ℝ}
    (hconv : ∀ᵐ p ∂(G.infinitePlayMeasure σ s₀),
      Tendsto (fun n => G.pathwiseAveragePayoff who n p) atTop (𝓝 (f p))) :
    v who - ε ≤ ∫ p, liminf (fun n => G.pathwiseAveragePayoff who n p) atTop
      ∂(G.infinitePlayMeasure σ s₀) := by
  apply le_integral_liminf_of_bounded_of_tendsto_ae_of_eventually_le
    (G.measurable_pathwiseAveragePayoff who) (G.abs_pathwiseAveragePayoff_le who hC0 hC) hconv
  filter_upwards [eventually_ge_atTop T₀] with T hT
  rw [G.integral_pathwiseAveragePayoff σ s₀ who T]
  have hlower := (abs_le.mp ((hσ T hT).2 who)).1
  linarith

omit [DecidableEq G.State] [∀ i, DecidableEq (G.Act i)] in
/-- The on-path direction of the finite-horizon/limsup-average bridge,
instantiated against `IsUniformEquilibriumPayoff`. The limsup-side twin of
`onPath_le_liminf_integral_of_isUniformEquilibriumPayoff`, obtained from
`le_integral_limsup_of_bounded_of_eventually_le` instead of its liminf
counterpart. `σ`, `T₀`, `hσ` are the witnesses `IsUniformEquilibriumPayoff`
supplies at accuracy `ε`. Given a uniform bound on stage payoffs (`hC0`,
`hC`), the limsup-average payoff of `σ`, realized pathwise on
`infinitePlayMeasure`, is at least `v who - ε`.

Unconditionally: unlike the liminf on-path bound, no almost-sure-convergence
hypothesis is needed here — this is the free half of the limsup game (see
the module docstring's asymmetry table). -/
theorem onPath_le_limsup_integral_of_isUniformEquilibriumPayoff
    (s₀ : G.State) (v : Payoff ι) {ε : ℝ} (who : ι)
    {σ : G.BehaviorProfile} {T₀ : ℕ}
    (hσ : ∀ T, T₀ ≤ T → G.IsεHorizonNash s₀ T ε σ ∧
      ∀ who', |G.finiteAveragePayoff s₀ T σ who' - v who'| ≤ ε)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ s a, |G.stagePayoff s a who| ≤ C) :
    v who - ε ≤ ∫ p, limsup (fun n => G.pathwiseAveragePayoff who n p) atTop
      ∂(G.infinitePlayMeasure σ s₀) := by
  apply le_integral_limsup_of_bounded_of_eventually_le
    (G.measurable_pathwiseAveragePayoff who) (G.abs_pathwiseAveragePayoff_le who hC0 hC)
  filter_upwards [eventually_ge_atTop T₀] with T hT
  rw [G.integral_pathwiseAveragePayoff σ s₀ who T]
  have hlower := (abs_le.mp ((hσ T hT).2 who)).1
  linarith

omit [DecidableEq G.State] [∀ i, DecidableEq (G.Act i)] in
/-- The deviation direction of the finite-horizon/limsup-average bridge,
instantiated against `IsUniformEquilibriumPayoff`. The limsup-side twin of
`deviation_liminf_le_of_isUniformEquilibriumPayoff`, obtained from
`integral_limsup_le_of_bounded_of_tendsto_ae_of_eventually_le` instead of its
liminf counterpart. `σ`, `T₀`, `hσ` are the witnesses `IsUniformEquilibriumPayoff`
supplies at accuracy `ε`. Given a uniform bound on stage payoffs to `who`
(`hC0`, `hC`) and that the deviation profile's own pathwise averages on
`infinitePlayMeasure` converge almost surely (`hconv`), the limsup-average
payoff of the deviation profile `Function.update σ who dev` is capped by
`v who + 2 * ε`.

Unlike the on-path direction above, `hconv` is a genuine extra mathematical
hypothesis here, not just an infrastructure gap: this is the *costly* half of
the limsup game, dual to the liminf game's costly (on-path) half — see the
module docstring's asymmetry table. Negating the moving-bump counterexample
shows `hconv` cannot be dropped. -/
theorem deviation_limsup_le_of_isUniformEquilibriumPayoff
    (s₀ : G.State) (v : Payoff ι) {ε : ℝ} {who : ι} (dev : G.BehaviorStrategy who)
    {σ : G.BehaviorProfile} {T₀ : ℕ}
    (hσ : ∀ T, T₀ ≤ T → G.IsεHorizonNash s₀ T ε σ ∧
      ∀ who', |G.finiteAveragePayoff s₀ T σ who' - v who'| ≤ ε)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ s a, |G.stagePayoff s a who| ≤ C)
    {f : G.Play → ℝ}
    (hconv : ∀ᵐ p ∂(G.infinitePlayMeasure (Function.update σ who dev) s₀),
      Tendsto (fun n => G.pathwiseAveragePayoff who n p) atTop (𝓝 (f p))) :
    ∫ p, limsup (fun n => G.pathwiseAveragePayoff who n p) atTop
      ∂(G.infinitePlayMeasure (Function.update σ who dev) s₀) ≤ v who + 2 * ε := by
  apply integral_limsup_le_of_bounded_of_tendsto_ae_of_eventually_le
    (G.measurable_pathwiseAveragePayoff who) (G.abs_pathwiseAveragePayoff_le who hC0 hC) hconv
  filter_upwards [eventually_ge_atTop T₀] with T hT
  rw [G.integral_pathwiseAveragePayoff (Function.update σ who dev) s₀ who T]
  obtain ⟨hNash, hpin⟩ := hσ T hT
  have hdev := hNash who dev
  have hupper := (abs_le.mp (hpin who)).2
  linarith

end StochasticGame

end GameTheory
