/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.BellmanGermFinkBridge
import Mathlib.Analysis.Analytic.Order

/-!
# Canonical first hierarchy datum of an analytic Bellman germ

Let `q` be the ramification exponent of an analytic Bellman germ and let
`V(t)` be its decoded value curve.  The average-reward relative-bias scale is

`((1 - t ^ q) / t ^ q) • (V(t) - V(0))`.

There is a canonical analytic-order dichotomy.  If `V(t) - V(0)` vanishes to
order at least `q`, the relative bias has an analytic extension through zero
and therefore a fixed limit `H`.  Otherwise the analytic order is a unique
natural number `n < q`, and the corresponding nonzero leading vector is the
next lower hierarchy coefficient.

This file performs only that standard analytic extraction.  Proving that a
lower-order coefficient forces a harmonic/rank response, and recursively
assembling those responses along public histories, belongs to the global
game-theoretic invariant.
-/

set_option autoImplicit false

noncomputable section

open Filter Set Topology

namespace GameTheory
namespace StochasticGame

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

namespace AnalyticBellmanGerm

/-- The decoded value curve carried by an analytic Bellman germ. -/
def valueCurve (germ : G.AnalyticBellmanGerm) :
    ℝ → G.State → Payoff ι :=
  fun t => G.bellmanDecodeValue (germ.assignment t)

/-- The endpoint value of the analytic Bellman germ. -/
def endpointValue (germ : G.AnalyticBellmanGerm) :
    G.State → Payoff ι :=
  germ.valueCurve 0

/-- The value increment relative to the endpoint. -/
def valueIncrement (germ : G.AnalyticBellmanGerm) :
    ℝ → G.State → Payoff ι :=
  fun t => germ.valueCurve t - germ.endpointValue

omit [DecidableEq G.State] in
theorem analytic_valueCurve (germ : G.AnalyticBellmanGerm) :
    AnalyticAt ℝ germ.valueCurve 0 := by
  rw [analyticAt_pi_iff]
  intro s
  rw [analyticAt_pi_iff]
  intro who
  exact germ.analytic_coordinate (BellmanVar.val s who)

omit [DecidableEq G.State] in
theorem analytic_valueIncrement (germ : G.AnalyticBellmanGerm) :
    AnalyticAt ℝ germ.valueIncrement 0 := by
  exact germ.analytic_valueCurve.sub analyticAt_const

omit [DecidableEq G.State] in
@[simp]
theorem valueIncrement_zero (germ : G.AnalyticBellmanGerm) :
    germ.valueIncrement 0 = 0 := by
  simp [valueIncrement, endpointValue]

/-- The raw relative-bias curve at the exact discount complement `t ^ q`.
It is used only away from `t = 0`. -/
def rawRelativeBiasCurve (germ : G.AnalyticBellmanGerm) :
    ℝ → G.State → Payoff ι :=
  fun t =>
    ((1 - t ^ germ.ramification) / t ^ germ.ramification) •
      germ.valueIncrement t

/-- Data certifying that the relative-bias curve extends analytically
through the singular discount endpoint. -/
structure FiniteBiasSeed (germ : G.AnalyticBellmanGerm) where
  factor : ℝ → G.State → Payoff ι
  analytic_factor : AnalyticAt ℝ factor 0
  valueIncrement_eq :
    ∀ᶠ t in 𝓝 0,
      germ.valueIncrement t = t ^ germ.ramification • factor t

namespace FiniteBiasSeed

/-- The analytic extension of the raw relative bias. -/
def extension {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed) :
    ℝ → G.State → Payoff ι :=
  fun t => (1 - t ^ germ.ramification) • seed.factor t

/-- The selected finite relative-bias coefficient. -/
def H {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed) :
    G.State → Payoff ι :=
  seed.extension 0

omit [DecidableEq G.State] in
theorem analytic_extension {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed) :
    AnalyticAt ℝ seed.extension 0 := by
  exact
    ((analyticAt_const.sub (analyticAt_id.pow germ.ramification)).smul
      seed.analytic_factor)

omit [DecidableEq G.State] in
theorem extension_zero {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed) :
    seed.extension 0 = seed.factor 0 := by
  have hq : germ.ramification ≠ 0 :=
    Nat.ne_of_gt germ.ramification_pos
  simp [extension, hq]

omit [DecidableEq G.State] in
theorem eventually_extension_eq_rawRelativeBiasCurve
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed) :
    ∀ᶠ t in nhdsWithin 0 ({0}ᶜ),
      seed.extension t = germ.rawRelativeBiasCurve t := by
  filter_upwards
      [seed.valueIncrement_eq.filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with t htFactor ht
  have ht_ne : t ≠ 0 := by simpa using ht
  have hpow_ne : t ^ germ.ramification ≠ 0 :=
    pow_ne_zero _ ht_ne
  rw [rawRelativeBiasCurve, htFactor, extension]
  simp only [smul_smul]
  congr 1
  field_simp

omit [DecidableEq G.State] in
theorem tendsto_rawRelativeBiasCurve
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed) :
    Tendsto germ.rawRelativeBiasCurve
      (nhdsWithin 0 ({0}ᶜ)) (nhds seed.H) := by
  exact Filter.Tendsto.congr'
    seed.eventually_extension_eq_rawRelativeBiasCurve
    seed.analytic_extension.continuousAt.continuousWithinAt

omit [DecidableEq G.State] in
/-- At every positive germ point, the finite-bias forcing either has a
Poisson correction `K`, or retains a nonzero harmonic obstruction.

This selects the second hierarchy coefficient exactly in the branch where
it exists.  The nonzero harmonic branch is intentionally returned to the
global rank/phase invariant rather than hidden as a failed linear solve. -/
theorem poissonCorrection_or_harmonicObstructionAt
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius) :
    (∃ K : G.State → Payoff ι,
      G.finkBellmanForcingVector germ.endpointValue seed.H
          (germ.finkPointAt ht) =
        -G.finkContinuationResidualVector K (germ.finkPointAt ht)) ∨
      ∃ O K : G.State → Payoff ι,
        G.finkContinuationResidualVector O (germ.finkPointAt ht) = 0 ∧
        O ≠ 0 ∧
        G.finkBellmanForcingVector germ.endpointValue seed.H
            (germ.finkPointAt ht) =
          O - G.finkContinuationResidualVector K (germ.finkPointAt ht) := by
  obtain ⟨O, K, hO, hforcing, _hcesaro⟩ :=
    G.exists_finkBellmanForcing_harmonicObstruction_decomposition
      (germ.finkPointAt ht) germ.endpointValue seed.H
  by_cases hOzero : O = 0
  · left
    refine ⟨-K, ?_⟩
    rw [hforcing, hOzero, zero_add,
      G.finkContinuationResidualVector_neg]
    simp
  · right
    refine ⟨O, -K, hO, hOzero, ?_⟩
    rw [hforcing, G.finkContinuationResidualVector_neg]
    abel

end FiniteBiasSeed

/-- A nonzero value jet appearing strictly below the discount scale. -/
structure LowerValueJet (germ : G.AnalyticBellmanGerm) where
  order : ℕ
  order_lt_ramification : order < germ.ramification
  factor : ℝ → G.State → Payoff ι
  analytic_factor : AnalyticAt ℝ factor 0
  leading_ne_zero : factor 0 ≠ 0
  valueIncrement_eq :
    ∀ᶠ t in 𝓝 0,
      germ.valueIncrement t = t ^ order • factor t

/-- Exact analytic-order condition for a finite relative bias. -/
def HasFiniteBiasOrder (germ : G.AnalyticBellmanGerm) : Prop :=
  (germ.ramification : ℕ∞) ≤ analyticOrderAt germ.valueIncrement 0

omit [DecidableEq G.State] in
/-- If the value increment vanishes to at least the discount order, its
relative bias has an analytic extension. -/
theorem finiteBiasSeed_of_hasFiniteBiasOrder
    (germ : G.AnalyticBellmanGerm)
    (horder : germ.HasFiniteBiasOrder) :
    Nonempty germ.FiniteBiasSeed := by
  obtain ⟨factor, hfactorAnalytic, hfactor⟩ :=
    (natCast_le_analyticOrderAt germ.analytic_valueIncrement).mp horder
  exact ⟨
    { factor := factor
      analytic_factor := hfactorAnalytic
      valueIncrement_eq := by
        simpa only [sub_zero] using hfactor }⟩

omit [DecidableEq G.State] in
/-- If finite relative bias fails, analytic order produces one unique
nonzero lower-order hierarchy jet. -/
theorem lowerValueJet_of_not_hasFiniteBiasOrder
    (germ : G.AnalyticBellmanGerm)
    (horder : ¬germ.HasFiniteBiasOrder) :
    Nonempty germ.LowerValueJet := by
  have hlt :
      analyticOrderAt germ.valueIncrement 0 <
        (germ.ramification : ℕ∞) :=
    lt_of_not_ge horder
  have hneTop :
      analyticOrderAt germ.valueIncrement 0 ≠ ⊤ := by
    exact ne_top_of_lt hlt
  obtain ⟨factor, hfactorAnalytic, hfactorZero, hfactor⟩ :=
    (germ.analytic_valueIncrement.analyticOrderAt_ne_top.mp hneTop)
  let order := analyticOrderNatAt germ.valueIncrement 0
  have horderCast :
      (order : ℕ∞) = analyticOrderAt germ.valueIncrement 0 := by
    exact Nat.cast_analyticOrderNatAt hneTop
  have horderLt : order < germ.ramification := by
    exact_mod_cast horderCast.symm ▸ hlt
  exact ⟨
    { order := order
      order_lt_ramification := horderLt
      factor := factor
      analytic_factor := hfactorAnalytic
      leading_ne_zero := hfactorZero
      valueIncrement_eq := by
        filter_upwards [hfactor] with t ht
        simpa only [order, sub_zero] using ht }⟩

omit [DecidableEq G.State] in
/-- Canonical first-level hierarchy extraction.

The first branch supplies a finite relative-bias coefficient `H`.  The
second branch supplies the unique nonzero value jet below the discount
scale. -/
theorem finiteBiasSeed_or_lowerValueJet
    (germ : G.AnalyticBellmanGerm) :
    Nonempty germ.FiniteBiasSeed ∨ Nonempty germ.LowerValueJet := by
  by_cases horder : germ.HasFiniteBiasOrder
  · exact Or.inl (germ.finiteBiasSeed_of_hasFiniteBiasOrder horder)
  · exact Or.inr (germ.lowerValueJet_of_not_hasFiniteBiasOrder horder)

omit [DecidableEq G.State] in
/-- On a positive Bellman-germ point, the raw value formula agrees with
Fink's relative bias around the endpoint value. -/
theorem finkRelativeBias_finkPointAt_eq_rawRelativeBiasCurve
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius) :
    G.finkRelativeBias
        (1 - t ^ germ.ramification)
        germ.endpointValue (germ.finkPointAt ht) =
      germ.rawRelativeBiasCurve t := by
  ext s who
  unfold finkRelativeBias rawRelativeBiasCurve valueIncrement
    valueCurve endpointValue
  rw [germ.finkValue_finkPointAt ht]
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  have hpow_ne : t ^ germ.ramification ≠ 0 :=
    pow_ne_zero _ (ne_of_gt ht.1)
  field_simp [hpow_ne]
  ring

end AnalyticBellmanGerm

end StochasticGame
end GameTheory
