/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Exact-power normalization of a positive analytic arc

This file isolates the analytic last step of sign-compatible curve
selection. If the first coordinate of an analytic arc vanishes at zero and
is positive immediately to the right, an orientation-preserving analytic
change of parameter makes that coordinate an exact positive integral power.
-/

noncomputable section

open Filter Set Topology

namespace Math

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Let `ell` be the first coordinate of an analytic arc and `u` its
remaining coordinates. If `ell 0 = 0` and `ell` is positive immediately to
the right of zero, then an analytic orientation-preserving local
reparameterization makes `ell` an exact power.

The returned map `u ∘ psi` is the normalized analytic arc. Positivity of
`psi` on the returned interval lets any property known for the original
positive half-arc be transported to the normalized arc. -/
theorem exists_analytic_reparam_firstCoordinate_eq_pow
    {ell : ℝ → ℝ} {u : ℝ → E}
    (hell : AnalyticAt ℝ ell 0)
    (hu : AnalyticAt ℝ u 0)
    (hell0 : ell 0 = 0)
    (hell_pos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < ell s) :
    ∃ (q : ℕ) (psi : ℝ → ℝ) (eta : ℝ),
      0 < q ∧
      0 < eta ∧
      AnalyticAt ℝ psi 0 ∧
      psi 0 = 0 ∧
      AnalyticAt ℝ (u ∘ psi) 0 ∧
      (u ∘ psi) 0 = u 0 ∧
      ∀ t ∈ Ioo (0 : ℝ) eta,
        0 < psi t ∧ ell (psi t) = t ^ q := by
  have hell_ne :
      ¬∀ᶠ s in 𝓝 (0 : ℝ), ell s = 0 := by
    intro hzero
    have hzero_right :
        ∀ᶠ s in 𝓝[>] (0 : ℝ), ell s = 0 :=
      hzero.filter_mono nhdsWithin_le_nhds
    have hfalse : ∀ᶠ _s in 𝓝[>] (0 : ℝ), False :=
      (hzero_right.and hell_pos).mono fun _s h =>
        (ne_of_gt h.2) h.1
    exact hfalse.exists.elim fun _s h => h
  obtain ⟨q, b, hb_analytic, hb_ne, hell_factor⟩ :=
    hell.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hell_ne
  have hq_pos : 0 < q := by
    by_contra hq
    have hq0 : q = 0 := Nat.eq_zero_of_not_pos hq
    subst q
    have hfactor0 := hell_factor.self_of_nhds
    apply hb_ne
    simpa [hell0] using hfactor0.symm
  have hb_pos_right : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < b s := by
    have hfactor_right :
        ∀ᶠ s in 𝓝[>] (0 : ℝ),
          ell s = (s - 0) ^ q • b s :=
      hell_factor.filter_mono nhdsWithin_le_nhds
    filter_upwards [hfactor_right, hell_pos, self_mem_nhdsWithin] with
      s hfactor hpos hs
    have hpos' : 0 < s ^ q * b s := by
      simpa [hfactor, smul_eq_mul] using hpos
    exact pos_of_mul_pos_right hpos' (pow_pos hs q).le
  have hb_nonneg : 0 ≤ b 0 := by
    exact ge_of_tendsto
      hb_analytic.continuousAt.continuousWithinAt
      (hb_pos_right.mono fun _ h => h.le)
  have hb_pos : 0 < b 0 :=
    lt_of_le_of_ne hb_nonneg (Ne.symm hb_ne)
  let root : ℝ → ℝ :=
    fun s => Real.exp (Real.log (b s) / (q : ℝ))
  have hroot_analytic : AnalyticAt ℝ root 0 := by
    exact (hb_analytic.log hb_pos).div_const.rexp'
  have hroot_pos : ∀ s, 0 < root s :=
    fun s => Real.exp_pos _
  have hb_pos_nhds : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < b s :=
    continuousAt_const.eventually_lt hb_analytic.continuousAt hb_pos
  have hroot_pow : ∀ᶠ s in 𝓝 (0 : ℝ), root s ^ q = b s := by
    filter_upwards [hb_pos_nhds] with s hs
    calc
      root s ^ q =
          Real.exp ((q : ℝ) * (Real.log (b s) / (q : ℝ))) := by
            rw [Real.exp_nat_mul]
      _ = Real.exp (Real.log (b s)) := by
            congr 1
            field_simp
      _ = b s := Real.exp_log hs
  let rho : ℝ → ℝ :=
    id * root
  have hrho_analytic : AnalyticAt ℝ rho 0 := by
    exact analyticAt_id.mul hroot_analytic
  have hrho0 : rho 0 = 0 := by
    simp [rho]
  have hrho_hasDeriv : HasDerivAt rho (root 0) 0 := by
    simpa [rho] using
      (hasDerivAt_id (𝕜 := ℝ) 0).mul
        hroot_analytic.hasStrictDerivAt.hasDerivAt
  have hrho_deriv : deriv rho 0 = root 0 :=
    hrho_hasDeriv.deriv
  have hrho_deriv_ne : deriv rho 0 ≠ 0 := by
    rw [hrho_deriv]
    exact (hroot_pos 0).ne'
  let psi : ℝ → ℝ :=
    hrho_analytic.hasStrictDerivAt.localInverse
      rho (deriv rho 0) 0 hrho_deriv_ne
  have hpsi_analytic : AnalyticAt ℝ psi 0 := by
    simpa [psi, hrho0] using
      hrho_analytic.analyticAt_localInverse hrho_deriv_ne
  have hpsi0 : psi 0 = 0 := by
    have himage : psi (rho 0) = 0 :=
      (hrho_analytic.hasStrictDerivAt.eventually_left_inverse
        hrho_deriv_ne).self_of_nhds
    simpa [hrho0] using himage
  have hrho_psi :
      ∀ᶠ t in 𝓝 (0 : ℝ), rho (psi t) = t := by
    simpa [psi, hrho0] using
      hrho_analytic.hasStrictDerivAt.eventually_right_inverse
        hrho_deriv_ne
  have hfactor_psi :
      ∀ᶠ t in 𝓝 (0 : ℝ),
        ell (psi t) = psi t ^ q * b (psi t) := by
    have hpsi_tendsto :
        Tendsto psi (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      have h := hpsi_analytic.continuousAt.tendsto
      rw [hpsi0] at h
      exact h
    have h := hpsi_tendsto.eventually hell_factor
    simpa only [sub_zero, smul_eq_mul] using h
  have hroot_pow_psi :
      ∀ᶠ t in 𝓝 (0 : ℝ), root (psi t) ^ q = b (psi t) := by
    have hpsi_tendsto :
        Tendsto psi (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      have h := hpsi_analytic.continuousAt.tendsto
      rw [hpsi0] at h
      exact h
    exact hpsi_tendsto.eventually hroot_pow
  have hexact :
      ∀ᶠ t in 𝓝 (0 : ℝ), ell (psi t) = t ^ q := by
    filter_upwards [hfactor_psi, hroot_pow_psi, hrho_psi] with
      t hfactor hroot hright
    calc
      ell (psi t) = psi t ^ q * b (psi t) := hfactor
      _ = psi t ^ q * root (psi t) ^ q := by rw [hroot]
      _ = (psi t * root (psi t)) ^ q := (mul_pow ..).symm
      _ = rho (psi t) ^ q := by rfl
      _ = t ^ q := by rw [hright]
  have hpsi_pos :
      ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < psi t := by
    have hright :
        ∀ᶠ t in 𝓝[>] (0 : ℝ), rho (psi t) = t :=
      hrho_psi.filter_mono nhdsWithin_le_nhds
    filter_upwards [hright, self_mem_nhdsWithin] with t hright ht
    have hrho_pos : 0 < rho (psi t) := by
      rw [hright]
      exact ht
    exact pos_of_mul_pos_left
      (show 0 < psi t * root (psi t) by simpa [rho] using hrho_pos)
      (hroot_pos (psi t)).le
  have hgood :
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        0 < psi t ∧ ell (psi t) = t ^ q :=
    hpsi_pos.and (hexact.filter_mono nhdsWithin_le_nhds)
  obtain ⟨eta, heta, hsubset⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp hgood
  have hcomp : AnalyticAt ℝ (u ∘ psi) 0 :=
    hu.comp_of_eq hpsi_analytic hpsi0
  refine ⟨q, psi, eta, hq_pos, heta, hpsi_analytic, hpsi0,
    hcomp, ?_, ?_⟩
  · simp [hpsi0]
  · intro t ht
    exact hsubset ht

/-- Exact-power normalization transports membership in an arbitrary set.

This is the curve-selection-facing form: once some analytic positive half-arc
in `A` has been constructed, no semialgebraic infrastructure is needed to
replace its first coordinate by `t ^ q`. -/
theorem exists_analytic_power_parameterization
    {A : Set (ℝ × E)} {ell : ℝ → ℝ} {u : ℝ → E}
    (hell : AnalyticAt ℝ ell 0)
    (hu : AnalyticAt ℝ u 0)
    (hell0 : ell 0 = 0)
    (hell_pos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < ell s)
    (harc : ∀ᶠ s in 𝓝[>] (0 : ℝ), (ell s, u s) ∈ A) :
    ∃ (q : ℕ) (gamma : ℝ → E) (eta : ℝ),
      0 < q ∧
      0 < eta ∧
      AnalyticAt ℝ gamma 0 ∧
      gamma 0 = u 0 ∧
      ∀ t ∈ Ioo (0 : ℝ) eta, (t ^ q, gamma t) ∈ A := by
  obtain ⟨q, psi, eta, hq, heta, hpsi_analytic, hpsi0,
      hgamma_analytic, hgamma0, hnormalize⟩ :=
    exists_analytic_reparam_firstCoordinate_eq_pow
      hell hu hell0 hell_pos
  have hnormalized :
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        0 < psi t ∧ ell (psi t) = t ^ q := by
    filter_upwards [Ioo_mem_nhdsGT heta] with t ht
    exact hnormalize t ht
  have hpsi_tendsto_nhds :
      Tendsto psi (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hfull :
        Tendsto psi (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      have h := hpsi_analytic.continuousAt.tendsto
      rw [hpsi0] at h
      exact h
    exact hfull.mono_left nhdsWithin_le_nhds
  have hpsi_tendsto :
      Tendsto psi (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hpsi_tendsto_nhds,
        hnormalized.mono fun _ h => h.1⟩
  have harc_psi :
      ∀ᶠ t in 𝓝[>] (0 : ℝ), (ell (psi t), u (psi t)) ∈ A :=
    hpsi_tendsto.eventually harc
  have hgood :
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        (t ^ q, (u ∘ psi) t) ∈ A := by
    filter_upwards [hnormalized, harc_psi] with t ht hmem
    simpa [Function.comp_apply, ← ht.2] using hmem
  obtain ⟨eta', heta', hsubset⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp hgood
  exact ⟨q, u ∘ psi, eta', hq, heta', hgamma_analytic,
    hgamma0, fun t ht => hsubset ht⟩

end Math
