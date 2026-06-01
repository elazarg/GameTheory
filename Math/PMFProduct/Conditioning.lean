/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Math.ProbabilityMassFunction
import Math.Reindex
import Math.PMFProduct.Bind

namespace Math
namespace PMFProduct

open scoped BigOperators
open Math.ProbabilityMassFunction

universe uι uA uα uβ uγ

set_option autoImplicit false


-- ============================================================================
-- Conditioning
-- ============================================================================

section Conditioning

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
variable {A : ι → Type uA}
variable {α : Type uα}

omit [DecidableEq ι] in
/-- The mass of the coordinate-lifted event under a product is the mass under the factor. -/
theorem pmfMass_pmfPi_coord
    [∀ i, Finite (A i)]
    (σ : ∀ i, PMF (A i)) (j : ι)
    (E : A j → Prop) :
    pmfMass (μ := pmfPi (A := A) σ) (fun s => E (s j))
      =
    pmfMass (μ := σ j) E := by
  calc
    pmfMass (μ := pmfPi (A := A) σ) (fun s => E (s j))
        = pmfMass (μ := pushforward (pmfPi (A := A) σ) (fun s => s j)) E :=
            (pmfMass_pushforward (pmfPi (A := A) σ) (fun s => s j) E).symm
    _ = pmfMass (μ := σ j) E := by rw [pmfPi_push_coord σ j]

omit [DecidableEq ι] in
open Classical in
/-- The mass of a coordinatewise conjunction under a product PMF factors as the
    product of the coordinate event masses. -/
theorem pmfMass_pmfPi_forall
    (σ : ∀ i, PMF (A i)) (E : ∀ i, A i → Prop) :
    pmfMass (μ := pmfPi (A := A) σ) (fun s => ∀ i, E i (s i)) =
      ∏ i, pmfMass (μ := σ i) (E i) := by
  classical
  simp only [pmfMass, pmfMask, pmfPi_apply]
  rw [← ENNReal_tsum_pi (g := fun i a => if E i a then σ i a else 0)]
  apply tsum_congr
  intro s
  by_cases hs : ∀ i, E i (s i)
  · simp [hs]
  · rw [if_neg hs]
    symm
    push Not at hs
    rcases hs with ⟨i, hi⟩
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- Conditioning a product PMF on a coordinate event updates only that coordinate's factor. -/
theorem pmfPi_cond_coord
    [∀ i, Finite (A i)]
    (σ : ∀ i, PMF (A i)) (j : ι)
    (E : A j → Prop)
    (hE : pmfMass (μ := σ j) E ≠ 0) :
    pmfCond (μ := pmfPi (A := A) σ) (fun s => E (s j))
      (by
        simpa [pmfMass_pmfPi_coord (A := A) (σ := σ) (j := j) (E := E)] using hE)
      =
    pmfPi (A := A) (Function.update σ j (pmfCond (μ := σ j) E hE)) := by
  classical
  ext s
  simp only [pmfCond_apply, pmfPi_apply, pmfMask, pmfMass_pmfPi_coord]
  -- Factor the RHS product at j
  rw [prod_factor_erase
    (fun i x => (Function.update σ j (pmfCond (μ := σ j) E hE)) i x) j s]
  -- The j-th factor
  have hj : (Function.update σ j (pmfCond (μ := σ j) E hE)) j (s j)
      = (if E (s j) then σ j (s j) else 0) / pmfMass (μ := σ j) E := by
    simp [Function.update, pmfCond_apply, pmfMask]
  rw [hj]
  -- The rest factors are unchanged
  have h_rest : (∏ i ∈ Finset.univ.erase j,
      (Function.update σ j (pmfCond (μ := σ j) E hE)) i (s i))
      = ∏ i ∈ Finset.univ.erase j, σ i (s i) := by
    apply Finset.prod_congr rfl; intro i hi
    simp [Function.update, Finset.ne_of_mem_erase hi]
  rw [h_rest, prod_factor_erase (fun i x => σ i x) j s]
  -- Now algebra: LHS = (if E then σj*rest else 0) / mass
  --              RHS = ((if E then σj else 0) / mass) * rest
  by_cases hE_s : E (s j)
  · simp only [hE_s, ↓reduceIte]
    -- σ j (s j) * rest / mass = (σ j (s j) / mass) * rest
    simp only [div_eq_mul_inv, mul_comm, mul_left_comm]
  · simp [hE_s]

omit [DecidableEq ι] in
/-- Conditioning on coordinate `j` does not change other coordinate marginals. -/
theorem pmfPi_cond_coord_push_other
    [∀ i, Finite (A i)]
    (σ : ∀ i, PMF (A i)) {j q : ι} (hq : q ≠ j)
    (E : A j → Prop)
    (hE : pmfMass (μ := σ j) E ≠ 0) :
    pushforward
      (pmfCond (μ := pmfPi (A := A) σ) (fun s => E (s j))
        (by simpa [pmfMass_pmfPi_coord (A := A) (σ := σ) (j := j) (E := E)] using hE))
      (fun s => s q)
      =
    σ q := by
  classical
  rw [pmfPi_cond_coord σ j E hE,
      pmfPi_push_coord (Function.update σ j (pmfCond (μ := σ j) E hE)) q]
  simp [Function.update, hq]

end Conditioning

-- ============================================================================
-- PMF disintegration
-- ============================================================================

section Disintegration

variable {α : Type*} {β : Type*} {γ : Type*}

/-- **Disintegration / law of total probability for PMF.bind.**
    Decompose `μ.bind g` by first projecting via `proj`, then conditioning on
    the projected value:
    `μ.bind g = (pushforward μ proj).bindOnSupport
        (fun b _ => (μ.filter {a | proj a = b} _).bind g)`.
    The normalisation constant in `PMF.filter` cancels against the pushforward
    weight, recovering the original `μ.bind g`. -/
theorem pmf_bind_disintegrate
    [Finite α] [Finite β]
    (μ : PMF α) (proj : α → β) (g : α → PMF γ) :
    μ.bind g =
    (pushforward μ proj).bindOnSupport (fun b hb =>
      (μ.filter {a | proj a = b} (pushforward_support_fibre μ proj b hb)).bind g) := by
  letI : Fintype α := Fintype.ofFinite α
  letI : Fintype β := Fintype.ofFinite β
  classical
  ext y
  let Z : β → ENNReal := fun b => ∑ a : α, if b = proj a then μ a else 0
  let W : β → ENNReal := fun b => ∑ a : α, if b = proj a then μ a * g a y else 0
  have hZ_push : ∀ b, Z b = (pushforward μ proj) b := by
    intro b
    change Z b = (μ.bind (fun a => PMF.pure (proj a))) b
    simp [Z, PMF.bind_apply, PMF.pure_apply]
  have hcond : ∀ b, (∀ i : α, b = proj i → μ i = 0) ↔ Z b = 0 := by
    intro b
    constructor
    · intro hb
      refine (Finset.sum_eq_zero_iff_of_nonneg ?_).2 ?_
      · intro a ha
        split_ifs <;> simp
      · intro a ha
        by_cases hba : b = proj a
        · simp [hba, hb a hba]
        · simp [hba]
    · intro hZ i hi
      have hle :
          (if b = proj i then μ i else 0) ≤ ∑ a : α, if b = proj a then μ a else 0 := by
        exact Finset.single_le_sum
          (s := Finset.univ) (f := fun a : α => if b = proj a then μ a else 0)
          (fun a _ => by simp) (Finset.mem_univ i)
      have hμle : μ i ≤ Z b := by simpa [Z, hi] using hle
      exact le_antisymm (by simpa [hZ] using hμle) bot_le
  have hterm :
      ∀ b,
        (if ∀ i : α, b = proj i → μ i = 0 then 0
          else Z b * ∑ a : α,
            ({a | proj a = b}.indicator (⇑μ) a) * (∑ a', ({a | proj a = b}.indicator (⇑μ) a'))⁻¹ *
              g a y)
          = W b := by
    intro b
    by_cases hzb : Z b = 0
    · have hb0 : ∀ i : α, b = proj i → μ i = 0 := (hcond b).2 hzb
      have hw0 : W b = 0 := by
        refine (Finset.sum_eq_zero_iff_of_nonneg ?_).2 ?_
        · intro a ha
          split_ifs <;> simp
        · intro a ha
          by_cases hba : b = proj a
          · simp [hba, hb0 a hba]
          · simp [hba]
      simp [hzb, hw0]
    · have hz_ne_top : Z b ≠ ⊤ := by
        exact ne_of_lt <| calc
          Z b = (pushforward μ proj) b := hZ_push b
          _ ≤ 1 := PMF.coe_le_one _ _
          _ < ⊤ := ENNReal.one_lt_top
      have hb0 : ¬ (∀ i : α, b = proj i → μ i = 0) := by
        exact mt (fun h => (hcond b).1 h) hzb
      have hsum_ind : (∑ a', ({a | proj a = b}.indicator (⇑μ) a')) = Z b := by
        simp [Z, Set.indicator, eq_comm]
      have hmulinv : Z b * (Z b)⁻¹ = 1 := ENNReal.mul_inv_cancel hzb hz_ne_top
      calc
        (if ∀ i : α, b = proj i → μ i = 0 then 0
          else Z b * ∑ a : α,
            ({a | proj a = b}.indicator (⇑μ) a) * (∑ a', ({a | proj a = b}.indicator (⇑μ) a'))⁻¹ *
              g a y)
            = Z b * ∑ a : α, ({a | proj a = b}.indicator (⇑μ) a) * (Z b)⁻¹ * g a y := by
                simp [hb0, hsum_ind]
        _ = ∑ a : α, if b = proj a then μ a * g a y else 0 := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro a ha
              by_cases hba : b = proj a
              · calc
                  Z b * ({a | proj a = b}.indicator (⇑μ) a * (Z b)⁻¹ * g a y)
                      = Z b * (μ a * (Z b)⁻¹ * g a y) := by simp [Set.indicator, hba]
                  _ = μ a * (Z b * ((Z b)⁻¹ * g a y)) := by ac_rfl
                  _ = μ a * ((Z b * (Z b)⁻¹) * g a y) := by ac_rfl
                  _ = μ a * (1 * g a y) := by rw [hmulinv]
                  _ = (if b = proj a then μ a * g a y else 0) := by simp [hba]
              · have hproj : proj a ≠ b := by
                  intro h
                  exact hba h.symm
                simp [hba, hproj]
        _ = W b := by
              simp [W]
  calc
    (μ.bind g) y = ∑ a : α, μ a * g a y := by simp [PMF.bind_apply, tsum_fintype]
    _ = ∑ b : β, W b := by
          calc
            (∑ a : α, μ a * g a y)
                = ∑ a : α, ∑ b : β, if b = proj a then μ a * g a y else 0 := by
                    refine Finset.sum_congr rfl ?_
                    intro a ha
                    simp
            _ = ∑ b : β, ∑ a : α, if b = proj a then μ a * g a y else 0 := by
                    simpa using (Finset.sum_comm :
                      (∑ a : α, ∑ b : β, if b = proj a then μ a * g a y else 0) =
                        ∑ b : β, ∑ a : α, if b = proj a then μ a * g a y else 0)
            _ = ∑ b : β, W b := by simp [W]
    _ = ((pushforward μ proj).bindOnSupport (fun b hb =>
          (μ.filter {a | proj a = b} (pushforward_support_fibre μ proj b hb)).bind g)) y := by
          rw [PMF.bindOnSupport_apply]
          simp only [PMF.bind_apply, PMF.filter_apply, tsum_fintype, dite_eq_ite, mul_ite, mul_zero]
          refine Finset.sum_congr rfl ?_
          intro b hb
          have hcond' :
              (∀ i : α, b = proj i → μ i = 0) ↔ (pushforward μ proj) b = 0 := by
            constructor
            · intro h
              simpa [hZ_push b] using (hcond b).1 h
            · intro h
              exact (hcond b).2 (by simpa [hZ_push b] using h)
          simpa [hZ_push b, hcond'] using (hterm b).symm

end Disintegration

end PMFProduct

end Math
