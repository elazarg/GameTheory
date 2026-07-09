/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Foundations.VNM.Basic

/-!
# GameTheory.Concepts.Foundations.VNM.AxiomIndependence

Axiom-independence examples for finite von Neumann-Morgenstern preferences.
-/

namespace GameTheory

namespace VNM

/-! ## Axiom Independence -/

namespace AxiomIndependence

private noncomputable def lottery3 (p0 p1 p2 : ℝ)
    (h0 : 0 ≤ p0) (h1 : 0 ≤ p1) (h2 : 0 ≤ p2)
    (hsum : p0 + p1 + p2 = 1) : Lottery (Fin 3) :=
  PMF.ofFintype
    (fun i : Fin 3 => ![ENNReal.ofReal p0, ENNReal.ofReal p1, ENNReal.ofReal p2] i)
    (by
      rw [Fin.sum_univ_three]
      calc
        ENNReal.ofReal p0 + ENNReal.ofReal p1 + ENNReal.ofReal p2
            = ENNReal.ofReal (p0 + p1) + ENNReal.ofReal p2 := by
              rw [ENNReal.ofReal_add h0 h1]
        _ = ENNReal.ofReal ((p0 + p1) + p2) := by
              rw [ENNReal.ofReal_add (add_nonneg h0 h1) h2]
        _ = 1 := by
              rw [show (p0 + p1) + p2 = 1 by linarith]
              simp)

@[simp] private theorem probOf_lottery3_zero (p0 p1 p2 : ℝ)
    (h0 : 0 ≤ p0) (h1 : 0 ≤ p1) (h2 : 0 ≤ p2)
    (hsum : p0 + p1 + p2 = 1) :
    probOf (0 : Fin 3) (lottery3 p0 p1 p2 h0 h1 h2 hsum) = p0 := by
  simp [probOf, lottery3, h0]

@[simp] private theorem probOf_lottery3_one (p0 p1 p2 : ℝ)
    (h0 : 0 ≤ p0) (h1 : 0 ≤ p1) (h2 : 0 ≤ p2)
    (hsum : p0 + p1 + p2 = 1) :
    probOf (1 : Fin 3) (lottery3 p0 p1 p2 h0 h1 h2 hsum) = p1 := by
  simp [probOf, lottery3, h1]

namespace NotComplete

private def pref (L M : Lottery (Fin 3)) : Prop :=
  probOf (0 : Fin 3) L = probOf (0 : Fin 3) M ∧
    probOf (1 : Fin 3) L ≥ probOf (1 : Fin 3) M

private theorem not_complete : ¬ Completeness pref := by
  intro h
  have hc := h (PMF.pure (0 : Fin 3)) (PMF.pure (1 : Fin 3))
  unfold pref at hc
  norm_num [probOf] at hc

private theorem transitive : Transitivity pref := by
  intro L M N hLM hMN
  exact ⟨hLM.1.trans hMN.1, le_trans hMN.2 hLM.2⟩

private theorem independent : Independence pref := by
  intro L M N t ht0 ht1
  unfold pref
  simp only [probOf_mix]
  constructor
  · intro h
    constructor <;> nlinarith [h.1, h.2, ht0]
  · intro h
    constructor <;> nlinarith [h.1, h.2, ht0]

private theorem continuous : Continuity pref := by
  intro L M N hLM hMN
  unfold pref at hLM hMN
  by_cases heq : probOf (1 : Fin 3) L = probOf (1 : Fin 3) N
  · refine ⟨0, by norm_num, by norm_num, ?_⟩
    have hM_eq_N : probOf (1 : Fin 3) M = probOf (1 : Fin 3) N := by
      exact le_antisymm (by linarith) hMN.2
    have h0_eq : probOf (0 : Fin 3) M =
        probOf (0 : Fin 3) (mix 0 (by norm_num) (by norm_num) L N) := by
      rw [probOf_mix]
      nlinarith [hMN.1]
    have h1_eq : probOf (1 : Fin 3) M =
        probOf (1 : Fin 3) (mix 0 (by norm_num) (by norm_num) L N) := by
      rw [probOf_mix]
      nlinarith [hM_eq_N]
    unfold indiff pref
    constructor <;> constructor <;> linarith
  · have hNL : probOf (1 : Fin 3) N < probOf (1 : Fin 3) L := by
      exact lt_of_le_of_ne (le_trans hMN.2 hLM.2) (Ne.symm heq)
    let t := (probOf (1 : Fin 3) M - probOf (1 : Fin 3) N) /
      (probOf (1 : Fin 3) L - probOf (1 : Fin 3) N)
    have hden_pos : 0 < probOf (1 : Fin 3) L - probOf (1 : Fin 3) N :=
      sub_pos.mpr hNL
    have ht0 : 0 ≤ t := by
      dsimp [t]
      exact div_nonneg (sub_nonneg.mpr hMN.2) (le_of_lt hden_pos)
    have ht1 : t ≤ 1 := by
      dsimp [t]
      rw [div_le_one hden_pos]
      linarith
    refine ⟨t, ht0, ht1, ?_⟩
    have h0_eq : probOf (0 : Fin 3) M =
        probOf (0 : Fin 3) (mix t ht0 ht1 L N) := by
      rw [probOf_mix]
      nlinarith [hLM.1, hMN.1]
    have h1_eq : probOf (1 : Fin 3) M =
        probOf (1 : Fin 3) (mix t ht0 ht1 L N) := by
      rw [probOf_mix]
      dsimp [t]
      field_simp [ne_of_gt hden_pos]
      ring
    unfold indiff pref
    constructor <;> constructor <;> linarith

theorem completeness_independent :
    ∃ pref : Lottery (Fin 3) → Lottery (Fin 3) → Prop,
      ¬ Completeness pref ∧ Transitivity pref ∧
      Independence pref ∧ Continuity pref :=
  ⟨pref, not_complete, transitive, independent, continuous⟩

end NotComplete

namespace NotContinuous

private def pref (L M : Lottery (Fin 3)) : Prop :=
  probOf (0 : Fin 3) L > probOf (0 : Fin 3) M ∨
    (probOf (0 : Fin 3) L = probOf (0 : Fin 3) M ∧
      probOf (1 : Fin 3) L ≥ probOf (1 : Fin 3) M)

private theorem complete : Completeness pref := by
  intro L M
  unfold pref
  rcases lt_trichotomy (probOf (0 : Fin 3) L) (probOf (0 : Fin 3) M) with h | h | h
  · right; left; exact h
  · rcases le_total (probOf (1 : Fin 3) M) (probOf (1 : Fin 3) L) with h1 | h1
    · left; right; exact ⟨h, h1⟩
    · right; right; exact ⟨h.symm, h1⟩
  · left; left; exact h

private theorem transitive : Transitivity pref := by
  intro L M N hLM hMN
  unfold pref at *
  rcases hLM with hLM | ⟨hLM0, hLM1⟩ <;>
    rcases hMN with hMN | ⟨hMN0, hMN1⟩
  · left; linarith
  · left; linarith
  · left; linarith
  · right; exact ⟨by linarith, by linarith⟩

private theorem independent : Independence pref := by
  intro L M N t ht0 ht1
  unfold pref
  simp only [probOf_mix]
  constructor
  · intro h
    rcases h with h | ⟨h0, h1⟩
    · left; nlinarith
    · right; constructor <;> nlinarith
  · intro h
    rcases h with h | ⟨h0, h1⟩
    · left; nlinarith
    · right; constructor <;> nlinarith

private theorem not_continuous : ¬ Continuity pref := by
  intro h
  let L0 : Lottery (Fin 3) := PMF.pure 0
  let L1 : Lottery (Fin 3) := PMF.pure 1
  let L2 : Lottery (Fin 3) := PMF.pure 2
  have h01 : pref L0 L1 := by
    unfold pref L0 L1
    left
    norm_num
  have h12 : pref L1 L2 := by
    unfold pref L1 L2
    right
    constructor <;> simp [probOf]
  obtain ⟨t, ht0, ht1, hindiff⟩ := h L0 L1 L2 h01 h12
  rcases hindiff with ⟨hleft, hright⟩
  unfold pref at hleft hright
  simp only [probOf_mix] at hleft hright
  unfold L0 L1 L2 at hleft hright
  have hleft' : 0 > t ∨ (0 = t ∧ 1 ≥ (0 : ℝ)) := by
    simpa [probOf] using hleft
  have hright' : t > 0 ∨ (t = 0 ∧ (0 : ℝ) ≥ 1) := by
    simpa [probOf] using hright
  rcases hright' with htpos | ⟨htzero, hbad⟩
  · rcases hleft' with hneg | ⟨hzero, _⟩ <;> linarith
  · linarith

theorem continuity_independent :
    ∃ pref : Lottery (Fin 3) → Lottery (Fin 3) → Prop,
      ¬ Continuity pref ∧ Completeness pref ∧
      Transitivity pref ∧ Independence pref :=
  ⟨pref, not_continuous, complete, transitive, independent⟩

end NotContinuous

namespace NotIndependent

private def pref (L M : Lottery (Fin 3)) : Prop :=
  probOf (0 : Fin 3) L ≥ 1 / 2 ∨ probOf (0 : Fin 3) M < 1 / 2

private theorem complete : Completeness pref := by
  intro L M
  unfold pref
  rcases le_or_gt (1 / 2 : ℝ) (probOf (0 : Fin 3) L) with h | h
  · left; left; exact h
  · right; right; exact h

private theorem transitive : Transitivity pref := by
  intro L M N hLM hMN
  unfold pref at *
  rcases hLM with hL | hM
  · left; exact hL
  · rcases hMN with hM' | hN
    · linarith
    · right; exact hN

private theorem not_independent : ¬ Independence pref := by
  intro h
  let L : Lottery (Fin 3) := lottery3 (2 / 5) (3 / 5) 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let M : Lottery (Fin 3) := lottery3 (3 / 5) (2 / 5) 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let N : Lottery (Fin 3) := lottery3 (4 / 5) (1 / 5) 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnot : ¬ pref L M := by
    unfold pref L M
    simp
    constructor <;> norm_num
  have hmix : pref (mix (1 / 2) (by norm_num) (by norm_num) L N)
      (mix (1 / 2) (by norm_num) (by norm_num) M N) := by
    unfold pref L M N
    simp only [probOf_mix]
    left
    norm_num
  exact hnot ((h L M N (1 / 2) (by norm_num) (by norm_num)).mpr hmix)

private theorem continuous : Continuity pref := by
  intro L M N hLM hMN
  rcases le_or_gt (1 / 2 : ℝ) (probOf (0 : Fin 3) M) with hMhigh | hMlow
  · have hLhigh : probOf (0 : Fin 3) L ≥ 1 / 2 := by
      unfold pref at hLM
      rcases hLM with h | h <;> linarith
    refine ⟨1, by norm_num, le_rfl, ?_⟩
    unfold indiff pref
    simp only [probOf_mix]
    constructor
    · left; nlinarith
    · left; nlinarith
  · have hNlow : probOf (0 : Fin 3) N < 1 / 2 := by
      unfold pref at hMN
      rcases hMN with h | h <;> linarith
    refine ⟨0, le_rfl, by norm_num, ?_⟩
    unfold indiff pref
    simp only [probOf_mix]
    constructor
    · right; nlinarith
    · right; nlinarith

theorem independence_independent :
    ∃ pref : Lottery (Fin 3) → Lottery (Fin 3) → Prop,
      ¬ Independence pref ∧ Completeness pref ∧
      Transitivity pref ∧ Continuity pref :=
  ⟨pref, not_independent, complete, transitive, continuous⟩

end NotIndependent

namespace NotTransitive

private def pref (L M : Lottery (Fin 3)) : Prop :=
  probOf (0 : Fin 3) L ≥ probOf (0 : Fin 3) M ∨
    probOf (1 : Fin 3) L ≥ probOf (1 : Fin 3) M

private theorem complete : Completeness pref := by
  intro L M
  unfold pref
  rcases le_total (probOf (0 : Fin 3) M) (probOf (0 : Fin 3) L) with h | h
  · left; left; exact h
  · right; left; exact h

private theorem not_transitive : ¬ Transitivity pref := by
  intro h
  let L : Lottery (Fin 3) := lottery3 (2 / 5) (1 / 10) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let M : Lottery (Fin 3) := lottery3 (3 / 10) (3 / 10) (2 / 5)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let N : Lottery (Fin 3) := lottery3 (1 / 2) (1 / 5) (3 / 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hLM : pref L M := by
    unfold pref L M
    left
    norm_num
  have hMN : pref M N := by
    unfold pref M N
    right
    norm_num
  have hLN := h L M N hLM hMN
  unfold pref at hLN
  dsimp only [L, M, N] at hLN
  rcases hLN with h0 | h1
  · norm_num at h0
  · norm_num at h1

private theorem independent : Independence pref := by
  intro L M N t ht0 ht1
  unfold pref
  simp only [probOf_mix]
  constructor
  · intro h
    rcases h with h | h
    · left; nlinarith
    · right; nlinarith
  · intro h
    rcases h with h | h
    · left; nlinarith
    · right; nlinarith

private theorem continuous : Continuity pref := by
  intro L M N hLM hMN
  by_cases hNM : pref N M
  · refine ⟨0, le_rfl, by norm_num, ?_⟩
    unfold indiff
    unfold pref
    simp only [probOf_mix]
    constructor
    · rcases hMN with h | h
      · left; nlinarith
      · right; nlinarith
    · rcases hNM with h | h
      · left; nlinarith
      · right; nlinarith
  · by_cases hML : pref M L
    · refine ⟨1, by norm_num, le_rfl, ?_⟩
      unfold indiff
      unfold pref
      simp only [probOf_mix]
      constructor
      · rcases hML with h | h
        · left; nlinarith
        · right; nlinarith
      · rcases hLM with h | h
        · left; nlinarith
        · right; nlinarith
    · unfold pref at hNM hML hLM hMN
      push Not at hNM hML
      obtain ⟨hNM0, hNM1⟩ := hNM
      obtain ⟨hML0, hML1⟩ := hML
      have hden_pos : 0 < probOf (0 : Fin 3) L - probOf (0 : Fin 3) N := by
        linarith
      have hnum_pos : 0 < probOf (0 : Fin 3) M - probOf (0 : Fin 3) N := by
        linarith
      have hnum_lt : probOf (0 : Fin 3) M - probOf (0 : Fin 3) N <
          probOf (0 : Fin 3) L - probOf (0 : Fin 3) N := by
        linarith
      set t := (probOf (0 : Fin 3) M - probOf (0 : Fin 3) N) /
        (probOf (0 : Fin 3) L - probOf (0 : Fin 3) N)
      have ht0 : 0 ≤ t := le_of_lt (div_pos hnum_pos hden_pos)
      have ht1 : t ≤ 1 := le_of_lt (by
        rw [div_lt_one hden_pos]
        exact hnum_lt)
      refine ⟨t, ht0, ht1, ?_⟩
      have ht_eq : t * probOf (0 : Fin 3) L + (1 - t) * probOf (0 : Fin 3) N =
          probOf (0 : Fin 3) M := by
        have hne : probOf (0 : Fin 3) L - probOf (0 : Fin 3) N ≠ 0 :=
          ne_of_gt hden_pos
        simp only [t]
        field_simp [hne]
        ring
      unfold indiff pref
      simp only [probOf_mix]
      constructor
      · left; linarith
      · left; linarith

theorem transitivity_independent :
    ∃ pref : Lottery (Fin 3) → Lottery (Fin 3) → Prop,
      ¬ Transitivity pref ∧ Completeness pref ∧
      Independence pref ∧ Continuity pref :=
  ⟨pref, not_transitive, complete, independent, continuous⟩

end NotTransitive

end AxiomIndependence

/-- Completeness is independent from transitivity, independence, and continuity
for preferences over three-outcome lotteries. -/
theorem completeness_independent :
    ∃ pref : Lottery (Fin 3) → Lottery (Fin 3) → Prop,
      ¬ Completeness pref ∧ Transitivity pref ∧
      Independence pref ∧ Continuity pref :=
  AxiomIndependence.NotComplete.completeness_independent

/-- Continuity is independent from completeness, transitivity, and independence
for preferences over three-outcome lotteries. -/
theorem continuity_independent :
    ∃ pref : Lottery (Fin 3) → Lottery (Fin 3) → Prop,
      ¬ Continuity pref ∧ Completeness pref ∧
      Transitivity pref ∧ Independence pref :=
  AxiomIndependence.NotContinuous.continuity_independent

/-- Independence is independent from completeness, transitivity, and continuity
for preferences over three-outcome lotteries. -/
theorem independence_independent :
    ∃ pref : Lottery (Fin 3) → Lottery (Fin 3) → Prop,
      ¬ Independence pref ∧ Completeness pref ∧
      Transitivity pref ∧ Continuity pref :=
  AxiomIndependence.NotIndependent.independence_independent

/-- Transitivity is independent from completeness, independence, and continuity
for preferences over three-outcome lotteries. -/
theorem transitivity_independent :
    ∃ pref : Lottery (Fin 3) → Lottery (Fin 3) → Prop,
      ¬ Transitivity pref ∧ Completeness pref ∧
      Independence pref ∧ Continuity pref :=
  AxiomIndependence.NotTransitive.transitivity_independent

/-- The four vNM preference axioms are independent: each can fail while the
other three hold for a preference relation over three-outcome lotteries. -/
theorem axioms_independent :
    (∃ pref : Lottery (Fin 3) → Lottery (Fin 3) → Prop,
      ¬ Completeness pref ∧ Transitivity pref ∧ Independence pref ∧ Continuity pref) ∧
    (∃ pref : Lottery (Fin 3) → Lottery (Fin 3) → Prop,
      ¬ Transitivity pref ∧ Completeness pref ∧ Independence pref ∧ Continuity pref) ∧
    (∃ pref : Lottery (Fin 3) → Lottery (Fin 3) → Prop,
      ¬ Independence pref ∧ Completeness pref ∧ Transitivity pref ∧ Continuity pref) ∧
    (∃ pref : Lottery (Fin 3) → Lottery (Fin 3) → Prop,
      ¬ Continuity pref ∧ Completeness pref ∧ Transitivity pref ∧ Independence pref) :=
  ⟨completeness_independent, transitivity_independent,
    independence_independent, continuity_independent⟩

end VNM

end GameTheory
