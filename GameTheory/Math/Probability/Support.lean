/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace GameTheory.Math.Probability

/-- A PMF has full support when every point is possible. -/
def FullSupport {α : Type*} (μ : PMF α) : Prop :=
  ∀ a, a ∈ μ.support

/-- A supported point gives positive mass to every event containing it. -/
theorem outerMeasure_pos_of_mem_support {α : Type*} {μ : PMF α}
    {event : Set α} (a : α) (ha : a ∈ event) (hsupport : a ∈ μ.support) :
    0 < μ.toOuterMeasure event := by
  apply pos_iff_ne_zero.mpr
  intro hzero
  rw [PMF.toOuterMeasure_apply_eq_zero_iff] at hzero
  exact (Set.disjoint_left.mp hzero hsupport ha)

/-- Every event has mass at most one under a PMF. -/
theorem outerMeasure_le_one {α : Type*} (μ : PMF α) (event : Set α) :
    μ.toOuterMeasure event ≤ 1 := by
  rw [PMF.toOuterMeasure_apply]
  calc
    ∑' a : α, event.indicator μ a ≤ ∑' a : α, μ a := by
      apply ENNReal.tsum_le_tsum
      intro a
      by_cases ha : a ∈ event <;> simp [Set.indicator, ha]
    _ = 1 := μ.tsum_coe

/-- Event mass under a PMF is finite. -/
theorem outerMeasure_ne_top {α : Type*} (μ : PMF α) (event : Set α) :
    μ.toOuterMeasure event ≠ ⊤ := by
  exact ne_of_lt (lt_of_le_of_lt (outerMeasure_le_one μ event)
    ENNReal.one_lt_top)

/-- Real event masses inherit monotonicity from a PMF outer measure. -/
theorem outerMeasure_toReal_mono {α : Type*} (μ : PMF α)
    {smaller larger : Set α} (hsubset : smaller ⊆ larger) :
    (μ.toOuterMeasure smaller).toReal ≤ (μ.toOuterMeasure larger).toReal := by
  apply ENNReal.toReal_mono (outerMeasure_ne_top μ larger)
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases hsmall : a ∈ smaller
  · simp [Set.indicator, hsmall, hsubset hsmall]
  · by_cases hlarge : a ∈ larger <;>
      simp [Set.indicator, hsmall, hlarge]

/-- A subevent of a PMF-null event has zero real mass. -/
theorem outerMeasure_toReal_eq_zero_of_subset {α : Type*} (μ : PMF α)
    {smaller larger : Set α} (hsubset : smaller ⊆ larger)
    (hzero : μ.toOuterMeasure larger = 0) :
    (μ.toOuterMeasure smaller).toReal = 0 := by
  have hsmall : μ.toOuterMeasure smaller = 0 := by
    rw [PMF.toOuterMeasure_apply_eq_zero_iff] at hzero ⊢
    exact hzero.mono_right hsubset
  simp [hsmall]

/-- Injective relabeling reflects equality of ordinary probability laws. -/
theorem pmf_map_injective {α β : Type*} {f : α → β}
    (hf : Function.Injective f) : Function.Injective (PMF.map f) := by
  intro first second hequal
  let : Nonempty α := ⟨first.support_nonempty.choose⟩
  have hback := congrArg (PMF.map (Function.invFun f)) hequal
  rw [PMF.map_comp, PMF.map_comp] at hback
  have hleft : Function.invFun f ∘ f = id := by
    funext value
    exact Function.leftInverse_invFun hf value
  simpa only [hleft, PMF.map_id] using hback

/-- An injective relabeling preserves each atom mass at its image. -/
theorem pmf_map_apply_of_injective {α β : Type*} (μ : PMF α)
    {f : α → β} (hf : Function.Injective f) (a : α) :
    (μ.map f) (f a) = μ a := by
  rw [PMF.map_apply, tsum_eq_single a]
  · simp
  · intro b hba
    have hne : f a ≠ f b := fun heq => hba (hf heq).symm
    simp [hne]

theorem pmf_eq_pure_of_support_subset_singleton {α : Type*}
    (μ : PMF α) (a : α) (h : μ.support ⊆ ({a} : Set α)) :
    μ = PMF.pure a := by
  have hs : μ.support = ({a} : Set α) := by
    apply Set.Subset.antisymm h
    obtain ⟨x, hx⟩ := μ.support_nonempty
    have hxa := Set.mem_singleton_iff.mp (h hx)
    rw [← hxa]
    exact Set.singleton_subset_iff.mpr hx
  apply PMF.ext
  intro x
  by_cases hxa : x = a
  · subst x
    simpa [PMF.pure_apply] using (μ.apply_eq_one_iff a).2 hs
  · simp only [PMF.pure_apply, hxa, ite_false]
    have hx : x ∉ μ.support := by
      intro hp
      exact hxa (Set.mem_singleton_iff.mp (h hp))
    exact μ.apply_eq_zero_iff x |>.2 hx

theorem eq_pure_of_subsingleton {α : Type*} [Subsingleton α]
    (μ : PMF α) (a : α) : μ = PMF.pure a := by
  have hsum : (∑' b, μ b) = μ a :=
    tsum_eq_single a (fun b hb => (hb (Subsingleton.elim b a)).elim)
  have hμ : μ a = 1 := hsum.symm.trans (PMF.tsum_coe μ)
  ext b
  have h : b = a := Subsingleton.elim b a
  subst b
  simp [hμ]

theorem bind_congr_on_support {α β : Type*} (μ : PMF α)
    {f g : α → PMF β} (hfg : ∀ a ∈ μ.support, f a = g a) :
    μ.bind f = μ.bind g := by
  ext b
  rw [PMF.bind_apply, PMF.bind_apply]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ μ.support
  · rw [hfg a ha]
  · have hzero : μ a = 0 := μ.apply_eq_zero_iff a |>.2 ha
    simp [hzero]

theorem bindOnSupport_congr {α β : Type*} (μ : PMF α)
    {f g : ∀ a ∈ μ.support, PMF β}
    (hfg : ∀ a ha, f a ha = g a ha) :
    μ.bindOnSupport f = μ.bindOnSupport g := by
  ext b
  rw [PMF.bindOnSupport_apply, PMF.bindOnSupport_apply]
  apply tsum_congr
  intro a
  by_cases hzero : μ a = 0
  · simp [hzero]
  · have ha : a ∈ μ.support := hzero
    simp only [hzero, ↓reduceDIte]
    rw [hfg a ha]

theorem bindOnSupport_eq_bind_of_eq_on_support {α β : Type*} (μ : PMF α)
    {f : ∀ a ∈ μ.support, PMF β} {g : α → PMF β}
    (hfg : ∀ a ha, f a ha = g a) :
    μ.bindOnSupport f = μ.bind g := by
  calc
    μ.bindOnSupport f = μ.bindOnSupport (fun a _ => g a) := by
      apply bindOnSupport_congr
      exact hfg
    _ = μ.bind g := PMF.bindOnSupport_eq_bind μ g

/-- Injectivity on the source support makes a support-indexed pure bind preserve
the point mass of every supported image. -/
theorem bindOnSupport_pure_apply_of_injective {α β : Type*} (μ : PMF α)
    (f : ∀ a ∈ μ.support, β)
    (hf : ∀ a ha b hb, f a ha = f b hb → a = b)
    (a : α) (ha : a ∈ μ.support) :
    (μ.bindOnSupport fun b hb => PMF.pure (f b hb)) (f a ha) = μ a := by
  classical
  obtain ⟨fallback, hfallback⟩ := μ.support_nonempty
  let total : α → β := fun b =>
    if hb : μ b ≠ 0 then f b ((PMF.mem_support_iff μ b).mpr hb)
    else f fallback hfallback
  have hmap : μ.bindOnSupport (fun b hb => PMF.pure (f b hb)) =
      PMF.map total μ := by
    calc
      μ.bindOnSupport (fun b hb => PMF.pure (f b hb)) =
          μ.bindOnSupport (fun b _ => PMF.pure (total b)) := by
        apply bindOnSupport_congr
        intro b hb
        have hnz : μ b ≠ 0 := (PMF.mem_support_iff μ b).mp hb
        simp only [total, dite_eq_left hnz]
      _ = μ.bind (fun b => PMF.pure (total b)) := PMF.bindOnSupport_eq_bind _ _
      _ = PMF.map total μ := PMF.bind_pure_comp _ _
  rw [hmap, PMF.map_apply, tsum_eq_single a]
  · have hnz : μ a ≠ 0 := (PMF.mem_support_iff μ a).mp ha
    simp only [total, dite_eq_left hnz]
    simp
  · intro b hba
    by_cases hnz : μ b ≠ 0
    · have hb : b ∈ μ.support := (PMF.mem_support_iff μ b).mpr hnz
      have hne : f a ha ≠ f b hb := fun heq => hba (hf a ha b hb heq).symm
      simp [total, hnz, hne]
    · have hzero : μ b = 0 := not_ne_iff.mp hnz
      simp [total, hzero]

theorem map_bindOnSupport {α β γ : Type*} (μ : PMF α)
    (f : ∀ a ∈ μ.support, PMF β) (g : β → γ) :
    (μ.bindOnSupport f).map g =
      μ.bindOnSupport (fun a ha => PMF.map g (f a ha)) := by
  calc
    (μ.bindOnSupport f).map g =
        (μ.bindOnSupport f).bindOnSupport (fun b _ => PMF.pure (g b)) := by
      rw [PMF.bindOnSupport_eq_bind, ← PMF.bind_pure_comp]
      rfl
    _ = μ.bindOnSupport (fun a ha =>
        (f a ha).bindOnSupport (fun b _ => PMF.pure (g b))) :=
      PMF.bindOnSupport_bindOnSupport μ f (fun b _ => PMF.pure (g b))
    _ = μ.bindOnSupport (fun a ha => PMF.map g (f a ha)) := by
      apply bindOnSupport_congr
      intro a ha
      rw [PMF.bindOnSupport_eq_bind, ← PMF.bind_pure_comp]
      rfl

theorem map_bindOnSupport_const {α β γ : Type*} {μ : PMF α}
    {f : ∀ a ∈ μ.support, PMF β} {ν : PMF γ} (g : β → γ)
    (h : ∀ a ha, PMF.map g (f a ha) = ν) :
    PMF.map g (μ.bindOnSupport f) = ν := by
  rw [map_bindOnSupport]
  rw [bindOnSupport_eq_bind_of_eq_on_support μ h]
  exact PMF.bind_const μ ν

theorem bindOnSupport_bind {α β γ : Type*} (μ : PMF α)
    (f : ∀ a ∈ μ.support, PMF β) (g : β → PMF γ) :
    (μ.bindOnSupport f).bind g =
      μ.bindOnSupport (fun a ha => (f a ha).bind g) := by
  calc
    (μ.bindOnSupport f).bind g =
        (μ.bindOnSupport f).bindOnSupport (fun b _ => g b) :=
      (PMF.bindOnSupport_eq_bind _ _).symm
    _ = μ.bindOnSupport (fun a ha =>
        (f a ha).bindOnSupport (fun b _ => g b)) :=
      PMF.bindOnSupport_bindOnSupport μ f (fun b _ => g b)
    _ = μ.bindOnSupport (fun a ha => (f a ha).bind g) := by
      apply bindOnSupport_congr
      intro a ha
      exact PMF.bindOnSupport_eq_bind _ _

theorem bind_bindOnSupport_comm {α β γ : Type*} (μ : PMF α) (ν : PMF β)
    (f : α → ∀ b ∈ ν.support, PMF γ) :
    μ.bind (fun a => ν.bindOnSupport (f a)) =
      ν.bindOnSupport (fun b hb => μ.bind (fun a => f a b hb)) := by
  calc
    μ.bind (fun a => ν.bindOnSupport (f a)) =
        μ.bindOnSupport (fun a _ => ν.bindOnSupport (f a)) :=
      (PMF.bindOnSupport_eq_bind μ _).symm
    _ = ν.bindOnSupport (fun b hb =>
        μ.bindOnSupport (fun a _ => f a b hb)) :=
      PMF.bindOnSupport_comm μ ν (fun a _ b hb => f a b hb)
    _ = ν.bindOnSupport (fun b hb => μ.bind (fun a => f a b hb)) := by
      apply bindOnSupport_congr
      intro b hb
      exact PMF.bindOnSupport_eq_bind μ _

end GameTheory.Math.Probability
