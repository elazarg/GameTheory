import GameTheory.Math.Probability.Support
import GameTheory.Math.Probability.Measure
import GameTheory.Math.Probability.Mixture
import GameTheory.Math.Probability.Joint
import Mathlib.Probability.ProbabilityMassFunction.Constructions

noncomputable section

open scoped BigOperators

namespace GameTheory.Math.Probability

/-- Filtering a point mass on an event containing its atom changes nothing. -/
theorem filter_pure_of_mem {α : Type*} (a : α) (event : Set α)
    (ha : a ∈ event)
    (h : ∃ b ∈ event, b ∈ (PMF.pure a).support) :
    (PMF.pure a).filter event h = PMF.pure a := by
  classical
  have hmass : (∑' b, event.indicator (PMF.pure a) b) = 1 := by
    rw [tsum_eq_single a]
    · simp [ha, PMF.pure_apply]
    · intro b hb
      simp [Set.indicator_apply, PMF.pure_apply, hb]
  ext b
  rw [PMF.filter_apply, hmass]
  by_cases hb : b = a <;> simp [PMF.pure_apply, ha, hb]

/-- An event already containing a PMF's support does not change that PMF. -/
theorem filter_of_support_subset {α : Type*} (μ : PMF α)
    (event : Set α) (h : ∃ a ∈ event, a ∈ μ.support)
    (hsub : μ.support ⊆ event) :
    μ.filter event h = μ := by
  classical
  have hmass : (∑' a, event.indicator μ a) = 1 := by
    calc
      (∑' a, event.indicator μ a) = ∑' a, μ a := by
        apply tsum_congr
        intro a
        by_cases ha : a ∈ μ.support
        · simp [hsub ha]
        · have hzero : μ a = 0 := not_ne_iff.mp ha
          simp [hzero]
      _ = 1 := μ.tsum_coe
  ext a
  rw [PMF.filter_apply, hmass]
  by_cases ha : a ∈ μ.support
  · simp [hsub ha]
  · have hzero : μ a = 0 := not_ne_iff.mp ha
    simp [hzero]

/-- A PMF with mass on both an atom and its complement is a strict mixture
of that atom and the law filtered on the complement. -/
theorem exists_mix_pure_filter {α : Type*}
    (μ : PMF α) (a : α) (ha : a ∈ μ.support)
    (hrest : ∃ b ∈ ({a}ᶜ : Set α), b ∈ μ.support) :
    ∃ (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1),
      μ = mix t ht0.le ht1.le (PMF.pure a) (μ.filter ({a}ᶜ) hrest) := by
  classical
  let q : ENNReal := ∑' b, ({a}ᶜ : Set α).indicator μ b
  have hsum : μ a + q = 1 := by
    rw [← μ.tsum_coe, ENNReal.tsum_eq_add_tsum_ite a]
    congr 1
    apply tsum_congr
    intro b
    by_cases hba : b = a <;> simp [hba, Set.indicator]
  have hμfin : μ a ≠ ⊤ := μ.apply_ne_top a
  have hqfin : q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (by
    calc q ≤ μ a + q := le_add_of_nonneg_left bot_le
      _ = 1 := hsum)
  have hqpos : 0 < q := by
    obtain ⟨b, hb, hbs⟩ := hrest
    have hbpos : 0 < ({a}ᶜ : Set α).indicator μ b := by
      simpa [Set.indicator, hb] using (μ.apply_pos_iff b).mpr hbs
    exact lt_of_lt_of_le hbpos (ENNReal.le_tsum b)
  let t := (μ a).toReal
  have ht0 : 0 < t :=
    ENNReal.toReal_pos ((μ.mem_support_iff a).mp ha) hμfin
  have ht1 : t < 1 := by
    have hlt : μ a < 1 := by
      have : μ a < μ a + q := ENNReal.lt_add_right hμfin hqpos.ne'
      simpa [hsum] using this
    exact (ENNReal.toReal_lt_toReal hμfin ENNReal.one_ne_top).mpr hlt
  refine ⟨t, ht0, ht1, ?_⟩
  ext b
  rw [mix_apply, PMF.filter_apply]
  have htreal : t + q.toReal = 1 := by
    have hr := congrArg ENNReal.toReal hsum
    simpa [ENNReal.toReal_add hμfin hqfin, t] using hr
  have hqreal : 1 - t = q.toReal := by linarith
  have htcoe : ENNReal.ofReal t = μ a := ENNReal.ofReal_toReal hμfin
  have hqcoe : ENNReal.ofReal (1 - t) = q := by
    rw [hqreal, ENNReal.ofReal_toReal hqfin]
  rw [htcoe, hqcoe]
  by_cases hba : b = a
  · subst b
    simp [q]
  · have hbmem : b ∈ ({a}ᶜ : Set α) := by simpa using hba
    simp only [Set.indicator_of_mem hbmem]
    simp only [PMF.pure_apply, ite_eq_right hba]
    simpa [q, mul_comm, mul_left_comm, mul_assoc] using
      (ENNReal.mul_inv_cancel_right (a := μ b) hqpos.ne' hqfin).symm

/-- Filtering first on an outer event and then on its subset agrees with
filtering directly on the smaller event. -/
theorem filter_filter_of_subset {α : Type*}
    (μ : PMF α) (outer inner : Set α)
    (houter : ∃ a ∈ outer, a ∈ μ.support)
    (hinner : ∃ a ∈ inner, a ∈ (μ.filter outer houter).support)
    (hsub : inner ⊆ outer) :
    (μ.filter outer houter).filter inner hinner =
      μ.filter inner (by
        obtain ⟨a, ha, hsupport⟩ := hinner
        exact ⟨a, ha,
          ((PMF.mem_support_filter_iff houter).mp hsupport).2⟩) := by
  let : MeasurableSpace α := ⊤
  have houterMeas : MeasurableSet outer := by trivial
  have hinnerMeas : MeasurableSet inner := by trivial
  apply PMF.toMeasure_injective
  rw [toMeasure_filter (μ.filter outer houter) inner hinnerMeas hinner,
    toMeasure_filter μ outer houterMeas houter,
    toMeasure_filter μ inner hinnerMeas]
  rw [ProbabilityTheory.cond_cond_eq_cond_inter houterMeas hinnerMeas]
  congr 1
  exact Set.inter_eq_right.mpr hsub

/-- Condition on the fiber of a map when its marginal has positive mass. -/
noncomputable def fiberPosterior {α β : Type*} (μ : PMF α)
    (f : α → β) (b : β) (hb : b ∈ (PMF.map f μ).support) : PMF α :=
  μ.filter {a | f a = b} (by classical
    by_contra h
    have hall : ∀ a, (if f a = b then μ a else 0) = 0 := by
      intro a
      by_cases hab : f a = b
      · have hnot : a ∉ μ.support := by
          intro hsup
          exact h ⟨a, hab, hsup⟩
        have hzero : μ a = 0 := not_ne_iff.mp
          (by simpa only [μ.mem_support_iff] using hnot)
        simp [hab, hzero]
      · simp [hab]
    have hall' : ∀ a, (if b = f a then μ a else 0) = 0 := by
      intro a
      by_cases hab : b = f a
      · simpa [hab, eq_comm] using hall a
      · simp [hab]
    have hzero : (∑' a, if b = f a then μ a else 0) = 0 :=
      ENNReal.tsum_eq_zero.mpr hall'
    have hq : (PMF.map f μ) b ≠ 0 :=
      ((PMF.map f μ).mem_support_iff b).mp hb
    rw [PMF.map_apply] at hq
    exact hq hzero)

theorem fiberPosterior_apply {α β : Type*} (μ : PMF α)
    (f : α → β) (b : β) (hb : b ∈ (PMF.map f μ).support) (a : α) :
    fiberPosterior μ f b hb a =
      {a | f a = b}.indicator μ a * ((PMF.map f μ) b)⁻¹ := by
  classical
  have hevent : (∑' x, {a | f a = b}.indicator μ x) =
      (PMF.map f μ) b := by
    rw [PMF.map_apply]
    refine tsum_congr fun x => ?_
    simp [Set.indicator, eq_comm]
  rw [fiberPosterior, PMF.filter_apply, hevent]

/-- The term marginal of a fiber posterior has the joint atom mass divided by
the conditioning marginal. -/
theorem fiberPosterior_map_snd_apply {α β : Type*}
    (joint : PMF (α × β)) (left : α)
    (hleft : left ∈ (joint.map Prod.fst).support) (right : β) :
    ((fiberPosterior joint Prod.fst left hleft).map Prod.snd) right =
      joint (left, right) * ((joint.map Prod.fst) left)⁻¹ := by
  classical
  rw [PMF.map_apply, tsum_eq_single (left, right)]
  · rw [fiberPosterior_apply]
    simp [Set.indicator]
  · intro pair hne
    rw [fiberPosterior_apply]
    by_cases hfst : pair.1 = left
    · have hsnd : pair.2 ≠ right := by
        intro heq
        exact hne (Prod.ext hfst heq)
      have hsnd' : right ≠ pair.2 := Ne.symm hsnd
      simp [hsnd']
    · simp [Set.indicator, hfst]

theorem fiberPosterior_support {α β : Type*} (μ : PMF α)
    (f : α → β) (b : β) (hb : b ∈ (PMF.map f μ).support) :
    (fiberPosterior μ f b hb).support = {a | f a = b} ∩ μ.support := by
  rw [fiberPosterior, PMF.support_filter]

/-- The fiber law represented on the actual subtype of the fiber. -/
noncomputable def fiberPosteriorSubtype {α β : Type*} (μ : PMF α)
    (f : α → β) (b : β) (hb : b ∈ (PMF.map f μ).support) :
    PMF {a // f a = b} :=
  (fiberPosterior μ f b hb).bindOnSupport fun a ha => by
    have hmem : a ∈ {x | f x = b} ∩ μ.support := by
      simpa only [fiberPosterior_support] using ha
    exact PMF.pure ⟨a, hmem.1⟩

/-- Projecting the subtype-valued posterior recovers the law on the carrier. -/
theorem fiberPosteriorSubtype_map_val {α β : Type*} (μ : PMF α)
    (f : α → β) (b : β) (hb : b ∈ (PMF.map f μ).support) :
    (fiberPosteriorSubtype μ f b hb).map Subtype.val =
      fiberPosterior μ f b hb := by
  simp only [fiberPosteriorSubtype, map_bindOnSupport, PMF.pure_map,
    PMF.bindOnSupport_pure]

/-- Disintegration holds on positive-mass fibers; outside a fiber the term is zero. -/
theorem fiberPosterior_disintegrate {α β : Type*} (μ : PMF α)
    (f : α → β) (b : β) (hb : b ∈ (PMF.map f μ).support) (a : α) :
    (PMF.map f μ) b * fiberPosterior μ f b hb a =
      {a | f a = b}.indicator μ a := by
  classical
  rw [fiberPosterior_apply]
  have hpos : (PMF.map f μ) b ≠ 0 :=
    ((PMF.map f μ).mem_support_iff b).mp hb
  have hfinite : (PMF.map f μ) b ≠ ⊤ := PMF.apply_ne_top _ _
  have hmass : (∑' x, if b = f x then μ x else 0) =
      (PMF.map f μ) b := by
    rw [PMF.map_apply]
  have hsum_pos : (∑' x, if b = f x then μ x else 0) ≠ 0 := by
    rw [hmass]
    exact hpos
  have hsum_finite : (∑' x, if b = f x then μ x else 0) ≠ ⊤ := by
    rw [hmass]
    exact hfinite
  by_cases hab : f a = b
  · rw [PMF.map_apply]
    simp [Set.indicator, hab]
    calc
      (∑' x, if b = f x then μ x else 0) *
          (μ a * (∑' x, if b = f x then μ x else 0)⁻¹) =
          μ a * ((∑' x, if b = f x then μ x else 0) *
            (∑' x, if b = f x then μ x else 0)⁻¹) := by ac_rfl
      _ = μ a := by
        rw [ENNReal.mul_inv_cancel hsum_pos hsum_finite, mul_one]
  · simp [Set.indicator, hab]

/-- Summing the fiber posteriors against the marginal reconstructs the law.
Only positive-mass fibers occur in the support-dependent continuation.
-/
theorem fiberPosterior_reconstruct {α β : Type*} (μ : PMF α)
    (f : α → β) :
    (PMF.map f μ).bindOnSupport
      (fun b hb => fiberPosterior μ f b hb) = μ := by
  classical
  ext a
  rw [PMF.bindOnSupport_apply]
  have hterms :
      (fun b => (PMF.map f μ) b *
        if h : (PMF.map f μ) b = 0 then 0
        else fiberPosterior μ f b
          (((PMF.map f μ).mem_support_iff b).mpr h) a) =
      (fun b => if b = f a then μ a else 0) := by
    funext b
    by_cases hz : (PMF.map f μ) b = 0
    · by_cases hba : b = f a
      · have hsum : (∑' x, if b = f x then μ x else 0) = 0 := by
          simpa only [PMF.map_apply] using hz
        have hpoint := ENNReal.tsum_eq_zero.mp hsum a
        have hzero : μ a = 0 := by
          simpa [hba, eq_comm] using hpoint.symm
        have htarget : (if b = f a then μ a else 0) = 0 := by
          simp [hba, hzero]
        rw [dite_eq_left hz]
        simp [htarget]
      · simp [hz, hba]
    · have hb : b ∈ (PMF.map f μ).support :=
        ((PMF.map f μ).mem_support_iff b).mpr hz
      rw [dite_eq_right hz]
      rw [fiberPosterior_disintegrate μ f b hb a]
      simp [Set.indicator, eq_comm]
  rw [hterms, tsum_eq_single (f a)]
  · simp
  · intro b hne
    simp [hne]

/-- Replacing continuations away from marginal support does not change
the reconstruction; the support-dependent domain contains only positive fibers.
-/
theorem fiberPosterior_reconstruct_irrelevant {α β : Type*} (μ : PMF α)
    (f : α → β) (g : ∀ b ∈ (PMF.map f μ).support, PMF α)
    (hagree : ∀ b hb, g b hb = fiberPosterior μ f b hb) :
    (PMF.map f μ).bindOnSupport g = μ := by
  rw [bindOnSupport_congr (PMF.map f μ) hagree]
  exact fiberPosterior_reconstruct μ f

end GameTheory.Math.Probability
