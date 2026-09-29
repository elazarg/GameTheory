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

/-- Conditioning on an event rescales what remains of every other event. -/
theorem toOuterMeasure_filter_apply {α : Type*} (μ : PMF α) (s : Set α)
    (h : ∃ a ∈ s, a ∈ μ.support) (t : Set α) :
    (μ.filter s h).toOuterMeasure t = μ.toOuterMeasure (t ∩ s) / μ.toOuterMeasure s := by
  classical
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply,
    div_eq_mul_inv, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro a
  by_cases ht : a ∈ t <;> by_cases hs : a ∈ s <;> simp [Set.indicator, ht, hs, PMF.filter_apply]

/-- An event has positive mass exactly when it meets the support. -/
theorem toOuterMeasure_ne_zero_iff {α : Type*} (μ : PMF α) (s : Set α) :
    μ.toOuterMeasure s ≠ 0 ↔ ∃ a ∈ s, a ∈ μ.support := by
  rw [ne_eq, PMF.toOuterMeasure_apply_eq_zero_iff, Set.not_disjoint_iff]
  exact ⟨fun ⟨a, supported, member⟩ => ⟨a, member, supported⟩,
    fun ⟨a, member, supported⟩ => ⟨a, supported, member⟩⟩

/-- An event meeting the support has positive real mass. -/
theorem toOuterMeasure_toReal_pos {α : Type*} (μ : PMF α) {s : Set α}
    (meets : ∃ a ∈ s, a ∈ μ.support) : 0 < (μ.toOuterMeasure s).toReal :=
  ENNReal.toReal_pos ((toOuterMeasure_ne_zero_iff μ s).mpr meets) (outerMeasure_ne_top μ s)

open Classical in
/-- The real mass of a conditioned atom is its share of the event's mass. -/
theorem toReal_filter_apply {α : Type*} (μ : PMF α) (s : Set α) (h : ∃ a ∈ s, a ∈ μ.support)
    (a : α) :
    ((μ.filter s h) a).toReal =
      if a ∈ s then (μ a).toReal / (μ.toOuterMeasure s).toReal else 0 := by
  rw [PMF.filter_apply, ← PMF.toOuterMeasure_apply, ENNReal.toReal_mul, ENNReal.toReal_inv]
  by_cases member : a ∈ s
  · rw [Set.indicator_of_mem member, ite_eq_left member, div_eq_mul_inv]
  · rw [Set.indicator_of_notMem member, ite_eq_right member, ENNReal.toReal_zero, zero_mul]

/-- The law conditioned on the fiber of `f` over `b`. On a fiber of mass zero it
is the law itself, which no bind against the marginal of `f` ever consults. -/
noncomputable def fiberPosterior {α β : Type*} (μ : PMF α) (f : α → β) (b : β) : PMF α := by
  classical
  exact if meets : ∃ a ∈ {a | f a = b}, a ∈ μ.support then μ.filter {a | f a = b} meets else μ

/-- A value of positive marginal mass has a supported point in its fiber. -/
theorem exists_mem_fiber_of_mem_support_map {α β : Type*} {μ : PMF α} {f : α → β} {b : β}
    (hb : b ∈ (PMF.map f μ).support) : ∃ a ∈ {a | f a = b}, a ∈ μ.support := by
  obtain ⟨a, ha, rfl⟩ := (PMF.mem_support_map_iff f μ _).mp hb
  exact ⟨a, rfl, ha⟩

/-- A fiber meeting the support has positive marginal mass. -/
theorem mem_support_map_of_exists_mem_fiber {α β : Type*} {μ : PMF α} {f : α → β} {b : β}
    (meets : ∃ a ∈ {a | f a = b}, a ∈ μ.support) : b ∈ (PMF.map f μ).support := by
  obtain ⟨a, rfl, ha⟩ := meets
  exact (PMF.mem_support_map_iff f μ _).mpr ⟨a, ha, rfl⟩

theorem fiberPosterior_of_mem_support {α β : Type*} (μ : PMF α) (f : α → β) {b : β}
    (hb : b ∈ (PMF.map f μ).support) :
    fiberPosterior μ f b = μ.filter {a | f a = b} (exists_mem_fiber_of_mem_support_map hb) := by
  classical
  rw [fiberPosterior, dite_eq_left (exists_mem_fiber_of_mem_support_map hb)]

theorem fiberPosterior_of_not_mem_support {α β : Type*} (μ : PMF α) (f : α → β) {b : β}
    (hb : b ∉ (PMF.map f μ).support) : fiberPosterior μ f b = μ := by
  classical
  rw [fiberPosterior, dite_eq_right fun meets => hb (mem_support_map_of_exists_mem_fiber meets)]

theorem fiberPosterior_apply {α β : Type*} (μ : PMF α)
    (f : α → β) (b : β) (hb : b ∈ (PMF.map f μ).support) (a : α) :
    fiberPosterior μ f b a =
      {a | f a = b}.indicator μ a * ((PMF.map f μ) b)⁻¹ := by
  classical
  have hevent : (∑' x, {a | f a = b}.indicator μ x) =
      (PMF.map f μ) b := by
    rw [PMF.map_apply]
    refine tsum_congr fun x => ?_
    simp [Set.indicator, eq_comm]
  rw [fiberPosterior_of_mem_support μ f hb, PMF.filter_apply, hevent]

/-- The term marginal of a fiber posterior has the joint atom mass divided by
the conditioning marginal. -/
theorem fiberPosterior_map_snd_apply {α β : Type*}
    (joint : PMF (α × β)) (left : α)
    (hleft : left ∈ (joint.map Prod.fst).support) (right : β) :
    ((fiberPosterior joint Prod.fst left).map Prod.snd) right =
      joint (left, right) * ((joint.map Prod.fst) left)⁻¹ := by
  classical
  rw [PMF.map_apply, tsum_eq_single (left, right)]
  · rw [fiberPosterior_apply _ _ _ hleft]
    simp [Set.indicator]
  · intro pair hne
    rw [fiberPosterior_apply _ _ _ hleft]
    by_cases hfst : pair.1 = left
    · have hsnd : pair.2 ≠ right := by
        intro heq
        exact hne (Prod.ext hfst heq)
      have hsnd' : right ≠ pair.2 := Ne.symm hsnd
      simp [hsnd']
    · simp [Set.indicator, hfst]

theorem fiberPosterior_support {α β : Type*} (μ : PMF α)
    (f : α → β) (b : β) (hb : b ∈ (PMF.map f μ).support) :
    (fiberPosterior μ f b).support = {a | f a = b} ∩ μ.support := by
  rw [fiberPosterior_of_mem_support μ f hb, PMF.support_filter]

/-- A point of a conditional law on a fiber of positive mass lies in that
fiber and in the original support. -/
theorem mem_support_fiberPosterior {α β : Type*} {μ : PMF α} {f : α → β} {b : β}
    (hb : b ∈ (PMF.map f μ).support) {a : α} (ha : a ∈ (fiberPosterior μ f b).support) :
    f a = b ∧ a ∈ μ.support := by
  rw [fiberPosterior_support μ f b hb] at ha
  exact ha

/-- The fiber law represented on the actual subtype of the fiber. -/
noncomputable def fiberPosteriorSubtype {α β : Type*} (μ : PMF α)
    (f : α → β) (b : β) (hb : b ∈ (PMF.map f μ).support) :
    PMF {a // f a = b} :=
  (fiberPosterior μ f b).bindOnSupport fun a ha => by
    have hmem : a ∈ {x | f x = b} ∩ μ.support := by
      simpa only [fiberPosterior_support μ f b hb] using ha
    exact PMF.pure ⟨a, hmem.1⟩

/-- Projecting the subtype-valued posterior recovers the law on the carrier. -/
theorem fiberPosteriorSubtype_map_val {α β : Type*} (μ : PMF α)
    (f : α → β) (b : β) (hb : b ∈ (PMF.map f μ).support) :
    (fiberPosteriorSubtype μ f b hb).map Subtype.val = fiberPosterior μ f b := by
  simp only [fiberPosteriorSubtype, map_bindOnSupport, PMF.pure_map,
    PMF.bindOnSupport_pure]

/-- Disintegration holds on positive-mass fibers; outside a fiber the term is zero. -/
theorem fiberPosterior_disintegrate {α β : Type*} (μ : PMF α)
    (f : α → β) (b : β) (hb : b ∈ (PMF.map f μ).support) (a : α) :
    (PMF.map f μ) b * fiberPosterior μ f b a =
      {a | f a = b}.indicator μ a := by
  classical
  rw [fiberPosterior_apply μ f b hb]
  have hpos : (PMF.map f μ) b ≠ 0 :=
    ((PMF.map f μ).mem_support_iff b).mp hb
  have hfinite : (PMF.map f μ) b ≠ ⊤ := PMF.apply_ne_top _ _
  rw [mul_comm, mul_assoc, ENNReal.inv_mul_cancel hpos hfinite, mul_one]

/-- **Disintegration.** Drawing from a law is drawing the image of `f` and then
drawing from the conditional law of that image's fiber. -/
theorem fiberPosterior_reconstruct {α β : Type*} (μ : PMF α) (f : α → β) :
    (PMF.map f μ).bind (fiberPosterior μ f) = μ := by
  classical
  ext a
  rw [PMF.bind_apply, tsum_eq_single (f a)]
  · by_cases hz : (PMF.map f μ) (f a) = 0
    · have hzero : μ a = 0 := by
        have hsum := ENNReal.tsum_eq_zero.mp (show (∑' x, if f a = f x then μ x else 0) = 0 by
          simpa only [PMF.map_apply] using hz) a
        simpa using hsum
      rw [hz, zero_mul, hzero]
    · rw [fiberPosterior_disintegrate μ f (f a) (((PMF.map f μ).mem_support_iff _).mpr hz)]
      simp [Set.indicator]
  · intro b hne
    by_cases hz : (PMF.map f μ) b = 0
    · rw [hz, zero_mul]
    · rw [fiberPosterior_disintegrate μ f b (((PMF.map f μ).mem_support_iff _).mpr hz)]
      simp [Set.indicator, Ne.symm hne]

/-- Two observation maps conditioning the same supported points give the same
conditional law, including when neither event has mass. -/
theorem fiberPosterior_eq_of_support_fiber {α β γ : Type*} (μ : PMF α)
    (first : α → β) (second : α → γ) (left : β) (right : γ)
    (same : ∀ a ∈ μ.support, first a = left ↔ second a = right) :
    fiberPosterior μ first left = fiberPosterior μ second right := by
  classical
  by_cases meets : ∃ a ∈ {a | first a = left}, a ∈ μ.support
  · obtain ⟨witness, matched, supported⟩ := meets
    have meets : ∃ a ∈ {a | first a = left}, a ∈ μ.support := ⟨witness, matched, supported⟩
    have other : ∃ a ∈ {a | second a = right}, a ∈ μ.support :=
      ⟨witness, (same witness supported).mp matched, supported⟩
    rw [fiberPosterior, dite_eq_left meets, fiberPosterior, dite_eq_left other]
    have indicators : {a | first a = left}.indicator μ = {a | second a = right}.indicator μ := by
      funext a
      by_cases present : a ∈ μ.support
      · simp only [Set.indicator, Set.mem_ofPred_eq, same a present]
      · simp [Set.indicator, (PMF.apply_eq_zero_iff μ a).mpr present]
    ext a
    rw [PMF.filter_apply, PMF.filter_apply, indicators]
  · have other : ¬ ∃ a ∈ {a | second a = right}, a ∈ μ.support := by
      rintro ⟨a, matched, supported⟩
      exact meets ⟨a, (same a supported).mpr matched, supported⟩
    rw [fiberPosterior, dite_eq_right meets, fiberPosterior, dite_eq_right other]

/-- Sample the first coordinate, then the conditional second coordinate. The
conditional law is total, including first coordinates of zero probability. -/
theorem eq_bind_fst_fiberPosterior_snd {α β : Type*} (law : PMF (α × β)) :
    law = (law.map Prod.fst).bind fun first =>
      ((fiberPosterior law Prod.fst first).map Prod.snd).map
        (fun second => (first, second)) := by
  conv_lhs => rw [← fiberPosterior_reconstruct law Prod.fst]
  apply bind_congr_on_support
  intro first supported
  rw [PMF.map_comp]
  symm
  calc
    _ = (fiberPosterior law Prod.fst first).map id := by
      apply map_congr_on_support
      intro pair member
      exact Prod.ext (mem_support_fiberPosterior supported member).1.symm rfl
    _ = _ := PMF.map_id _

end GameTheory.Math.Probability
