import GameTheory.Math.Probability.Conditioning
import GameTheory.Math.Probability.ExpectationBind
import GameTheory.Math.Probability.ExpectationAlgebra

noncomputable section

open scoped BigOperators

namespace GameTheory.Math.Probability

private def eventCode {α : Type*} (event : Set α) (a : α) : Bool :=
  by classical exact decide (a ∈ event)

private theorem eventMass_eq_indicator_tsum {α : Type*} (μ : PMF α)
    (event : Set α) :
    (PMF.map (eventCode event) μ) true =
      ∑' a, event.indicator μ a := by
  classical
  rw [PMF.map_apply]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ event <;> simp [eventCode, ha]

private theorem eventMass_le_one {α : Type*} (μ : PMF α)
    (event : Set α) : (PMF.map (eventCode event) μ) true ≤ 1 := by
  rw [eventMass_eq_indicator_tsum]
  calc
    (∑' a, event.indicator μ a) ≤ ∑' a, μ a :=
      ENNReal.tsum_le_tsum fun a => Set.indicator_le_self' (fun _ _ => bot_le) a
    _ = 1 := μ.tsum_coe

private theorem eventMass_ne_zero {α : Type*} (μ : PMF α)
    (event : Set α) (h : ∃ a ∈ event, a ∈ μ.support) :
    (PMF.map (eventCode event) μ) true ≠ 0 := by
  have hsupport : true ∈ (PMF.map (eventCode event) μ).support := by
    rw [PMF.support_map]
    obtain ⟨a, ha, hμ⟩ := h
    exact ⟨a, hμ, by simp [eventCode, ha]⟩
  exact ((PMF.map (eventCode event) μ).mem_support_iff true).mp hsupport

private theorem eventMass_top {α : Type*} (μ : PMF α)
    (event : Set α) : (PMF.map (eventCode event) μ) true ≠ ⊤ := by
  apply ne_of_lt
  exact (eventMass_le_one μ event).trans_lt ENNReal.one_lt_top

/-- Filtering a law preserves absolute integrability of every payoff that was
integrable under the original law. -/
theorem payoffIntegrable_filter {α : Type*} (μ : PMF α)
    (event : Set α) (h : ∃ a ∈ event, a ∈ μ.support) (f : α → ℝ)
    (hf : PayoffIntegrable μ f) :
    PayoffIntegrable (μ.filter event h) f := by
  classical
  let mass := (PMF.map (eventCode event) μ) true
  have hmass : mass = ∑' a, event.indicator μ a :=
    eventMass_eq_indicator_tsum μ event
  have hmass_pos : 0 < mass.toReal :=
    ENNReal.toReal_pos (eventMass_ne_zero μ event h)
      (eventMass_top μ event)
  have hrestricted : PayoffIntegrable μ (event.indicator f) :=
    payoffIntegrable_indicator event hf
  have hscale := hrestricted.mul_left mass.toReal⁻¹
  have hterms : ∀ a,
      (μ.filter event h a).toReal * |f a| =
        mass.toReal⁻¹ * ((μ a).toReal * |event.indicator f a|) := by
    intro a
    rw [PMF.filter_apply, ← hmass, ENNReal.toReal_mul,
      ENNReal.toReal_inv]
    by_cases ha : a ∈ event
    · simp [Set.indicator_of_mem ha, mul_assoc, mul_comm]
    · simp [Set.indicator_of_notMem ha, ENNReal.toReal_zero]
  unfold PayoffIntegrable at hscale ⊢
  exact hscale.congr fun a => (hterms a).symm

/-- Absolute integrability under a filtered law is exactly integrability of
the event-restricted payoff under the original law. -/
theorem payoffIntegrable_filter_iff {α : Type*} (μ : PMF α)
    (event : Set α) (h : ∃ a ∈ event, a ∈ μ.support) (f : α → ℝ) :
    PayoffIntegrable (μ.filter event h) f ↔
      PayoffIntegrable μ (event.indicator f) := by
  classical
  let mass := (PMF.map (eventCode event) μ) true
  have hmass : mass = ∑' a, event.indicator μ a :=
    eventMass_eq_indicator_tsum μ event
  have hmass_pos : 0 < mass.toReal :=
    ENNReal.toReal_pos (eventMass_ne_zero μ event h)
      (eventMass_top μ event)
  have hterms : ∀ a,
      (μ.filter event h a).toReal * |f a| =
        mass.toReal⁻¹ * ((μ a).toReal * |event.indicator f a|) := by
    intro a
    rw [PMF.filter_apply, ← hmass, ENNReal.toReal_mul,
      ENNReal.toReal_inv]
    by_cases ha : a ∈ event
    · simp [Set.indicator_of_mem ha, mul_assoc, mul_comm]
    · simp [Set.indicator_of_notMem ha, ENNReal.toReal_zero]
  have hinv : mass.toReal⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hmass_pos)
  unfold PayoffIntegrable
  constructor
  · intro hfilter
    have hscaled := hfilter.congr fun a => hterms a
    exact (summable_mul_left_iff hinv).mp hscaled
  · intro hrestricted
    have hscaled := (summable_mul_left_iff hinv).mpr hrestricted
    exact hscaled.congr fun a => (hterms a).symm

/-- Expectation under a filtered law is the event-restricted expectation,
divided by the event's probability. -/
theorem expect_filter {α : Type*} (μ : PMF α) (event : Set α)
    (h : ∃ a ∈ event, a ∈ μ.support) (f : α → ℝ)
    (hf : PayoffIntegrable μ (event.indicator f)) :
    expect (μ.filter event h) f
        (payoffIntegrable_filter_iff μ event h f |>.2 hf) =
      expect μ (event.indicator f) hf /
        (∑' a, event.indicator μ a).toReal := by
  classical
  let mass := (PMF.map (eventCode event) μ) true
  have hmass : mass = ∑' a, event.indicator μ a :=
    eventMass_eq_indicator_tsum μ event
  have hterms : ∀ a,
      (μ.filter event h a).toReal * f a =
        ((μ a).toReal * event.indicator f a) * mass.toReal⁻¹ := by
    intro a
    rw [PMF.filter_apply, ← hmass, ENNReal.toReal_mul,
      ENNReal.toReal_inv]
    by_cases ha : a ∈ event
    · simp [Set.indicator_of_mem ha, mul_assoc, mul_comm]
    · simp [Set.indicator_of_notMem ha, ENNReal.toReal_zero]
  unfold expect
  rw [div_eq_mul_inv, ← tsum_mul_right]
  apply tsum_congr
  intro a
  rw [← hmass]
  exact hterms a

/-- Restricting two globally compared payoffs to an event preserves their
comparison when they agree off the event on the original support. -/
theorem expect_indicator_le_of_expect_le_eq_off {α : Type*} (μ : PMF α)
    (event : Set α) (f g : α → ℝ)
    (hf : PayoffIntegrable μ f) (hg : PayoffIntegrable μ g)
    (hfg : ∀ a ∈ μ.support, a ∉ event → f a = g a)
    (hle : expect μ f hf ≤ expect μ g hg) :
    expect μ (event.indicator f) (payoffIntegrable_indicator event hf) ≤
      expect μ (event.indicator g) (payoffIntegrable_indicator event hg) := by
  let fpart := event.indicator f
  let gpart := event.indicator g
  have hfpart : PayoffIntegrable μ fpart := payoffIntegrable_indicator event hf
  have hgpart : PayoffIntegrable μ gpart := payoffIntegrable_indicator event hg
  have hdiff : ∀ a ∈ μ.support, f a - g a = fpart a - gpart a := by
    intro a haμ
    by_cases ha : a ∈ event
    · simp [fpart, gpart, Set.indicator_of_mem ha]
    · simp [fpart, gpart, Set.indicator_of_notMem ha, hfg a haμ ha]
  have hdiffValue : expect μ f hf - expect μ g hg =
      expect μ fpart hfpart - expect μ gpart hgpart := by
    calc
      _ = expect μ (fun a => f a - g a) (payoffIntegrable_sub hf hg) :=
        (expect_sub hf hg).symm
      _ = expect μ (fun a => fpart a - gpart a)
          (payoffIntegrable_sub hfpart hgpart) := by
            exact expect_congr_on_support hdiff
              (payoffIntegrable_sub hf hg) (payoffIntegrable_sub hfpart hgpart)
      _ = _ := expect_sub hfpart hgpart
  apply sub_nonpos.mp
  rw [← hdiffValue]
  exact sub_nonpos.mpr hle

/-- A global expectation comparison restricts to an event when the two
payoffs agree everywhere outside that event. -/
theorem expect_filter_le_of_expect_le_of_eq_off {α : Type*} (μ : PMF α)
    (event : Set α) (h : ∃ a ∈ event, a ∈ μ.support)
    (f g : α → ℝ) (hf : PayoffIntegrable μ f) (hg : PayoffIntegrable μ g)
    (hfg : ∀ a ∈ μ.support, a ∉ event → f a = g a)
    (hle : expect μ f hf ≤ expect μ g hg) :
    expect (μ.filter event h) f
      (payoffIntegrable_filter_iff μ event h f |>.2
        (payoffIntegrable_indicator event hf)) ≤
    expect (μ.filter event h) g
      (payoffIntegrable_filter_iff μ event h g |>.2
        (payoffIntegrable_indicator event hg)) := by
  classical
  let fpart := event.indicator f
  let gpart := event.indicator g
  have hfpart : PayoffIntegrable μ fpart := payoffIntegrable_indicator event hf
  have hgpart : PayoffIntegrable μ gpart := payoffIntegrable_indicator event hg
  have hdiff : ∀ a ∈ μ.support, f a - g a = fpart a - gpart a := by
    intro a haμ
    by_cases ha : a ∈ event
    · simp [fpart, gpart, Set.indicator_of_mem ha]
    · simp [fpart, gpart, Set.indicator_of_notMem ha, hfg a haμ ha]
  have hdiffValue : expect μ f hf - expect μ g hg =
      expect μ fpart hfpart - expect μ gpart hgpart := by
    calc
      _ = expect μ (fun a => f a - g a) (payoffIntegrable_sub hf hg) :=
        (expect_sub hf hg).symm
      _ = expect μ (fun a => fpart a - gpart a)
          (payoffIntegrable_sub hfpart hgpart) := by
            exact expect_congr_on_support hdiff
              (payoffIntegrable_sub hf hg) (payoffIntegrable_sub hfpart hgpart)
      _ = _ := expect_sub hfpart hgpart
  have hslice : expect μ fpart hfpart ≤ expect μ gpart hgpart := by
    apply sub_nonpos.mp
    rw [← hdiffValue]
    exact sub_nonpos.mpr hle
  have hmass_pos : 0 < (∑' a, event.indicator μ a).toReal := by
    have hm : (PMF.map (eventCode event) μ) true ≠ 0 :=
      eventMass_ne_zero μ event h
    have ht : (PMF.map (eventCode event) μ) true ≠ ⊤ :=
      eventMass_top μ event
    have hp : 0 < ((PMF.map (eventCode event) μ) true).toReal :=
      ENNReal.toReal_pos hm ht
    rw [eventMass_eq_indicator_tsum μ event] at hp
    exact hp
  rw [expect_filter μ event h f hfpart, expect_filter μ event h g hgpart]
  exact div_le_div_of_nonneg_right hslice (le_of_lt hmass_pos)

/-- A finite-valued observation partitions expectation into unnormalised
expectations on its fibers. -/
theorem expect_eq_sum_fibers {α κ : Type*} [Fintype κ] (μ : PMF α)
    (observation : α → κ) (f : α → ℝ) (hf : PayoffIntegrable μ f) :
    expect μ f hf =
      ∑ k, expect μ ((observation ⁻¹' {k}).indicator f)
        (payoffIntegrable_indicator (observation ⁻¹' {k}) hf) := by
  classical
  let pieces := fun k => (observation ⁻¹' {k}).indicator f
  have hpieces : ∀ k, PayoffIntegrable μ (pieces k) :=
    fun k => payoffIntegrable_indicator _ hf
  have hpoint : ∀ a, (∑ k, pieces k a) = f a := by
    intro a
    simp [pieces, Set.indicator_apply, Set.mem_preimage,
      Set.mem_singleton_iff]
  calc
    expect μ f hf =
        expect μ (fun a => ∑ k, pieces k a)
          (payoffIntegrable_sum μ pieces hpieces) := by
            exact expect_congr_on_support
              (fun a _ => (hpoint a).symm) hf
              (payoffIntegrable_sum μ pieces hpieces)
    _ = ∑ k, expect μ (pieces k) (hpieces k) :=
      expect_sum μ pieces hpieces

/-- Whole-law integrability supplies every positive-fiber posterior guard. -/
theorem payoffIntegrable_fiberPosterior {α κ : Type*} (μ : PMF α)
    (observation : α → κ) (f : α → ℝ)
    (hf : PayoffIntegrable μ f) (b : κ)
    (hb : b ∈ (PMF.map observation μ).support) :
    PayoffIntegrable (fiberPosterior μ observation b hb) f := by
  exact payoffIntegrable_bindOnSupport_conditional_on_support
    (PMF.map observation μ)
    (fun b hb => fiberPosterior μ observation b hb) f
    (payoffIntegrable_congr_law
      (fiberPosterior_reconstruct μ observation).symm hf) b hb

/-- A posterior expectation is the unnormalised fiber expectation divided by
the positive marginal mass. -/
theorem expect_fiberPosterior {α κ : Type*} (μ : PMF α)
    (observation : α → κ) (f : α → ℝ) (hf : PayoffIntegrable μ f)
    (b : κ) (hb : b ∈ (PMF.map observation μ).support) :
    expect (fiberPosterior μ observation b hb) f
        (payoffIntegrable_fiberPosterior μ observation f hf b hb) =
      expect μ ((observation ⁻¹' {b}).indicator f)
        (payoffIntegrable_indicator _ hf) /
        (∑' a, (observation ⁻¹' {b}).indicator μ a).toReal := by
  classical
  have hsupport : ∃ a ∈ observation ⁻¹' {b}, a ∈ μ.support := by
    rw [PMF.support_map] at hb
    obtain ⟨a, ha, hab⟩ := hb
    exact ⟨a, hab, ha⟩
  have hlaw : fiberPosterior μ observation b hb =
      μ.filter (observation ⁻¹' {b}) hsupport := by
    unfold fiberPosterior
    congr 1
  rw [expect_congr_law hlaw]
  exact expect_filter μ (observation ⁻¹' {b}) hsupport f
    (payoffIntegrable_indicator _ hf)

/-- Every supported observation fiber has positive real prior mass. -/
theorem fiberMass_toReal_pos {α κ : Type*} (μ : PMF α)
    (observation : α → κ) (b : κ)
    (hb : b ∈ (PMF.map observation μ).support) :
    0 < (∑' a, (observation ⁻¹' {b}).indicator μ a).toReal := by
  classical
  have hmass : ∑' a, (observation ⁻¹' {b}).indicator μ a =
      (PMF.map observation μ) b := by
    rw [PMF.map_apply]
    apply tsum_congr
    intro a
    by_cases hab : observation a = b
    · subst b
      simp [Set.indicator]
    · have hne : b ≠ observation a := Ne.symm hab
      simp [Set.indicator, hab, hne]
  apply ENNReal.toReal_pos
  · rw [hmass]
    exact ((PMF.map observation μ).mem_support_iff b).mp hb
  · rw [hmass]
    exact (PMF.map observation μ).apply_ne_top b

/-- Fiberwise conditional comparisons imply the unconditional comparison.
Only positive-mass observation fibers need conditional expectations. -/
theorem expect_fiberwise_le {α κ : Type*} (μ : PMF α)
    (observation : α → κ) (f g : α → ℝ)
    (hf : PayoffIntegrable μ f) (hg : PayoffIntegrable μ g)
    (hcond : ∀ b (hb : b ∈ (PMF.map observation μ).support),
      expect (fiberPosterior μ observation b hb) f
        (payoffIntegrable_fiberPosterior μ observation f hf b hb) ≤
      expect (fiberPosterior μ observation b hb) g
        (payoffIntegrable_fiberPosterior μ observation g hg b hb)) :
    expect μ f hf ≤ expect μ g hg := by
  classical
  let marginal := PMF.map observation μ
  let posterior := fun b hb => fiberPosterior μ observation b hb
  have hμf : PayoffIntegrable (marginal.bindOnSupport posterior) f :=
    payoffIntegrable_congr_law
      (fiberPosterior_reconstruct μ observation).symm hf
  have hμg : PayoffIntegrable (marginal.bindOnSupport posterior) g :=
    payoffIntegrable_congr_law
      (fiberPosterior_reconstruct μ observation).symm hg
  let vf : κ → ℝ := fun b =>
    if hb : b ∈ marginal.support then
      expect (posterior b hb) f
        (payoffIntegrable_bindOnSupport_conditional_on_support
          marginal posterior f hμf b hb)
    else 0
  let vg : κ → ℝ := fun b =>
    if hb : b ∈ marginal.support then
      expect (posterior b hb) g
        (payoffIntegrable_bindOnSupport_conditional_on_support
          marginal posterior g hμg b hb)
    else 0
  have hvf : PayoffIntegrable marginal vf :=
    payoffIntegrable_bindOnSupport_conditionalValue_on_support
      marginal posterior f hμf vf (by
        intro b hb
        have hmem : marginal b ≠ 0 := (marginal.mem_support_iff b).mp hb
        simp [vf, hmem])
  have hvg : PayoffIntegrable marginal vg :=
    payoffIntegrable_bindOnSupport_conditionalValue_on_support
      marginal posterior g hμg vg (by
        intro b hb
        have hmem : marginal b ≠ 0 := (marginal.mem_support_iff b).mp hb
        simp [vg, hmem])
  have htf := expect_bindOnSupport_tower_on_support
    marginal posterior f hμf vf (by
      intro b hb
      have hmem : marginal b ≠ 0 := (marginal.mem_support_iff b).mp hb
      simp [vf, hmem])
  have htg := expect_bindOnSupport_tower_on_support
    marginal posterior g hμg vg (by
      intro b hb
      have hmem : marginal b ≠ 0 := (marginal.mem_support_iff b).mp hb
      simp [vg, hmem])
  have hle : expect marginal vf hvf ≤ expect marginal vg hvg := by
    apply expect_mono _ hvf hvg
    intro b hb
    have hb' : b ∈ (PMF.map observation μ).support := by
      simpa only [marginal] using hb
    have hmem : marginal b ≠ 0 := (marginal.mem_support_iff b).mp hb
    have hvfb : vf b = expect (posterior b hb) f
        (payoffIntegrable_bindOnSupport_conditional_on_support
          marginal posterior f hμf b hb) := by
      simp [vf, hmem]
    have hcondb := hcond b hb'
    rw [hvfb]
    have hvgv : vg b = expect (posterior b hb) g
        (payoffIntegrable_bindOnSupport_conditional_on_support
          marginal posterior g hμg b hb) := by
      simp [vg, hmem]
    rw [hvgv]
    exact hcondb
  have hμf' := expect_congr_law
    (fiberPosterior_reconstruct μ observation) f hμf hf
  have hμg' := expect_congr_law
    (fiberPosterior_reconstruct μ observation) g hμg hg
  have htf' : expect (marginal.bindOnSupport posterior) f hμf =
      expect marginal vf hvf := by simpa only [marginal, posterior] using htf
  have htg' : expect (marginal.bindOnSupport posterior) g hμg =
      expect marginal vg hvg := by simpa only [marginal, posterior] using htg
  calc
    expect μ f hf = expect (marginal.bindOnSupport posterior) f hμf :=
      hμf'.symm
    _ = expect marginal vf hvf := htf'
    _ ≤ expect marginal vg hvg := hle
    _ = expect (marginal.bindOnSupport posterior) g hμg := htg'.symm
    _ = expect μ g hg := hμg'

theorem expect_bindOnSupport_le_of_le_of_eq_off
    {α β : Type*} (p : PMF α) (q₁ q₂ : ∀ a, a ∈ p.support → PMF β)
    (f : β → ℝ) (h₁ : PayoffIntegrable (p.bindOnSupport q₁) f)
    (h₂ : PayoffIntegrable (p.bindOnSupport q₂) f)
    (hle : expect (p.bindOnSupport q₂) f h₂ ≤
      expect (p.bindOnSupport q₁) f h₁)
    (a₀ : α) (ha₀ : a₀ ∈ p.support)
    (hoff : ∀ a, ∀ ha : a ∈ p.support, a ≠ a₀ → q₁ a ha = q₂ a ha) :
    expect (q₂ a₀ ha₀) f
        (payoffIntegrable_bindOnSupport_conditional_on_support p q₂ f h₂ a₀ ha₀) ≤
      expect (q₁ a₀ ha₀) f
        (payoffIntegrable_bindOnSupport_conditional_on_support p q₁ f h₁ a₀ ha₀) := by
  classical
  let v₁ : α → ℝ := extendFromSupport p (fun a ha =>
    expect (q₁ a ha) f
      (payoffIntegrable_bindOnSupport_conditional_on_support p q₁ f h₁ a ha))
  let v₂ : α → ℝ := extendFromSupport p (fun a ha =>
    expect (q₂ a ha) f
      (payoffIntegrable_bindOnSupport_conditional_on_support p q₂ f h₂ a ha))
  have hv₁ : ∀ a, ∀ ha : a ∈ p.support,
      v₁ a = expect (q₁ a ha) f
        (payoffIntegrable_bindOnSupport_conditional_on_support p q₁ f h₁ a ha) := by
    intro a ha
    have hne : p a ≠ 0 := (p.mem_support_iff a).mp ha
    simp [v₁, extendFromSupport, hne]
  have hv₂ : ∀ a, ∀ ha : a ∈ p.support,
      v₂ a = expect (q₂ a ha) f
        (payoffIntegrable_bindOnSupport_conditional_on_support p q₂ f h₂ a ha) := by
    intro a ha
    have hne : p a ≠ 0 := (p.mem_support_iff a).mp ha
    simp [v₂, extendFromSupport, hne]
  have ht₁ := expect_bindOnSupport_tower_on_support p q₁ f h₁ v₁ hv₁
  have ht₂ := expect_bindOnSupport_tower_on_support p q₂ f h₂ v₂ hv₂
  have houter : expect p v₂
      (payoffIntegrable_bindOnSupport_conditionalValue_on_support p q₂ f h₂
        v₂ hv₂) ≤
      expect p v₁
      (payoffIntegrable_bindOnSupport_conditionalValue_on_support p q₁ f h₁
        v₁ hv₁) := by
    calc
      _ = expect (p.bindOnSupport q₂) f h₂ := ht₂.symm
      _ ≤ expect (p.bindOnSupport q₁) f h₁ := hle
      _ = _ := ht₁
  have hoffValue : ∀ a ∈ p.support,
      a ∉ ({a₀} : Set α) → v₂ a = v₁ a := by
    intro a ha hnot
    have hne : a ≠ a₀ := by
      simpa only [Set.mem_singleton_iff] using hnot
    rw [hv₂ a ha, hv₁ a ha]
    exact (expect_congr_law (hoff a ha hne) f
      (payoffIntegrable_bindOnSupport_conditional_on_support p q₁ f h₁ a ha)
      (payoffIntegrable_bindOnSupport_conditional_on_support p q₂ f h₂ a ha)).symm
  have hfiltered := expect_filter_le_of_expect_le_of_eq_off p {a₀}
    ⟨a₀, Set.mem_singleton _, ha₀⟩ v₂ v₁
    (payoffIntegrable_bindOnSupport_conditionalValue_on_support p q₂ f h₂
      v₂ hv₂)
    (payoffIntegrable_bindOnSupport_conditionalValue_on_support p q₁ f h₁
      v₁ hv₁) hoffValue houter
  have hfilter : p.filter {a₀} ⟨a₀, Set.mem_singleton _, ha₀⟩ = PMF.pure a₀ := by
    ext a
    rw [PMF.filter_apply, PMF.pure_apply]
    by_cases ha : a = a₀
    · subst a
      have hmass : (∑' a, ({a₀} : Set α).indicator p a) = p a₀ := by
        rw [tsum_eq_single a₀]
        · simp [Set.mem_singleton_iff]
        · intro a ha
          have hne : a ≠ a₀ := ha
          simp [Set.indicator, hne]
      rw [hmass, Set.indicator_of_mem (Set.mem_singleton a₀)]
      calc
        p a₀ * (p a₀)⁻¹ = 1 := ENNReal.mul_inv_cancel
          ((p.mem_support_iff a₀).mp ha₀) (p.apply_ne_top a₀)
        _ = if a₀ = a₀ then 1 else 0 := by simp
    · simp [Set.indicator, ha]
  have hleft : expect (p.filter {a₀} ⟨a₀, Set.mem_singleton _, ha₀⟩) v₂
      (payoffIntegrable_filter_iff p {a₀}
        ⟨a₀, Set.mem_singleton _, ha₀⟩ v₂ |>.2
        (payoffIntegrable_indicator _
          (payoffIntegrable_bindOnSupport_conditionalValue_on_support
            p q₂ f h₂ v₂ hv₂))) = v₂ a₀ := by
    calc
      _ = expect (PMF.pure a₀) v₂ (payoffIntegrable_pure a₀ v₂) :=
        expect_congr_law hfilter v₂ _ _
      _ = v₂ a₀ := expect_pure a₀ v₂ _
  have hright : expect (p.filter {a₀} ⟨a₀, Set.mem_singleton _, ha₀⟩) v₁
      (payoffIntegrable_filter_iff p {a₀}
        ⟨a₀, Set.mem_singleton _, ha₀⟩ v₁ |>.2
        (payoffIntegrable_indicator _
          (payoffIntegrable_bindOnSupport_conditionalValue_on_support
            p q₁ f h₁ v₁ hv₁))) = v₁ a₀ := by
    calc
      _ = expect (PMF.pure a₀) v₁ (payoffIntegrable_pure a₀ v₁) :=
        expect_congr_law hfilter v₁ _ _
      _ = v₁ a₀ := expect_pure a₀ v₁ _
  rw [hleft, hright] at hfiltered
  rw [hv₂ a₀ ha₀, hv₁ a₀ ha₀] at hfiltered
  exact hfiltered


end GameTheory.Math.Probability
