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
    (h : ∃ a ∈ event, a ∈ μ.support) (f : α → ℝ) :
    expect (μ.filter event h) f =
      expect μ (event.indicator f) /
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
    (hle : expect μ f ≤ expect μ g) :
    expect μ (event.indicator f) ≤
      expect μ (event.indicator g) := by
  let fpart := event.indicator f
  let gpart := event.indicator g
  have hfpart : PayoffIntegrable μ fpart := payoffIntegrable_indicator event hf
  have hgpart : PayoffIntegrable μ gpart := payoffIntegrable_indicator event hg
  have hdiff : ∀ a ∈ μ.support, f a - g a = fpart a - gpart a := by
    intro a haμ
    by_cases ha : a ∈ event
    · simp [fpart, gpart, Set.indicator_of_mem ha]
    · simp [fpart, gpart, Set.indicator_of_notMem ha, hfg a haμ ha]
  have hdiffValue : expect μ f - expect μ g =
      expect μ fpart - expect μ gpart := by
    calc
      _ = expect μ (fun a => f a - g a) :=
        (expect_sub hf hg).symm
      _ = expect μ (fun a => fpart a - gpart a) := by
            exact expect_congr_on_support hdiff
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
    (hle : expect μ f ≤ expect μ g) :
    expect (μ.filter event h) f ≤
    expect (μ.filter event h) g := by
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
  have hdiffValue : expect μ f - expect μ g =
      expect μ fpart - expect μ gpart := by
    calc
      _ = expect μ (fun a => f a - g a) :=
        (expect_sub hf hg).symm
      _ = expect μ (fun a => fpart a - gpart a) := by
            exact expect_congr_on_support hdiff
      _ = _ := expect_sub hfpart hgpart
  have hslice : expect μ fpart ≤ expect μ gpart := by
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
  rw [expect_filter μ event h f, expect_filter μ event h g]
  exact div_le_div_of_nonneg_right hslice (le_of_lt hmass_pos)

/-- A finite-valued observation partitions expectation into unnormalised
expectations on its fibers. -/
theorem expect_eq_sum_fibers {α κ : Type*} [Fintype κ] (μ : PMF α)
    (observation : α → κ) (f : α → ℝ) (hf : PayoffIntegrable μ f) :
    expect μ f =
      ∑ k, expect μ ((observation ⁻¹' {k}).indicator f) := by
  classical
  let pieces := fun k => (observation ⁻¹' {k}).indicator f
  have hpieces : ∀ k, PayoffIntegrable μ (pieces k) :=
    fun k => payoffIntegrable_indicator _ hf
  have hpoint : ∀ a, (∑ k, pieces k a) = f a := by
    intro a
    simp [pieces, Set.indicator_apply, Set.mem_preimage,
      Set.mem_singleton_iff]
  calc
    expect μ f =
        expect μ (fun a => ∑ k, pieces k a) := by
            exact expect_congr_on_support
              (fun a _ => (hpoint a).symm)
    _ = ∑ k, expect μ (pieces k) :=
      expect_sum μ pieces hpieces

/-- Conditioning on a fiber keeps a payoff integrable: on a fiber of positive
mass it rescales the law, and on a null fiber it is the law itself. -/
theorem payoffIntegrable_fiberPosterior {α κ : Type*} (μ : PMF α)
    (observation : α → κ) (f : α → ℝ)
    (hf : PayoffIntegrable μ f) (b : κ) :
    PayoffIntegrable (fiberPosterior μ observation b) f := by
  by_cases hb : b ∈ (PMF.map observation μ).support
  · exact payoffIntegrable_bind_conditional_on_support (PMF.map observation μ)
      (fiberPosterior μ observation) f
      (payoffIntegrable_congr_law (fiberPosterior_reconstruct μ observation).symm hf) b hb
  · rwa [fiberPosterior_of_not_mem_support μ observation hb]

/-- A posterior expectation is the unnormalised fiber expectation divided by
the positive marginal mass. -/
theorem expect_fiberPosterior {α κ : Type*} (μ : PMF α)
    (observation : α → κ) (f : α → ℝ)
    (b : κ) (hb : b ∈ (PMF.map observation μ).support) :
    expect (fiberPosterior μ observation b) f =
      expect μ ((observation ⁻¹' {b}).indicator f) /
        (∑' a, (observation ⁻¹' {b}).indicator μ a).toReal := by
  classical
  have hsupport : ∃ a ∈ observation ⁻¹' {b}, a ∈ μ.support :=
    exists_mem_fiber_of_mem_support_map hb
  have hlaw : fiberPosterior μ observation b =
      μ.filter (observation ⁻¹' {b}) hsupport :=
    fiberPosterior_of_mem_support μ observation hb
  rw [expect_congr_law hlaw]
  exact expect_filter μ (observation ⁻¹' {b}) hsupport f

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
    (hcond : ∀ b (_ : b ∈ (PMF.map observation μ).support),
      expect (fiberPosterior μ observation b) f ≤
      expect (fiberPosterior μ observation b) g) :
    expect μ f ≤ expect μ g := by
  have hbind (h : α → ℝ) (hh : PayoffIntegrable μ h) :
      PayoffIntegrable ((PMF.map observation μ).bind (fiberPosterior μ observation)) h :=
    payoffIntegrable_congr_law (fiberPosterior_reconstruct μ observation).symm hh
  have htower (h : α → ℝ) (hh : PayoffIntegrable μ h) :
      expect μ h = expect (PMF.map observation μ)
        (fun b => expect (fiberPosterior μ observation b) h) :=
    (expect_congr_law (fiberPosterior_reconstruct μ observation) h).symm.trans
      (expect_bind_tower _ _ h (hbind h hh))
  rw [htower f hf, htower g hg]
  exact expect_mono (fun b hb => hcond b hb)
    (payoffIntegrable_bind_conditionalExpectation _ _ f (hbind f hf))
    (payoffIntegrable_bind_conditionalExpectation _ _ g (hbind g hg))

theorem expect_bindOnSupport_le_of_le_of_eq_off
    {α β : Type*} (p : PMF α) (q₁ q₂ : ∀ a, a ∈ p.support → PMF β)
    (f : β → ℝ) (h₁ : PayoffIntegrable (p.bindOnSupport q₁) f)
    (h₂ : PayoffIntegrable (p.bindOnSupport q₂) f)
    (hle : expect (p.bindOnSupport q₂) f ≤
      expect (p.bindOnSupport q₁) f)
    (a₀ : α) (ha₀ : a₀ ∈ p.support)
    (hoff : ∀ a, ∀ ha : a ∈ p.support, a ≠ a₀ → q₁ a ha = q₂ a ha) :
    expect (q₂ a₀ ha₀) f ≤
      expect (q₁ a₀ ha₀) f := by
  classical
  let v₁ : α → ℝ := extendFromSupport p (fun a ha =>
    expect (q₁ a ha) f)
  let v₂ : α → ℝ := extendFromSupport p (fun a ha =>
    expect (q₂ a ha) f)
  have hv₁ : ∀ a, ∀ ha : a ∈ p.support,
      v₁ a = expect (q₁ a ha) f := by
    intro a ha
    have hne : p a ≠ 0 := (p.mem_support_iff a).mp ha
    simp [v₁, extendFromSupport, hne]
  have hv₂ : ∀ a, ∀ ha : a ∈ p.support,
      v₂ a = expect (q₂ a ha) f := by
    intro a ha
    have hne : p a ≠ 0 := (p.mem_support_iff a).mp ha
    simp [v₂, extendFromSupport, hne]
  have ht₁ := expect_bindOnSupport_tower_on_support p q₁ f h₁ v₁ hv₁
  have ht₂ := expect_bindOnSupport_tower_on_support p q₂ f h₂ v₂ hv₂
  have houter : expect p v₂ ≤ expect p v₁ := by
    calc
      _ = expect (p.bindOnSupport q₂) f := ht₂.symm
      _ ≤ expect (p.bindOnSupport q₁) f := hle
      _ = _ := ht₁
  have hoffValue : ∀ a ∈ p.support,
      a ∉ ({a₀} : Set α) → v₂ a = v₁ a := by
    intro a ha hnot
    have hne : a ≠ a₀ := by
      simpa only [Set.mem_singleton_iff] using hnot
    rw [hv₂ a ha, hv₁ a ha]
    exact (expect_congr_law (hoff a ha hne) f
      ).symm
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
       = v₂ a₀ := by
    calc
      _ = expect (PMF.pure a₀) v₂ :=
        expect_congr_law hfilter v₂
      _ = v₂ a₀ := expect_pure a₀ v₂
  have hright : expect (p.filter {a₀} ⟨a₀, Set.mem_singleton _, ha₀⟩) v₁
       = v₁ a₀ := by
    calc
      _ = expect (PMF.pure a₀) v₁ :=
        expect_congr_law hfilter v₁
      _ = v₁ a₀ := expect_pure a₀ v₁
  rw [hleft, hright] at hfiltered
  rw [hv₂ a₀ ha₀, hv₁ a₀ ha₀] at hfiltered
  exact hfiltered


end GameTheory.Math.Probability
