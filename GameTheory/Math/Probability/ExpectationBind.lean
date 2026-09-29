import GameTheory.Math.Probability.Expectation
import GameTheory.Math.Probability.ExpectationMap
import GameTheory.Math.Probability.Joint
import GameTheory.Math.Probability.Support

noncomputable section

open scoped BigOperators

namespace GameTheory.Math.Probability

/-- Absolute summability of payoff contributions under the joint law of a
PMF bind. -/
def JointPayoffIntegrable {α β : Type*} (p : PMF α) (q : α → PMF β)
    (f : β → ℝ) : Prop :=
  Summable (fun ab : α × β =>
    (p ab.1).toReal * (q ab.1 ab.2).toReal * |f ab.2|)

theorem payoffIntegrable_bind_iff_joint {α β : Type*}
    (p : PMF α) (q : α → PMF β) (f : β → ℝ) :
    PayoffIntegrable (p.bind q) f ↔ JointPayoffIntegrable p q f := by
  rw [← bindPairLaw_map_snd]
  rw [payoffIntegrable_map_iff]
  have hpoint (ab : α × β) :
      ((bindPairLaw p q) ab).toReal * |f ab.2| =
        (p ab.1).toReal * (q ab.1 ab.2).toReal * |f ab.2| := by
    cases ab with
    | mk a b =>
      rw [bindPairLaw_apply]
      simp [ENNReal.toReal_mul, mul_assoc]
  constructor
  · intro h
    have hs : Summable (fun ab : α × β =>
        ((bindPairLaw p q) ab).toReal * |f ab.2|) := by
      simpa only [PayoffIntegrable, Function.comp_apply] using h
    have hs' := hs.congr fun ab => hpoint ab
    simpa only [JointPayoffIntegrable] using hs'
  · intro h
    have hs : Summable (fun ab : α × β =>
        (p ab.1).toReal * (q ab.1 ab.2).toReal * |f ab.2|) := by
      simpa only [JointPayoffIntegrable] using h
    have hs' := hs.congr fun ab => (hpoint ab).symm
    simpa only [PayoffIntegrable, Function.comp_apply] using hs'

private theorem bind_apply_toReal {α β : Type*} (p : PMF α)
    (q : α → PMF β) (b : β) :
    (p.bind q b).toReal = ∑' a, (p a).toReal * (q a b).toReal := by
  rw [PMF.bind_apply, ENNReal.tsum_toReal_eq
    (fun a => ENNReal.mul_ne_top (p.apply_ne_top a) ((q a).apply_ne_top b))]
  simp_rw [ENNReal.toReal_mul]

theorem payoffIntegrable_bind_conditional_on_support {α β : Type*}
    (p : PMF α) (q : α → PMF β) (f : β → ℝ)
    (hbind : PayoffIntegrable (p.bind q) f) :
    ∀ a, a ∈ p.support → PayoffIntegrable (q a) f := by
  classical
  intro a ha
  have hjoint : Summable (fun ab : α × β =>
      (p ab.1).toReal * (q ab.1 ab.2).toReal * |f ab.2|) := by
    simpa only [JointPayoffIntegrable] using
      ((payoffIntegrable_bind_iff_joint p q f).mp hbind)
  have hslice : Summable (fun b : β =>
      (p a).toReal * (q a b).toReal * |f b|) := by
    simpa [Function.comp_def] using
      (hjoint.comp_injective (i := fun b : β => (a, b)) fun b₁ b₂ h =>
        congrArg Prod.snd h)
  have hp : (p a).toReal ≠ 0 := by
    have hpos := ENNReal.toReal_pos ((p.mem_support_iff a).mp ha)
      (p.apply_ne_top a)
    exact ne_of_gt hpos
  have hscaled : Summable (fun b : β =>
      (p a).toReal * ((q a b).toReal * |f b|)) := by
    simpa [mul_assoc] using hslice
  have hrow := (summable_mul_left_iff hp).mp hscaled
  simpa only [PayoffIntegrable] using hrow

private theorem toReal_eq_zero_of_not_mem_support {α : Type*} {p : PMF α} {a : α}
    (ha : a ∉ p.support) : (p a).toReal = 0 := by
  have hzero : p a = 0 := not_ne_iff.mp ha
  simp [hzero]

/-- Integrability of a bind makes its conditional expectation integrable under
the outer law. Off the outer support the conditional value carries no weight. -/
theorem payoffIntegrable_bind_conditionalExpectation
    {α β : Type*} (p : PMF α) (q : α → PMF β) (f : β → ℝ)
    (hbind : PayoffIntegrable (p.bind q) f) :
    PayoffIntegrable p (fun a => expect (q a) f) := by
  have hjoint := payoffIntegrable_bind_iff_joint p q f |>.mp hbind
  have hrows : Summable (fun a => ∑' b,
      (p a).toReal * (q a b).toReal * |f b|) := by
    simpa only [JointPayoffIntegrable] using hjoint.prod
  apply Summable.of_nonneg_of_le
    (fun a => mul_nonneg ENNReal.toReal_nonneg (abs_nonneg _)) (fun a => ?_) hrows
  by_cases ha : a ∈ p.support
  · have habs : Summable (fun b => (q a b).toReal * |f b|) := by
      simpa only [PayoffIntegrable] using
        payoffIntegrable_bind_conditional_on_support p q f hbind a ha
    have hnorm : Summable (fun b => ‖(q a b).toReal * f b‖) := by
      simpa [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg ENNReal.toReal_nonneg] using habs
    have hinner : |expect (q a) f| ≤ ∑' b, (q a b).toReal * |f b| := by
      simpa [expect, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg ENNReal.toReal_nonneg] using norm_tsum_le_tsum_norm hnorm
    calc
      (p a).toReal * |expect (q a) f| ≤
          (p a).toReal * ∑' b, (q a b).toReal * |f b| :=
        mul_le_mul_of_nonneg_left hinner ENNReal.toReal_nonneg
      _ = ∑' b, (p a).toReal * (q a b).toReal * |f b| := by
        rw [← tsum_mul_left]
        simp_rw [mul_assoc]
  · simp [toReal_eq_zero_of_not_mem_support ha]

/-- Joint integrability makes any total function agreeing with conditional
values on the outer support integrable under the outer law. -/
theorem payoffIntegrable_bind_conditionalValue_on_support {α β : Type*} (p : PMF α)
    (q : α → PMF β) (f : β → ℝ)
    (hbind : PayoffIntegrable (p.bind q) f) (g : α → ℝ)
    (hcond : ∀ a ∈ p.support, g a = expect (q a) f) :
    PayoffIntegrable p g :=
  payoffIntegrable_congr_on_support (fun a ha => (hcond a ha).symm)
    (payoffIntegrable_bind_conditionalExpectation p q f hbind)

/-- The tower law: an integrable bind has the expectation of its conditional
expectations. -/
theorem expect_bind_tower {α β : Type*} (p : PMF α)
    (q : α → PMF β) (f : β → ℝ)
    (hbind : PayoffIntegrable (p.bind q) f) :
    expect (p.bind q) f = expect p (fun a => expect (q a) f) := by
  have hvalue (a : α) :
      ∑' b, (p a).toReal * (q a b).toReal * f b =
        (p a).toReal * expect (q a) f := by
    by_cases ha : a ∈ p.support
    · have habs : Summable (fun b => (q a b).toReal * |f b|) := by
        simpa only [PayoffIntegrable] using
          payoffIntegrable_bind_conditional_on_support p q f hbind a ha
      have hnorm : Summable (fun b => ‖(q a b).toReal * f b‖) := by
        simpa [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg ENNReal.toReal_nonneg] using habs
      simpa only [expect, mul_assoc] using hnorm.of_norm.tsum_mul_left (p a).toReal
    · simp [toReal_eq_zero_of_not_mem_support ha]
  have hjoint := payoffIntegrable_bind_iff_joint p q f |>.mp hbind
  have hjointSigned : Summable (fun ab : α × β =>
      (p ab.1).toReal * (q ab.1 ab.2).toReal * f ab.2) := by
    have habs : Summable (fun ab : α × β =>
        (p ab.1).toReal * ((q ab.1 ab.2).toReal * |f ab.2|)) := by
      simpa [JointPayoffIntegrable, mul_assoc] using hjoint
    apply Summable.of_norm
    simpa [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg ENNReal.toReal_nonneg, mul_assoc] using habs
  calc
    expect (p.bind q) f =
        ∑' b, ∑' a, (p a).toReal * (q a b).toReal * f b := by
      simp only [expect, bind_apply_toReal, ← tsum_mul_right]
    _ = ∑' a, ∑' b, (p a).toReal * (q a b).toReal * f b := hjointSigned.tsum_comm
    _ = expect p (fun a => expect (q a) f) := tsum_congr hvalue

/-- The tower law for any conditional value that agrees with the conditional
expectations on the outer support. -/
theorem expect_bind_tower_on_support {α β : Type*} (p : PMF α)
    (q : α → PMF β) (f : β → ℝ)
    (hbind : PayoffIntegrable (p.bind q) f) (g : α → ℝ)
    (hcond : ∀ a ∈ p.support, g a = expect (q a) f) :
    expect (p.bind q) f = expect p g :=
  (expect_bind_tower p q f hbind).trans
    (expect_congr_on_support fun a ha => (hcond a ha).symm)

theorem expect_bind_mono_on_support {α β : Type*} (p : PMF α)
    (q₁ q₂ : α → PMF β) (f : β → ℝ)
    (h₁ : PayoffIntegrable (p.bind q₁) f)
    (h₂ : PayoffIntegrable (p.bind q₂) f)
    (hle : ∀ a ∈ p.support, expect (q₁ a) f ≤ expect (q₂ a) f) :
    expect (p.bind q₁) f ≤ expect (p.bind q₂) f := by
  rw [expect_bind_tower p q₁ f h₁, expect_bind_tower p q₂ f h₂]
  exact expect_mono hle (payoffIntegrable_bind_conditionalExpectation p q₁ f h₁)
    (payoffIntegrable_bind_conditionalExpectation p q₂ f h₂)

/-- A strict conditional improvement at one supported outer atom makes the
integrated bind expectation strict, provided all supported conditionals are
weakly ordered. -/
theorem expect_bind_lt_on_support {α β : Type*} (p : PMF α)
    (q₁ q₂ : α → PMF β) (f : β → ℝ)
    (h₁ : PayoffIntegrable (p.bind q₁) f)
    (h₂ : PayoffIntegrable (p.bind q₂) f)
    (hle : ∀ a ∈ p.support, expect (q₁ a) f ≤ expect (q₂ a) f)
    (a : α) (ha : a ∈ p.support)
    (hlt : expect (q₁ a) f < expect (q₂ a) f) :
    expect (p.bind q₁) f < expect (p.bind q₂) f := by
  rw [expect_bind_tower p q₁ f h₁, expect_bind_tower p q₂ f h₂]
  exact expect_lt_of_mem_support
    (payoffIntegrable_bind_conditionalExpectation p q₁ f h₁)
    (payoffIntegrable_bind_conditionalExpectation p q₂ f h₂) hle a ha hlt

/-- A uniform upper bound on the supported conditional expectations bounds the
expectation of the bound law. -/
theorem expect_bind_le_of_forall_on_support {α β : Type*} (p : PMF α)
    (q : α → PMF β) (f : β → ℝ)
    (hbind : PayoffIntegrable (p.bind q) f) (c : ℝ)
    (hle : ∀ a ∈ p.support, expect (q a) f ≤ c) :
    expect (p.bind q) f ≤ c := by
  rw [expect_bind_tower p q f hbind]
  exact expect_le_const p _ (payoffIntegrable_bind_conditionalExpectation p q f hbind)
    c hle

/-- Monotonicity for support-dependent continuation kernels. The joint laws
provide the conditional integrability certificates on every supported branch. -/
theorem expect_bindOnSupport_mono_on_support {α β : Type*} (p : PMF α)
    (q₁ q₂ : ∀ a, a ∈ p.support → PMF β) (f : β → ℝ)
    (h₁ : PayoffIntegrable (p.bindOnSupport q₁) f)
    (h₂ : PayoffIntegrable (p.bindOnSupport q₂) f)
    (hle : ∀ a ha, PayoffIntegrable (q₁ a ha) f → PayoffIntegrable (q₂ a ha) f →
      expect (q₁ a ha) f ≤ expect (q₂ a ha) f) :
    expect (p.bindOnSupport q₁) f ≤
      expect (p.bindOnSupport q₂) f := by
  classical
  let k₁ : α → PMF β := fun a =>
    if ha : a ∈ p.support then q₁ a ha else p.bindOnSupport q₁
  let k₂ : α → PMF β := fun a =>
    if ha : a ∈ p.support then q₂ a ha else p.bindOnSupport q₂
  have heq₁ : p.bindOnSupport q₁ = p.bind k₁ :=
    bindOnSupport_eq_bind_of_eq_on_support p (fun a ha => by
      have hne : p a ≠ 0 := (p.mem_support_iff a).mp ha
      simp [k₁, hne])
  have heq₂ : p.bindOnSupport q₂ = p.bind k₂ :=
    bindOnSupport_eq_bind_of_eq_on_support p (fun a ha => by
      have hne : p a ≠ 0 := (p.mem_support_iff a).mp ha
      simp [k₂, hne])
  have hk₁ : PayoffIntegrable (p.bind k₁) f := by rwa [← heq₁]
  have hk₂ : PayoffIntegrable (p.bind k₂) f := by rwa [← heq₂]
  have hmono := expect_bind_mono_on_support p k₁ k₂ f hk₁ hk₂
    (fun a ha => by
      have hne : p a ≠ 0 := (p.mem_support_iff a).mp ha
      have hk₁a : k₁ a = q₁ a ha := by simp [k₁, hne]
      have hk₂a : k₂ a = q₂ a ha := by simp [k₂, hne]
      have hcond₁ : PayoffIntegrable (q₁ a ha) f := by
        rw [← hk₁a]
        exact
          (payoffIntegrable_bind_conditional_on_support p k₁ f hk₁ a ha)
      have hcond₂ : PayoffIntegrable (q₂ a ha) f := by
        rw [← hk₂a]
        exact
          (payoffIntegrable_bind_conditional_on_support p k₂ f hk₂ a ha)
      rw [hk₁a, hk₂a]
      exact hle a ha hcond₁ hcond₂)
  simpa only [← heq₁, ← heq₂] using hmono

private noncomputable def supportKernelExtend {α β : Type*} (p : PMF α)
    (q : ∀ a, a ∈ p.support → PMF β) : α → PMF β := by
  classical
  exact fun a => if ha : a ∈ p.support then q a ha else p.bindOnSupport q

private theorem supportKernelExtend_on_support {α β : Type*} (p : PMF α)
    (q : ∀ a, a ∈ p.support → PMF β) (a : α) (ha : a ∈ p.support) :
    supportKernelExtend p q a = q a ha := by
  classical
  have hne : p a ≠ 0 := (p.mem_support_iff a).mp ha
  simp [supportKernelExtend, hne]

private theorem bindOnSupport_eq_bind_supportKernelExtend {α β : Type*}
    (p : PMF α) (q : ∀ a, a ∈ p.support → PMF β) :
    p.bindOnSupport q = p.bind (supportKernelExtend p q) :=
  bindOnSupport_eq_bind_of_eq_on_support p
    (fun a ha => (supportKernelExtend_on_support p q a ha).symm)

private theorem jointPayoffIntegrable_of_finite_support {α β : Type*}
    (p : PMF α) (q : α → PMF β) (f : β → ℝ)
    (hfinite : p.support.Finite)
    (hcond : ∀ a, a ∈ p.support → PayoffIntegrable (q a) f) :
    JointPayoffIntegrable p q f := by
  let w : α × β → ℝ := fun ab =>
    (p ab.1).toReal * (q ab.1 ab.2).toReal * |f ab.2|
  have hw_nonneg (ab : α × β) : 0 ≤ w ab := by
    simp only [w]
    positivity
  have hrows : ∀ a, Summable (fun b => w (a, b)) := by
    intro a
    by_cases ha : a ∈ p.support
    · have hca := hcond a ha
      have hrow := hca.mul_left (p a).toReal
      apply hrow.congr
      intro b
      simp only [w]
      ring
    · have hpa : p a = 0 := by
        apply not_ne_iff.mp
        exact ha
      simp [w, hpa]
  let rowSum : α → ℝ := fun a => ∑' b, w (a, b)
  have hrowSupport : Function.HasFiniteSupport rowSum := by
    apply hfinite.subset
    intro a ha
    by_contra hnot
    have hpa : p a = 0 := by
      apply not_ne_iff.mp
      exact hnot
    have hzero : rowSum a = 0 := by
      simp [rowSum, w, hpa]
    exact ha (by simpa only [Function.mem_support] using hzero)
  have houter : Summable rowSum := summable_of_hasFiniteSupport hrowSupport
  have hprod := (summable_prod_of_nonneg hw_nonneg).2 ⟨hrows, houter⟩
  exact hprod

/-- Finite outer support and supported conditional integration imply
integrability of an ordinary PMF bind. -/
theorem payoffIntegrable_bind_of_finite_support {α β : Type*}
    (p : PMF α) (q : α → PMF β) (f : β → ℝ)
    (hfinite : p.support.Finite)
    (hcond : ∀ a, a ∈ p.support → PayoffIntegrable (q a) f) :
    PayoffIntegrable (p.bind q) f := by
  exact (payoffIntegrable_bind_iff_joint p q f).2
    (jointPayoffIntegrable_of_finite_support p q f hfinite hcond)

/-- A finite outer carrier removes the support premise on the conditionals. -/
theorem payoffIntegrable_bind_of_finite {α β : Type*} [Finite α]
    (p : PMF α) (q : α → PMF β) (f : β → ℝ)
    (hcond : ∀ a, PayoffIntegrable (q a) f) :
    PayoffIntegrable (p.bind q) f :=
  payoffIntegrable_bind_of_finite_support p q f
    (Set.finite_univ.subset (Set.subset_univ _)) (fun a _ => hcond a)

/-- Finite outer support and supported conditional integration imply
integrability of a dependent bindOnSupport. -/
theorem payoffIntegrable_bindOnSupport_of_finite_support {α β : Type*}
    (p : PMF α) (q : ∀ a, a ∈ p.support → PMF β) (f : β → ℝ)
    (hfinite : p.support.Finite)
    (hcond : ∀ a, ∀ ha : a ∈ p.support, PayoffIntegrable (q a ha) f) :
    PayoffIntegrable (p.bindOnSupport q) f := by
  let k := supportKernelExtend p q
  have hk : PayoffIntegrable (p.bind k) f :=
    payoffIntegrable_bind_of_finite_support p k f hfinite
      (fun a ha => by
        simpa only [k, supportKernelExtend_on_support p q a ha] using hcond a ha)
  simpa only [k, bindOnSupport_eq_bind_supportKernelExtend] using hk

/-- For a finite outer carrier, every dependent continuation may be
integrated. -/
theorem payoffIntegrable_bindOnSupport_of_finite {α β : Type*} [Finite α]
    (p : PMF α) (q : ∀ a, a ∈ p.support → PMF β) (f : β → ℝ)
    (hcond : ∀ a, ∀ ha : a ∈ p.support, PayoffIntegrable (q a ha) f) :
    PayoffIntegrable (p.bindOnSupport q) f :=
  payoffIntegrable_bindOnSupport_of_finite_support p q f
    (Set.finite_univ.subset (Set.subset_univ _)) hcond

/-- The integrated dependent bind supplies each supported conditional guard. -/
theorem payoffIntegrable_bindOnSupport_conditional_on_support {α β : Type*}
    (p : PMF α) (q : ∀ a, a ∈ p.support → PMF β) (f : β → ℝ)
    (hbind : PayoffIntegrable (p.bindOnSupport q) f)
    (a : α) (ha : a ∈ p.support) : PayoffIntegrable (q a ha) f := by
  let k := supportKernelExtend p q
  have hk : PayoffIntegrable (p.bind k) f := by
    rw [← bindOnSupport_eq_bind_supportKernelExtend]
    exact hbind
  have hcond := payoffIntegrable_bind_conditional_on_support p k f hk a ha
  have hka : k a = q a ha := supportKernelExtend_on_support p q a ha
  rwa [hka] at hcond

/-- A total conditional-value function needs agreement only on outer support. -/
theorem payoffIntegrable_bindOnSupport_conditionalValue_on_support {α β : Type*}
    (p : PMF α) (q : ∀ a, a ∈ p.support → PMF β) (f : β → ℝ)
    (hbind : PayoffIntegrable (p.bindOnSupport q) f) (g : α → ℝ)
    (hagree : ∀ a, ∀ ha : a ∈ p.support,
      g a = expect (q a ha) f) :
    PayoffIntegrable p g := by
  let k := supportKernelExtend p q
  have hk : PayoffIntegrable (p.bind k) f := by
    rw [← bindOnSupport_eq_bind_supportKernelExtend]
    exact hbind
  apply payoffIntegrable_bind_conditionalValue_on_support p k f hk g
  intro a ha
  have hka : k a = q a ha := supportKernelExtend_on_support p q a ha
  have h := hagree a ha
  unfold expect at h ⊢
  rw [hka]
  exact h

/-- The guarded tower for a continuation defined only at supported draws. -/
theorem expect_bindOnSupport_tower_on_support {α β : Type*} (p : PMF α)
    (q : ∀ a, a ∈ p.support → PMF β) (f : β → ℝ)
    (hbind : PayoffIntegrable (p.bindOnSupport q) f) (g : α → ℝ)
    (hagree : ∀ a, ∀ ha : a ∈ p.support,
      g a = expect (q a ha) f) :
    expect (p.bindOnSupport q) f =
      expect p g := by
  let k := supportKernelExtend p q
  have hk : PayoffIntegrable (p.bind k) f := by
    rw [← bindOnSupport_eq_bind_supportKernelExtend]
    exact hbind
  have hcond : ∀ a, ∀ ha : a ∈ p.support,
      g a = expect (k a) f := by
    intro a ha
    have h := hagree a ha
    unfold expect at h ⊢
    have hka : k a = q a ha := supportKernelExtend_on_support p q a ha
    rw [hka]
    exact h
  have htower := expect_bind_tower_on_support p k f hk g hcond
  unfold expect at htower ⊢
  rw [← bindOnSupport_eq_bind_supportKernelExtend] at htower
  exact htower

/-- A whole-law integration certificate and supported conditional upper
bounds control the expectation of an arbitrary PMF bind. -/
theorem expect_bind_le_constant_on_support {α β : Type*}
    (μ : PMF α) (kernel : α → PMF β) (f : β → ℝ) (c : ℝ)
    (hbind : PayoffIntegrable (μ.bind kernel) f)
    (hle : ∀ a ∈ μ.support, expect (kernel a) f ≤ c) :
    expect (μ.bind kernel) f ≤ c :=
  expect_bind_le_of_forall_on_support μ kernel f hbind c hle

/-- The corresponding supported conditional lower-bound rule. -/
theorem expect_bind_ge_constant_on_support {α β : Type*}
    (μ : PMF α) (kernel : α → PMF β) (f : β → ℝ) (c : ℝ)
    (hbind : PayoffIntegrable (μ.bind kernel) f)
    (hle : ∀ a ∈ μ.support, c ≤ expect (kernel a) f) :
    c ≤ expect (μ.bind kernel) f := by
  rw [expect_bind_tower μ kernel f hbind]
  calc
    c = expect μ (fun _ => c) := (expect_constant μ c).symm
    _ ≤ expect μ (fun a => expect (kernel a) f) :=
      expect_mono hle (payoffIntegrable_constant μ c)
        (payoffIntegrable_bind_conditionalExpectation μ kernel f hbind)

end GameTheory.Math.Probability
