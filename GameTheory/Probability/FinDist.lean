/-
# Finite-support probability laws

`FinDist α` is a Mathlib `PMF` paired with a proof that its support is finite.
That representation is deliberately *not* part of the public contract. Downstream
modules use `pure`, `map`, `bind`, `pi`, `prob`, and `expect` together with the
lemmas below, never `toPMF`.

Finite support is a capability of a particular law, not a `Fintype` assumption
on its carrier: `expect` is an unconditional real number for an
arbitrary observable, and `FinDist Nat` is inhabited by genuinely two-point
laws.

The convexity-facing `stdSimplex` bridge lives outside this module, which stays
free of convexity and topology imports.
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Probability.ProbabilityMassFunction.Monad

noncomputable section

open scoped BigOperators NNReal

namespace GameTheory.Probability

universe u v w z

/-- A probability law whose support is finite. The representation is private to
this module's API surface. -/
def FinDist (α : Type u) := { μ : PMF α // μ.support.Finite }

namespace FinDist

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type z}

/-- Representation escape hatch. Public modules must not use this; it exists so
that this module and the designated `Analysis` bridge can state their proofs. -/
def toPMF (μ : FinDist α) : PMF α := μ.1

/-- The set of outcomes the law gives positive mass. -/
def support (μ : FinDist α) : Set α := μ.toPMF.support

theorem support_finite (μ : FinDist α) : μ.support.Finite := μ.2

/-- The finite support as a `Finset`. -/
def supportFinset (μ : FinDist α) : Finset α := μ.support_finite.toFinset

@[simp]
theorem mem_supportFinset {μ : FinDist α} {a : α} :
    a ∈ μ.supportFinset ↔ a ∈ μ.support :=
  Set.Finite.mem_toFinset _

@[ext]
theorem ext {μ ν : FinDist α} (h : μ.toPMF = ν.toPMF) : μ = ν := Subtype.ext h

/-! ## Operations -/

/-- The point mass at `a`. -/
def pure (a : α) : FinDist α := ⟨PMF.pure a, by simp⟩

/-- Sequential composition. Finite support is preserved because a finite union
of finite supports is finite. -/
def bind (μ : FinDist α) (f : α → FinDist β) : FinDist β :=
  ⟨μ.toPMF.bind fun a => (f a).toPMF, by
    rw [PMF.support_bind]
    exact μ.support_finite.biUnion fun a _ => (f a).support_finite⟩

/-- Pushforward along `f`. Defined from `bind` and `pure` so that this module
needs only Mathlib's `PMF` monad layer. -/
def map (f : α → β) (μ : FinDist α) : FinDist β :=
  bind μ fun a => pure (f a)

/-- Independent product of two laws. -/
def product (μ : FinDist α) (ν : FinDist β) : FinDist (α × β) :=
  bind μ fun a => map (fun b => (a, b)) ν

@[simp]
theorem toPMF_pure (a : α) : (pure a).toPMF = PMF.pure a := rfl

@[simp]
theorem toPMF_map (f : α → β) (μ : FinDist α) :
    (map f μ).toPMF = μ.toPMF.bind fun a => PMF.pure (f a) := rfl

@[simp]
theorem toPMF_bind (μ : FinDist α) (f : α → FinDist β) :
    (bind μ f).toPMF = μ.toPMF.bind fun a => (f a).toPMF := rfl

@[simp]
theorem pure_bind (a : α) (f : α → FinDist β) : bind (pure a) f = f a := by
  apply ext; simp

@[simp]
theorem bind_pure (μ : FinDist α) : bind μ pure = μ := by
  apply ext; simp

@[simp]
theorem bind_bind (μ : FinDist α) (f : α → FinDist β) (g : β → FinDist γ) :
    bind (bind μ f) g = bind μ fun a => bind (f a) g := by
  apply ext; simp [PMF.bind_bind]

theorem map_eq_bind (f : α → β) (μ : FinDist α) :
    map f μ = bind μ fun a => pure (f a) := rfl

@[simp]
theorem map_id (μ : FinDist α) : map id μ = μ := bind_pure μ

@[simp]
theorem map_comp (g : β → γ) (f : α → β) (μ : FinDist α) :
    map g (map f μ) = map (g ∘ f) μ := by
  simp only [map_eq_bind, bind_bind, pure_bind, Function.comp_def]

@[simp]
theorem map_pure (f : α → β) (a : α) : map f (pure a) = pure (f a) := by
  rw [map_eq_bind, pure_bind]

@[simp]
theorem map_bind (g : β → γ) (μ : FinDist α) (f : α → FinDist β) :
    map g (bind μ f) = bind μ fun a => map g (f a) := by
  simp [map_eq_bind]

@[simp]
theorem bind_map (f : α → β) (μ : FinDist α) (g : β → FinDist γ) :
    bind (map f μ) g = bind μ fun a => g (f a) := by
  simp [map_eq_bind]

@[simp]
theorem mem_support_pure {a b : α} : a ∈ (pure b).support ↔ a = b := by
  simp [support]

@[simp]
theorem support_bind (μ : FinDist α) (f : α → FinDist β) :
    (bind μ f).support = ⋃ a ∈ μ.support, (f a).support :=
  PMF.support_bind ..

@[simp]
theorem support_map (f : α → β) (μ : FinDist α) :
    (map f μ).support = f '' μ.support := by
  rw [map_eq_bind, support_bind]
  ext b
  simp [eq_comm]

/-! ## Support-dependent composition

`bind` hands its continuation an outcome. Some continuations need more than
that: they need evidence that the outcome actually occurs. A law over histories
is the motivating case, since extending a history by one transition is only
meaningful for a transition that was realized.

Finite support survives, because the result is a union of finitely many finite
supports indexed by a finite support. -/

/-- Sequential composition whose continuation may read a proof that its input
lies in the support. -/
def bindOnSupport (μ : FinDist α) (f : ∀ a ∈ μ.support, FinDist β) : FinDist β :=
  ⟨μ.toPMF.bindOnSupport fun a ha => (f a ha).toPMF, by
    rw [PMF.support_bindOnSupport]
    have hrewrite :
        (⋃ (a : α) (ha : a ∈ μ.toPMF.support), ((f a ha).toPMF).support) =
          ⋃ a : μ.supportFinset, ((f a.1 (mem_supportFinset.mp a.2)).toPMF).support := by
      ext b
      simp only [Set.mem_iUnion]
      exact ⟨fun ⟨a, ha, hb⟩ => ⟨⟨a, mem_supportFinset.mpr ha⟩, hb⟩,
        fun ⟨a, hb⟩ => ⟨a.1, mem_supportFinset.mp a.2, hb⟩⟩
    rw [hrewrite]
    exact Set.finite_iUnion fun a => (f a.1 (mem_supportFinset.mp a.2)).support_finite⟩

@[simp]
theorem toPMF_bindOnSupport (μ : FinDist α) (f : ∀ a ∈ μ.support, FinDist β) :
    (μ.bindOnSupport f).toPMF = μ.toPMF.bindOnSupport fun a ha => (f a ha).toPMF := rfl

@[simp]
theorem support_bindOnSupport (μ : FinDist α) (f : ∀ a ∈ μ.support, FinDist β) :
    (μ.bindOnSupport f).support = ⋃ (a : α) (ha : a ∈ μ.support), (f a ha).support :=
  PMF.support_bindOnSupport ..

theorem bindOnSupport_congr {μ : FinDist α} {f g : ∀ a ∈ μ.support, FinDist β}
    (h : ∀ a (ha : a ∈ μ.support), f a ha = g a ha) : μ.bindOnSupport f = μ.bindOnSupport g := by
  simp only [funext fun a => funext fun ha => h a ha]

/-- A continuation that ignores its evidence is an ordinary `bind`. -/
@[simp]
theorem bindOnSupport_eq_bind (μ : FinDist α) (f : α → FinDist β) :
    (μ.bindOnSupport fun a _ => f a) = μ.bind f := by
  apply ext; simp

/-- **The composition collapses when the evidence is not used.** A continuation
that happens to agree with a total one on the support is that total one, which
is how a law defined by support-dependent recursion is compared with a law that
never needed the evidence. -/
theorem bindOnSupport_eq_bind_of_eq_on_support {μ : FinDist α}
    {f : ∀ a ∈ μ.support, FinDist β} {g : α → FinDist β}
    (h : ∀ a (ha : a ∈ μ.support), f a ha = g a) : μ.bindOnSupport f = μ.bind g := by
  rw [← bindOnSupport_eq_bind μ g]
  exact bindOnSupport_congr h

@[simp]
theorem pure_bindOnSupport (a : α) (f : ∀ b ∈ (pure a).support, FinDist β) :
    (pure a).bindOnSupport f = f a (mem_support_pure.mpr rfl) := by
  apply ext; simp

@[simp]
theorem bind_bindOnSupport (μ : FinDist α) (f : ∀ a ∈ μ.support, FinDist β) (g : β → FinDist γ) :
    (μ.bindOnSupport f).bind g = μ.bindOnSupport fun a ha => (f a ha).bind g := by
  apply ext
  rw [toPMF_bind, toPMF_bindOnSupport, ← PMF.bindOnSupport_eq_bind _ fun b => (g b).toPMF,
    PMF.bindOnSupport_bindOnSupport]
  simp

@[simp]
theorem map_bindOnSupport (g : β → γ) (μ : FinDist α) (f : ∀ a ∈ μ.support, FinDist β) :
    map g (μ.bindOnSupport f) = μ.bindOnSupport fun a ha => map g (f a ha) := by
  simp only [map_eq_bind, bind_bindOnSupport]


/-! ## Real masses -/

/-- The real probability of a single outcome. Finite support keeps this an
ordinary real number with no `ENNReal` obligations for the caller. -/
def prob (μ : FinDist α) (a : α) : ℝ := (μ.toPMF a).toReal

theorem prob_def (μ : FinDist α) (a : α) : μ.prob a = (μ.toPMF a).toReal := rfl

theorem prob_nonneg (μ : FinDist α) (a : α) : 0 ≤ μ.prob a := ENNReal.toReal_nonneg

theorem prob_eq_zero_of_toPMF {μ : FinDist α} {a : α} (h : μ.toPMF a = 0) : μ.prob a = 0 := by
  simp [prob_def, h]

theorem prob_eq_zero_iff {μ : FinDist α} {a : α} : μ.prob a = 0 ↔ a ∉ μ.support := by
  rw [prob_def, ENNReal.toReal_eq_zero_iff]
  simp [support, PMF.mem_support_iff, PMF.apply_ne_top]

theorem prob_pos_iff {μ : FinDist α} {a : α} : 0 < μ.prob a ↔ a ∈ μ.support :=
  ⟨fun h => by
      by_contra hmem
      exact absurd (prob_eq_zero_iff.2 hmem) h.ne',
   fun h => lt_of_le_of_ne (prob_nonneg μ a) fun h0 => prob_eq_zero_iff.1 h0.symm h⟩

@[simp]
theorem prob_pure_self [DecidableEq α] (a : α) : (pure a).prob a = 1 := by
  simp [prob_def, PMF.pure_apply]

theorem prob_pure_of_ne {a b : α} (h : a ≠ b) : (pure b).prob a = 0 := by
  simp [prob_def, PMF.pure_apply, h]

theorem prob_pure_eq_ite [DecidableEq α] (a b : α) :
    (pure a).prob b = if b = a then 1 else 0 := by
  by_cases h : b = a
  · subst h; simp
  · simp [prob_pure_of_ne h, h]

/-- Total mass is one. Finite support makes this an ordinary real identity. -/
theorem tsum_prob (μ : FinDist α) : ∑' a, μ.prob a = 1 := by
  rw [show (∑' a, μ.prob a) = ∑' a, (μ.toPMF a).toReal from rfl,
    ← ENNReal.tsum_toReal_eq fun a => PMF.apply_ne_top μ.toPMF a, PMF.tsum_coe]
  norm_num

theorem sum_prob_supportFinset (μ : FinDist α) : ∑ a ∈ μ.supportFinset, μ.prob a = 1 := by
  rw [← tsum_prob μ, tsum_eq_sum (s := μ.supportFinset)]
  intro a ha
  exact prob_eq_zero_iff.2 fun hmem => ha (mem_supportFinset.2 hmem)

/-- Every law's mass sums to one over a finite carrier. -/
theorem sum_prob [Fintype α] (μ : FinDist α) : ∑ a, μ.prob a = 1 := by
  simpa [tsum_fintype] using tsum_prob μ

/-- Build a law on a finite carrier from a real weight vector. This is the
entry point used to compile an explicitly presented (for instance rational)
distribution into the semantic core. -/
def ofWeights [Fintype α] (weight : α → ℝ) (hnonneg : ∀ a, 0 ≤ weight a)
    (hsum : ∑ a, weight a = 1) : FinDist α :=
  ⟨⟨fun a => ENNReal.ofReal (weight a), by
      have : ∑ a, ENNReal.ofReal (weight a) = 1 := by
        rw [← ENNReal.ofReal_sum_of_nonneg fun a _ => hnonneg a, hsum]
        norm_num
      simpa [tsum_fintype, this] using hasSum_fintype fun a => ENNReal.ofReal (weight a)⟩,
    Set.toFinite _⟩

@[simp]
theorem prob_ofWeights [Fintype α] (weight : α → ℝ) (hnonneg : ∀ a, 0 ≤ weight a)
    (hsum : ∑ a, weight a = 1) (a : α) :
    (ofWeights weight hnonneg hsum).prob a = weight a :=
  ENNReal.toReal_ofReal (hnonneg a)

/-! ## Expectation

Finite support makes real expectation unconditional: no summability or
boundedness hypothesis appears in any statement below. -/

/-- The expected value of a real observable. -/
def expect (μ : FinDist α) (u : α → ℝ) : ℝ := ∑' a, μ.prob a * u a

theorem summable_prob_mul (μ : FinDist α) (u : α → ℝ) :
    Summable fun a => μ.prob a * u a := by
  apply summable_of_hasFiniteSupport
  apply μ.support_finite.subset
  intro a ha
  by_contra hnot
  exact ha (by simp [prob_eq_zero_iff.2 hnot])

theorem expect_eq_sum_support (μ : FinDist α) (u : α → ℝ) :
    expect μ u = ∑ a ∈ μ.supportFinset, μ.prob a * u a := by
  unfold expect
  rw [tsum_eq_sum (s := μ.supportFinset)]
  intro a ha
  simp [prob_eq_zero_iff.2 (fun hmem => ha (mem_supportFinset.2 hmem))]

theorem expect_eq_sum [Fintype α] (μ : FinDist α) (u : α → ℝ) :
    expect μ u = ∑ a, μ.prob a * u a := by
  simp [expect, tsum_fintype]

@[simp]
theorem expect_pure (a : α) (u : α → ℝ) : expect (pure a) u = u a := by
  classical
  unfold expect
  rw [tsum_eq_single a]
  · simp [prob_def, PMF.pure_apply]
  · intro b hba
    simp [prob_pure_of_ne hba]

@[simp]
theorem expect_const (μ : FinDist α) (c : ℝ) : expect μ (fun _ => c) = c := by
  rw [expect_eq_sum_support, ← Finset.sum_mul, sum_prob_supportFinset, one_mul]

theorem expect_add (μ : FinDist α) (u v : α → ℝ) :
    expect μ (fun a => u a + v a) = expect μ u + expect μ v := by
  unfold expect
  rw [← Summable.tsum_add (summable_prob_mul μ u) (summable_prob_mul μ v)]
  exact tsum_congr fun a => by ring

theorem expect_smul (c : ℝ) (μ : FinDist α) (u : α → ℝ) :
    expect μ (fun a => c * u a) = c * expect μ u := by
  unfold expect
  rw [← tsum_mul_left]
  exact tsum_congr fun a => by ring

theorem expect_congr {μ : FinDist α} {u v : α → ℝ}
    (h : ∀ a ∈ μ.support, u a = v a) : expect μ u = expect μ v := by
  rw [expect_eq_sum_support, expect_eq_sum_support]
  exact Finset.sum_congr rfl fun a ha => by rw [h a (mem_supportFinset.1 ha)]

theorem expect_mono {μ : FinDist α} {u v : α → ℝ}
    (h : ∀ a ∈ μ.support, u a ≤ v a) : expect μ u ≤ expect μ v := by
  rw [expect_eq_sum_support, expect_eq_sum_support]
  refine Finset.sum_le_sum fun a ha => ?_
  exact mul_le_mul_of_nonneg_left (h a (mem_supportFinset.1 ha)) (prob_nonneg μ a)

/-- Expectation distributes over finite-support `bind`. Adapted from the v1
finite-support expectation development. -/
theorem expect_bind (μ : FinDist α) (f : α → FinDist β) (u : β → ℝ) :
    expect (bind μ f) u = expect μ fun a => expect (f a) u := by
  classical
  let F : α → β → ℝ := fun a b => μ.prob a * ((f a).prob b * u b)
  have hrow (a : α) : Summable (F a) := (summable_prob_mul (f a) u).mul_left _
  have hcol (b : β) : Summable fun a => F a b := by
    apply summable_of_hasFiniteSupport
    apply μ.support_finite.subset
    intro a ha
    by_contra hnot
    exact ha (by simp [F, prob_eq_zero_iff.2 hnot])
  have hjoint : Summable (Function.uncurry F) := by
    apply summable_of_hasFiniteSupport
    apply (μ.support_finite.biUnion fun a _ =>
      (Set.finite_singleton a).prod (f a).support_finite).subset
    rintro ⟨a, b⟩ hab
    by_contra hnot
    apply hnot
    simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff]
    refine ⟨a, ?_, rfl, ?_⟩
    · intro ha
      exact hab (by simp [Function.uncurry, F, prob_eq_zero_of_toPMF ha])
    · intro hb
      exact hab (by simp [Function.uncurry, F, prob_eq_zero_of_toPMF hb])
  have hinner (b : β) :
      (bind μ f).prob b = ∑' a, μ.prob a * (f a).prob b := by
    rw [prob_def, toPMF_bind, PMF.bind_apply,
      ENNReal.tsum_toReal_eq fun a =>
        ENNReal.mul_ne_top (PMF.apply_ne_top μ.toPMF a) (PMF.apply_ne_top (f a).toPMF b)]
    exact tsum_congr fun a => ENNReal.toReal_mul
  unfold expect
  simp_rw [hinner, ← tsum_mul_right]
  rw [show (∑' b, ∑' a, μ.prob a * (f a).prob b * u b) = ∑' b, ∑' a, F a b from
    tsum_congr fun b => tsum_congr fun a => by simp [F, mul_assoc]]
  rw [hjoint.tsum_comm' hrow hcol]
  exact tsum_congr fun a => by rw [← tsum_mul_left]

@[simp]
theorem expect_map (f : α → β) (μ : FinDist α) (u : β → ℝ) :
    expect (map f μ) u = expect μ (fun a => u (f a)) := by
  rw [map_eq_bind, expect_bind]
  simp

theorem expect_mul_const (μ : FinDist α) (u : α → ℝ) (c : ℝ) :
    expect μ (fun a => u a * c) = expect μ u * c := by
  unfold expect
  rw [← tsum_mul_right]
  exact tsum_congr fun a => by ring

/-- The mass of a `bind` is the expected mass of its branches. -/
theorem prob_bind (μ : FinDist α) (f : α → FinDist β) (b : β) :
    (bind μ f).prob b = μ.expect fun a => (f a).prob b := by
  rw [prob_def, toPMF_bind, PMF.bind_apply,
    ENNReal.tsum_toReal_eq fun a =>
      ENNReal.mul_ne_top (PMF.apply_ne_top μ.toPMF a) (PMF.apply_ne_top (f a).toPMF b)]
  exact tsum_congr fun a => ENNReal.toReal_mul

/-- Averaging point masses recovers the averaging law. -/
theorem expect_prob_pure (μ : FinDist α) (b : α) :
    (μ.expect fun a => (pure a).prob b) = μ.prob b := by
  classical
  unfold expect
  rw [tsum_eq_single b]
  · simp
  · intro a hab
    simp [prob_pure_of_ne (Ne.symm hab)]

/-- Two laws with the same real masses are equal. This is the public
extensionality principle; it mentions no representation. -/
theorem ext_of_prob {μ ν : FinDist α} (h : ∀ a, μ.prob a = ν.prob a) : μ = ν := by
  refine ext (PMF.ext fun a => ?_)
  exact (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).1 (h a)

/-- Branches agreeing on the support give the same `bind`. -/
theorem bind_congr {μ : FinDist α} {f g : α → FinDist β}
    (h : ∀ a ∈ μ.support, f a = g a) : μ.bind f = μ.bind g := by
  refine ext_of_prob fun b => ?_
  rw [prob_bind, prob_bind]
  exact expect_congr fun a ha => by rw [h a ha]

/-- Binding a constant branch discards the first law. -/
@[simp]
theorem bind_const (μ : FinDist α) (ν : FinDist β) : (μ.bind fun _ => ν) = ν := by
  refine ext_of_prob fun b => ?_
  rw [prob_bind, expect_const]

/-- When every branch pushes forward to the same law, so does the composition —
so an observable that cannot tell the branches apart sees no composition at
all. -/
theorem map_bindOnSupport_const {μ : FinDist α} {f : ∀ a ∈ μ.support, FinDist β}
    {ν : FinDist γ} (g : β → γ) (h : ∀ a (ha : a ∈ μ.support), map g (f a ha) = ν) :
    map g (μ.bindOnSupport f) = ν := by
  rw [map_bindOnSupport, bindOnSupport_eq_bind_of_eq_on_support h]
  exact bind_const μ ν


/-- Finite-support Fubini: independent expectations commute. -/
theorem expect_comm (μ : FinDist α) (ν : FinDist β) (g : α → β → ℝ) :
    expect μ (fun a => expect ν (fun b => g a b)) =
      expect ν (fun b => expect μ (fun a => g a b)) := by
  simp_rw [expect_eq_sum_support, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

/-! ## Reading a mass off a pushforward

`prob` after `map` is a sum over a fibre in general. The two cases below are the
ones that arise: an injective pushforward moves masses without merging them, and
a product's masses factor. -/

theorem expect_ite_eq [DecidableEq α] (μ : FinDist α) (a : α) (c : ℝ) :
    (μ.expect fun x => if a = x then c else 0) = μ.prob a * c := by
  rw [expect_eq_sum_support]
  by_cases hmem : a ∈ μ.support
  · rw [Finset.sum_eq_single a (fun b _ hne => by simp [Ne.symm hne])
      (fun hnot => absurd (mem_supportFinset.mpr hmem) hnot)]
    simp
  · rw [prob_eq_zero_iff.mpr hmem, zero_mul]
    refine Finset.sum_eq_zero fun b hb => ?_
    by_cases h : a = b
    · subst h
      exact absurd (mem_supportFinset.mp hb) hmem
    · simp [h]

theorem prob_map [DecidableEq β] (f : α → β) (μ : FinDist α) (b : β) :
    (map f μ).prob b = μ.expect fun a => if b = f a then 1 else 0 := by
  rw [map_eq_bind, prob_bind]
  exact expect_congr fun a _ => by rw [prob_pure_eq_ite]

/-- An injective pushforward carries each mass to its image untouched. -/
theorem prob_map_of_injective [DecidableEq α] [DecidableEq β] (f : α → β)
    (hf : Function.Injective f) (μ : FinDist α) (a : α) :
    (map f μ).prob (f a) = μ.prob a := by
  rw [prob_map, show (fun x => if f a = f x then (1:ℝ) else 0) =
    fun x => if a = x then (1:ℝ) else 0 from funext fun x => by simp [hf.eq_iff],
    expect_ite_eq, mul_one]

/-- Independence, as masses: a product law factors at every point. -/
theorem prob_product [DecidableEq α] [DecidableEq β] (μ : FinDist α) (ν : FinDist β)
    (p : α × β) : (product μ ν).prob p = μ.prob p.1 * ν.prob p.2 := by
  rw [product, prob_bind]
  rw [show (fun a => (map (fun b => (a, b)) ν).prob p) =
      fun a => if p.1 = a then ν.prob p.2 else 0 from funext fun a => ?_]
  · exact expect_ite_eq μ p.1 (ν.prob p.2)
  · by_cases h : p.1 = a
    · subst h
      rw [if_pos rfl, show p = ((fun b => (p.1, b)) p.2) from rfl,
        prob_map_of_injective _ (fun x y hxy => (Prod.mk.inj hxy).2) ν p.2]
    · rw [if_neg h, prob_map,
        show (fun b => if p = (a, b) then (1:ℝ) else 0) = fun _ => (0:ℝ) from
          funext fun b => if_neg fun hcontra => h (congrArg Prod.fst hcontra),
        expect_const]

/-- Pushing a product forward coordinatewise is the product of the
pushforwards. -/
theorem map_product (f : α → γ) (g : β → δ) (μ : FinDist α) (ν : FinDist β) :
    map (Prod.map f g) (product μ ν) = product (map f μ) (map g ν) := by
  rw [product, product, map_bind, bind_map]
  exact bind_congr fun a _ => by rw [map_comp, map_comp]; rfl

/-- Forgetting the second coordinate of a product returns the first factor. -/
theorem map_fst_product (μ : FinDist α) (ν : FinDist β) : map Prod.fst (product μ ν) = μ := by
  rw [product, map_bind]
  refine Eq.trans (bind_congr fun a _ => ?_) (bind_pure μ)
  rw [map_comp]
  exact bind_const ν (pure a)

/-! ## Convex mixing -/

/-- Mix two laws, with weight `t` on the first. The interface is real-valued;
the nonnegative representation stays internal. -/
def mix (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (μ ν : FinDist α) : FinDist α :=
  ⟨⟨fun a => ENNReal.ofReal t * μ.toPMF a + ENNReal.ofReal (1 - t) * ν.toPMF a,
      ENNReal.summable.hasSum_iff.2 (by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
          PMF.tsum_coe, PMF.tsum_coe, mul_one, mul_one,
          ← ENNReal.ofReal_add h0 (by linarith)]
        norm_num)⟩,
    by
      change Set.Finite
        {a | ENNReal.ofReal t * μ.toPMF a + ENNReal.ofReal (1 - t) * ν.toPMF a ≠ 0}
      apply (μ.support_finite.union ν.support_finite).subset
      intro a ha
      simp only [Set.mem_union]
      by_contra h
      push Not at h
      have hμ : μ.toPMF a = 0 := μ.toPMF.apply_eq_zero_iff a |>.2 h.1
      have hν : ν.toPMF a = 0 := ν.toPMF.apply_eq_zero_iff a |>.2 h.2
      exact ha (by simp [hμ, hν])⟩

@[simp]
theorem prob_mix (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (μ ν : FinDist α) (a : α) :
    (mix t h0 h1 μ ν).prob a = t * μ.prob a + (1 - t) * ν.prob a := by
  show (ENNReal.ofReal t * μ.toPMF a + ENNReal.ofReal (1 - t) * ν.toPMF a).toReal = _
  rw [ENNReal.toReal_add
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (PMF.apply_ne_top _ _))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (PMF.apply_ne_top _ _)),
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ 1 - t)]
  rfl

/-- Expectation is affine in the law. -/
theorem expect_mix (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (μ ν : FinDist α) (u : α → ℝ) :
    expect (mix t h0 h1 μ ν) u = t * expect μ u + (1 - t) * expect ν u := by
  unfold expect
  simp_rw [prob_mix, add_mul, mul_assoc]
  rw [Summable.tsum_add ((summable_prob_mul μ u).mul_left _)
      ((summable_prob_mul ν u).mul_left _),
    tsum_mul_left, tsum_mul_left]

/-! ## Dependent finite products

Independent products need finitely many players and nothing else. -/

theorem ennreal_tsum_pi_fin {n : ℕ} {A : Fin n → Type*}
    (g : (i : Fin n) → A i → ENNReal) :
    ∑' s : ((i : Fin n) → A i), ∏ i, g i (s i) = ∏ i, ∑' a, g i a := by
  induction n with
  | zero =>
    haveI : Unique ((i : Fin 0) → A i) := Pi.uniqueOfIsEmpty _
    rw [tsum_eq_single default (fun s hs => absurd (Unique.eq_default s) hs)]
    simp [Finset.prod_eq_one (fun (i : Fin 0) _ => Fin.elim0 i)]
  | succ n ih =>
    let e : A 0 × ((i : Fin n) → A i.succ) ≃ ((i : Fin (n + 1)) → A i) := Fin.consEquiv A
    rw [← e.tsum_eq (f := fun s => ∏ i, g i (s i)), ENNReal.tsum_prod']
    have hsplit (a₀ : A 0) (s' : (i : Fin n) → A i.succ) :
        (∏ i, g i (e (a₀, s') i)) = g 0 a₀ * ∏ i, g i.succ (s' i) := by
      rw [Fin.prod_univ_succ]; rfl
    simp_rw [hsplit, ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_right, ih, Fin.prod_univ_succ]

theorem ennreal_tsum_pi {ι : Type*} [Fintype ι] {A : ι → Type*}
    (g : (i : ι) → A i → ENNReal) :
    ∑' s : ((i : ι) → A i), ∏ i, g i (s i) = ∏ i, ∑' a, g i a := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let ePi : ((j : Fin (Fintype.card ι)) → A (e j)) ≃ ((i : ι) → A i) :=
    Equiv.piCongrLeft A e
  rw [← ePi.tsum_eq (f := fun s => ∏ i, g i (s i))]
  have hprod (t : (j : Fin (Fintype.card ι)) → A (e j)) :
      (∏ i : ι, g i (ePi t i)) = ∏ j, g (e j) (t j) := by
    rw [← e.prod_comp (g := fun i => g i (ePi t i))]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [show (ePi t (e j) : A (e j)) = t j from Equiv.piCongrLeft_apply_apply A e t j]
  simp_rw [hprod]
  rw [ennreal_tsum_pi_fin (A := fun j => A (e j)) (g := fun j a => g (e j) a)]
  rw [← e.prod_comp (g := fun i => ∑' a : A i, g i a)]

section Pi

variable {ι : Type*} [Fintype ι] {A : ι → Type*}

private def pmfPi (μ : ∀ i, PMF (A i)) : PMF (∀ i, A i) :=
  ⟨fun s => ∏ i, μ i (s i),
    ENNReal.summable.hasSum_iff.2 (by
      rw [ennreal_tsum_pi (g := fun i a => μ i a)]
      simp [PMF.tsum_coe])⟩

/-- Independent product of a finite family of finite-support laws. -/
def pi (μ : ∀ i, FinDist (A i)) : FinDist (∀ i, A i) :=
  ⟨pmfPi fun i => (μ i).toPMF, by
    classical
    let embed : (∀ i, {a : A i // a ∈ (μ i).support}) → (∀ i, A i) := fun t i => (t i).1
    letI (i : ι) : Fintype {a : A i // a ∈ (μ i).support} := (μ i).support_finite.fintype
    apply (Set.finite_range embed).subset
    intro s hs
    have hcoord (i : ι) : s i ∈ (μ i).support := by
      intro hnot
      have hz : (μ i).toPMF (s i) = 0 := by simpa [PMF.mem_support_iff] using hnot
      exact hs (Finset.prod_eq_zero (Finset.mem_univ i) hz)
    exact ⟨fun i => ⟨s i, hcoord i⟩, rfl⟩⟩

@[simp]
theorem prob_pi (μ : ∀ i, FinDist (A i)) (s : ∀ i, A i) :
    (pi μ).prob s = ∏ i, (μ i).prob (s i) := by
  show (∏ i, (μ i).toPMF (s i)).toReal = _
  rw [ENNReal.toReal_prod]
  rfl

/-- **A finite product factors at any one coordinate**: the law of a whole tuple
is the law of that coordinate together with an independent law of the rest. This
is the decomposition an argument uses when it has to single out the coordinate
play is about to consult and integrate over the others. -/
theorem pi_eq_map_product [DecidableEq ι] (i : ι) (μ : ∀ j, FinDist (A j)) :
    pi μ = map (Equiv.piSplitAt i A).symm
      (product (μ i) (pi fun j : {j // j ≠ i} => μ j.1)) := by
  classical
  refine ext_of_prob fun s => ?_
  conv_rhs => rw [show s = (Equiv.piSplitAt i A).symm ((Equiv.piSplitAt i A) s) from
    ((Equiv.piSplitAt i A).symm_apply_apply s).symm]
  rw [prob_map_of_injective _ (Equiv.injective _), prob_product, prob_pi, prob_pi,
    Equiv.piSplitAt_apply]
  rw [← Finset.mul_prod_erase Finset.univ (fun j => (μ j).prob (s j)) (Finset.mem_univ i)]
  exact congrArg _ (Finset.prod_subtype (p := fun x => x ≠ i) (Finset.univ.erase i)
    (fun x => by simp) (fun j => (μ j).prob (s j)))

/-- The marginal of an independent product at one coordinate is that
coordinate's own law. -/
theorem map_apply_pi [DecidableEq ι] (i : ι) (μ : ∀ j, FinDist (A j)) :
    map (fun s => s i) (pi μ) = μ i := by
  rw [pi_eq_map_product i μ, map_comp,
    show (fun s => s i) ∘ (Equiv.piSplitAt i A).symm = Prod.fst from funext fun p => by simp]
  exact map_fst_product _ _

/-- An independent draw lands on a tuple exactly when every coordinate is
possible for its own factor. -/
theorem mem_support_pi {μ : ∀ i, FinDist (A i)} {s : ∀ i, A i} :
    s ∈ (pi μ).support ↔ ∀ i, s i ∈ (μ i).support := by
  rw [← prob_pos_iff, prob_pi]
  constructor
  · intro hpos i
    rw [← prob_pos_iff]
    rcases (prob_nonneg (μ i) (s i)).lt_or_eq with hlt | hzero
    · exact hlt
    · exact absurd (Finset.prod_eq_zero (Finset.mem_univ i) hzero.symm) hpos.ne'
  · exact fun hall =>
      Finset.prod_pos fun i _ => prob_pos_iff.mpr (hall i)

@[simp]
theorem pi_pure [DecidableEq ι] (s : ∀ i, A i) :
    pi (fun i => pure (s i)) = pure s := by
  classical
  apply ext
  apply PMF.ext
  intro t
  show (∏ i, (PMF.pure (s i)) (t i)) = PMF.pure s t
  by_cases h : t = s
  · subst h
    simp [PMF.pure_apply]
  · have ⟨i, hi⟩ : ∃ i, t i ≠ s i := by
      by_contra hall
      exact h (funext fun i => not_not.1 (fun hne => hall ⟨i, hne⟩))
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [PMF.pure_apply, hi]),
      PMF.pure_apply]
    simp [h]

end Pi

end FinDist

end GameTheory.Probability
