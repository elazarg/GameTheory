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

open scoped BigOperators NNReal ENNReal

namespace GameTheory.Math.Probability

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

/-- Every law puts mass somewhere. -/
theorem support_nonempty (μ : FinDist α) : μ.support.Nonempty := PMF.support_nonempty _

/-- Every point of the carrier occurs with positive probability. -/
def FullSupport (μ : FinDist α) : Prop :=
  ∀ a, a ∈ μ.support

theorem FullSupport.apply {μ : FinDist α} (h : μ.FullSupport) (a : α) :
    a ∈ μ.support :=
  h a

/-- The finite support as a `Finset`. -/
def supportFinset (μ : FinDist α) : Finset α := μ.support_finite.toFinset

@[simp]
theorem mem_supportFinset {μ : FinDist α} {a : α} :
    a ∈ μ.supportFinset ↔ a ∈ μ.support :=
  Set.Finite.mem_toFinset _

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
theorem map_const (μ : FinDist α) (b : β) : map (fun _ => b) μ = pure b := by
  apply ext
  ext a
  simp [toPMF_map]

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

/-- Two independent finite draws may be sampled in either order. -/
theorem bind_comm (μ : FinDist α) (ν : FinDist β)
    (f : α → β → FinDist γ) :
    μ.bind (fun a => ν.bind (f a)) =
      ν.bind fun b => μ.bind fun a => f a b := by
  apply ext
  simp only [toPMF_bind]
  exact PMF.bind_comm μ.toPMF ν.toPMF
    (fun a b => (f a b).toPMF)

theorem map_eq_bind (f : α → β) (μ : FinDist α) :
    map f μ = bind μ fun a => pure (f a) := rfl

@[simp]
theorem map_id (μ : FinDist α) : map id μ = μ := bind_pure μ

@[simp]
theorem map_comp (g : β → γ) (f : α → β) (μ : FinDist α) :
    map g (map f μ) = map (g ∘ f) μ := by
  simp only [map_eq_bind, bind_bind, pure_bind, Function.comp_def]

/-- Pushforward along an injective function is injective on finite laws. -/
theorem map_injective {f : α → β} (hf : Function.Injective f) :
    Function.Injective (map f) := by
  intro first second hequal
  letI : Nonempty α := ⟨first.support_nonempty.choose⟩
  have hback := congrArg (map (Function.invFun f)) hequal
  rw [map_comp, map_comp] at hback
  have hleft : Function.invFun f ∘ f = id := by
    funext value
    exact Function.leftInverse_invFun hf value
  simpa only [hleft, map_id] using hback

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

/-- Two support-dependent compositions in either order. -/
theorem bindOnSupport_comm (μ : FinDist α) (ν : FinDist β)
    (f : ∀ a ∈ μ.support, ∀ b ∈ ν.support, FinDist γ) :
    (μ.bindOnSupport fun a ha => ν.bindOnSupport (f a ha)) =
      ν.bindOnSupport fun b hb => μ.bindOnSupport fun a ha => f a ha b hb := by
  apply ext
  simp only [toPMF_bindOnSupport]
  exact PMF.bindOnSupport_comm _ _ _

/-- A plain composition passes through a support-dependent one. -/
theorem bind_bindOnSupport_comm (μ : FinDist α) (ν : FinDist β)
    (f : α → ∀ b ∈ ν.support, FinDist γ) :
    (μ.bind fun a => ν.bindOnSupport (f a)) =
      ν.bindOnSupport fun b hb => μ.bind fun a => f a b hb := by
  rw [← bindOnSupport_eq_bind μ fun a => ν.bindOnSupport (f a), bindOnSupport_comm]
  exact bindOnSupport_congr fun b hb => bindOnSupport_eq_bind μ fun a => f a b hb

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

theorem prob_le_one (μ : FinDist α) (a : α) : μ.prob a ≤ 1 := by
  simpa [prob_def] using
    ENNReal.toReal_mono (by simp) (PMF.coe_le_one μ.toPMF a)

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

/-- The uniform finite-support law on a nonempty finite ordinal. -/
def uniformFin (n : ℕ) [NeZero n] : FinDist (Fin n) :=
  ofWeights (fun _ => (n : ℝ)⁻¹)
    (fun _ => inv_nonneg.mpr (Nat.cast_nonneg n))
    (by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact mul_inv_cancel₀ (by exact_mod_cast NeZero.ne n))

@[simp]
theorem prob_uniformFin (n : ℕ) [NeZero n] (t : Fin n) :
    (uniformFin n).prob t = (n : ℝ)⁻¹ :=
  prob_ofWeights ..

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

/-- Expectation under the uniform law on `Fin n` is the finite average. -/
theorem expect_uniformFin {n : ℕ} [NeZero n] (u : Fin n → ℝ) :
    expect (uniformFin n) u = (∑ t, u t) / n := by
  rw [expect_eq_sum]
  simp_rw [prob_uniformFin]
  rw [← Finset.mul_sum]
  simp [div_eq_inv_mul]

/-- A sum over any finite superset of the support computes an expectation. This
is what lets two laws built from the same family be compared term by term over
one shared index set. -/
theorem expect_eq_sum_of_subset (μ : FinDist α) (u : α → ℝ) (s : Finset α)
    (hsub : μ.support ⊆ ↑s) : μ.expect u = ∑ a ∈ s, μ.prob a * u a := by
  classical
  rw [expect_eq_sum_support]
  refine Finset.sum_subset (fun a ha => ?_) (fun a _ hnot => ?_)
  · exact hsub (mem_supportFinset.mp ha)
  · rw [prob_eq_zero_iff.mpr fun hmem => hnot (mem_supportFinset.mpr hmem), zero_mul]

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

theorem expect_sub (μ : FinDist α) (u v : α → ℝ) :
    expect μ (fun a => u a - v a) = expect μ u - expect μ v := by
  unfold expect
  rw [← Summable.tsum_sub (summable_prob_mul μ u) (summable_prob_mul μ v)]
  exact tsum_congr fun a => by ring

/-- A finite sum of integrands commutes with finite-support expectation. -/
theorem expect_sum_comm {κ : Type*} [Fintype κ] (μ : FinDist α) (f : κ → α → ℝ) :
    ∑ i, μ.expect (fun a => f i a) = μ.expect (fun a => ∑ i, f i a) := by
  simp only [expect_eq_sum_support]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ =>
    (Finset.mul_sum Finset.univ (fun i => f i a) (μ.prob a)).symm

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

/-- An expectation is no larger than a bound respected everywhere on the
finite support. -/
theorem expect_le_of_forall (mu : FinDist α) (observable : α → ℝ) (bound : ℝ)
    (hbound : ∀ a ∈ mu.support, observable a ≤ bound) :
    mu.expect observable ≤ bound := by
  refine le_of_le_of_eq (expect_mono hbound) ?_
  exact expect_const mu bound

/-- A pointwise absolute bound on the support bounds finite-support
expectation by the same constant. -/
theorem abs_expect_le_of_abs_bound (μ : FinDist α) (u : α → ℝ) {C : ℝ}
    (h : ∀ a ∈ μ.support, |u a| ≤ C) : |μ.expect u| ≤ C := by
  rw [abs_le]
  constructor
  · have hlower : μ.expect (fun _ => -C) ≤ μ.expect u :=
      expect_mono fun a ha => (abs_le.mp (h a ha)).1
    simpa [expect_const] using hlower
  · have hupper : μ.expect u ≤ μ.expect (fun _ => C) :=
      expect_mono fun a ha => (abs_le.mp (h a ha)).2
    simpa [expect_const] using hupper

/-- Expectation distributes over finite-support `bind`. -/
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

/-- Expectation is monotone branchwise for support-dependent composition.

The continuations may use the evidence that their input occurs. Extending each
one arbitrarily off the support reduces the statement to ordinary
`expect_bind`; the extension is invisible because those inputs have zero mass. -/
theorem expect_bindOnSupport_mono {μ : FinDist α}
    {f g : ∀ a ∈ μ.support, FinDist β} {u : β → ℝ}
    (h : ∀ a (ha : a ∈ μ.support), expect (f a ha) u ≤ expect (g a ha) u) :
    expect (μ.bindOnSupport f) u ≤ expect (μ.bindOnSupport g) u := by
  classical
  obtain ⟨fallback, hfallback⟩ := μ.support_nonempty
  let f' : α → FinDist β := fun a =>
    if ha : a ∈ μ.support then f a ha else f fallback hfallback
  let g' : α → FinDist β := fun a =>
    if ha : a ∈ μ.support then g a ha else g fallback hfallback
  rw [bindOnSupport_eq_bind_of_eq_on_support
      (g := f') (fun a ha => by simp [f', ha]),
    bindOnSupport_eq_bind_of_eq_on_support
      (g := g') (fun a ha => by simp [g', ha]),
    expect_bind, expect_bind]
  exact expect_mono fun a ha => by
    simpa [f', g', ha] using h a ha

/-- Two support-dependent compositions have the same expectation when their
branch expectations agree. The branch laws and their evaluated outcome types
may differ; only the resulting real values are compared. -/
theorem expect_bindOnSupport_congr {μ : FinDist α}
    {f : ∀ a ∈ μ.support, FinDist β} {g : ∀ a ∈ μ.support, FinDist γ}
    {u : β → ℝ} {v : γ → ℝ}
    (h : ∀ a (ha : a ∈ μ.support), expect (f a ha) u = expect (g a ha) v) :
    expect (μ.bindOnSupport f) u = expect (μ.bindOnSupport g) v := by
  classical
  obtain ⟨fallback, hfallback⟩ := μ.support_nonempty
  let f' : α → FinDist β := fun a =>
    if ha : a ∈ μ.support then f a ha else f fallback hfallback
  let g' : α → FinDist γ := fun a =>
    if ha : a ∈ μ.support then g a ha else g fallback hfallback
  rw [bindOnSupport_eq_bind_of_eq_on_support
      (g := f') (fun a ha => by simp [f', ha]),
    bindOnSupport_eq_bind_of_eq_on_support
      (g := g') (fun a ha => by simp [g', ha]),
    expect_bind, expect_bind]
  exact expect_congr fun a ha => by
    simpa [f', g', ha] using h a ha

@[simp]
theorem expect_map (f : α → β) (μ : FinDist α) (u : β → ℝ) :
    expect (map f μ) u = expect μ (fun a => u (f a)) := by
  rw [map_eq_bind, expect_bind]
  simp

/-- Expectation under an independent product, for an arbitrary observable. -/
theorem expect_product (μ : FinDist α) (ν : FinDist β) (u : α × β → ℝ) :
    expect (product μ ν) u = expect μ (fun a => expect ν (fun b => u (a, b))) := by
  rw [product, expect_bind]
  exact expect_congr fun a _ => by rw [expect_map]

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

/-! ## Event probabilities under the finite-law operations -/

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
@[ext]
theorem ext_of_prob {μ ν : FinDist α} (h : ∀ a, μ.prob a = ν.prob a) : μ = ν := by
  refine ext (PMF.ext fun a => ?_)
  exact (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).1 (h a)

/-- A law on a type with only one element is the point mass there. -/
theorem eq_pure_of_subsingleton [Subsingleton α] (μ : FinDist α) (a : α) : μ = pure a := by
  classical
  refine ext_of_prob fun b => ?_
  rw [Subsingleton.elim b a, prob_pure_self]
  have htotal := tsum_prob μ
  rwa [tsum_eq_single a fun c hc => absurd (Subsingleton.elim c a) hc] at htotal

/-- A law supported at one point is that point mass. -/
theorem eq_pure_of_support_subset_singleton (μ : FinDist α) (a : α)
    (hsub : μ.support ⊆ {a}) : μ = pure a := by
  classical
  refine ext_of_prob fun b => ?_
  by_cases hba : b = a
  · subst hba
    rw [prob_pure_self]
    have htotal := tsum_prob μ
    rwa [tsum_eq_single b fun c hca => by
      rw [prob_eq_zero_iff]
      intro hc
      exact hca (Set.mem_singleton_iff.mp (hsub hc))] at htotal
  · rw [prob_pure_of_ne hba, prob_eq_zero_iff]
    intro hb
    exact hba (Set.mem_singleton_iff.mp (hsub hb))

/-- Branches agreeing on the support give the same `bind`. -/
theorem bind_congr {μ : FinDist α} {f g : α → FinDist β}
    (h : ∀ a ∈ μ.support, f a = g a) : μ.bind f = μ.bind g := by
  refine ext_of_prob fun b => ?_
  rw [prob_bind, prob_bind]
  exact expect_congr fun a ha => by rw [h a ha]

/-- Pushforwards agree when their functions agree everywhere the source law
can actually draw. -/
theorem map_congr_of_eq_on_support {μ : FinDist α} {f g : α → β}
    (h : ∀ a ∈ μ.support, f a = g a) : μ.map f = μ.map g := by
  rw [map_eq_bind, map_eq_bind]
  exact bind_congr fun a ha => by rw [h a ha]

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

/-- Tagging the output of a dependent kernel retains exactly the selected
outer point mass and its conditional point mass. -/
theorem prob_bind_map_prod
    (outer : FinDist α) (kernel : α → FinDist β) (a : α) (b : β) :
    (outer.bind fun candidate =>
      (kernel candidate).map fun value => (candidate, value)).prob (a, b) =
      outer.prob a * (kernel a).prob b := by
  classical
  rw [prob_bind]
  calc
    outer.expect (fun candidate =>
        ((kernel candidate).map fun value => (candidate, value)).prob
          (a, b)) =
        outer.expect (fun candidate =>
          if a = candidate then (kernel a).prob b else 0) := by
      apply expect_congr
      intro candidate _
      by_cases h : a = candidate
      · subst candidate
        rw [if_pos rfl]
        exact prob_map_of_injective
          (fun value => (a, value)) (fun _ _ hxy => (Prod.mk.inj hxy).2)
          (kernel a) b
      · rw [if_neg h, prob_eq_zero_iff]
        intro hsupport
        rw [support_map] at hsupport
        obtain ⟨value, _, hvalue⟩ := hsupport
        exact h (congrArg Prod.fst hvalue).symm
    _ = outer.prob a * (kernel a).prob b := by
      rw [expect_ite_eq]

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

/-! Product algebra. -/

/-- Forgetting the first coordinate of a product returns the second factor. -/
@[simp]
theorem map_snd_product (μ : FinDist α) (ν : FinDist β) :
    map Prod.snd (product μ ν) = ν := by
  rw [product, map_bind]
  refine Eq.trans (bind_congr fun a _ => ?_) (bind_const μ ν)
  rw [map_comp]
  rw [show Prod.snd ∘ (fun b => (a, b)) = id from by funext b; rfl, map_id]

/-- Pairing a law with a point mass is the corresponding graph pushforward. -/
@[simp]
theorem product_pure_right (μ : FinDist α) (b : β) :
    product μ (pure b) = map (fun a => (a, b)) μ := by
  rw [product, map_eq_bind]
  apply bind_congr
  intro a _
  rw [map_eq_bind, pure_bind]

/-- Reassociating a left-nested independent product gives a right-nested one. -/
theorem map_assoc_product (μ : FinDist α) (ν : FinDist β) (ξ : FinDist γ) :
    map (fun p : (α × β) × γ => (p.1.1, (p.1.2, p.2)))
        (product (product μ ν) ξ) = product μ (product ν ξ) := by
  rw [product, map_bind]
  simp only [map_comp, Function.comp_def]
  rw [product, bind_bind]
  rw [product, product]
  simp only [map_bind, map_comp]
  apply bind_congr
  intro a _
  rw [bind_map]
  apply bind_congr
  intro b _
  rfl

/-! ## Conditioning

A law restricted to an event it gives positive mass, renormalized. This is built
by hand rather than through Mathlib's `PMF.filter`, which lives in a module this
one deliberately does not import: taking that import would put convexity and
polynomial theory back into the closure of everything downstream, which is the
dependency this module exists to keep narrow. The construction below needs only
the probability monad. -/

private def massOf (μ : FinDist α) (S : Set α) : ℝ≥0∞ := ∑' a, S.indicator μ.toPMF a

private theorem massOf_le_one (μ : FinDist α) (S : Set α) : massOf μ S ≤ 1 :=
  le_trans (ENNReal.tsum_le_tsum fun a => Set.indicator_le_self' (fun _ _ => bot_le) a)
    (le_of_eq μ.toPMF.tsum_coe)

private theorem massOf_ne_top (μ : FinDist α) (S : Set α) : massOf μ S ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (massOf_le_one μ S)

private theorem massOf_ne_zero {μ : FinDist α} {S : Set α}
    (hmeet : ∃ a ∈ S, a ∈ μ.support) : massOf μ S ≠ 0 := by
  obtain ⟨a, haS, hasupp⟩ := hmeet
  intro hzero
  rw [massOf, ENNReal.tsum_eq_zero] at hzero
  exact hasupp (by simpa [Set.indicator_of_mem haS] using hzero a)

/-- The mass an event carries. -/
def probOf (μ : FinDist α) (S : Set α) : ℝ := (massOf μ S).toReal

/-- A law restricted to an event it gives positive mass, renormalized. -/
def condOn (μ : FinDist α) (S : Set α) (hmeet : ∃ a ∈ S, a ∈ μ.support) : FinDist α :=
  ⟨⟨fun a => S.indicator μ.toPMF a / massOf μ S, by
      rw [ENNReal.summable.hasSum_iff]
      simp_rw [div_eq_mul_inv]
      rw [ENNReal.tsum_mul_right]
      exact ENNReal.mul_inv_cancel (massOf_ne_zero hmeet) (massOf_ne_top μ S)⟩, by
    refine μ.support_finite.subset fun a ha => ?_
    by_contra hnot
    refine ha ?_
    have hzero : S.indicator μ.toPMF a = 0 := by
      by_cases haS : a ∈ S
      · rw [Set.indicator_of_mem haS]
        exact (PMF.apply_eq_zero_iff _ _).mpr hnot
      · rw [Set.indicator_of_notMem haS]
    show S.indicator μ.toPMF a / massOf μ S = 0
    rw [hzero, ENNReal.zero_div]⟩

theorem probOf_pos {μ : FinDist α} {S : Set α} (hmeet : ∃ a ∈ S, a ∈ μ.support) :
    0 < μ.probOf S :=
  ENNReal.toReal_pos (massOf_ne_zero hmeet) (massOf_ne_top μ S)

theorem prob_condOn (μ : FinDist α) (S : Set α) (hmeet : ∃ a ∈ S, a ∈ μ.support)
    [DecidablePred (· ∈ S)] (a : α) :
    (μ.condOn S hmeet).prob a = if a ∈ S then μ.prob a / μ.probOf S else 0 := by
  show (S.indicator μ.toPMF a / massOf μ S).toReal = _
  rw [div_eq_mul_inv, ENNReal.toReal_mul, ENNReal.toReal_inv]
  by_cases haS : a ∈ S
  · rw [if_pos haS, Set.indicator_of_mem haS, probOf, div_eq_mul_inv, prob_def]
  · rw [if_neg haS, Set.indicator_of_notMem haS]
    simp

theorem support_condOn (μ : FinDist α) (S : Set α) (hmeet : ∃ a ∈ S, a ∈ μ.support) :
    (μ.condOn S hmeet).support ⊆ S ∩ μ.support := by
  classical
  intro a ha
  have hpos : 0 < (μ.condOn S hmeet).prob a := prob_pos_iff.mpr ha
  rw [prob_condOn] at hpos
  by_cases haS : a ∈ S
  · rw [if_pos haS] at hpos
    refine ⟨haS, prob_pos_iff.mp ?_⟩
    rcases (prob_nonneg μ a).lt_or_eq with hlt | hzero
    · exact hlt
    · rw [← hzero, zero_div] at hpos
      exact absurd hpos (lt_irrefl 0)
  · rw [if_neg haS] at hpos
    exact absurd hpos (lt_irrefl 0)

/-- Conditioning on everything changes nothing. -/
theorem condOn_univ (μ : FinDist α) (hmeet : ∃ a ∈ Set.univ, a ∈ μ.support) :
    μ.condOn Set.univ hmeet = μ := by
  classical
  refine ext_of_prob fun a => ?_
  have hmass : μ.probOf Set.univ = 1 := by
    show (massOf μ Set.univ).toReal = 1
    rw [massOf]
    simp [μ.toPMF.tsum_coe]
  rw [prob_condOn, if_pos (Set.mem_univ a), hmass, div_one]

theorem probOf_pure_self [DecidableEq α] (a : α) (S : Set α) (ha : a ∈ S) :
    (pure a).probOf S = 1 := by
  show (massOf (pure a) S).toReal = 1
  rw [massOf, tsum_eq_single a fun b hb => by
    simp [toPMF_pure, PMF.pure_apply, hb]]
  simp [Set.indicator_of_mem ha, toPMF_pure, PMF.pure_apply]

/-- Conditioning a point mass changes nothing: whatever event it is compatible
with, it is still that point. -/
theorem condOn_pure (a : α) (S : Set α) (hmeet : ∃ b ∈ S, b ∈ (pure a).support) :
    (pure a).condOn S hmeet = pure a := by
  classical
  obtain ⟨b, hbS, hbmem⟩ := hmeet
  rw [mem_support_pure] at hbmem
  subst hbmem
  refine ext_of_prob fun x => ?_
  rw [prob_condOn, probOf_pure_self b S hbS, div_one]
  by_cases hxS : x ∈ S
  · rw [if_pos hxS]
  · rw [if_neg hxS, prob_pure_eq_ite, if_neg]
    exact fun hxb => hxS (by rw [hxb]; exact hbS)

private theorem massOf_eq_one_of_support_subset {μ : FinDist α} {S : Set α}
    (hsub : μ.support ⊆ S) : massOf μ S = 1 := by
  rw [massOf, tsum_congr fun a => ?_, μ.toPMF.tsum_coe]
  by_cases haS : a ∈ S
  · rw [Set.indicator_of_mem haS]
  · rw [Set.indicator_of_notMem haS]
    exact ((PMF.apply_eq_zero_iff _ _).mpr fun hmem => haS (hsub hmem)).symm

/-- A law already carried by an event is unchanged by conditioning on it. -/
theorem condOn_of_support_subset (μ : FinDist α) (S : Set α) (hmeet : ∃ a ∈ S, a ∈ μ.support)
    (hsub : μ.support ⊆ S) : μ.condOn S hmeet = μ := by
  refine ext (PMF.ext fun a => ?_)
  show S.indicator μ.toPMF a / massOf μ S = μ.toPMF a
  rw [massOf_eq_one_of_support_subset hsub, div_one]
  by_cases haS : a ∈ S
  · rw [Set.indicator_of_mem haS]
  · rw [Set.indicator_of_notMem haS]
    exact ((PMF.apply_eq_zero_iff _ _).mpr fun hmem => haS (hsub hmem)).symm

private theorem massOf_condOn {μ : FinDist α} {C D : Set α} (hC : ∃ a ∈ C, a ∈ μ.support)
    (hDC : D ∩ μ.support ⊆ C) : massOf (μ.condOn C hC) D = massOf μ D / massOf μ C := by
  rw [massOf, massOf]
  simp_rw [div_eq_mul_inv]
  rw [← ENNReal.tsum_mul_right]
  refine tsum_congr fun a => ?_
  by_cases haD : a ∈ D
  · rw [Set.indicator_of_mem haD, Set.indicator_of_mem haD]
    show C.indicator μ.toPMF a * (massOf μ C)⁻¹ = _
    by_cases hasupp : a ∈ μ.support
    · rw [Set.indicator_of_mem (hDC ⟨haD, hasupp⟩)]
    · rw [(PMF.apply_eq_zero_iff _ _).mpr hasupp, Set.indicator_apply_eq_zero.mpr
        fun _ => (PMF.apply_eq_zero_iff _ _).mpr hasupp, zero_mul]
  · rw [Set.indicator_of_notMem haD, Set.indicator_of_notMem haD, zero_mul]

/-- Conditioning measures an event by intersecting it with the conditioning
event and renormalizing. -/
theorem probOf_condOn_eq_inter {μ : FinDist α} {C D : Set α}
    (hC : ∃ a ∈ C, a ∈ μ.support) :
    (μ.condOn C hC).probOf D = μ.probOf (C ∩ D) / μ.probOf C := by
  have hmass :
      massOf (μ.condOn C hC) D = massOf μ (C ∩ D) / massOf μ C := by
    rw [massOf, massOf]
    simp_rw [div_eq_mul_inv]
    rw [← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro a
    show D.indicator (fun x => C.indicator μ.toPMF x / massOf μ C) a =
      (C ∩ D).indicator μ.toPMF a * (massOf μ C)⁻¹
    by_cases haC : a ∈ C <;> by_cases haD : a ∈ D <;>
      simp [haC, haD, div_eq_mul_inv]
  show (massOf (μ.condOn C hC) D).toReal = _
  rw [hmass, ENNReal.toReal_div]
  rfl

/-- Conditioning keeps everything the event allows. -/
theorem mem_support_condOn (μ : FinDist α) (S : Set α) (hmeet : ∃ a ∈ S, a ∈ μ.support)
    {a : α} (haS : a ∈ S) (ha : a ∈ μ.support) : a ∈ (μ.condOn S hmeet).support := by
  classical
  refine prob_pos_iff.mp ?_
  rw [prob_condOn, if_pos haS]
  exact div_pos (prob_pos_iff.mpr ha) (probOf_pos hmeet)

/-- Conditioning depends on the event, not on the proof that it has mass. -/
theorem condOn_congr (μ : FinDist α) {S T : Set α} (hST : S = T)
    (hS : ∃ a ∈ S, a ∈ μ.support) (hT : ∃ a ∈ T, a ∈ μ.support) :
    μ.condOn S hS = μ.condOn T hT := by
  subst hST; rfl

/-- The mass a smaller event keeps after conditioning on a larger one. -/
theorem probOf_condOn {μ : FinDist α} {C D : Set α} (hC : ∃ a ∈ C, a ∈ μ.support)
    (hDC : D ∩ μ.support ⊆ C) : (μ.condOn C hC).probOf D = μ.probOf D / μ.probOf C := by
  show (massOf (μ.condOn C hC) D).toReal = _
  rw [massOf_condOn hC hDC, ENNReal.toReal_div]
  rfl

/-- **Conditioning again on a smaller event forgets the first one.** This is what
lets an argument that keeps conditioning as play advances go on referring to the
law it started from.

The smaller event need only be smaller *where the law lives*: what a law does
outside its own support is not something conditioning can see. -/
theorem condOn_condOn (μ : FinDist α) {C D : Set α} (hC : ∃ a ∈ C, a ∈ μ.support)
    (hD : ∃ a ∈ D, a ∈ μ.support) (hDC : D ∩ μ.support ⊆ C)
    (hDcond : ∃ a ∈ D, a ∈ (μ.condOn C hC).support) :
    (μ.condOn C hC).condOn D hDcond = μ.condOn D hD := by
  classical
  refine ext_of_prob fun a => ?_
  rw [prob_condOn, prob_condOn, prob_condOn, probOf_condOn hC hDC]
  by_cases haD : a ∈ D
  · rw [if_pos haD, if_pos haD]
    by_cases hasupp : a ∈ μ.support
    · rw [if_pos (hDC ⟨haD, hasupp⟩)]
      have hc := (probOf_pos hC).ne'
      have hd := (probOf_pos hD).ne'
      field_simp
    · simp [prob_eq_zero_iff.mpr hasupp]
  · rw [if_neg haD, if_neg haD]

/-- An event's mass is the expectation of its indicator, which is how a
conditioning meets the real-valued interface. -/
theorem expect_indicator_eq_probOf (μ : FinDist α) (S : Set α) [DecidablePred (· ∈ S)] :
    (μ.expect fun a => if a ∈ S then 1 else 0) = μ.probOf S := by
  show ∑' a, μ.prob a * (if a ∈ S then 1 else 0) = (massOf μ S).toReal
  rw [massOf, ENNReal.tsum_toReal_eq fun a => ?_]
  · refine tsum_congr fun a => ?_
    by_cases haS : a ∈ S
    · rw [if_pos haS, mul_one, Set.indicator_of_mem haS, prob_def]
    · rw [if_neg haS, mul_zero, Set.indicator_of_notMem haS, ENNReal.toReal_zero]
  · by_cases haS : a ∈ S
    · rw [Set.indicator_of_mem haS]
      exact PMF.apply_ne_top _ _
    · rw [Set.indicator_of_notMem haS]
      exact ENNReal.zero_ne_top

/-- Event probability on a singleton is the corresponding point mass. -/
theorem probOf_singleton (μ : FinDist α) (a : α) :
    μ.probOf ({a} : Set α) = μ.prob a := by
  classical
  rw [← expect_indicator_eq_probOf]
  unfold expect
  rw [tsum_eq_single a]
  · simp
  · intro b hba
    simp [hba]

/-- A pushforward assigns an event the mass of its preimage. -/
theorem probOf_map (f : α → β) (μ : FinDist α) (S : Set β) :
    (map f μ).probOf S = μ.probOf (f ⁻¹' S) := by
  classical
  rw [← expect_indicator_eq_probOf, ← expect_indicator_eq_probOf, expect_map]
  exact expect_congr fun a _ => by
    by_cases h : f a ∈ S <;> simp [h]

/-- A pushforward's point mass is the source mass of its singleton preimage. -/
theorem prob_map_eq_probOf_preimage_singleton (f : α → β) (μ : FinDist α) (b : β) :
    (map f μ).prob b = μ.probOf (f ⁻¹' ({b} : Set β)) := by
  rw [← probOf_singleton, probOf_map]

/-- The probability of a finite set is the ordinary sum of its point masses. -/
theorem probOf_finset_eq_sum [DecidableEq α] (μ : FinDist α) (S : Finset α) :
    μ.probOf (S : Set α) = ∑ a ∈ S, μ.prob a := by
  rw [← expect_indicator_eq_probOf]
  unfold expect
  rw [tsum_eq_sum (s := S)]
  · simp
  · intro a ha
    simp [ha]

/-- Conditioning rescales the expectation of an observable that vanishes off
the conditioning event. -/
theorem expect_condOn_eq_div_of_eq_zero_off (μ : FinDist α) (S : Set α)
    (hmeet : ∃ a ∈ S, a ∈ μ.support) (u : α → ℝ)
    (hzero : ∀ a ∈ μ.support, a ∉ S → u a = 0) :
    (μ.condOn S hmeet).expect u = μ.expect u / μ.probOf S := by
  classical
  rw [expect_eq_sum_of_subset (μ.condOn S hmeet) u μ.supportFinset, expect_eq_sum_support,
    div_eq_mul_inv, Finset.sum_mul]
  · refine Finset.sum_congr rfl fun a ha => ?_
    rw [prob_condOn]
    by_cases haS : a ∈ S
    · rw [if_pos haS]
      ring
    · rw [if_neg haS, zero_mul, hzero a (mem_supportFinset.mp ha) haS, mul_zero]
      simp
  · intro a ha
    apply mem_supportFinset.mpr
    exact (support_condOn μ S hmeet ha).2

/-- If two observables have ordered global expectations and agree away from a
positive-mass event, their conditional expectations on that event are ordered.

This is the finite-support form of the cancellation used by conditional
obedience: all mass outside the observed event contributes equally to both
global expectations. -/
theorem expect_condOn_le_of_expect_le_of_eq_off (μ : FinDist α) (S : Set α)
    (hmeet : ∃ a ∈ S, a ∈ μ.support) {f g : α → ℝ}
    (hle : μ.expect f ≤ μ.expect g)
    (heq : ∀ a ∈ μ.support, a ∉ S → f a = g a) :
    (μ.condOn S hmeet).expect f ≤ (μ.condOn S hmeet).expect g := by
  apply sub_nonpos.mp
  rw [← expect_sub]
  rw [expect_condOn_eq_div_of_eq_zero_off]
  · exact div_nonpos_of_nonpos_of_nonneg (by simpa [expect_sub] using sub_nonpos.mpr hle)
      (le_of_lt (probOf_pos hmeet))
  · intro a ha haS
    exact sub_eq_zero.mpr (heq a ha haS)

open Classical in
/-- The law restricted to the fibre of `f` over `b`, or the law itself where
that fibre carries no mass. The fallback is never reached along a draw, and
naming it here keeps the disintegration below a total `bind`. -/
noncomputable def condOnFibre (μ : FinDist α) (f : α → β) (b : β) : FinDist α :=
  if hfibre : ∃ a ∈ f ⁻¹' {b}, a ∈ μ.support then μ.condOn (f ⁻¹' {b}) hfibre else μ

/-- **Disintegration.** Drawing from a law is drawing its image and then drawing
from what remains. This is how a conditioning is introduced with nothing
assumed: one draw becomes an observed part and a conditioned remainder. -/
theorem eq_bind_condOnFibre (μ : FinDist α) (f : α → β) :
    μ = (map f μ).bind (μ.condOnFibre f) := by
  classical
  refine ext_of_prob fun x => ?_
  rw [prob_bind, expect_map]
  symm
  by_cases hx : x ∈ μ.support
  · have hfibre : ∃ a ∈ f ⁻¹' {f x}, a ∈ μ.support := ⟨x, rfl, hx⟩
    refine Eq.trans (expect_congr (v := fun a =>
      μ.prob x / μ.probOf (f ⁻¹' {f x}) * (if a ∈ f ⁻¹' {f x} then 1 else 0)) ?_) ?_
    · intro a ha
      by_cases hfa : a ∈ f ⁻¹' {f x}
      · have hfa' : f a = f x := hfa
        rw [if_pos hfa, mul_one, condOnFibre, hfa', dif_pos hfibre, prob_condOn]
        exact if_pos (Set.mem_preimage.mpr rfl)
      · rw [if_neg hfa, mul_zero, condOnFibre, dif_pos ⟨a, Set.mem_preimage.mpr rfl, ha⟩,
          prob_condOn, if_neg]
        exact fun hmem => hfa (Set.mem_preimage.mpr (Set.mem_preimage.mp hmem).symm)
    · rw [expect_smul, expect_indicator_eq_probOf, div_mul_cancel₀ _ (probOf_pos hfibre).ne']
  · have hzero : μ.prob x = 0 := prob_eq_zero_iff.mpr hx
    rw [hzero]
    refine Eq.trans (expect_congr (v := fun _ => (0 : ℝ)) ?_) (expect_const μ 0)
    intro a _
    rw [condOnFibre]
    split
    · rw [prob_condOn]
      split
      · rw [hzero, zero_div]
      · rfl
    · exact hzero

/-- An expectation is *strictly* below a bound as soon as one point of positive
mass is. -/
theorem expect_lt_of_mem_support (μ : FinDist α) (observable : α → ℝ) (bound : ℝ)
    (hle : ∀ a ∈ μ.support, observable a ≤ bound) {witness : α}
    (hwitness : witness ∈ μ.support) (hlt : observable witness < bound) :
    μ.expect observable < bound := by
  classical
  rw [expect_eq_sum_support]
  have hsum : ∑ a ∈ μ.supportFinset, μ.prob a * bound = bound := by
    rw [← Finset.sum_mul, sum_prob_supportFinset, one_mul]
  rw [← hsum]
  refine Finset.sum_lt_sum (fun a ha =>
    mul_le_mul_of_nonneg_left (hle a (mem_supportFinset.mp ha)) (prob_nonneg μ a)) ?_
  exact ⟨witness, mem_supportFinset.mpr hwitness,
    mul_lt_mul_of_pos_left hlt (prob_pos_iff.mpr hwitness)⟩

/-- **An average that attains its bound attains it everywhere it looks.** If no
point of the support beats `bound` and the expectation equals it, every point of
the support equals it. -/
theorem eq_of_expect_eq_of_le (μ : FinDist α) (observable : α → ℝ) (bound : ℝ)
    (hle : ∀ a ∈ μ.support, observable a ≤ bound) (hexpect : μ.expect observable = bound)
    {a : α} (ha : a ∈ μ.support) : observable a = bound := by
  by_contra hne
  exact absurd hexpect
    (ne_of_lt (expect_lt_of_mem_support μ observable bound hle ha
      (lt_of_le_of_ne (hle a ha) hne)))

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

@[simp]
theorem mix_self (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (μ : FinDist α) :
    mix t h0 h1 μ μ = μ := by
  apply ext_of_prob
  intro a
  rw [prob_mix]
  ring

@[simp]
theorem mix_zero (μ ν : FinDist α) : mix 0 le_rfl (by norm_num) μ ν = ν := by
  apply ext_of_prob
  intro a
  rw [prob_mix]
  ring

@[simp]
theorem mix_one (μ ν : FinDist α) : mix 1 (by norm_num) le_rfl μ ν = μ := by
  apply ext_of_prob
  intro a
  rw [prob_mix]
  ring

/-- Swapping mixture branches replaces the weight by its complement. -/
theorem mix_swap (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (μ ν : FinDist α) :
    mix t h0 h1 μ ν = mix (1 - t) (by linarith) (by linarith) ν μ := by
  apply ext_of_prob
  intro a
  simp only [prob_mix]
  ring

/-- A point in the first law's support remains supported by a mixture with
positive first weight. -/
theorem mem_support_mix_left (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (ht : 0 < t) {μ ν : FinDist α} {a : α} (ha : a ∈ μ.support) :
    a ∈ (mix t h0 h1 μ ν).support := by
  rw [← prob_pos_iff, prob_mix]
  exact add_pos_of_pos_of_nonneg
    (mul_pos ht (prob_pos_iff.mpr ha))
    (mul_nonneg (by linarith) (prob_nonneg ν a))

/-- A point in the second law's support remains supported by a mixture whose
second weight is positive. -/
theorem mem_support_mix_right (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (ht : t < 1) {μ ν : FinDist α} {a : α} (ha : a ∈ ν.support) :
    a ∈ (mix t h0 h1 μ ν).support := by
  rw [← prob_pos_iff, prob_mix]
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg h0 (prob_nonneg μ a))
    (mul_pos (sub_pos.mpr ht) (prob_pos_iff.mpr ha))

/-- With both weights positive, the support of a mixture is exactly the union
of the two supports. -/
theorem mem_support_mix_iff (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (ht0 : 0 < t) (ht1 : t < 1) {μ ν : FinDist α} {a : α} :
    a ∈ (mix t h0 h1 μ ν).support ↔ a ∈ μ.support ∨ a ∈ ν.support := by
  constructor
  · intro ha
    by_contra hmem
    have hμ : a ∉ μ.support := fun h => hmem (Or.inl h)
    have hν : a ∉ ν.support := fun h => hmem (Or.inr h)
    rw [← prob_pos_iff, prob_mix, prob_eq_zero_iff.mpr hμ,
      prob_eq_zero_iff.mpr hν] at ha
    linarith
  · rintro (ha | ha)
    · exact mem_support_mix_left t h0 h1 ht0 ha
    · exact mem_support_mix_right t h0 h1 ht1 ha

/-- A nondegenerate mixture of two point masses supports exactly its named
points. -/
theorem mem_support_mix_pure_iff [DecidableEq α]
    (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (ht0 : 0 < t) (ht1 : t < 1)
    (first second a : α) :
    a ∈ (mix t h0 h1 (pure first) (pure second)).support ↔
      a = first ∨ a = second := by
  rw [mem_support_mix_iff t h0 h1 ht0 ht1,
    mem_support_pure, mem_support_pure]

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

private theorem ennreal_tsum_pi_fin {n : ℕ} {A : Fin n → Type*}
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

private theorem ennreal_tsum_pi {ι : Type*} [Fintype ι] {A : ι → Type*}
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

/-- Composition is affine in the law it composes with: mixing before a
continuation is mixing after it. This is what makes a set defined by comparing
`bind`s convex. -/
theorem mix_bind (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (μ ν : FinDist α) (f : α → FinDist β) :
    (mix t h0 h1 μ ν).bind f = mix t h0 h1 (μ.bind f) (ν.bind f) := by
  classical
  refine ext_of_prob fun b => ?_
  rw [prob_bind, prob_mix, prob_bind, prob_bind, expect_mix]

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

/-- Independent product of a `Fin`-indexed family, assembled in increasing
coordinate order. -/
def piFin : {n : ℕ} → {A : Fin n → Type*} →
    ((i : Fin n) → FinDist (A i)) → FinDist ((i : Fin n) → A i)
  | 0, _, _ => pure fun i => Fin.elim0 i
  | _ + 1, A, μ =>
    map (Fin.consEquiv A)
      (product (μ 0) (piFin fun i => μ i.succ))

@[simp]
theorem prob_pi (μ : ∀ i, FinDist (A i)) (s : ∀ i, A i) :
    (pi μ).prob s = ∏ i, (μ i).prob (s i) := by
  show (∏ i, (μ i).toPMF (s i)).toReal = _
  rw [ENNReal.toReal_prod]
  rfl

/-- The explicit ordered product agrees with the finite independent product. -/
theorem piFin_eq_pi : ∀ {n : ℕ} {A : Fin n → Type*}
    (μ : (i : Fin n) → FinDist (A i)), piFin μ = pi μ
  | 0, A, μ => by
    classical
    apply ext_of_prob
    intro s
    have hs : s = fun i => Fin.elim0 i := funext fun i => Fin.elim0 i
    subst s
    rw [piFin, prob_pure_eq_ite, prob_pi]
    simp
  | n + 1, A, μ => by
    classical
    let e : A 0 × ((i : Fin n) → A i.succ) ≃ ((i : Fin (n + 1)) → A i) := Fin.consEquiv A
    apply ext_of_prob
    intro s
    conv_lhs => rw [show s = e (e.symm s) from (e.apply_symm_apply s).symm]
    rw [piFin, prob_map_of_injective e e.injective, prob_product,
      piFin_eq_pi, prob_pi, prob_pi]
    simpa [e, Fin.tail] using (Fin.prod_univ_succ fun i => (μ i).prob (s i)).symm

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

/-- The mass of a product event under independent draws is the product of the
masses — the statement that conditioning on each coordinate separately is
conditioning on all of them together. -/
theorem probOf_pi (μ : ∀ i, FinDist (A i)) (C : ∀ i, Set (A i)) :
    (pi μ).probOf { s | ∀ i, s i ∈ C i } = ∏ i, (μ i).probOf (C i) := by
  classical
  have hmass : massOf (pi μ) { s | ∀ i, s i ∈ C i } = ∏ i, massOf (μ i) (C i) := by
    simp only [massOf]
    rw [← ennreal_tsum_pi fun i a => (C i).indicator (μ i).toPMF a]
    refine tsum_congr fun s => ?_
    by_cases hevery : ∀ i, s i ∈ C i
    · rw [Set.indicator_of_mem (show s ∈ { s | ∀ i, s i ∈ C i } from hevery)]
      exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (hevery i) _).symm
    · obtain ⟨i, hi⟩ := not_forall.mp hevery
      rw [Set.indicator_of_notMem (show ¬ s ∈ { s | ∀ i, s i ∈ C i } from hevery),
        Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)]
  show (massOf (pi μ) _).toReal = _
  rw [hmass, ENNReal.toReal_prod]
  rfl

/-- **Independent draws stay independent under conditioning on a product
event.** Each coordinate is conditioned on its own event and nothing couples
them, which is what lets a per-player conditioning be assembled into one. -/
theorem condOn_pi (μ : ∀ i, FinDist (A i)) (C : ∀ i, Set (A i))
    (hcoord : ∀ i, ∃ a ∈ C i, a ∈ (μ i).support)
    (hall : ∃ s ∈ { s | ∀ i, s i ∈ C i }, s ∈ (pi μ).support) :
    (pi μ).condOn { s | ∀ i, s i ∈ C i } hall = pi fun i => (μ i).condOn (C i) (hcoord i) := by
  classical
  refine ext_of_prob fun s => ?_
  rw [prob_condOn, prob_pi, probOf_pi]
  by_cases hmem : ∀ i, s i ∈ C i
  · rw [if_pos (show s ∈ { s | ∀ i, s i ∈ C i } from hmem), prob_pi, ← Finset.prod_div_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [prob_condOn, if_pos (hmem i)]
  · obtain ⟨i, hi⟩ := not_forall.mp hmem
    rw [if_neg (show ¬ s ∈ { s | ∀ i, s i ∈ C i } from hmem), prob_pi,
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [prob_condOn, if_neg hi])]

theorem support_pi_subset [DecidableEq ι] (μ : ∀ i, FinDist (A i)) :
    (pi μ).support ⊆ ↑(Fintype.piFinset fun i => (μ i).supportFinset) := by
  classical
  intro s hs
  simp only [Finset.mem_coe, Fintype.mem_piFinset, mem_supportFinset]
  exact mem_support_pi.mp hs

/-- **Independent products commute with inverse coordinate reindexing.**
The dependent transports induced by the index equivalence remain contained in
`Equiv.piCongrLeft'`; callers see an equality of ordinary finite laws. -/
theorem pi_unreindex {κ : Type*} [Fintype κ] (A : ι → Type*)
    (equiv : ι ≃ κ)
    (laws : (target : κ) → FinDist (A (equiv.symm target))) :
    map (Equiv.piCongrLeft' A equiv).symm (pi laws) =
      pi ((Equiv.piCongrLeft' (fun player => FinDist (A player)) equiv).symm laws) := by
  classical
  let profileEquiv := Equiv.piCongrLeft' A equiv
  let lawEquiv :=
    Equiv.piCongrLeft' (fun player => FinDist (A player)) equiv
  apply ext_of_prob
  intro source
  have htarget :
      source = profileEquiv.symm (profileEquiv source) :=
    (profileEquiv.symm_apply_apply source).symm
  conv_lhs => rw [htarget]
  rw [prob_map_of_injective profileEquiv.symm
      profileEquiv.symm.injective,
    prob_pi, prob_pi,
    ← equiv.prod_comp
      (g := fun target => (laws target).prob (profileEquiv source target))]
  apply Finset.prod_congr rfl
  intro player _
  obtain ⟨target, rfl⟩ := equiv.symm.surjective player
  simp [profileEquiv]
  rw [equiv.apply_symm_apply target]

/-- **Independent products commute with forward coordinate reindexing.**
This orientation exposes the target family as ordinary composition with the
equivalence, which is the form used by serialization consumers. -/
theorem pi_reindex {κ : Type*} [Fintype κ] (A : ι → Type*)
    (equiv : κ ≃ ι) (laws : (source : ι) → FinDist (A source)) :
    map (Equiv.piCongrLeft A equiv).symm (pi laws) =
      pi (fun target => laws (equiv target)) := by
  classical
  apply ext_of_prob
  intro target
  let profileEquiv := Equiv.piCongrLeft A equiv
  have htarget :
      target = profileEquiv.symm (profileEquiv target) :=
    (profileEquiv.symm_apply_apply target).symm
  conv_lhs => rw [htarget]
  rw [prob_map_of_injective profileEquiv.symm
      profileEquiv.symm.injective,
    prob_pi, prob_pi,
    ← equiv.prod_comp
      (g := fun source => (laws source).prob (profileEquiv target source))]
  apply Finset.prod_congr rfl
  intro player _
  simp [profileEquiv]

/-- **Independent draws commute with coordinatewise pushforward.** Drawing a
tuple and then relabelling each coordinate is drawing from the relabelled
factors. -/
theorem pi_map {B : ι → Type*} (f : ∀ i, A i → B i) (μ : ∀ i, FinDist (A i)) :
    pi (fun i => map (f i) (μ i)) = map (fun s i => f i (s i)) (pi μ) := by
  classical
  refine ext_of_prob fun t => ?_
  rw [prob_pi, prob_map,
    expect_eq_sum_of_subset _ _ (Fintype.piFinset fun i => (μ i).supportFinset)
      (support_pi_subset μ),
    show (fun i => (map (f i) (μ i)).prob (t i)) =
        fun i => ∑ a ∈ (μ i).supportFinset, (μ i).prob a * (if t i = f i a then 1 else 0) from
      funext fun i => by
        rw [prob_map,
          expect_eq_sum_of_subset _ _ (μ i).supportFinset fun a ha => by simpa using ha],
    Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [prob_pi, Finset.prod_mul_distrib]
  refine congrArg _ ?_
  by_cases hall : ∀ i, t i = f i (s i)
  · rw [if_pos (funext hall)]
    exact Finset.prod_eq_one fun i _ => if_pos (hall i)
  · obtain ⟨i, hi⟩ := not_forall.mp hall
    rw [if_neg fun hcontra => hi (congrFun hcontra i)]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- **Independent draws of pairs are a pair of independent draws.** The two
families are drawn independently of each other as well as across coordinates,
which is what lets a per-coordinate factorization be reassembled. -/
theorem map_pi_product {B : ι → Type*} (μ : ∀ i, FinDist (A i)) (ν : ∀ i, FinDist (B i)) :
    map (fun p => (fun i => (p i).1, fun i => (p i).2)) (pi fun i => product (μ i) (ν i)) =
      product (pi μ) (pi ν) := by
  classical
  refine ext_of_prob fun q => ?_
  rw [show q = ((fun p : ∀ i, A i × B i => (fun i => (p i).1, fun i => (p i).2))
      fun i => (q.1 i, q.2 i)) from rfl,
    prob_map_of_injective _ (fun x y hxy => funext fun i =>
      Prod.ext (congrFun (congrArg Prod.fst hxy) i) (congrFun (congrArg Prod.snd hxy) i)),
    prob_pi, prob_product, prob_pi, prob_pi, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => prob_product (μ i) (ν i) (q.1 i, q.2 i)

/-- The same interchange read the other way: a product of pairs is drawn by
drawing each family independently and pairing coordinatewise. -/
theorem pi_product {B : ι → Type*} (μ : ∀ i, FinDist (A i)) (ν : ∀ i, FinDist (B i)) :
    (pi fun i => product (μ i) (ν i)) =
      map (fun q i => ((q.1 i, q.2 i) : A i × B i)) (product (pi μ) (pi ν)) := by
  rw [← map_pi_product μ ν, map_comp]
  exact (map_id _).symm

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

/-! ## Ordered dependent draws -/

namespace DependentAssignment

/-- Replace a finite set of coordinates in a dependent assignment. -/
def resolve [DecidableEq ι] (assignment : (i : ι) → A i) (indices : Finset ι)
    (draw : (index : {index // index ∈ indices}) → A index.1) :
    (i : ι) → A i :=
  fun i => if hi : i ∈ indices then draw ⟨i, hi⟩ else assignment i

/-- Replace one coordinate in a dependent assignment. -/
def setOne [DecidableEq ι] (assignment : (i : ι) → A i) (entry : Sigma A) :
    (i : ι) → A i :=
  resolve assignment {entry.1} fun index => by
    have hindex : index.1 = entry.1 := Finset.mem_singleton.mp index.2
    cases index with
    | mk value _ =>
      dsimp only at hindex
      subst value
      exact entry.2

omit [Fintype ι] in
theorem resolve_of_mem [DecidableEq ι] (assignment : (i : ι) → A i) (indices : Finset ι)
    (draw : (index : {index // index ∈ indices}) → A index.1)
    {index : ι} (hindex : index ∈ indices) :
    resolve assignment indices draw index = draw ⟨index, hindex⟩ := by
  simp [resolve, hindex]

omit [Fintype ι] in
theorem resolve_of_notMem [DecidableEq ι] (assignment : (i : ι) → A i) (indices : Finset ι)
    (draw : (index : {index // index ∈ indices}) → A index.1)
    {index : ι} (hindex : index ∉ indices) :
    resolve assignment indices draw index = assignment index := by
  simp [resolve, hindex]

end DependentAssignment

/-- Sequentially draw laws in list order and write each draw into an assignment. -/
def runDependent [DecidableEq ι] (laws : (index : ι) → FinDist (A index)) :
    List ι → ((index : ι) → A index) → FinDist ((index : ι) → A index)
  | [], assignment => pure assignment
  | index :: rest, assignment =>
    (laws index).bind fun value =>
      runDependent laws rest (DependentAssignment.setOne assignment ⟨index, value⟩)

omit [Fintype ι] in
/-- A duplicate-free sequential draw is the independent product on the listed
coordinates, mapped into the initial assignment. -/
theorem runDependent_eq_pi_subtype [DecidableEq ι] (laws : (index : ι) → FinDist (A index)) :
    ∀ (indices : List ι), indices.Nodup → ∀ assignment : (index : ι) → A index,
      runDependent laws indices assignment =
        map (DependentAssignment.resolve assignment indices.toFinset)
          (pi fun index : {index // index ∈ indices.toFinset} => laws index.1) := by
  intro indices
  induction indices with
  | nil =>
      intro _ assignment
      let emptyDraw :
          (index : {index : ι // index ∈ ([] : List ι).toFinset}) → A index.1 :=
        fun index => by
          exfalso
          exact List.not_mem_nil (List.mem_toFinset.mp index.2)
      have hlaws :
          (fun index : {index : ι // index ∈ ([] : List ι).toFinset} => laws index.1) =
            fun index => pure (emptyDraw index) := by
        funext index
        exfalso
        exact List.not_mem_nil (List.mem_toFinset.mp index.2)
      rw [runDependent, hlaws, pi_pure, map_pure]
      apply congrArg pure
      funext index
      simp [DependentAssignment.resolve]
  | cons head tail ih =>
      intro hnodup assignment
      have hheadNotMem : head ∉ tail := (List.nodup_cons.mp hnodup).1
      have htailNodup : tail.Nodup := (List.nodup_cons.mp hnodup).2
      have hheadNotFinset : head ∉ tail.toFinset := by simpa using hheadNotMem
      let full := {index : ι // index ∈ (head :: tail).toFinset}
      let headIndex : full := ⟨head, by simp⟩
      let remaining := {index : full // index ≠ headIndex}
      let tailIndex := {index : ι // index ∈ tail.toFinset}
      let remainingEquiv : tailIndex ≃ remaining :=
        { toFun := fun index => ⟨⟨index.1, by simp [index.2]⟩, by
            intro heq
            have hindexValue : index.1 = head := by
              simpa [headIndex] using congrArg (fun value : full => value.1) heq
            have hheadFinset : head ∈ tail.toFinset := by
              rw [← hindexValue]
              exact index.2
            exact hheadNotMem (by simpa using hheadFinset)⟩
          invFun := fun index => ⟨index.1.1, by
            have hmem : index.1.1 = head ∨ index.1.1 ∈ tail.toFinset := by
              simpa using index.1.2
            rcases hmem with hhead | htail
            · exfalso
              apply index.2
              apply Subtype.ext
              exact hhead
            · exact htail⟩
          left_inv := fun index => by
            apply Subtype.ext
            rfl
          right_inv := fun index => by
            apply Subtype.ext
            rfl }
      let remainingValue (index : remaining) := A index.1.1
      let remainingLaws (index : remaining) : FinDist (remainingValue index) := laws index.1.1
      have hreindex :
          map (Equiv.piCongrLeft remainingValue remainingEquiv).symm (pi remainingLaws) =
            pi (fun index : tailIndex => laws index.1) := by
        simpa [remainingEquiv, remainingValue, remainingLaws, tailIndex] using
          pi_reindex remainingValue remainingEquiv remainingLaws
      have hresolve (value : A head) :
          map
              (fun draw : (index : remaining) → remainingValue index =>
                DependentAssignment.resolve assignment (head :: tail).toFinset
                  ((Equiv.piSplitAt headIndex
                    (fun index : full => A index.1)).symm (value, draw)))
              (pi remainingLaws) =
            map
              (DependentAssignment.resolve
                (DependentAssignment.setOne assignment ⟨head, value⟩) tail.toFinset)
              (pi (fun index : tailIndex => laws index.1)) := by
        rw [← hreindex, map_comp]
        apply congrArg (fun f => map f (pi remainingLaws))
        funext draw index
        by_cases hindexHead : index = head
        · subst index
          simp [DependentAssignment.resolve, DependentAssignment.setOne,
            headIndex, full, remainingEquiv, hheadNotFinset]
        · by_cases hindexTail : index ∈ tail.toFinset
          · simp [DependentAssignment.resolve, DependentAssignment.setOne,
              hindexHead, hindexTail, headIndex, full, remainingEquiv,
              remainingValue, tailIndex]
          · simp [DependentAssignment.resolve, DependentAssignment.setOne,
              hindexHead, hindexTail]
      rw [runDependent]
      simp_rw [ih htailNodup]
      let fullLaws : (index : full) → FinDist (A index.1) := fun index => laws index.1
      rw [show (fun index : {index : ι // index ∈ (head :: tail).toFinset} => laws index.1) =
          fullLaws by rfl,
        pi_eq_map_product headIndex fullLaws, map_comp]
      unfold product
      rw [map_bind]
      apply bind_congr
      intro value _
      refine (hresolve value).symm.trans ?_
      rw [map_comp]
      apply congrArg (fun f => map f (pi remainingLaws))
      funext draw
      rfl

/-- A duplicate-free exhaustive sequential draw is the independent product of
the whole law family. -/
theorem runDependent_eq_pi [DecidableEq ι] (laws : (index : ι) → FinDist (A index))
    (indices : List ι) (hnodup : indices.Nodup) (hcomplete : ∀ index, index ∈ indices)
    (assignment : (index : ι) → A index) :
    runDependent laws indices assignment = pi laws := by
  rw [runDependent_eq_pi_subtype laws indices hnodup assignment]
  have hmem (index : ι) : index ∈ indices.toFinset := by simpa using hcomplete index
  let equiv : {index : ι // index ∈ indices.toFinset} ≃ ι :=
    { toFun := fun index => index.1
      invFun := fun index => ⟨index, hmem index⟩
      left_inv := fun index => by
        apply Subtype.ext
        rfl
      right_inv := fun index => rfl }
  have hpi :
      pi (fun index : {index : ι // index ∈ indices.toFinset} => laws index.1) =
        map (Equiv.piCongrLeft A equiv).symm (pi laws) := by
    simpa [equiv] using (pi_reindex A equiv laws).symm
  rw [hpi, map_comp]
  have hresolve :
      DependentAssignment.resolve assignment indices.toFinset ∘
          (Equiv.piCongrLeft A equiv).symm = id := by
    funext draw index
    simp [DependentAssignment.resolve, equiv, hmem]
  rw [hresolve, map_id]

end Pi

/-! ## Finite partial dependent products -/

variable {ι : Type*} {A : ι → Type*}

/-- A duplicate-free dependent draw depends only on the finite set of
coordinates drawn, not on the list used to enumerate it. -/
theorem runDependent_eq_of_toFinset_eq [DecidableEq ι]
    (laws : (index : ι) → FinDist (A index))
    (first second : List ι) (hfirst : first.Nodup) (hsecond : second.Nodup)
    (hindices : first.toFinset = second.toFinset)
    (assignment : (index : ι) → A index) :
    runDependent laws first assignment = runDependent laws second assignment := by
  rw [runDependent_eq_pi_subtype laws first hfirst assignment,
    runDependent_eq_pi_subtype laws second hsecond assignment, hindices]

/-- Dependent draws are congruent when their coordinate laws agree everywhere
the supplied list asks for a draw. -/
theorem runDependent_congr_laws [DecidableEq ι]
    {first second : (index : ι) → FinDist (A index)}
    (indices : List ι) (assignment : (index : ι) → A index)
    (hagree : ∀ index ∈ indices, first index = second index) :
    runDependent first indices assignment =
      runDependent second indices assignment := by
  induction indices generalizing assignment with
  | nil => rfl
  | cons head tail ih =>
      rw [runDependent, runDependent, hagree head (by simp)]
      refine bind_congr fun value _ => ?_
      exact ih _ fun index hindex => hagree index (by simp [hindex])

/-- Writing a coordinate that the remaining dependent draw never visits
commutes through that draw. -/
theorem runDependent_setOne_of_not_mem [DecidableEq ι]
    (laws : (index : ι) → FinDist (A index)) (indices : List ι)
    (assignment : (index : ι) → A index) (index : ι) (value : A index)
    (hindex : index ∉ indices) :
    runDependent laws indices (DependentAssignment.setOne assignment ⟨index, value⟩) =
      map (fun rest => DependentAssignment.setOne rest ⟨index, value⟩)
        (runDependent laws indices assignment) := by
  induction indices generalizing assignment with
  | nil =>
      simp [runDependent]
  | cons head tail ih =>
      have hne : index ≠ head := by
        intro heq
        subst head
        exact hindex (by simp)
      have htail : index ∉ tail := by
        intro hmem
        exact hindex (by simp [hmem])
      rw [runDependent, runDependent, map_bind]
      refine bind_congr fun headValue _ => ?_
      have hcommute :
          DependentAssignment.setOne
              (DependentAssignment.setOne assignment ⟨index, value⟩)
              ⟨head, headValue⟩ =
            DependentAssignment.setOne
              (DependentAssignment.setOne assignment ⟨head, headValue⟩)
              ⟨index, value⟩ := by
        funext other
        by_cases hotherIndex : other = index
        · subst other
          simp [DependentAssignment.setOne, DependentAssignment.resolve, hne]
        · by_cases hotherHead : other = head
          · subst other
            simp [DependentAssignment.setOne, DependentAssignment.resolve,
              hotherIndex]
          · simp [DependentAssignment.setOne, DependentAssignment.resolve,
              hotherIndex, hotherHead]
      rw [hcommute, ih _ htail]

namespace DependentAssignment

/-- Reinstalling the value already stored at one dependent coordinate changes
nothing. -/
theorem setOne_eq_self [DecidableEq ι]
    (assignment : (index : ι) → A index) (index : ι) :
    setOne assignment ⟨index, assignment index⟩ = assignment := by
  funext other
  by_cases hother : other = index
  · subst other
    simp [setOne, resolve]
  · simp [setOne, resolve, hother]

@[simp]
theorem setOne_apply_self [DecidableEq ι]
    (assignment : (index : ι) → A index) (index : ι) (value : A index) :
    setOne assignment ⟨index, value⟩ index = value := by
  simp [setOne, resolve]

@[simp]
theorem setOne_apply_of_ne [DecidableEq ι]
    (assignment : (index : ι) → A index) {index other : ι}
    (value : A index) (hne : other ≠ index) :
    setOne assignment ⟨index, value⟩ other = assignment other := by
  simp [setOne, resolve, hne]

end DependentAssignment

/-- A finite dependent product can be factored at any coordinate it draws. -/
theorem runDependent_factor_of_mem [DecidableEq ι]
    (laws : (index : ι) → FinDist (A index)) (sites : Finset ι)
    (assignment : (index : ι) → A index) (index : ι)
    (hindex : index ∈ sites) :
    runDependent laws sites.toList assignment =
      map
        (fun pair => DependentAssignment.setOne pair.2 ⟨index, pair.1⟩)
        (product (laws index)
          (runDependent laws (sites.erase index).toList assignment)) := by
  have hrest : index ∉ (sites.erase index).toList := by simp
  have horder :
      runDependent laws sites.toList assignment =
        runDependent laws (index :: (sites.erase index).toList) assignment := by
    apply runDependent_eq_of_toFinset_eq laws
    · exact sites.nodup_toList
    · exact List.nodup_cons.mpr ⟨hrest, (sites.erase index).nodup_toList⟩
    · simp [hindex]
  rw [horder, runDependent, product, map_bind]
  refine bind_congr fun value _ => ?_
  rw [runDependent_setOne_of_not_mem laws _ assignment index value hrest,
    map_comp]
  rfl

/-- A coordinate omitted from the finite draw can still be factored when its
law is the point mass supplied by the fallback assignment. -/
theorem runDependent_factor_of_not_mem [DecidableEq ι]
    (laws : (index : ι) → FinDist (A index)) (sites : Finset ι)
    (assignment : (index : ι) → A index) (index : ι)
    (hindex : index ∉ sites) (hlaw : laws index = pure (assignment index)) :
    runDependent laws sites.toList assignment =
      map
        (fun pair => DependentAssignment.setOne pair.2 ⟨index, pair.1⟩)
        (product (laws index)
          (runDependent laws (sites.erase index).toList assignment)) := by
  have hlist : index ∉ sites.toList := by simpa
  have hset := runDependent_setOne_of_not_mem laws sites.toList assignment
    index (assignment index) hlist
  rw [DependentAssignment.setOne_eq_self assignment index] at hset
  rw [Finset.erase_eq_self.mpr hindex, hlaw, product, pure_bind, map_comp]
  exact hset

end FinDist

end GameTheory.Math.Probability
