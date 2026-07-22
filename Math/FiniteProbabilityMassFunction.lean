/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.ProbabilityMassFunction

/-!
# Finite-support probability mass functions

`FinPMF α` is the finite-distribution monad on an arbitrary carrier `α`.
Keeping finiteness in the type makes expectation an unconditional algebra on
`ℝ`, even when the ambient carrier is infinite.  The coercion to Mathlib's
`PMF` is the interoperability boundary used by the rest of the library.
-/

noncomputable section

open scoped BigOperators

namespace Math

universe u v w

/-- A probability mass function whose support is finite. -/
def FinPMF (α : Type u) := { μ : PMF α // μ.support.Finite }

namespace FinPMF

variable {α : Type u} {β : Type v} {γ : Type w}

/-- Forget the finite-support witness. -/
def toPMF (μ : FinPMF α) : PMF α := μ.1

instance : Coe (FinPMF α) (PMF α) := ⟨toPMF⟩

/-- The support carried by a finite distribution. -/
def support (μ : FinPMF α) : Set α := μ.toPMF.support

theorem support_finite (μ : FinPMF α) : μ.support.Finite :=
  μ.2

/-- A finite distribution is determined by its underlying `PMF`. -/
@[ext] theorem ext {μ ν : FinPMF α} (h : μ.toPMF = ν.toPMF) : μ = ν :=
  Subtype.ext h

/-- Extensionality by point probabilities. -/
theorem ext_apply {μ ν : FinPMF α}
    (h : ∀ a, μ.toPMF a = ν.toPMF a) : μ = ν := by
  apply ext
  exact PMF.ext h

/-- A point mass, with its singleton support witness. -/
def pure (a : α) : FinPMF α :=
  ⟨PMF.pure a, by simp⟩

/-- Every distribution on a finite carrier is finitely supported. -/
def ofPMF [Finite α] (μ : PMF α) : FinPMF α :=
  ⟨μ, Set.toFinite μ.support⟩

/-- Push a finite distribution forward along a function. -/
def map (f : α → β) (μ : FinPMF α) : FinPMF β :=
  ⟨μ.toPMF.map f, by
    rw [PMF.support_map]
    exact μ.support_finite.image f⟩

/-- Kleisli composition preserves finite support. -/
def bind (μ : FinPMF α) (f : α → FinPMF β) : FinPMF β :=
  ⟨μ.toPMF.bind (fun a => (f a).toPMF), by
    rw [PMF.support_bind]
    exact μ.support_finite.biUnion fun a _ha => (f a).support_finite⟩

/-- Independent product (the double strength of the finite-distribution
monad). -/
def product (μ : FinPMF α) (ν : FinPMF β) : FinPMF (α × β) :=
  bind μ fun a => map (fun b => (a, b)) ν

@[simp] theorem toPMF_pure (a : α) : (pure a).toPMF = PMF.pure a :=
  rfl

@[simp] theorem toPMF_map (f : α → β) (μ : FinPMF α) :
    (map f μ).toPMF = μ.toPMF.map f :=
  rfl

@[simp] theorem toPMF_bind (μ : FinPMF α) (f : α → FinPMF β) :
    (bind μ f).toPMF = μ.toPMF.bind fun a => (f a).toPMF :=
  rfl

@[simp] theorem toPMF_ofPMF [Finite α] (μ : PMF α) :
    (ofPMF μ).toPMF = μ :=
  rfl

@[simp] theorem support_pure (a : α) : (pure a).support = {a} :=
  PMF.support_pure a

@[simp] theorem support_map (f : α → β) (μ : FinPMF α) :
    (map f μ).support = f '' μ.support :=
  PMF.support_map f μ.toPMF

@[simp] theorem support_bind (μ : FinPMF α) (f : α → FinPMF β) :
    (bind μ f).support = ⋃ a ∈ μ.support, (f a).support :=
  PMF.support_bind μ.toPMF fun a => (f a).toPMF

theorem mem_support_product_iff (μ : FinPMF α) (ν : FinPMF β)
    (a : α) (b : β) :
    (a, b) ∈ (product μ ν).support ↔ a ∈ μ.support ∧ b ∈ ν.support := by
  simp [product, and_comm]

@[simp] theorem product_apply (μ : FinPMF α) (ν : FinPMF β)
    (a : α) (b : β) :
    (product μ ν).toPMF (a, b) = μ.toPMF a * ν.toPMF b := by
  simp only [product, toPMF_bind, PMF.bind_apply, toPMF_map, PMF.map_apply]
  rw [tsum_eq_single a]
  · rw [tsum_eq_single b]
    · simp
    · intro b' hb
      have hpair : (a, b) ≠ (a, b') := by
        intro h
        exact hb (congrArg Prod.snd h).symm
      simp [hpair]
  · intro a' ha
    have hpair : ∀ b', (a, b) ≠ (a', b') := by
      intro b' h
      exact ha (congrArg Prod.fst h).symm
    simp [hpair]

@[simp] theorem pure_bind (a : α) (f : α → FinPMF β) :
    bind (pure a) f = f a := by
  apply ext
  simp

@[simp] theorem bind_pure (μ : FinPMF α) :
    bind μ pure = μ := by
  apply ext
  simp

@[simp] theorem bind_const (μ : FinPMF α) (ν : FinPMF β) :
    bind μ (fun _ => ν) = ν := by
  apply ext
  exact PMF.bind_const μ.toPMF ν.toPMF

@[simp] theorem bind_bind (μ : FinPMF α) (f : α → FinPMF β)
    (g : β → FinPMF γ) :
    bind (bind μ f) g = bind μ fun a => bind (f a) g := by
  apply ext
  simp [PMF.bind_bind]

@[simp] theorem map_id (μ : FinPMF α) : map id μ = μ := by
  apply ext
  exact PMF.map_id μ.toPMF

@[simp] theorem map_comp (g : β → γ) (f : α → β) (μ : FinPMF α) :
    map g (map f μ) = map (g ∘ f) μ := by
  apply ext
  simp [PMF.map_comp]

@[simp] theorem map_pure (f : α → β) (a : α) :
    map f (pure a) = pure (f a) := by
  apply ext
  exact PMF.pure_map f a

@[simp] theorem map_bind (g : β → γ) (μ : FinPMF α)
    (f : α → FinPMF β) :
    map g (bind μ f) = bind μ fun a => map g (f a) := by
  apply ext
  simp [PMF.map_bind]

@[simp] theorem bind_map (f : α → β) (μ : FinPMF α)
    (g : β → FinPMF γ) :
    bind (map f μ) g = bind μ (g ∘ f) := by
  apply ext
  exact PMF.bind_map μ.toPMF f (fun b => (g b).toPMF)

@[simp] theorem map_fst_product (μ : FinPMF α) (ν : FinPMF β) :
    map Prod.fst (product μ ν) = μ := by
  apply ext
  simp [product]

@[simp] theorem map_snd_product (μ : FinPMF α) (ν : FinPMF β) :
    map Prod.snd (product μ ν) = ν := by
  apply ext
  simp [product]

@[simp] theorem product_pure (a : α) (b : β) :
    product (pure a) (pure b) = pure (a, b) := by
  simp [product]

/-- Independent product is commutative up to swapping coordinates. -/
theorem map_swap_product (μ : FinPMF α) (ν : FinPMF β) :
    map Prod.swap (product μ ν) = product ν μ := by
  apply ext
  change
    (μ.toPMF.bind fun a => (ν.toPMF.map fun b => (a, b))).map Prod.swap =
      ν.toPMF.bind fun b => μ.toPMF.map fun a => (b, a)
  rw [PMF.map_bind]
  simp_rw [PMF.map_comp]
  simp_rw [← PMF.bind_pure_comp]
  simpa [Function.comp_def] using
    (PMF.bind_comm μ.toPMF ν.toPMF fun a b => PMF.pure (b, a))

/-- Flatten a finite distribution of finite distributions. -/
def join (μ : FinPMF (FinPMF α)) : FinPMF α :=
  bind μ id

@[simp] theorem join_pure (μ : FinPMF α) : join (pure μ) = μ := by
  simp [join]

@[simp] theorem join_map_pure (μ : FinPMF α) : join (map pure μ) = μ := by
  simp [join]

@[simp] theorem join_map_map (f : α → β) (μ : FinPMF (FinPMF α)) :
    join (map (map f) μ) = map f (join μ) := by
  simp [join]

noncomputable instance : Monad FinPMF where
  pure := pure
  bind := bind
  map := map

noncomputable instance : LawfulMonad FinPMF := LawfulMonad.mk'
  (bind_pure_comp := by
    intro _ _ f μ
    apply ext
    rfl)
  (id_map := fun μ => map_id μ)
  (pure_bind := fun a f => pure_bind a f)
  (bind_assoc := fun μ f g => bind_bind μ f g)

/-- Expectation commutes with finite-support bind without a global boundedness
hypothesis on the carrier.  The proof truncates the observable outside the
finite support of the bind and then uses the library's bounded Fubini theorem. -/
theorem expect_bind (μ : FinPMF α) (f : α → FinPMF β) (u : β → ℝ) :
    Probability.expect (bind μ f).toPMF u =
      Probability.expect μ.toPMF
        (fun a => Probability.expect (f a).toPMF u) := by
  classical
  let ν : FinPMF β := bind μ f
  let s : Finset β := ν.support_finite.toFinset
  let u' : β → ℝ := fun b => if b ∈ s then u b else 0
  let C : ℝ := ∑ b ∈ s, |u b|
  have hbounded : ∀ b, |u' b| ≤ C := by
    intro b
    by_cases hb : b ∈ s
    · simp only [u', if_pos hb]
      exact Finset.single_le_sum (fun q _hq => abs_nonneg (u q)) hb
    · simp only [u', if_neg hb, abs_zero, C]
      exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hu'_eq (b : β) (hb : b ∈ ν.support) : u' b = u b := by
    simp [u', s, Set.Finite.mem_toFinset, hb]
  calc
    Probability.expect (bind μ f).toPMF u =
        Probability.expect ν.toPMF u' := by
          apply ProbabilityMassFunction.expect_congr_on_support
          intro b hb
          exact (hu'_eq b hb).symm
    _ = Probability.expect μ.toPMF
          (fun a => Probability.expect (f a).toPMF u') := by
          exact Probability.expect_bind_of_bounded μ.toPMF
            (fun a => (f a).toPMF) u' hbounded
    _ = Probability.expect μ.toPMF
          (fun a => Probability.expect (f a).toPMF u) := by
          apply ProbabilityMassFunction.expect_congr_on_support
          intro a ha
          apply ProbabilityMassFunction.expect_congr_on_support
          intro b hb
          apply hu'_eq
          change b ∈ (μ.toPMF.bind fun a => (f a).toPMF).support
          rw [PMF.mem_support_bind_iff]
          exact ⟨a, ha, hb⟩

/-- Expectation of a finite distribution is literally a sum over its support,
even when the carrier is infinite. -/
theorem expect_eq_sum_support (μ : FinPMF α) (u : α → ℝ) :
    Probability.expect μ.toPMF u =
      ∑ a ∈ μ.support_finite.toFinset, (μ.toPMF a).toReal * u a := by
  rw [Probability.expect, tsum_eq_sum (s := μ.support_finite.toFinset)]
  intro a ha
  have ha0 : μ.toPMF a = 0 := by
    rw [← not_ne_iff]
    intro hne
    exact ha (Set.Finite.mem_toFinset _ |>.2 hne)
  simp [ha0]

/-- Pointwise monotonicity of finite-support expectation, with no finiteness
assumption on the ambient carrier. -/
theorem expect_mono (μ : FinPMF α) {u v : α → ℝ}
    (huv : ∀ a, u a ≤ v a) :
    Probability.expect μ.toPMF u ≤ Probability.expect μ.toPMF v := by
  rw [expect_eq_sum_support, expect_eq_sum_support]
  exact Finset.sum_le_sum fun a _ =>
    mul_le_mul_of_nonneg_left (huv a) ENNReal.toReal_nonneg

theorem expect_le_const (μ : FinPMF α) (u : α → ℝ) (c : ℝ)
    (h : ∀ a, u a ≤ c) :
    Probability.expect μ.toPMF u ≤ c := by
  calc
    Probability.expect μ.toPMF u ≤
        Probability.expect μ.toPMF (fun _ => c) := expect_mono μ h
    _ = c := Probability.expect_const μ.toPMF c

/-- Fubini for an independent finite product. -/
theorem expect_product (μ : FinPMF α) (ν : FinPMF β) (u : α × β → ℝ) :
    Probability.expect (product μ ν).toPMF u =
      Probability.expect μ.toPMF
        (fun a => Probability.expect ν.toPMF (fun b => u (a, b))) := by
  rw [show product μ ν = bind μ (fun a => map (fun b => (a, b)) ν) from rfl]
  rw [expect_bind]
  congr 1
  funext a
  rw [toPMF_map, Probability.expect_map]

/-- The symmetric Fubini order for an independent finite product. -/
theorem expect_product_swap (μ : FinPMF α) (ν : FinPMF β)
    (u : α × β → ℝ) :
    Probability.expect (product μ ν).toPMF u =
      Probability.expect ν.toPMF
        (fun b => Probability.expect μ.toPMF (fun a => u (a, b))) := by
  rw [← map_swap_product ν μ, toPMF_map, Probability.expect_map]
  exact expect_product ν μ fun p => u (p.2, p.1)

/-! ## Relational Kleisli lifting -/

/-- Convex closure under finite barycenters.  No ambient vector-space
structure is needed: the elements being combined are themselves
distributions. -/
def convexClosure (S : Set (FinPMF α)) : Set (FinPMF α) :=
  {ν | ∃ θ : FinPMF (FinPMF α), θ.support ⊆ S ∧ join θ = ν}

/-- The concrete relational Kleisli lifting `D̄#` from Definition 11 of
Ghani--Kupke--Lambert--Nordvall Forsberg.  At each supported input it may
randomize among admissible output distributions, then takes their total
barycenter. -/
def RelKleisli (R : α → Set (FinPMF β))
    (μ : FinPMF α) (ν : FinPMF β) : Prop :=
  ∃ choose : α → FinPMF (FinPMF β),
    (∀ a, a ∈ μ.support → (choose a).support ⊆ R a) ∧
      join (bind μ choose) = ν

theorem relKleisli_mono {R Q : α → Set (FinPMF β)}
    (hRQ : ∀ a, R a ⊆ Q a) {μ : FinPMF α} {ν : FinPMF β}
    (h : RelKleisli R μ ν) : RelKleisli Q μ ν := by
  rcases h with ⟨choose, hsupp, hjoin⟩
  exact ⟨choose, fun a ha => (hsupp a ha).trans (hRQ a), hjoin⟩

/-- A pointwise admissible distribution is admitted by the lifting at a point
mass.  The converse is convex closure rather than literal membership; this is
the paper's warning that the distributive law does not preserve `D`'s unit. -/
theorem relKleisli_pure_of_mem (R : α → Set (FinPMF β))
    {a : α} {ν : FinPMF β} (hν : ν ∈ R a) :
    RelKleisli R (pure a) ν := by
  refine ⟨fun _ => pure ν, ?_, ?_⟩
  · intro x hx
    have hxa : x = a := by simpa using hx
    subst x
    simpa using hν
  · simp [join]

/-- On a constant predicate, the relational lifting is exactly finite convex
closure.  This gives a direct semantic reading of `D̄#` when later-stage
optimality does not depend on the incoming history. -/
theorem relKleisli_const_iff (S : Set (FinPMF β))
    (μ : FinPMF α) (ν : FinPMF β) :
    RelKleisli (fun _ => S) μ ν ↔ ν ∈ convexClosure S := by
  constructor
  · rintro ⟨choose, hsupp, hjoin⟩
    refine ⟨bind μ choose, ?_, hjoin⟩
    intro ψ hψ
    rw [show (bind μ choose).support =
      ⋃ a ∈ μ.support, (choose a).support by exact support_bind μ choose] at hψ
    simp only [Set.mem_iUnion] at hψ
    rcases hψ with ⟨a, ha, hψ⟩
    exact hsupp a ha hψ
  · rintro ⟨θ, hθ, hjoin⟩
    refine ⟨fun _ => θ, ?_, ?_⟩
    · intro _a _ha
      exact hθ
    · simpa using hjoin

/-- Naturality in the output carrier. -/
theorem relKleisli_map (g : β → γ) (R : α → Set (FinPMF β))
    {μ : FinPMF α} {ν : FinPMF β} (h : RelKleisli R μ ν) :
    RelKleisli (fun a => map g '' R a) μ (map g ν) := by
  rcases h with ⟨choose, hsupp, hjoin⟩
  refine ⟨fun a => map (map g) (choose a), ?_, ?_⟩
  · intro a ha ψ hψ
    rw [support_map] at hψ
    rcases hψ with ⟨φ, hφ, rfl⟩
    exact ⟨φ, hsupp a ha hφ, rfl⟩
  · calc
      join (bind μ fun a => map (map g) (choose a)) =
          join (map (map g) (bind μ choose)) := by
            rw [map_bind]
      _ = map g (join (bind μ choose)) := join_map_map g (bind μ choose)
      _ = map g ν := congrArg (map g) hjoin

end FinPMF

/-- An algebra for finite averaging.  These are the forward/backward boundary
objects used by probabilistic open games; `avg_bind` is the multiplication
law in bind form. -/
class AvgAlgebra (R : Type u) where
  avg : FinPMF R → R
  avg_pure (r : R) : avg (FinPMF.pure r) = r
  avg_bind {α : Type u} (μ : FinPMF α) (f : α → FinPMF R) :
    avg (FinPMF.bind μ f) =
      avg (FinPMF.map (fun x => avg (f x)) μ)

attribute [simp] AvgAlgebra.avg_pure

namespace AvgAlgebra

variable {R : Type u} {S : Type u}

noncomputable instance : AvgAlgebra ℝ where
  avg μ := Probability.expect μ.toPMF id
  avg_pure r := by simp
  avg_bind μ f := by
    calc
      Probability.expect (FinPMF.bind μ f).toPMF id =
          Probability.expect μ.toPMF
            (fun a => Probability.expect (f a).toPMF id) :=
        FinPMF.expect_bind μ f id
      _ = Probability.expect
          (FinPMF.map
            (fun a => Probability.expect (f a).toPMF id) μ).toPMF id := by
        rw [FinPMF.toPMF_map, Probability.expect_map]
        simp

theorem avg_map_real (μ : FinPMF α) (u : α → ℝ) :
    AvgAlgebra.avg (FinPMF.map u μ) = Probability.expect μ.toPMF u := by
  change Probability.expect (FinPMF.map u μ).toPMF id = _
  rw [FinPMF.toPMF_map, Probability.expect_map]
  rfl

noncomputable instance [AvgAlgebra R] [AvgAlgebra S] :
    AvgAlgebra (R × S) where
  avg μ :=
    (avg (FinPMF.map Prod.fst μ), avg (FinPMF.map Prod.snd μ))
  avg_pure r := by simp
  avg_bind μ f := by
    apply Prod.ext
    · change
        avg (FinPMF.map Prod.fst (FinPMF.bind μ f)) =
          avg (FinPMF.map Prod.fst
            (FinPMF.map
              (fun a =>
                (avg (FinPMF.map Prod.fst (f a)),
                  avg (FinPMF.map Prod.snd (f a)))) μ))
      rw [FinPMF.map_bind, AvgAlgebra.avg_bind, FinPMF.map_comp]
      rfl
    · change
        avg (FinPMF.map Prod.snd (FinPMF.bind μ f)) =
          avg (FinPMF.map Prod.snd
            (FinPMF.map
              (fun a =>
                (avg (FinPMF.map Prod.fst (f a)),
                  avg (FinPMF.map Prod.snd (f a)))) μ))
      rw [FinPMF.map_bind, AvgAlgebra.avg_bind, FinPMF.map_comp]
      rfl

end AvgAlgebra

end Math
