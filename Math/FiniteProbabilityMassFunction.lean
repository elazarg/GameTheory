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

theorem bind_congr_on_support (μ : FinPMF α)
    (f g : α → FinPMF β)
    (hfg : ∀ a, a ∈ μ.support → f a = g a) :
    bind μ f = bind μ g := by
  apply ext
  exact ProbabilityMassFunction.bind_congr_on_support μ.toPMF
    (fun a => (f a).toPMF) (fun a => (g a).toPMF)
    (fun a ha => congrArg toPMF (hfg a ha))

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

@[simp] theorem map_const (μ : FinPMF α) (b : β) :
    map (fun _ => b) μ = pure b := by
  apply ext
  exact PMF.map_const μ.toPMF b

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

@[simp] theorem pure_product (a : α) (ν : FinPMF β) :
    product (pure a) ν = map (fun b => (a, b)) ν := by
  simp [product]

@[simp] theorem product_pure_right (μ : FinPMF α) (b : β) :
    product μ (pure b) = map (fun a => (a, b)) μ := by
  apply ext
  simp only [product, toPMF_bind, toPMF_map, toPMF_pure,
    PMF.pure_map]
  change μ.toPMF.bind (PMF.pure ∘ fun a => (a, b)) = _
  exact PMF.bind_pure_comp _ _

@[simp] theorem map_fst_map_mk_right (μ : FinPMF α) (b : β) :
    map Prod.fst (map (fun a => (a, b)) μ) = μ := by
  rw [← product_pure_right, map_fst_product]

@[simp] theorem map_snd_map_mk_right (μ : FinPMF α) (b : β) :
    map Prod.snd (map (fun a => (a, b)) μ) = pure b := by
  rw [← product_pure_right, map_snd_product]

@[simp] theorem map_fst_unit_product (μ : FinPMF (Unit × α)) :
    map Prod.fst μ = pure () := by
  apply ext_apply
  intro u
  cases u
  simp

@[simp] theorem map_snd_product_unit (μ : FinPMF (α × Unit)) :
    map Prod.snd μ = pure () := by
  apply ext_apply
  intro u
  cases u
  simp

/-- Every law on `Unit × α` is independent: its first marginal is forced. -/
theorem product_pure_unit_map_snd (μ : FinPMF (Unit × α)) :
    product (pure ()) (map Prod.snd μ) = μ := by
  calc
    product (pure ()) (map Prod.snd μ) =
        map (fun a => ((), a)) (map Prod.snd μ) := pure_product _ _
    _ = map ((fun a => ((), a)) ∘ Prod.snd) μ := map_comp _ _ _
    _ = map id μ := by
      congr 1
    _ = μ := map_id μ

/-- Every law on `α × Unit` is independent: its second marginal is forced. -/
theorem product_map_fst_pure_unit (μ : FinPMF (α × Unit)) :
    product (map Prod.fst μ) (pure ()) = μ := by
  calc
    product (map Prod.fst μ) (pure ()) =
        map (fun a => (a, ())) (map Prod.fst μ) :=
      product_pure_right _ _
    _ = map ((fun a => (a, ())) ∘ Prod.fst) μ := map_comp _ _ _
    _ = map id μ := by
      congr 1
    _ = μ := map_id μ

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

/-- Expected real value of an observable under a finite distribution. -/
def expect (μ : FinPMF α) (u : α → ℝ) : ℝ :=
  Probability.expect μ.toPMF u

@[simp] theorem expect_pure (a : α) (u : α → ℝ) :
    expect (pure a) u = u a :=
  Probability.expect_pure u a

/-- Expectation commutes with finite-support bind without a global boundedness
hypothesis on the carrier.  The proof truncates the observable outside the
finite support of the bind and then uses the library's bounded Fubini theorem. -/
theorem expect_bind (μ : FinPMF α) (f : α → FinPMF β) (u : β → ℝ) :
    expect (bind μ f) u = expect μ (fun a => expect (f a) u) := by
  unfold expect
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
    expect μ u =
      ∑ a ∈ μ.support_finite.toFinset, (μ.toPMF a).toReal * u a := by
  unfold expect
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
    expect μ u ≤ expect μ v := by
  rw [expect_eq_sum_support, expect_eq_sum_support]
  exact Finset.sum_le_sum fun a _ =>
    mul_le_mul_of_nonneg_left (huv a) ENNReal.toReal_nonneg

theorem expect_mono_on_support (μ : FinPMF α) {u v : α → ℝ}
    (huv : ∀ a, a ∈ μ.support → u a ≤ v a) :
    expect μ u ≤ expect μ v := by
  rw [expect_eq_sum_support, expect_eq_sum_support]
  exact Finset.sum_le_sum fun a ha =>
    mul_le_mul_of_nonneg_left
      (huv a (Set.Finite.mem_toFinset _ |>.1 ha)) ENNReal.toReal_nonneg

theorem expect_le_const (μ : FinPMF α) (u : α → ℝ) (c : ℝ)
    (h : ∀ a, u a ≤ c) :
    expect μ u ≤ c := by
  calc
    expect μ u ≤ expect μ (fun _ => c) := expect_mono μ h
    _ = c := Probability.expect_const μ.toPMF c

/-- Fubini for an independent finite product. -/
theorem expect_product (μ : FinPMF α) (ν : FinPMF β) (u : α × β → ℝ) :
    expect (product μ ν) u =
      expect μ (fun a => expect ν (fun b => u (a, b))) := by
  rw [show product μ ν = bind μ (fun a => map (fun b => (a, b)) ν) from rfl]
  rw [expect_bind]
  congr 1
  funext a
  unfold expect
  rw [toPMF_map, Probability.expect_map]

/-- The symmetric Fubini order for an independent finite product. -/
theorem expect_product_swap (μ : FinPMF α) (ν : FinPMF β)
    (u : α × β → ℝ) :
    expect (product μ ν) u =
      expect ν (fun b => expect μ (fun a => u (a, b))) := by
  unfold expect
  rw [← map_swap_product ν μ, toPMF_map, Probability.expect_map]
  exact expect_product ν μ fun p => u (p.2, p.1)

/-! ## Relational Kleisli lifting -/

/-- Convex closure under finite barycenters.  No ambient vector-space
structure is needed: the elements being combined are themselves
distributions. -/
def convexClosure (S : Set (FinPMF α)) : Set (FinPMF α) :=
  {ν | ∃ θ : FinPMF (FinPMF α), θ.support ⊆ S ∧ join θ = ν}

theorem subset_convexClosure (S : Set (FinPMF α)) :
    S ⊆ convexClosure S := by
  intro ν hν
  exact ⟨pure ν, by simpa using hν, by simp⟩

theorem convexClosure_mono {S T : Set (FinPMF α)} (hST : S ⊆ T) :
    convexClosure S ⊆ convexClosure T := by
  rintro ν ⟨θ, hθ, hjoin⟩
  exact ⟨θ, hθ.trans hST, hjoin⟩

/-- Finite convex closure is idempotent. -/
theorem convexClosure_idempotent (S : Set (FinPMF α)) :
    convexClosure (convexClosure S) = convexClosure S := by
  classical
  apply Set.Subset.antisymm
  · rintro ν ⟨θ, hθ, hjoinθ⟩
    let choose : FinPMF α → FinPMF (FinPMF α) := fun ψ =>
      if hψ : ψ ∈ θ.support then Classical.choose (hθ hψ) else pure ψ
    have choose_support (ψ : FinPMF α) (hψ : ψ ∈ θ.support) :
        (choose ψ).support ⊆ S := by
      simpa only [choose, dif_pos hψ] using
        (Classical.choose_spec (hθ hψ)).1
    have choose_join (ψ : FinPMF α) (hψ : ψ ∈ θ.support) :
        join (choose ψ) = ψ := by
      simpa only [choose, dif_pos hψ] using
        (Classical.choose_spec (hθ hψ)).2
    refine ⟨bind θ choose, ?_, ?_⟩
    · intro φ hφ
      rw [support_bind] at hφ
      simp only [Set.mem_iUnion] at hφ
      rcases hφ with ⟨ψ, hψ, hφ⟩
      exact choose_support ψ hψ hφ
    · calc
        join (bind θ choose) = bind θ (fun ψ => join (choose ψ)) := by
          simp only [join, bind_bind]
        _ = bind θ id := bind_congr_on_support θ _ _ fun ψ hψ => by
          simpa using choose_join ψ hψ
        _ = join θ := rfl
        _ = ν := hjoinθ
  · exact subset_convexClosure (convexClosure S)

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

/-- Relational Kleisli lifting already performs pointwise convex saturation;
closing every fiber beforehand does not change the lifted relation. -/
theorem relKleisli_convexClosure_iff (R : α → Set (FinPMF β))
    (μ : FinPMF α) (ν : FinPMF β) :
    RelKleisli (fun a => convexClosure (R a)) μ ν ↔
      RelKleisli R μ ν := by
  classical
  constructor
  · rintro ⟨choose, hsupp, hjoin⟩
    have hfiber (a : α) (ha : a ∈ μ.support) :
        join (choose a) ∈ convexClosure (R a) := by
      have hdouble : join (choose a) ∈
          convexClosure (convexClosure (R a)) :=
        ⟨choose a, hsupp a ha, rfl⟩
      rwa [convexClosure_idempotent] at hdouble
    let refined : α → FinPMF (FinPMF β) := fun a =>
      if ha : a ∈ μ.support then Classical.choose (hfiber a ha)
      else choose a
    have refined_support (a : α) (ha : a ∈ μ.support) :
        (refined a).support ⊆ R a := by
      simpa only [refined, dif_pos ha] using
        (Classical.choose_spec (hfiber a ha)).1
    have refined_join (a : α) (ha : a ∈ μ.support) :
        join (refined a) = join (choose a) := by
      simpa only [refined, dif_pos ha] using
        (Classical.choose_spec (hfiber a ha)).2
    refine ⟨refined, refined_support, ?_⟩
    calc
      join (bind μ refined) = bind μ (fun a => join (refined a)) := by
        simp only [join, bind_bind]
      _ = bind μ (fun a => join (choose a)) :=
        bind_congr_on_support μ _ _ refined_join
      _ = join (bind μ choose) := by
        simp only [join, bind_bind]
      _ = ν := hjoin
  · intro h
    exact relKleisli_mono
      (fun a => subset_convexClosure (R a)) h

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

/-- At a point input, the lifting is exactly convex closure of the
pointwise admissible set. -/
theorem relKleisli_pure_iff (R : α → Set (FinPMF β))
    (a : α) (ν : FinPMF β) :
    RelKleisli R (pure a) ν ↔ ν ∈ convexClosure (R a) := by
  constructor
  · rintro ⟨choose, hsupp, hjoin⟩
    refine ⟨choose a, ?_, ?_⟩
    · exact hsupp a (by simp)
    · simpa using hjoin
  · rintro ⟨θ, hθ, hjoin⟩
    refine ⟨fun _ => θ, ?_, ?_⟩
    · intro x hx
      have hxa : x = a := by simpa using hx
      simpa [hxa] using hθ
    · simpa using hjoin

/-- A single output distribution that is admissible at every supported input
is admitted by the relational lifting. -/
theorem relKleisli_of_forall_mem (R : α → Set (FinPMF β))
    (μ : FinPMF α) (ν : FinPMF β)
    (hν : ∀ a, a ∈ μ.support → ν ∈ R a) :
    RelKleisli R μ ν := by
  refine ⟨fun _ => pure ν, ?_, ?_⟩
  · intro a ha
    simpa using hν a ha
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
objects used by probabilistic open games. -/
class AvgAlgebra (R : Type u) where
  avg : FinPMF R → R
  avg_pure (r : R) : avg (FinPMF.pure r) = r
  avg_join (μ : FinPMF (FinPMF R)) :
    avg (FinPMF.join μ) = avg (FinPMF.map avg μ)

attribute [simp] AvgAlgebra.avg_pure

namespace AvgAlgebra

variable {R : Type u} {S : Type u}

/-- The multiplication law in bind form.  Unlike a class field with an
independent universe parameter, this derived theorem does not add an
unconstrained universe level to `AvgAlgebra R`. -/
theorem avg_bind [AvgAlgebra R] {α : Type v}
    (μ : FinPMF α) (f : α → FinPMF R) :
    avg (FinPMF.bind μ f) =
      avg (FinPMF.map (fun x => avg (f x)) μ) := by
  calc
    avg (FinPMF.bind μ f) =
        avg (FinPMF.join (FinPMF.map f μ)) := by
      congr 1
      simp [FinPMF.join]
    _ = avg (FinPMF.map avg (FinPMF.map f μ)) :=
      AvgAlgebra.avg_join _
    _ = avg (FinPMF.map (fun x => avg (f x)) μ) := by
      rw [FinPMF.map_comp]
      rfl

noncomputable instance : AvgAlgebra ℝ where
  avg μ := FinPMF.expect μ id
  avg_pure r := by simp
  avg_join μ := by
    calc
      FinPMF.expect (FinPMF.join μ) id =
          FinPMF.expect μ (fun ν => FinPMF.expect ν id) :=
        FinPMF.expect_bind μ id id
      _ = FinPMF.expect
          (FinPMF.map (fun ν => FinPMF.expect ν id) μ) id := by
        unfold FinPMF.expect
        rw [FinPMF.toPMF_map, Probability.expect_map]
        simp

theorem avg_map_real (μ : FinPMF α) (u : α → ℝ) :
    AvgAlgebra.avg (FinPMF.map u μ) = FinPMF.expect μ u := by
  change FinPMF.expect (FinPMF.map u μ) id = _
  unfold FinPMF.expect
  rw [FinPMF.toPMF_map, Probability.expect_map]
  rfl

noncomputable instance [AvgAlgebra R] [AvgAlgebra S] :
    AvgAlgebra (R × S) where
  avg μ :=
    (avg (FinPMF.map Prod.fst μ), avg (FinPMF.map Prod.snd μ))
  avg_pure r := by simp
  avg_join μ := by
    apply Prod.ext
    · change
        avg (FinPMF.map Prod.fst (FinPMF.join μ)) =
          avg (FinPMF.map Prod.fst
            (FinPMF.map
              (fun ν =>
                (avg (FinPMF.map Prod.fst ν),
                  avg (FinPMF.map Prod.snd ν))) μ))
      rw [← FinPMF.join_map_map, AvgAlgebra.avg_join, FinPMF.map_comp,
        FinPMF.map_comp]
      rfl
    · change
        avg (FinPMF.map Prod.snd (FinPMF.join μ)) =
          avg (FinPMF.map Prod.snd
            (FinPMF.map
              (fun ν =>
                (avg (FinPMF.map Prod.fst ν),
                  avg (FinPMF.map Prod.snd ν))) μ))
      rw [← FinPMF.join_map_map, AvgAlgebra.avg_join, FinPMF.map_comp,
        FinPMF.map_comp]
      rfl

end AvgAlgebra

end Math
