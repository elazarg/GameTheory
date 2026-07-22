/-
# EXP-003 candidate A: a PMF carrying finite support

The operation and expectation proofs are adapted from the pinned v1 files
`Math/FiniteProbabilityMassFunction.lean` and
`Math/ProbabilityMassFunction/Simplex.lean` at commit `a3d8c67...`.
-/

import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Probability.ProbabilityMassFunction.Integrals

noncomputable section

open scoped BigOperators

namespace GameTheory.Experimental.Phase1.D2.FiniteSupportPMF

universe u v w

/-- A Mathlib `PMF` with a proof that its support is finite. -/
def Law (α : Type u) := { μ : PMF α // μ.support.Finite }

namespace Law

variable {α : Type u} {β : Type v} {γ : Type w}

def toPMF (μ : Law α) : PMF α := μ.1

instance : Coe (Law α) (PMF α) := ⟨toPMF⟩

def support (μ : Law α) : Set α := μ.toPMF.support

theorem support_finite (μ : Law α) : μ.support.Finite := μ.2

@[ext]
theorem ext {μ ν : Law α} (h : μ.toPMF = ν.toPMF) : μ = ν := Subtype.ext h

def pure (a : α) : Law α := ⟨PMF.pure a, by simp⟩

def map (f : α → β) (μ : Law α) : Law β :=
  ⟨μ.toPMF.map f, by
    rw [PMF.support_map]
    exact μ.support_finite.image f⟩

def bind (μ : Law α) (f : α → Law β) : Law β :=
  ⟨μ.toPMF.bind (fun a => (f a).toPMF), by
    rw [PMF.support_bind]
    exact μ.support_finite.biUnion fun a _ => (f a).support_finite⟩

def product (μ : Law α) (ν : Law β) : Law (α × β) :=
  bind μ fun a => map (fun b => (a, b)) ν

@[simp]
theorem toPMF_pure (a : α) : (pure a).toPMF = PMF.pure a := rfl

@[simp]
theorem toPMF_map (f : α → β) (μ : Law α) : (map f μ).toPMF = μ.toPMF.map f := rfl

@[simp]
theorem toPMF_bind (μ : Law α) (f : α → Law β) :
    (bind μ f).toPMF = μ.toPMF.bind fun a => (f a).toPMF := rfl

@[simp]
theorem pure_bind (a : α) (f : α → Law β) : bind (pure a) f = f a := by
  apply ext
  simp

@[simp]
theorem bind_pure (μ : Law α) : bind μ pure = μ := by
  apply ext
  simp

@[simp]
theorem bind_bind (μ : Law α) (f : α → Law β) (g : β → Law γ) :
    bind (bind μ f) g = bind μ fun a => bind (f a) g := by
  apply ext
  simp [PMF.bind_bind]

@[simp]
theorem map_id (μ : Law α) : map id μ = μ := by
  apply ext
  exact PMF.map_id μ.toPMF

@[simp]
theorem map_comp (g : β → γ) (f : α → β) (μ : Law α) :
    map g (map f μ) = map (g ∘ f) μ := by
  apply ext
  simp [PMF.map_comp]

@[simp]
theorem product_apply (μ : Law α) (ν : Law β) (a : α) (b : β) :
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

/-- Real expectation. Finite support makes this `tsum` unconditionally finite. -/
def expect (μ : Law α) (u : α → ℝ) : ℝ :=
  ∑' a, (μ.toPMF a).toReal * u a

@[simp]
theorem expect_pure (a : α) (u : α → ℝ) : expect (pure a) u = u a :=
  by
    classical
    unfold expect
    rw [tsum_eq_single a]
    · simp
    · intro b hba
      simp [PMF.pure_apply, hba]

/-- Expectation distributes over finite-support bind. -/
theorem expect_bind (μ : Law α) (f : α → Law β) (u : β → ℝ) :
    expect (bind μ f) u = expect μ fun a => expect (f a) u := by
  classical
  let F : α → β → ℝ := fun a b =>
    (μ.toPMF a).toReal * ((f a).toPMF b).toReal * u b
  have hrow (a : α) : Summable (F a) := by
    apply summable_of_hasFiniteSupport
    apply (f a).support_finite.subset
    intro b hb
    by_contra hnot
    have hz : (f a).toPMF b = 0 := (f a).toPMF.apply_eq_zero_iff b |>.2 hnot
    exact hb (by simp [F, hz])
  have hcol (b : β) : Summable (fun a => F a b) := by
    apply summable_of_hasFiniteSupport
    apply μ.support_finite.subset
    intro a ha
    by_contra hnot
    have hz : μ.toPMF a = 0 := μ.toPMF.apply_eq_zero_iff a |>.2 hnot
    exact ha (by simp [F, hz])
  have hjoint : Summable (Function.uncurry F) := by
    apply summable_of_hasFiniteSupport
    let S : Set (α × β) := ⋃ a ∈ μ.support, {a} ×ˢ (f a).support
    have hS : S.Finite := μ.support_finite.biUnion fun a _ =>
      (Set.finite_singleton a).prod (f a).support_finite
    apply hS.subset
    rintro ⟨a, b⟩ hab
    by_contra hnot
    apply hnot
    simp only [S, Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff]
    refine ⟨a, ?_, rfl, ?_⟩
    · intro ha
      exact hab (by simp [Function.uncurry, F, ha])
    · intro hb
      exact hab (by simp [Function.uncurry, F, hb])
  have hinner_real (b : β) :
      ((∑' a, μ.toPMF a * (f a).toPMF b : ENNReal)).toReal =
        ∑' a, (μ.toPMF a).toReal * ((f a).toPMF b).toReal := by
    rw [ENNReal.tsum_toReal_eq fun a =>
      ENNReal.mul_ne_top (PMF.apply_ne_top μ.toPMF a) (PMF.apply_ne_top (f a).toPMF b)]
    apply tsum_congr
    intro a
    exact ENNReal.toReal_mul
  simp only [expect, toPMF_bind, PMF.bind_apply]
  simp_rw [hinner_real, ← tsum_mul_right]
  rw [hjoint.tsum_comm' hrow hcol]
  apply tsum_congr
  intro a
  rw [← tsum_mul_left]
  apply tsum_congr
  intro b
  simp [F, mul_assoc]

theorem expect_eq_sum_support (μ : Law α) (u : α → ℝ) :
    expect μ u = ∑ a ∈ μ.support_finite.toFinset, (μ.toPMF a).toReal * u a := by
  unfold expect
  rw [tsum_eq_sum (s := μ.support_finite.toFinset)]
  intro a ha
  have ha0 : μ.toPMF a = 0 := by
    rw [← not_ne_iff]
    intro hne
    exact ha (Set.Finite.mem_toFinset _ |>.2 hne)
  simp [ha0]

/-! ## Dependent finite product -/

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
      rw [Fin.prod_univ_succ]
      rfl
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
    apply Finset.prod_congr rfl
    intro j hj
    rw [show (ePi t (e j) : A (e j)) = t j from Equiv.piCongrLeft_apply_apply A e t j]
  simp_rw [hprod]
  rw [ennreal_tsum_pi_fin (A := fun j => A (e j)) (g := fun j a => g (e j) a)]
  rw [← e.prod_comp (g := fun i => ∑' a : A i, g i a)]

section Pi

variable {ι : Type*} [Fintype ι] {A : ι → Type*}

def pmfPi (μ : ∀ i, PMF (A i)) : PMF (∀ i, A i) :=
  ⟨fun s => ∏ i, μ i (s i),
    ENNReal.summable.hasSum_iff.2 (by
      rw [ennreal_tsum_pi (g := fun i a => μ i a)]
      simp [PMF.tsum_coe])⟩

@[simp]
theorem pmfPi_apply (μ : ∀ i, PMF (A i)) (s : ∀ i, A i) :
    pmfPi μ s = ∏ i, μ i (s i) := rfl

/-- Independent product of a finite family of finite-support laws. -/
def pi (μ : ∀ i, Law (A i)) : Law (∀ i, A i) :=
  ⟨pmfPi (fun i => (μ i).toPMF), by
    classical
    let T : Type _ := ∀ i, {a : A i // a ∈ (μ i).support}
    let embed : T → (∀ i, A i) := fun t i => (t i).1
    letI (i : ι) : Fintype {a : A i // a ∈ (μ i).support} :=
      (μ i).support_finite.fintype
    letI : Fintype T := inferInstance
    apply (Set.finite_range embed).subset
    intro s hs
    have hcoord (i : ι) : s i ∈ (μ i).support := by
      intro hnot
      have hz : (μ i).toPMF (s i) = 0 := by simpa [PMF.mem_support_iff] using hnot
      have : pmfPi (fun i => (μ i).toPMF) s = 0 := by
        rw [pmfPi_apply]
        exact Finset.prod_eq_zero (Finset.mem_univ i) hz
      exact hs this
    exact ⟨fun i => ⟨s i, hcoord i⟩, rfl⟩⟩

end Pi

/-! ## Finite-simplex bridge -/

def pmfToVector [Fintype α] (μ : PMF α) : α → ℝ := fun a => (μ a).toReal

theorem pmf_toReal_tsum_one (μ : PMF α) : ∑' a, (μ a).toReal = 1 := by
  have key := @ENNReal.tsum_toReal_eq α (fun a => μ a) (fun a => PMF.apply_ne_top μ a)
  rw [show ∑' a, (μ a).toReal = ∑' a, ((fun a => μ a) a).toReal from rfl]
  rw [← key, PMF.tsum_coe]
  norm_num

theorem pmf_toReal_sum_one [Fintype α] (μ : PMF α) :
    ∑ a, (μ a).toReal = 1 := by
  simpa [tsum_fintype] using pmf_toReal_tsum_one μ

theorem pmfToVector_mem [Fintype α] (μ : PMF α) :
    pmfToVector μ ∈ stdSimplex ℝ α :=
  ⟨fun _ => ENNReal.toReal_nonneg, pmf_toReal_sum_one μ⟩

def pmfOfVector [Fintype α] (x : stdSimplex ℝ α) : PMF α :=
  ⟨fun a => ENNReal.ofReal (x a), by
    have hsum : ∑ a, ENNReal.ofReal (x a) = 1 := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => stdSimplex.zero_le x a),
        stdSimplex.sum_eq_one]
      norm_num
    simpa [tsum_fintype, hsum] using (hasSum_fintype fun a => ENNReal.ofReal (x a))⟩

@[simp]
theorem pmfOfVector_toReal [Fintype α] (x : stdSimplex ℝ α) (a : α) :
    (pmfOfVector x a).toReal = x a := ENNReal.toReal_ofReal (stdSimplex.zero_le x a)

def toSimplex [Fintype α] (μ : Law α) : stdSimplex ℝ α :=
  ⟨pmfToVector μ.toPMF, pmfToVector_mem μ.toPMF⟩

def ofSimplex [Fintype α] (x : stdSimplex ℝ α) : Law α :=
  ⟨pmfOfVector x, Set.toFinite _⟩

/-- Candidate A's finite-carrier Analysis bridge. -/
def simplexEquiv [Fintype α] : Law α ≃ stdSimplex ℝ α where
  toFun := toSimplex
  invFun := ofSimplex
  left_inv μ := by
    apply ext
    apply PMF.ext
    intro a
    apply ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)|>.mp
    exact pmfOfVector_toReal (toSimplex μ) a
  right_inv x := by
    apply stdSimplex.ext
    funext a
    exact pmfOfVector_toReal x a

theorem simplexEquiv_expect [Fintype α] (μ : Law α) (u : α → ℝ) :
    expect μ u = ∑ a, simplexEquiv μ a * u a := by
  rw [expect, tsum_fintype]
  change (∑ a, (μ.toPMF a).toReal * u a) = ∑ a, (μ.toPMF a).toReal * u a
  rfl

end Law

end GameTheory.Experimental.Phase1.D2.FiniteSupportPMF
