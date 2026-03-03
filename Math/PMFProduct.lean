import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Math.FunctionUpdate

namespace Math
namespace PMFProduct

open scoped BigOperators

universe uι uA uα uβ uγ

set_option autoImplicit false

-- ============================================================================
-- Auxiliary Helpers
-- ============================================================================

private lemma pmf_sum_eq_one {α : Type*} [Fintype α] (μ : PMF α) :
    ∑ a : α, μ a = 1 := by
  have h := PMF.tsum_coe μ
  rwa [tsum_eq_sum (s := Finset.univ)
    (fun x hx => absurd (Finset.mem_univ x) hx)] at h

section Aux

variable {ι : Type uι} [DecidableEq ι]
variable {A : ι → Type uA}

/-- Factor the product weight into the `j`-coordinate and the rest. -/
lemma prod_factor_erase [Fintype ι] (σ : ∀ i, PMF (A i)) (j : ι) (s : ∀ i, A i) :
    (∏ i : ι, σ i (s i))
      = (σ j) (s j) * (∏ i ∈ (Finset.univ.erase j), σ i (s i)) := by
  classical
  simpa [Finset.mem_univ] using
    (Finset.mul_prod_erase (s := (Finset.univ : Finset ι))
      (f := fun i => σ i (s i)) (a := j) (by simp)).symm

/-- Updating at coordinate `j` does not change the product over `univ.erase j`. -/
lemma prod_erase_update_eq [Fintype ι]
    (σ : ∀ i, PMF (A i)) (j : ι) (s : ∀ i, A i) (a : A j) :
    (∏ i ∈ Finset.univ.erase j, σ i ((Function.update s j a) i))
      = (∏ i ∈ Finset.univ.erase j, σ i (s i)) := by
  apply Finset.prod_congr rfl
  intro i hi
  simp [Function.update, Finset.ne_of_mem_erase hi]

/-- Swap outer `a` with the `j`-coordinate of `s`, and update `s` at `j` to `a`. -/
def swapJA (j : ι) : (A j × (∀ i, A i)) → (A j × (∀ i, A i)) :=
  fun p => (p.2 j, Function.update p.2 j p.1)

lemma swapJA_involutive (j : ι) : Function.Involutive (swapJA (A := A) j) := by
  intro ⟨a, s⟩
  apply Prod.ext
  · simp [swapJA]
  · funext i; by_cases h : i = j
    · subst h; simp [swapJA]
    · simp [swapJA, Function.update]

lemma sum_univ_eq_sum_univ_of_involutive
    {α : Type _} [Fintype α] {δ : Type _} [AddCommMonoid δ]
    (e : α → α) (he : Function.Involutive e) (f : α → δ) :
    (∑ x : α, f (e x)) = ∑ x : α, f x := by
  simpa using
    (Finset.sum_bij (s := Finset.univ) (t := Finset.univ)
      (fun x _ => e x) (by intro x _; simp))
      (by intro x₁ _ x₂ _ hxe; have := congrArg e hxe; simpa [he x₁, he x₂] using this)
      (by intro y _; exact ⟨e y, Finset.mem_univ _, he y⟩)
      (by intro _ _; rfl)

end Aux

-- ============================================================================
-- Product PMF & Coordinate Independence
-- ============================================================================

section Core

variable {ι : Type uι} [DecidableEq ι]
variable {A : ι → Type uA}

-- ---- Product PMF --------------------------------------------------------

open Classical in
/-- Product PMF over a finite index type: independently sample each coordinate. -/
noncomputable def pmfPi [Fintype ι] [∀ i, Fintype (A i)]
    (σ : ∀ i, PMF (A i)) : PMF (∀ i, A i) :=
  PMF.ofFintype (fun s => ∏ i, σ i (s i)) (by
    rw [← Fintype.prod_sum]
    have : ∀ i, ∑ j : A i, (σ i) j = 1 := fun i => pmf_sum_eq_one (σ i)
    simp [this])

@[simp] lemma pmfPi_apply [Fintype ι] [∀ i, Fintype (A i)]
    (σ : ∀ i, PMF (A i)) (s : ∀ i, A i) :
    pmfPi (A := A) σ s = ∏ i, σ i (s i) := by
  simp [pmfPi, PMF.ofFintype_apply]

open Classical in
/-- Product of point masses is a point mass at the joint assignment. -/
theorem pmfPi_pure [Fintype ι] [∀ i, Fintype (A i)] (σ : ∀ i, A i) :
    pmfPi (fun i => (PMF.pure (σ i) : PMF (A i))) = PMF.pure σ := by
  classical
  ext s
  by_cases hs : s = σ
  · subst hs
    simp [pmfPi_apply]
  · have hneq : ¬ ∀ i, s i = σ i := by
      intro hall
      apply hs
      funext i
      exact hall i
    obtain ⟨i, hi⟩ := not_forall.mp hneq
    have hfactor0 : (if s i = σ i then (1 : ENNReal) else 0) = 0 := by
      simp [hi]
    have hprod0 :
        (∏ x : ι, (if s x = σ x then (1 : ENNReal) else 0)) = 0 := by
      calc
        (∏ x : ι, (if s x = σ x then (1 : ENNReal) else 0))
            = (if s i = σ i then (1 : ENNReal) else 0) *
              (Finset.prod (Finset.univ.erase i)
                (fun x => (if s x = σ x then (1 : ENNReal) else 0))) := by
                simpa [Finset.mem_univ] using
                  (Finset.mul_prod_erase
                    (s := (Finset.univ : Finset ι))
                    (f := fun x => (if s x = σ x then (1 : ENNReal) else 0))
                    (a := i) (by simp)).symm
        _ = 0 := by simp [hfactor0]
    simpa [pmfPi_apply, PMF.pure_apply, hs] using hprod0

-- ---- Assignment operations -----------------------------------------------

/-- Coordinate projection. -/
@[simp] def coord (j : ι) (s : (∀ i, A i)) : A j := s j

/-- Update the `j`-coordinate of an assignment. -/
@[simp] def update (s : (∀ i, A i)) (j : ι) (a : A j) : (∀ i, A i) :=
  Function.update s j a

@[simp] lemma update_self (s : (∀ i, A i)) (j : ι) (a : A j) :
    update (A := A) s j a j = a := by
  simp [update]

@[simp] lemma update_ne (s : (∀ i, A i)) {i j : ι} (a : A j) (h : i ≠ j) :
    update (A := A) s j a i = s i := by
  simp [update, h]

-- ---- Coordinate independence (Ignores) -----------------------------------

/-- "`F` ignores coordinate `j`": updating `j` does not change `F`. -/
abbrev Ignores {α : Type uα} (j : ι) (F : (∀ i, A i) → α) : Prop :=
  Math.Function.Update.Ignores (A := A) j F

/-- "`G a0 s` ignores coordinate `j` in `s`", uniformly in the external parameter `a0`. -/
def Ignores₂ {α : Type uα} (j : ι) (G : A j → (∀ i, A i) → α) : Prop :=
  ∀ a0 s a, G a0 (update (A := A) s j a) = G a0 s

/-- A pointwise (extensional) criterion implying `Ignores`. -/
lemma Ignores_of_pointwise {α : Type uα} (j : ι) (F : (∀ i, A i) → α)
    (h : ∀ s₁ s₂, (∀ i, i ≠ j → s₁ i = s₂ i) → F s₁ = F s₂) :
    Ignores (A := A) j F := by
  intro s a
  apply h (update (A := A) s j a) s
  intro i hi
  simp [update, hi]

/-- A pointwise (extensional) criterion implying `Ignores₂`. -/
lemma Ignores₂_of_pointwise {α : Type uα} (j : ι) (G : A j → (∀ i, A i) → α)
    (h : ∀ a0 s₁ s₂, (∀ i, i ≠ j → s₁ i = s₂ i) → G a0 s₁ = G a0 s₂) :
    Ignores₂ (A := A) j G := by
  intro a0 s a
  apply h a0 (update (A := A) s j a) s
  intro i hi
  simp [update, hi]

lemma Ignores_coord_eq (j q : ι) (hq : q ≠ j) (a : A q) :
  Ignores (A := A) j (fun s => s q = a) := by
    intro s b; simp [hq]

lemma Ignores_coord_pred (j q : ι) (hq : q ≠ j) (E : A q → Prop) :
  Ignores (A := A) j (fun s => E (s q)) := by
    intro s b; simp [hq]

-- ---- Ignores algebra (closure properties) --------------------------------

section IgnoresAlgebra

variable {ι : Type uι} [DecidableEq ι]
variable {A : ι → Type uA}

/-- Prop-flavored version: ignoring a coordinate means iff, not Prop-equality. -/
def IgnoresP (j : ι) (P : (∀ i, A i) → Prop) : Prop :=
  ∀ s a, P (update (A := A) s j a) ↔ P s

/-- `Ignores` ⇒ `IgnoresP` (no classical axioms needed). -/
lemma IgnoresP_of_Ignores (j : ι) (P : (∀ i, A i) → Prop)
    (h : Ignores (A := A) j P) : IgnoresP (A := A) j P := by
  intro s a
  simp only [update]
  exact Eq.to_iff (h s a)

/-- `IgnoresP` ⇒ `Ignores` (needs propositional extensionality). -/
lemma Ignores_of_IgnoresP (j : ι) (P : (∀ i, A i) → Prop)
    (h : IgnoresP (A := A) j P) : Ignores (A := A) j P := by
  intro s a
  exact propext (h s a)

-- Generic (Type-valued) closure

lemma Ignores_const {α : Type uα} (j : ι) (c : α) :
    Ignores (A := A) j (fun _ => c) := by
  intro s a; rfl

lemma Ignores_comp {α : Type uα} {β : Type uβ} (j : ι)
    (F : (∀ i, A i) → α) (G : α → β)
    (hF : Ignores (A := A) j F) :
    Ignores (A := A) j (fun s => G (F s)) := by
  intro s a
  exact (congrArg G ∘ fun a_1 ↦ hF s a) ι

lemma Ignores_prod_mk {α : Type uα} {β : Type uβ} (j : ι)
    (F : (∀ i, A i) → α) (G : (∀ i, A i) → β)
    (hF : Ignores (A := A) j F) (hG : Ignores (A := A) j G) :
    Ignores (A := A) j (fun s => (F s, G s)) := by
  intro s a
  exact Prod.ext (hF s a) (hG s a)

lemma Ignores_fst {α : Type uα} {β : Type uβ} (j : ι)
    (F : (∀ i, A i) → α × β) (hF : Ignores (A := A) j F) :
    Ignores (A := A) j (fun s => (F s).1) :=
  Ignores_comp (A := A) j F Prod.fst hF

lemma Ignores_snd {α : Type uα} {β : Type uβ} (j : ι)
    (F : (∀ i, A i) → α × β) (hF : Ignores (A := A) j F) :
    Ignores (A := A) j (fun s => (F s).2) :=
  Ignores_comp (A := A) j F Prod.snd hF

lemma Ignores_app2 {α : Type uα} {β : Type uβ} {γ : Type uγ} (j : ι)
    (F : (∀ i, A i) → α) (G : (∀ i, A i) → β) (H : α → β → γ)
    (hF : Ignores (A := A) j F) (hG : Ignores (A := A) j G) :
    Ignores (A := A) j (fun s => H (F s) (G s)) := by
  intro s a
  exact
    Trans.simple (congrFun (congrArg H (hF s a)) (G (update s j a))) (congrArg (H (F s)) (hG s a))

open Classical in
lemma Ignores_ite {α : Type uα} (j : ι)
    (c : (∀ i, A i) → Prop)
    (t e : (∀ i, A i) → α)
    (hc : IgnoresP (A := A) j c)
    (ht : Ignores (A := A) j t) (he : Ignores (A := A) j e) :
    Ignores (A := A) j (fun s => if c s then t s else e s) := by
  intro s a
  have hc' : c (update (A := A) s j a) ↔ c s := hc s a
  by_cases hcs : c s
  · have : c (update (A := A) s j a) := (hc'.2 hcs)
    exact if_ctx_congr (hc s a) (fun a_1 ↦ ht s a) fun a_1 ↦ he s a
  · have : ¬ c (update (A := A) s j a) := by
      intro h; exact hcs ((hc'.1) h)
    exact if_ctx_congr (hc s a) (fun a_1 ↦ ht s a) fun a_1 ↦ he s a

-- Prop-valued closure

lemma IgnoresP_not (j : ι) (P : (∀ i, A i) → Prop)
    (hP : IgnoresP (A := A) j P) :
    IgnoresP (A := A) j (fun s => ¬ P s) := by
  intro s a
  exact not_congr (hP s a)

lemma IgnoresP_and (j : ι) (P Q : (∀ i, A i) → Prop)
    (hP : IgnoresP (A := A) j P) (hQ : IgnoresP (A := A) j Q) :
    IgnoresP (A := A) j (fun s => P s ∧ Q s) := by
  intro s a
  simp only [update]
  exact and_congr (hP s a) (hQ s a)

lemma IgnoresP_or (j : ι) (P Q : (∀ i, A i) → Prop)
    (hP : IgnoresP (A := A) j P) (hQ : IgnoresP (A := A) j Q) :
    IgnoresP (A := A) j (fun s => P s ∨ Q s) := by
  intro s a
  simp only [update]
  exact or_congr (hP s a) (hQ s a)

lemma IgnoresP_imp (j : ι) (P Q : (∀ i, A i) → Prop)
    (hP : IgnoresP (A := A) j P) (hQ : IgnoresP (A := A) j Q) :
    IgnoresP (A := A) j (fun s => P s → Q s) := by
  intro s a
  constructor
  · intro h hp
    have hp' : P (update (A := A) s j a) := (hP s a).2 hp
    have hq' : Q (update (A := A) s j a) := h hp'
    exact (hQ s a).1 hq'
  · intro h hp
    have hp' : P s := (hP s a).1 hp
    have hq : Q s := h hp'
    exact (hQ s a).2 hq

lemma IgnoresP_iff (j : ι) (P Q : (∀ i, A i) → Prop)
    (hP : IgnoresP (A := A) j P) (hQ : IgnoresP (A := A) j Q) :
    IgnoresP (A := A) j (fun s => P s ↔ Q s) := by
  intro s a
  exact iff_congr (hP s a) (hQ s a)

end IgnoresAlgebra

end Core

-- ============================================================================
-- Bind Factorization
-- ============================================================================

section BindFactor

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
variable {A : ι → Type uA} [∀ i, Fintype (A i)]
variable {β : Type uβ}

omit [Fintype ι] [∀ i, Fintype (A i)] in
@[simp] lemma update_update_same (σ : ∀ i, PMF (A i)) (j : ι) (τ₁ τ₂ : PMF (A j)) :
    Function.update (Function.update σ j τ₁) j τ₂ = Function.update σ j τ₂ := by
  funext i; by_cases h : i = j <;> simp [Function.update, h]

omit [Fintype ι] [∀ i, Fintype (A i)] in
lemma update_update_comm (σ) {j k : ι} (hjk : j ≠ k) (τj : PMF (A j)) (τk : PMF (A k)) :
    Function.update (Function.update σ j τj) k τk =
    Function.update (Function.update σ k τk) j τj := by
  funext i
  by_cases hi : i = j <;> by_cases hk : i = k
  · subst hi hk
    simp_all only [ne_eq, not_true_eq_false]
  · subst hi
    simp_all only [not_false_eq_true, ne_eq, Function.update_of_ne, Function.update_self]
  · subst hk
    simp_all only [ne_eq, Function.update_self, not_false_eq_true, Function.update_of_ne]
  · simp_all only [ne_eq, not_false_eq_true, Function.update_of_ne]

/-- ENNReal-sum version: "Fubini" for product weights with an `Ignores₂` condition. -/
theorem sum_pmfPi_factor
    (σ : ∀ i, PMF (A i)) (j : ι)
    (F : A j → (∀ i, A i) → ENNReal)
    (hF : Ignores₂ (A := A) j F) :
    (∑ s : (∀ i, A i), (∏ i, σ i (s i)) * F (s j) s)
      =
    ∑ a : A j, (σ j a) * (∑ s : (∀ i, A i), (∏ i, σ i (s i)) * F a s) := by
  have h_one : (∑ a : A j, σ j a) = 1 := pmf_sum_eq_one (σ j)
  let W : (A j × (∀ i, A i)) → ENNReal := fun p =>
    σ j p.1 * ((σ j (p.2 j) * ∏ i ∈ Finset.univ.erase j, σ i (p.2 i)) * F p.1 p.2)
  let e := swapJA (A := A) j
  have he : Function.Involutive e := swapJA_involutive j
  -- Key: each summand under the swap equals the original summand
  have H_W_eq : ∀ (a : A j) (s : ∀ i, A i),
      σ j a * ((∏ i : ι, σ i (s i)) * F (s j) s) = W (e (a, s)) := by
    intro a s
    -- F (s j) (Function.update s j a) = F (s j) s by Ignores₂
    have hF_upd : F (s j) (@Function.update ι A (inferInstance) s j a) = F (s j) s := by
      simpa [update] using (hF (s j) s a)
    dsimp [W, e, swapJA]
    rw [prod_erase_update_eq σ j s a, hF_upd]
    simp_rw [prod_factor_erase σ j s]
    simp [mul_left_comm, mul_comm]
  calc (∑ s, (∏ i, σ i (s i)) * F (s j) s)
      = (∑ s, (∏ i, σ i (s i)) * F (s j) s) * 1 := by simp
    _ = (∑ s, (∏ i, σ i (s i)) * F (s j) s) * (∑ a, σ j a) := by
        simp [h_one]
    _ = ∑ a, ∑ s, σ j a * ((∏ i, σ i (s i)) * F (s j) s) := by
        simp only [mul_comm, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
    _ = ∑ a, ∑ s, W (e (a, s)) := by
        simp only [H_W_eq]
    _ = ∑ p : A j × (∀ i, A i), W (e p) :=
        (Fintype.sum_prod_type fun x ↦ W (e x)).symm
    _ = ∑ p : A j × (∀ i, A i), W p :=
        sum_univ_eq_sum_univ_of_involutive e he W
    _ = ∑ a, σ j a * ∑ s, (∏ i, σ i (s i)) * F a s := by
        simp [W, Fintype.sum_prod_type, Finset.mul_sum,
          prod_factor_erase σ j, mul_left_comm, mul_comm]

/-- Bind factorization over a coordinate when the continuation ignores that coordinate. -/
theorem pmfPi_bind_factor
    (σ : ∀ i, PMF (A i)) (j : ι)
    (g : A j → (∀ i, A i) → PMF β)
    (hg : Ignores₂ (A := A) j g) :
    (pmfPi (A := A) σ).bind (fun s => g (s j) s)
      =
    (σ j).bind (fun a => (pmfPi (A := A) σ).bind (fun s => g a s)) := by
  ext b
  simp only [PMF.bind_apply, pmfPi_apply, tsum_fintype]
  exact sum_pmfPi_factor σ j (fun a s => g a s b) (fun a0 s a => by
    -- Need: (g a0 (update s j a)) b = (g a0 s) b
    -- hg gives: g a0 (update s j a) = g a0 s  (as PMFs)
    exact congrFun (congrArg DFunLike.coe (hg a0 s a)) b)

end BindFactor

-- ============================================================================
-- Pushforward & Marginals
-- ============================================================================

section Pushforward

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
variable {A : ι → Type uA} [∀ i, Fintype (A i)]
variable {α : Type uα} {β : Type uβ}

/-- Pushforward of a PMF along a function. -/
noncomputable def pushforward (μ : PMF α) (f : α → β) : PMF β :=
  μ.bind (fun a => PMF.pure (f a))

/-- Pushforward composition. -/
theorem pushforward_comp {γ : Type uγ}
    (μ : PMF α) (f : α → β) (g : β → γ) :
    pushforward (pushforward μ f) g = pushforward μ (g ∘ f) := by
  simp [pushforward, PMF.bind_bind, Function.comp]

open Classical in
/-- Pointwise marginal (sum-form) for a coordinate event. -/
theorem pmfPi_coord_mass
    (σ : ∀ i, PMF (A i)) (j : ι) (a : A j) :
    (∑ s : (∀ i, A i), if s j = a then (pmfPi (A := A) σ) s else 0) = σ j a := by
  simp only [pmfPi_apply]
  -- Use the Dirac trick: substitute coordinate j with PMF.pure a
  have h_sum := pmf_sum_eq_one (pmfPi (A := A) (Function.update σ j (PMF.pure a)))
  simp only [pmfPi_apply] at h_sum
  -- Expand the updated product into indicator * rest
  have h_expand : ∀ s : (∀ i, A i),
      (∏ i : ι, (Function.update σ j (PMF.pure a)) i (s i))
        = (if s j = a then 1 else 0) *
            ∏ i ∈ Finset.univ.erase j, σ i (s i) := by
    intro s
    rw [prod_factor_erase (Function.update σ j (PMF.pure a)) j s]
    congr 1
    · simp [Function.update, PMF.pure_apply, eq_comm]
    · apply Finset.prod_congr rfl; intro i hi
      simp [Function.update, Finset.ne_of_mem_erase hi]
  simp_rw [h_expand] at h_sum
  -- h_sum : ∑ s, (if s j = a then 1 else 0) * ∏ i ∈ erase j, σ i (s i) = 1
  -- Factor out σ j a from our goal and use h_sum
  have h_factor : ∀ s : (∀ i, A i),
      (if s j = a then ∏ i, σ i (s i) else 0)
        = σ j a * ((if s j = a then 1 else 0) *
            ∏ i ∈ Finset.univ.erase j, σ i (s i)) := by
    intro s; by_cases h : s j = a
    · simp [h, prod_factor_erase σ j s]
    · simp [h]
  simp_rw [h_factor, ← Finset.mul_sum, h_sum, mul_one]

open Classical in
/-- The pushforward of a product distribution along a coordinate
    is the factor at that coordinate. -/
theorem pmfPi_push_coord
    (σ : ∀ i, PMF (A i)) (j : ι) :
    pushforward (pmfPi (A := A) σ) (fun s => s j) = σ j := by
  ext a
  simp only [pushforward, PMF.bind_apply, PMF.pure_apply,
    tsum_fintype, mul_ite, mul_one, mul_zero]
  simp_rw [@eq_comm _ a]
  exact pmfPi_coord_mass σ j a

end Pushforward

-- ============================================================================
-- Conditioning
-- ============================================================================

section Conditioning

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
variable {A : ι → Type uA} [∀ i, Fintype (A i)]
variable {α : Type uα}

open Classical in
/-- Mask a PMF by a decidable event (as an ENNReal-valued function). -/
noncomputable def pmfMask (μ : PMF α) (E : α → Prop) : α → ENNReal :=
  fun a => if E a then μ a else 0

/-- Total mass of a masked PMF. -/
noncomputable def pmfMass (μ : PMF α) (E : α → Prop) [Fintype α] : ENNReal :=
  ∑ a : α, pmfMask (μ := μ) E a

/-- Condition a PMF on an event with nonzero mass. -/
noncomputable def pmfCond (μ : PMF α) (E : α → Prop) [Fintype α]
    (h : pmfMass (μ := μ) E ≠ 0) : PMF α :=
  PMF.ofFintype
    (fun a => pmfMask (μ := μ) E a / pmfMass (μ := μ) E)
    (by
      classical
      simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
      have h_ne_top : pmfMass (μ := μ) E ≠ ⊤ := by
        apply ne_of_lt
        calc pmfMass (μ := μ) E = ∑ a, pmfMask (μ := μ) E a := rfl
          _ ≤ ∑ a : α, μ a := by
              apply Finset.sum_le_sum; intro a _; simp [pmfMask]; split_ifs <;> simp
          _ = 1 := pmf_sum_eq_one μ
          _ < ⊤ := ENNReal.one_lt_top
      exact ENNReal.mul_inv_cancel h h_ne_top)

@[simp] lemma pmfCond_apply (μ : PMF α) (E : α → Prop) [Fintype α]
    (h : pmfMass (μ := μ) E ≠ 0) (a : α) :
    pmfCond (μ := μ) E h a = pmfMask (μ := μ) E a / pmfMass (μ := μ) E := by
  simp [pmfCond, PMF.ofFintype_apply]

/-- The mass of the coordinate-lifted event under a product is the mass under the factor. -/
theorem pmfMass_pmfPi_coord
    (σ : ∀ i, PMF (A i)) (j : ι)
    (E : A j → Prop) :
    pmfMass (μ := pmfPi (A := A) σ) (fun s => E (s j))
      =
    pmfMass (μ := σ j) E := by
  classical
  simp only [pmfMass, pmfMask, pmfPi_apply]
  -- Partition the sum over s by s j values, introducing a double sum
  have hdecomp : ∀ s : (∀ i, A i),
      (if E (s j) then ∏ i, σ i (s i) else 0 : ENNReal)
      = Finset.sum Finset.univ (fun a : A j =>
          if s j = a ∧ E a then ∏ i, σ i (s i) else 0) := by
    intro s
    symm
    rw [Finset.sum_eq_single (s j)]
    · simp
    · intro b _ hb; exact if_neg (fun ⟨heq, _⟩ => hb heq.symm)
    · intro h; exact absurd (Finset.mem_univ _) h
  simp_rw [hdecomp]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  by_cases hE : E a
  · simp only [hE, and_true, ↓reduceIte]
    have := pmfPi_coord_mass σ j a
    simpa [pmfPi_apply] using this
  · simp [hE]

/-- Conditioning a product PMF on a coordinate event updates only that coordinate's factor. -/
theorem pmfPi_cond_coord
    (σ : ∀ i, PMF (A i)) (j : ι)
    (E : A j → Prop)
    (hE : pmfMass (μ := σ j) E ≠ 0) :
    pmfCond (μ := pmfPi (A := A) σ) (fun s => E (s j))
      (by
        simpa [pmfMass_pmfPi_coord (A := A) (σ := σ) (j := j) (E := E)] using hE)
      =
    pmfPi (A := A) (Function.update σ j (pmfCond (μ := σ j) E hE)) := by
  classical
  ext s
  simp only [pmfCond_apply, pmfPi_apply, pmfMask, pmfMass_pmfPi_coord]
  -- Factor the RHS product at j
  rw [prod_factor_erase (Function.update σ j (pmfCond (μ := σ j) E hE)) j s]
  -- The j-th factor
  have hj : (Function.update σ j (pmfCond (μ := σ j) E hE)) j (s j)
      = (if E (s j) then σ j (s j) else 0) / pmfMass (μ := σ j) E := by
    simp [Function.update, pmfCond_apply, pmfMask]
  rw [hj]
  -- The rest factors are unchanged
  have h_rest : (∏ i ∈ Finset.univ.erase j,
      (Function.update σ j (pmfCond (μ := σ j) E hE)) i (s i))
      = ∏ i ∈ Finset.univ.erase j, σ i (s i) := by
    apply Finset.prod_congr rfl; intro i hi
    simp [Function.update, Finset.ne_of_mem_erase hi]
  rw [h_rest, prod_factor_erase σ j s]
  -- Now algebra: LHS = (if E then σj*rest else 0) / mass
  --              RHS = ((if E then σj else 0) / mass) * rest
  by_cases hE_s : E (s j)
  · simp only [hE_s, ↓reduceIte]
    -- σ j (s j) * rest / mass = (σ j (s j) / mass) * rest
    simp only [div_eq_mul_inv, mul_comm, mul_left_comm]
  · simp [hE_s]

/-- Conditioning on coordinate `j` does not change other coordinate marginals. -/
theorem pmfPi_cond_coord_push_other
    (σ : ∀ i, PMF (A i)) {j q : ι} (hq : q ≠ j)
    (E : A j → Prop)
    (hE : pmfMass (μ := σ j) E ≠ 0) :
    pushforward
      (pmfCond (μ := pmfPi (A := A) σ) (fun s => E (s j))
        (by simpa [pmfMass_pmfPi_coord (A := A) (σ := σ) (j := j) (E := E)] using hE))
      (fun s => s q)
      =
    σ q := by
  classical
  rw [pmfPi_cond_coord σ j E hE,
      pmfPi_push_coord (Function.update σ j (pmfCond (μ := σ j) E hE)) q]
  simp [Function.update, hq]

end Conditioning

-- ============================================================================
-- PMF disintegration
-- ============================================================================

section Disintegration

variable {α : Type*} [Fintype α] {β : Type*} [Fintype β] {γ : Type*}

set_option linter.unusedFintypeInType false in
omit [Fintype β] in
/-- If `b` is in the support of `pushforward μ proj`, then the fibre
    `{a | proj a = b}` meets the support of `μ`. -/
lemma pushforward_support_fibre
    (μ : PMF α) (proj : α → β) (b : β)
    (hb : b ∈ (pushforward μ proj).support) :
    ∃ a ∈ ({a | proj a = b} : Set α), a ∈ μ.support := by
  rw [PMF.mem_support_iff] at hb
  simp only [pushforward, PMF.bind_apply, PMF.pure_apply] at hb
  by_contra hall; push_neg at hall
  apply hb; simp only [tsum_fintype]
  apply Finset.sum_eq_zero; intro a _
  rcases eq_or_ne (proj a) b with h | h
  · have hns := hall a h
    rw [PMF.mem_support_iff] at hns; push_neg at hns
    simp [h, hns]
  · simp [Ne.symm h]

set_option linter.unusedFintypeInType false in
/-- **Disintegration / law of total probability for PMF.bind.**
    Decompose `μ.bind g` by first projecting via `proj`, then conditioning on
    the projected value:
    `μ.bind g = (pushforward μ proj).bindOnSupport
        (fun b _ => (μ.filter {a | proj a = b} _).bind g)`.
    The normalisation constant in `PMF.filter` cancels against the pushforward
    weight, recovering the original `μ.bind g`. -/
theorem pmf_bind_disintegrate
    (μ : PMF α) (proj : α → β) (g : α → PMF γ) :
    μ.bind g =
    (pushforward μ proj).bindOnSupport (fun b hb =>
      (μ.filter {a | proj a = b} (pushforward_support_fibre μ proj b hb)).bind g) := by
  classical
  ext y
  let Z : β → ENNReal := fun b => ∑ a : α, if b = proj a then μ a else 0
  let W : β → ENNReal := fun b => ∑ a : α, if b = proj a then μ a * g a y else 0
  have hZ_push : ∀ b, Z b = (pushforward μ proj) b := by
    intro b
    simp [Z, pushforward, PMF.bind_apply, PMF.pure_apply]
  have hcond : ∀ b, (∀ i : α, b = proj i → μ i = 0) ↔ Z b = 0 := by
    intro b
    constructor
    · intro hb
      refine (Finset.sum_eq_zero_iff_of_nonneg ?_).2 ?_
      · intro a ha
        split_ifs <;> simp
      · intro a ha
        by_cases hba : b = proj a
        · simp [hba, hb a hba]
        · simp [hba]
    · intro hZ i hi
      have hle :
          (if b = proj i then μ i else 0) ≤ ∑ a : α, if b = proj a then μ a else 0 := by
        exact Finset.single_le_sum
          (s := Finset.univ) (f := fun a : α => if b = proj a then μ a else 0)
          (fun a _ => by simp) (Finset.mem_univ i)
      have hμle : μ i ≤ Z b := by simpa [Z, hi] using hle
      exact le_antisymm (by simpa [hZ] using hμle) bot_le
  have hterm :
      ∀ b,
        (if ∀ i : α, b = proj i → μ i = 0 then 0
          else Z b * ∑ a : α,
            ({a | proj a = b}.indicator (⇑μ) a) * (∑ a', ({a | proj a = b}.indicator (⇑μ) a'))⁻¹ *
              g a y)
          = W b := by
    intro b
    by_cases hzb : Z b = 0
    · have hb0 : ∀ i : α, b = proj i → μ i = 0 := (hcond b).2 hzb
      have hw0 : W b = 0 := by
        refine (Finset.sum_eq_zero_iff_of_nonneg ?_).2 ?_
        · intro a ha
          split_ifs <;> simp
        · intro a ha
          by_cases hba : b = proj a
          · simp [hba, hb0 a hba]
          · simp [hba]
      simp [hzb, hw0]
    · have hz_ne_top : Z b ≠ ⊤ := by
        exact ne_of_lt <| calc
          Z b = (pushforward μ proj) b := hZ_push b
          _ ≤ 1 := PMF.coe_le_one _ _
          _ < ⊤ := ENNReal.one_lt_top
      have hb0 : ¬ (∀ i : α, b = proj i → μ i = 0) := by
        exact mt (fun h => (hcond b).1 h) hzb
      have hsum_ind : (∑ a', ({a | proj a = b}.indicator (⇑μ) a')) = Z b := by
        simp [Z, Set.indicator, eq_comm]
      have hmulinv : Z b * (Z b)⁻¹ = 1 := ENNReal.mul_inv_cancel hzb hz_ne_top
      calc
        (if ∀ i : α, b = proj i → μ i = 0 then 0
          else Z b * ∑ a : α,
            ({a | proj a = b}.indicator (⇑μ) a) * (∑ a', ({a | proj a = b}.indicator (⇑μ) a'))⁻¹ *
              g a y)
            = Z b * ∑ a : α, ({a | proj a = b}.indicator (⇑μ) a) * (Z b)⁻¹ * g a y := by
                simp [hb0, hsum_ind]
        _ = ∑ a : α, if b = proj a then μ a * g a y else 0 := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro a ha
              by_cases hba : b = proj a
              · calc
                  Z b * ({a | proj a = b}.indicator (⇑μ) a * (Z b)⁻¹ * g a y)
                      = Z b * (μ a * (Z b)⁻¹ * g a y) := by simp [Set.indicator, hba]
                  _ = μ a * (Z b * ((Z b)⁻¹ * g a y)) := by ac_rfl
                  _ = μ a * ((Z b * (Z b)⁻¹) * g a y) := by ac_rfl
                  _ = μ a * (1 * g a y) := by rw [hmulinv]
                  _ = (if b = proj a then μ a * g a y else 0) := by simp [hba]
              · have hproj : proj a ≠ b := by
                  intro h
                  exact hba h.symm
                simp [hba, hproj]
        _ = W b := by
              simp [W]
  calc
    (μ.bind g) y = ∑ a : α, μ a * g a y := by simp [PMF.bind_apply, tsum_fintype]
    _ = ∑ b : β, W b := by
          calc
            (∑ a : α, μ a * g a y)
                = ∑ a : α, ∑ b : β, if b = proj a then μ a * g a y else 0 := by
                    refine Finset.sum_congr rfl ?_
                    intro a ha
                    simp
            _ = ∑ b : β, ∑ a : α, if b = proj a then μ a * g a y else 0 := by
                    simpa using (Finset.sum_comm :
                      (∑ a : α, ∑ b : β, if b = proj a then μ a * g a y else 0) =
                        ∑ b : β, ∑ a : α, if b = proj a then μ a * g a y else 0)
            _ = ∑ b : β, W b := by simp [W]
    _ = ((pushforward μ proj).bindOnSupport (fun b hb =>
          (μ.filter {a | proj a = b} (pushforward_support_fibre μ proj b hb)).bind g)) y := by
          rw [PMF.bindOnSupport_apply]
          simp only [PMF.bind_apply, PMF.filter_apply, tsum_fintype, dite_eq_ite, mul_ite, mul_zero]
          refine Finset.sum_congr rfl ?_
          intro b hb
          have hcond' :
              (∀ i : α, b = proj i → μ i = 0) ↔ (pushforward μ proj) b = 0 := by
            constructor
            · intro h
              simpa [hZ_push b] using (hcond b).1 h
            · intro h
              exact (hcond b).2 (by simpa [hZ_push b] using h)
          simpa [hZ_push b, hcond'] using (hterm b).symm

end Disintegration

-- ============================================================================
-- Family Update Lemmas
-- ============================================================================

section UpdateLemmas

variable {ι : Type uι} [Fintype ι]
variable {A : ι → Type uA} [∀ i, Fintype (A i)]
variable {β : Type uβ}

open Classical in
/-- Pointwise: updating the *factor family* at `j` only changes that coordinate's factor. -/
@[simp] lemma pmfPi_apply_update_family (σ : ∀ i, PMF (A i)) (j : ι) (τ : PMF (A j))
    (s : ∀ i, A i) :
    pmfPi (A := A) (Function.update σ j τ) s
      =
    (τ (s j)) * (∏ i ∈ Finset.univ.erase j, σ i (s i)) := by
  classical
  simp only [pmfPi_apply]
  rw [prod_factor_erase (Function.update σ j τ) j s]
  congr 1
  · simp [Function.update]
  · apply Finset.prod_congr rfl; intro i hi
    simp [Function.update, Finset.ne_of_mem_erase hi]

open Classical in
/-- A robust, division-free form: cross-multiplication of the updated and original products. -/
lemma pmfPi_update_family_mul (σ : ∀ i, PMF (A i)) (j : ι) (τ : PMF (A j))
    (s : ∀ i, A i) :
    pmfPi (A := A) (Function.update σ j τ) s * σ j (s j)
      =
    pmfPi (A := A) σ s * τ (s j) := by
  rw [pmfPi_apply_update_family, pmfPi_apply, prod_factor_erase σ j s]
  -- LHS: (τ (s j) * rest) * σ j (s j)
  -- RHS: (σ j (s j) * rest) * τ (s j)
  simp [mul_comm, mul_left_comm]

open Classical in
/-- The product PMF with one component replaced by a mixture `d` equals the mixture of
    products with that component set to pure values. This is the "Fubini" identity for `pmfPi`. -/
theorem pmfPi_update_bind (σ : ∀ i, PMF (A i)) (j : ι) (d : PMF (A j)) :
    pmfPi (A := A) (Function.update σ j d) =
      d.bind (fun a => pmfPi (A := A) (Function.update σ j (PMF.pure a))) := by
  ext s
  simp only [PMF.bind_apply, pmfPi_apply_update_family, PMF.pure_apply]
  rw [tsum_eq_single (s j)]
  · simp
  · intro b hb; simp [Ne.symm hb]

open Classical in
/-- When `f` ignores coordinate `j`, the bind of a deterministic
    product (with `pure a` at `j`) through `f` is independent of `a`.
    This is the core step for marginalizing an irrelevant coordinate. -/
private theorem pmfPi_pure_bind_ignores
    (σ : ∀ i, PMF (A i)) (j : ι) (a a' : A j)
    {β : Type*}
    (f : (∀ i, A i) → PMF β)
    (hf : Ignores j f) :
    (pmfPi (Function.update σ j (PMF.pure a))).bind f =
      (pmfPi (Function.update σ j (PMF.pure a'))).bind f := by
  ext t; simp only [PMF.bind_apply, pmfPi_apply_update_family,
    PMF.pure_apply, tsum_fintype]
  -- Use Equiv.swap at coordinate j to biject the two sums
  let e := Equiv.piCongrRight (fun i : ι =>
    if h : i = j then h ▸ Equiv.swap a a' else Equiv.refl _)
  apply Fintype.sum_equiv e; intro acts
  -- Simplify e acts at coordinate j and elsewhere
  have hej : (e acts) j = Equiv.swap a a' (acts j) := by
    simp [e, Equiv.piCongrRight_apply]
  have hene : ∀ i, i ≠ j → (e acts) i = acts i := by
    intro i hi; simp [e, Equiv.piCongrRight_apply, hi]
  -- Product over i ≠ j is unchanged
  have hprod : (∏ i ∈ Finset.univ.erase j,
      (σ i) ((e acts) i)) =
      ∏ i ∈ Finset.univ.erase j, (σ i) (acts i) := by
    apply Finset.prod_congr rfl; intro i hi
    rw [hene i (Finset.ne_of_mem_erase hi)]
  rw [hej, hprod]
  -- f(e acts) = f(acts) since f ignores j
  have hfeq : f (e acts) = f acts := by
    show f (e acts) = f acts
    have : e acts = Function.update acts j
        (Equiv.swap a a' (acts j)) := by
      ext i; by_cases hi : i = j
      · subst hi; simp [hej, Function.update_self]
      · rw [hene i hi, Function.update_of_ne hi]
    rw [this]; exact hf acts _
  rw [hfeq]
  -- Remaining: ite (acts j = a) * ... = ite (swap(acts j) = a') * ...
  congr 1; congr 1
  by_cases h : acts j = a
  · simp [h, Equiv.swap_apply_left]
  · by_cases h' : acts j = a'
    · simp [h', Equiv.swap_apply_right, eq_comm]
    · simp [h, h', Equiv.swap_apply_of_ne_of_ne h h']

open Classical in
/-- If `f` ignores coordinate `j`, then `(pmfPi σ).bind f` is
    independent of `σ j`. That is, updating `σ j` does not change
    the expected value of `f` under the product. -/
theorem pmfPi_bind_ignores_coord
    (σ : ∀ i, PMF (A i)) (j : ι) (τ : PMF (A j))
    {β : Type*}
    (f : (∀ i, A i) → PMF β)
    (hf : Ignores j f) :
    (pmfPi (Function.update σ j τ)).bind f =
      (pmfPi σ).bind f := by
  -- Decompose both sides via pmfPi_update_bind
  rw [pmfPi_update_bind, PMF.bind_bind]
  conv_rhs =>
    rw [show σ = Function.update σ j (σ j) from by
      ext i x; by_cases h : i = j
      · subst h; simp
      · simp [Function.update_of_ne h]]
    rw [pmfPi_update_bind, PMF.bind_bind]
  -- Both: d.bind g where g a = pmfPi(update σ j (pure a)).bind f
  -- g is constant by pmfPi_pure_bind_ignores, so d doesn't matter.
  -- Pick a₀ from τ's support (PMF is nonempty).
  obtain ⟨a₀, _⟩ := τ.support_nonempty
  have hconst : ∀ a,
      (pmfPi (Function.update σ j (PMF.pure a))).bind f =
      (pmfPi (Function.update σ j (PMF.pure a₀))).bind f :=
    fun a => pmfPi_pure_bind_ignores σ j a a₀ f hf
  simp_rw [hconst]; simp [PMF.bind_const]

open Classical in
/-- Repeated coordinate updates do not change `pmfPi.bind f` when `f`
    ignores every updated coordinate.

    This is a list-iterated form of `pmfPi_bind_ignores_coord`, useful when
    many coordinates are rewritten one-by-one. -/
theorem pmfPi_bind_ignores_coord_list
    (σ τ : ∀ i, PMF (A i))
    {β : Type*}
    (f : (∀ i, A i) → PMF β)
    (l : List ι)
    (hNodup : l.Nodup)
    (hf : ∀ j, j ∈ l → Ignores j f) :
    (pmfPi (l.foldl (fun fam j => Function.update fam j (τ j)) σ)).bind f =
      (pmfPi σ).bind f := by
  induction l generalizing σ with
  | nil =>
      simp
  | cons j rest ih =>
      have hNodupRest : rest.Nodup := List.Nodup.of_cons hNodup
      have hfj : Ignores j f := hf j (by simp)
      have hfRest : ∀ k, k ∈ rest → Ignores k f := by
        intro k hk
        exact hf k (by simp [hk])
      simp only [List.foldl]
      calc
        (pmfPi (rest.foldl (fun fam j => Function.update fam j (τ j))
            (Function.update σ j (τ j)))).bind f
            =
          (pmfPi (Function.update σ j (τ j))).bind f := by
              exact ih (σ := Function.update σ j (τ j)) hNodupRest hfRest
        _ = (pmfPi σ).bind f := pmfPi_bind_ignores_coord σ j (τ j) f hfj

open Classical in
/-- Finset wrapper for `pmfPi_bind_ignores_coord_list`. -/
theorem pmfPi_bind_ignores_coord_finset
    (σ τ : ∀ i, PMF (A i))
    {β : Type*}
    (f : (∀ i, A i) → PMF β)
    (J : Finset ι)
    (hf : ∀ j, j ∈ J → Ignores j f) :
    (pmfPi ((J.toList).foldl (fun fam j => Function.update fam j (τ j)) σ)).bind f =
      (pmfPi σ).bind f := by
  refine pmfPi_bind_ignores_coord_list σ τ f J.toList J.nodup_toList ?_
  intro j hj
  exact hf j ((Finset.mem_toList.mp hj))

open Classical in
omit [Fintype ι] [(i : ι) → Fintype (A i)] in
/-- Folding coordinate updates along a nodup list rewrites exactly those
    coordinates (and leaves all others unchanged). -/
lemma foldl_update_family_eq_of_nodup
    (l : List ι) (hNodup : l.Nodup)
    (σ τ : ∀ i, PMF (A i)) :
    l.foldl (fun fam j => Function.update fam j (τ j)) σ
      = fun i => if i ∈ l then τ i else σ i := by
  induction l generalizing σ with
  | nil =>
      simp
  | cons j rest ih =>
      have hNodupRest : rest.Nodup := List.Nodup.of_cons hNodup
      simp only [List.foldl]
      -- rewrite fold over `rest` with updated base family
      rw [ih (σ := Function.update σ j (τ j)) hNodupRest]
      funext i
      by_cases hi : i = j
      · subst hi
        simp
      · simp [List.mem_cons, hi]

open Classical in
/-- If a continuation ignores every coordinate, binding it under any product PMF
    collapses to the same constant PMF value. -/
theorem pmfPi_bind_eq_of_forall_ignores
    (σ : ∀ i, PMF (A i))
    {β : Type*}
    (g : (∀ i, A i) → PMF β)
    (hg : ∀ j, Ignores j g)
    (s0 : ∀ i, A i) :
    (pmfPi σ).bind g = g s0 := by
  let τ : ∀ i, PMF (A i) := fun i => PMF.pure (s0 i)
  have hfold :
      (Finset.univ.toList.foldl
          (fun fam j => Function.update fam j (τ j)) σ) = τ := by
    have htmp := foldl_update_family_eq_of_nodup
      (l := Finset.univ.toList) (σ := σ) (τ := τ) (Finset.univ.nodup_toList)
    calc
      (Finset.univ.toList.foldl (fun fam j => Function.update fam j (τ j)) σ)
          = (fun i => if i ∈ Finset.univ.toList then τ i else σ i) := htmp
      _ = τ := by
          funext i
          simp
  have hbind :
      (pmfPi τ).bind g = (pmfPi σ).bind g := by
    have h := pmfPi_bind_ignores_coord_finset (σ := σ) (τ := τ)
      (f := g) (J := Finset.univ) (hf := fun j _ => hg j)
    simpa [hfold] using h
  calc
    (pmfPi σ).bind g = (pmfPi τ).bind g := hbind.symm
    _ = g s0 := by simp [τ, pmfPi_pure]

open Classical in
/-- "Fresh bind" corollary: if `g` ignores every coordinate, then
    integrating `g` against any product PMF equals evaluating `g` at an
    assignment chosen from each factor's support. -/
theorem pmfPi_bind_comm_fresh_support
    (σ : ∀ i, PMF (A i))
    {β : Type*}
    (g : (∀ i, A i) → PMF β)
    (hg : ∀ j, Ignores j g) :
    (pmfPi σ).bind g = g (fun i => (σ i).support_nonempty.choose) :=
  pmfPi_bind_eq_of_forall_ignores (σ := σ) (g := g) hg
    (fun i => (σ i).support_nonempty.choose)

open Classical in
/-- Arbitrary-point variant of `pmfPi_bind_comm_fresh_support`. -/
theorem pmfPi_bind_comm_fresh
    (σ : ∀ i, PMF (A i))
    {β : Type*}
    (g : (∀ i, A i) → PMF β)
    (hg : ∀ j, Ignores j g)
    [∀ i, Nonempty (A i)] :
    (pmfPi σ).bind g = g (fun i => Classical.arbitrary (A i)) :=
  pmfPi_bind_eq_of_forall_ignores (σ := σ) (g := g) hg
    (fun i => Classical.arbitrary (A i))

open Classical in
omit [Fintype ι] [∀ i, Fintype (A i)] in
@[simp] lemma update_family_same (σ : ∀ i, PMF (A i)) (j : ι) (τ : PMF (A j)) :
    (Function.update σ j τ) j = τ := by
  simp [Function.update]

open Classical in
omit [Fintype ι] [∀ i, Fintype (A i)] in
@[simp] lemma update_family_other (σ : ∀ i, PMF (A i)) {i j : ι}
    (τ : PMF (A j)) (h : i ≠ j) :
    (Function.update σ j τ) i = σ i := by
  simp [Function.update, h]

open Classical in
/-- Binding a product PMF with a function-dependent coordinate update equals the
    product with that component replaced by the pushforward. -/
theorem pmfPi_bind_update_map
    (σ : ∀ i, PMF (A i)) (j : ι) (f : A j → A j) :
    (pmfPi σ).bind (fun s => PMF.pure (Function.update s j (f (s j)))) =
      pmfPi (Function.update σ j (PMF.map f (σ j))) := by
  ext s
  simp only [PMF.bind_apply, PMF.pure_apply, pmfPi_apply_update_family,
    PMF.map_apply, tsum_fintype, mul_ite, mul_one, mul_zero]
  -- Rewrite condition: s = update t j (f(t j)) ↔ (∀ i ≠ j, t i = s i) ∧ f(t j) = s j
  have hcond : ∀ t : ∀ i, A i,
      (s = Function.update t j (f (t j))) ↔
        ((∀ i, i ≠ j → t i = s i) ∧ f (t j) = s j) := by
    intro t; constructor
    · intro h; exact ⟨fun i hi => by
        have := congr_fun h i
        simp [Function.update_of_ne hi] at this; exact this.symm,
        by have := congr_fun h j
           simp [Function.update_self] at this; exact this.symm⟩
    · intro ⟨heq, hf⟩; ext i; by_cases hi : i = j
      · subst hi; simp [Function.update_self, hf]
      · rw [Function.update_of_ne hi]; exact (heq i hi).symm
  simp_rw [hcond, pmfPi_apply, prod_factor_erase σ j]
  -- Under the outer condition, the erase-product is constant
  have hprod : ∀ (x : ∀ i, A i), (∀ i, i ≠ j → x i = s i) →
      ∏ i ∈ Finset.univ.erase j, (σ i) (x i) =
        ∏ i ∈ Finset.univ.erase j, (σ i) (s i) :=
    fun x hx => Finset.prod_congr rfl fun i hi =>
      congr_arg (σ i) (hx i (Finset.ne_of_mem_erase hi))
  -- Factor out the constant product
  have hfactor : ∀ x : ∀ i, A i,
      (if ((∀ i, i ≠ j → x i = s i) ∧ f (x j) = s j) then
        (σ j) (x j) * ∏ i ∈ Finset.univ.erase j, (σ i) (x i) else 0) =
      (if (∀ i, i ≠ j → x i = s i) then
        (if f (x j) = s j then (σ j) (x j) else 0) else 0) *
        ∏ i ∈ Finset.univ.erase j, (σ i) (s i) := by
    intro x; split_ifs with h₁ h₂ <;> simp_all [hprod x]
  simp_rw [hfactor, ← Finset.sum_mul]
  congr 1
  -- Biject with ∑ a : A j via x ↦ x j, inverse a ↦ update s j a
  rw [← Finset.sum_filter]
  exact Finset.sum_nbij' (fun x => x j) (fun a => Function.update s j a)
    (fun _ _ => Finset.mem_univ _)
    (fun a _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      fun i hi => by simp [Function.update_of_ne hi]⟩)
    (fun x hx => by
      have hx' := (Finset.mem_filter.mp hx).2
      ext i; by_cases hi : i = j
      · subst hi; simp [Function.update_self]
      · simp only [Function.update_of_ne hi]; exact (hx' i hi).symm)
    (fun a _ => by simp [Function.update_self])
    (fun _ _ => by simp [eq_comm])

open Classical in
/-- Binding a product PMF with a constant coordinate update equals the product
    with that component replaced by a point mass. Special case of
    `pmfPi_bind_update_map` with `f = fun _ => x`. -/
theorem pmfPi_bind_update_pure
    (σ : ∀ i, PMF (A i)) (j : ι) (x : A j) :
    (pmfPi σ).bind (fun s => PMF.pure (Function.update s j x)) =
      pmfPi (Function.update σ j (PMF.pure x)) := by
  have h := pmfPi_bind_update_map σ j (Function.const _ x)
  simp only [PMF.map_const] at h; exact h

end UpdateLemmas

-- ============================================================================
-- Conditioning on Coordinates & Mass Invariance
-- ============================================================================

section ConditioningCoord

variable {ι : Type uι} [Fintype ι]
variable {A : ι → Type uA} [∀ i, Fintype (A i)]

-- ---- Convenience alias ---------------------------------------------------

open Classical in
/-- Update family at `j` (thin wrapper around `Function.update`). -/
noncomputable def updateAt (σ : ∀ i, PMF (A i)) (j : ι) (τ : PMF (A j)) : ∀ i, PMF (A i) :=
  Function.update σ j τ

open Classical in
/-- Conditioning a product on a coordinate event = product of updated family (`updateAt` form). -/
theorem pmfPi_cond_coord_updateAt
    (σ : ∀ i, PMF (A i)) (j : ι)
    (E : A j → Prop)
    (hE : pmfMass (μ := σ j) E ≠ 0) :
    pmfCond (μ := pmfPi (A := A) σ) (fun s => E (s j))
      (by
        simpa [pmfMass_pmfPi_coord (A := A) (σ := σ) (j := j) (E := E)] using hE)
      =
    pmfPi (A := A) (updateAt (A := A) σ j (pmfCond (μ := σ j) E hE)) := by
  -- updateAt unfolds to Function.update, so this is exactly pmfPi_cond_coord.
  exact pmfPi_cond_coord σ j E hE

open Classical in
/-- Other marginals are unchanged after conditioning on a coordinate. -/
theorem pmfPi_cond_coord_other_marginal
    (σ : ∀ i, PMF (A i)) {j q : ι} (hq : q ≠ j)
    (E : A j → Prop)
    (hE : pmfMass (μ := σ j) E ≠ 0) :
    pushforward
      (pmfCond (μ := pmfPi (A := A) σ) (fun s => E (s j))
        (by simpa [pmfMass_pmfPi_coord (A := A) (σ := σ) (j := j) (E := E)] using hE))
      (fun s => s q)
      =
    σ q := by
  exact pmfPi_cond_coord_push_other σ hq E hE

-- ---- Event mass under product PMFs --------------------------------------

open Classical in
/-- The "event mass" of a predicate under a product PMF (sum form). -/
noncomputable def pmfPiMass (σ : ∀ i, PMF (A i))
    (P : (∀ i, A i) → Prop) : ENNReal :=
  ∑ s : (∀ i, A i), if P s then pmfPi (A := A) σ s else 0

/-- Basic bound: event mass ≤ 1 (hence never `⊤`). -/
lemma pmfPiMass_le_one (σ : ∀ i, PMF (A i)) (P : (∀ i, A i) → Prop) :
    pmfPiMass (A := A) σ P ≤ 1 := by
  classical
  -- pointwise: ite ≤ μ s
  have hle : ∀ s : (∀ i, A i),
      (if P s then pmfPi (A := A) σ s else 0) ≤ (pmfPi (A := A) σ s) := by
    intro s; by_cases h : P s <;> simp [h]
  have hsum :
      (∑ s : (∀ i, A i), if P s then pmfPi (A := A) σ s else 0)
        ≤
      (∑ s : (∀ i, A i), pmfPi (A := A) σ s) := by
    -- `Finset.sum_le_sum` on `univ`
    simpa using
      (Finset.sum_le_sum (s := (Finset.univ : Finset (∀ i, A i)))
        (fun s _hs => hle s))
  -- rewrite the RHS sum to `1`
  have htot : (∑ s : (∀ i, A i), pmfPi (A := A) σ s) = 1 :=
    pmf_sum_eq_one (pmfPi (A := A) σ)
  -- finish
  exact le_of_le_of_eq hsum htot

lemma pmfPiMass_ne_top (σ : ∀ i, PMF (A i)) (P : (∀ i, A i) → Prop) :
    pmfPiMass (A := A) σ P ≠ (⊤ : ENNReal) := by
  exact ne_of_lt (lt_of_le_of_lt (pmfPiMass_le_one (A := A) σ P) (by simp))

/-- Mass of the always-true event is 1. -/
lemma pmfPiMass_true (σ : ∀ i, PMF (A i)) :
    pmfPiMass (A := A) σ (fun _ : (∀ i, A i) => True) = 1 := by
  classical
  simpa [pmfPiMass] using (pmf_sum_eq_one (pmfPi (A := A) σ))

-- ---- Cross-multiplication & mass invariance ------------------------------

open Classical in
/-- The ratio of an event's mass is invariant under updating coordinate `j`,
    provided the event ignores coordinate `j`. -/
theorem pmfPi_event_ratio_invariant_of_ignores
    (σ : ∀ i, PMF (A i)) (j : ι) (τ : PMF (A j))
    (Num Denom : (∀ i, A i) → Prop)
    (hNum_ign : Ignores (A := A) j Num)
    (hDenom_ign : Ignores (A := A) j Denom) :
    (∑ s, if Num s then pmfPi (A := A) (Function.update σ j τ) s else 0)
      * (∑ s, if Denom s then pmfPi (A := A) σ s else 0)
      =
    (∑ s, if Num s then pmfPi (A := A) σ s else 0)
      * (∑ s, if Denom s then pmfPi (A := A) (Function.update σ j τ) s else 0) := by
  let W : (∀ i, A i) × (∀ i, A i) → ENNReal := fun p =>
    (if Num p.1 then pmfPi (A := A) (Function.update σ j τ) p.1 else 0) *
    (if Denom p.2 then pmfPi (A := A) σ p.2 else 0)
  let W_CD : (∀ i, A i) × (∀ i, A i) → ENNReal := fun p =>
    (if Num p.1 then pmfPi (A := A) σ p.1 else 0) *
    (if Denom p.2 then pmfPi (A := A) (Function.update σ j τ) p.2 else 0)
  -- The swap bijection
  let e : (∀ i, A i) × (∀ i, A i) → (∀ i, A i) × (∀ i, A i) :=
    fun p => (update (A := A) p.1 j (p.2 j), update (A := A) p.2 j (p.1 j))
  have he : Function.Involutive e := by
    intro ⟨s1, s2⟩
    dsimp [e]
    congr 1
    · ext i; by_cases hi : i = j
      · subst hi; simp
      · simp [hi]
    · ext i; by_cases hi : i = j
      · subst hi; simp
      · simp [hi]
  have hW : ∀ p, W (e p) = W_CD p := by
    intro ⟨s1, s2⟩
    dsimp only [W, W_CD, e]
    -- The events ignore j, so the conditions match.
    have hNum_eq : Num (update (A := A) s1 j (s2 j)) = Num s1 := by
      simpa [update] using (hNum_ign s1 (s2 j))
    have hDen_eq : Denom (update (A := A) s2 j (s1 j)) = Denom s2 := by
      simpa [update] using (hDenom_ign s2 (s1 j))
    simp_rw [hNum_eq, hDen_eq]
    have h1 : pmfPi (A := A) (Function.update σ j τ) (update (A := A) s1 j (s2 j))
              = τ (s2 j) * ∏ i ∈ Finset.univ.erase j, σ i (s1 i) := by
      rw [pmfPi_apply_update_family]
      congr 1
      · simp
      · apply Finset.prod_congr rfl; intro i hi
        simp [Finset.ne_of_mem_erase hi]
    have h2 : pmfPi (A := A) σ (update (A := A) s2 j (s1 j)) = σ j (s1 j)
              * ∏ i ∈ Finset.univ.erase j, σ i (s2 i) := by
      rw [pmfPi_apply, prod_factor_erase σ j (update (A := A) s2 j (s1 j))]
      congr 1
      · simp
      · apply Finset.prod_congr rfl; intro i hi
        simp [Finset.ne_of_mem_erase hi]
    have h3 : pmfPi (A := A) σ s1 = σ j (s1 j) * ∏ i ∈ Finset.univ.erase j, σ i (s1 i) := by
      rw [pmfPi_apply, prod_factor_erase σ j s1]
    have h4 : pmfPi (A := A) (Function.update σ j τ) s2 = τ (s2 j)
              * ∏ i ∈ Finset.univ.erase j, σ i (s2 i) := by
      rw [pmfPi_apply_update_family]
    -- Substitute all evaluations back into the equality
    rw [h1, h2, h3, h4]
    -- Push the if-statements and sort the commutative factors
    by_cases hN : Num s1 <;> by_cases hD : Denom s2
    · simp only [hN, hD, ↓reduceIte]
      simp only [mul_comm, mul_left_comm]
    · simp [hN, hD]
    · simp [hN, hD]
    · simp [hN, hD]
  -- Finally, thread the double sum through the bijection
  calc (∑ s, if Num s then pmfPi (A := A) (Function.update σ j τ) s else 0)
     * (∑ s, if Denom s then pmfPi (A := A) σ s else 0)
    _ = ∑ s1, ∑ s2, (if Num s1 then pmfPi (A := A) (Function.update σ j τ) s1 else 0)
      * (if Denom s2 then pmfPi (A := A) σ s2 else 0) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro s1 _
        rw [Finset.mul_sum]
    _ = ∑ p : (∀ i, A i) × (∀ i, A i), W p := (Fintype.sum_prod_type W).symm
    _ = ∑ p : (∀ i, A i) × (∀ i, A i), W (e p) := (sum_univ_eq_sum_univ_of_involutive e he W).symm
    _ = ∑ p : (∀ i, A i) × (∀ i, A i), W_CD p := by
        apply Finset.sum_congr rfl; intro p _
        exact hW p
    _ = ∑ s1, ∑ s2, W_CD (s1, s2) := Fintype.sum_prod_type W_CD
    _ = (∑ s, if Num s then pmfPi (A := A) σ s else 0)
      * (∑ s, if Denom s then pmfPi (A := A) (Function.update σ j τ) s else 0) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro s1 _
        rw [Finset.mul_sum]

open Classical in
/-- Mass is invariant under updating coordinate `j`, if the event ignores `j`. -/
theorem pmfPi_mass_invariant_of_ignores
    (σ : ∀ i, PMF (A i)) (j : ι) (τ : PMF (A j))
    (P : (∀ i, A i) → Prop)
    (hP : Ignores (A := A) j P) :
    pmfPiMass (A := A) (Function.update σ j τ) P
      =
    pmfPiMass (A := A) σ P := by
  classical
  have h :=
    pmfPi_event_ratio_invariant_of_ignores
      (A := A) (σ := σ) (j := j) (τ := τ)
      (Num := P) (Denom := (fun _ : (∀ i, A i) => True))
      (hNum_ign := hP)
      (hDenom_ign := (by intro s a; rfl))
  -- h : mU * mass(True under old) = mO * mass(True under updated)
  -- rewrite both True-masses to 1, then simp
  have h' :
      pmfPiMass (A := A) (Function.update σ j τ) P * 1
        =
      pmfPiMass (A := A) σ P * 1 := by
    -- first rewrite the two True-masses in `h` to `1`
    have hT_old :
        (∑ s : (∀ i, A i), if (fun _ => True) s then (pmfPi (A := A) σ) s else 0) = 1 := by
      simpa using (pmf_sum_eq_one (pmfPi (A := A) σ))
    have hT_upd :
        (∑ s : (∀ i, A i),
          if (fun _ => True) s
          then (pmfPi (A := A) (Function.update σ j τ)) s else 0) = 1 := by
      simpa using (pmf_sum_eq_one (pmfPi (A := A) (Function.update σ j τ)))
    -- now `simp` actually has concrete rewrite rules for those factors
    simp_all only [pmfPi_apply, ↓reduceIte, mul_one]
    exact h
  simpa [mul_one] using h'

open Classical in
/-- Conditional probability (ratio of masses) is invariant under updating coordinate `j`,
    provided both events ignore `j` and both denominators have nonzero mass. -/
theorem pmfPi_cond_prob_invariant_of_ignores
    (σ : ∀ i, PMF (A i)) (j : ι) (τ : PMF (A j))
    (Num Denom : (∀ i, A i) → Prop)
    (hNum : Ignores (A := A) j Num)
    (hDen : Ignores (A := A) j Denom)
    (hDO : pmfPiMass (A := A) σ Denom ≠ 0)
    (hDU : pmfPiMass (A := A) (Function.update σ j τ) Denom ≠ 0) :
    (pmfPiMass (A := A) (Function.update σ j τ) Num)
     / (pmfPiMass (A := A) (Function.update σ j τ) Denom)
      =
    (pmfPiMass (A := A) σ Num) / (pmfPiMass (A := A) σ Denom) := by
  classical
  -- abbreviate the four masses
  set mNU : ENNReal := pmfPiMass (A := A) (Function.update σ j τ) Num
  set mDU : ENNReal := pmfPiMass (A := A) (Function.update σ j τ) Denom
  set mNO : ENNReal := pmfPiMass (A := A) σ Num
  set mDO : ENNReal := pmfPiMass (A := A) σ Denom
  have hcross :
      mNU * mDO = mNO * mDU := by
    -- your cross-multiplication lemma, just unfolded
    simpa [mNU, mDU, mNO, mDO, pmfPiMass]
      using
        (pmfPi_event_ratio_invariant_of_ignores
          (A := A) (σ := σ) (j := j) (τ := τ)
          (Num := Num) (Denom := Denom) hNum hDen)
  -- non-top facts (needed for ENNReal.mul_inv_cancel)
  have hDO_top : mDO ≠ (⊤ : ENNReal) := by
    simpa [mDO] using pmfPiMass_ne_top (A := A) (σ := σ) (P := Denom)
  have hDU_top : mDU ≠ (⊤ : ENNReal) := by
    simpa [mDU] using pmfPiMass_ne_top (A := A) (σ := Function.update σ j τ) (P := Denom)
  have : mNU * mDU⁻¹ = mNO * mDO⁻¹ := by
    -- Step 1: cancel mDU on the RHS of hcross
    have h1 : (mNU * mDO) * mDU⁻¹ = mNO := by
      have := congrArg (fun x => x * mDU⁻¹) hcross
      -- RHS: (mNO * mDU) * mDU⁻¹ = mNO * (mDU * mDU⁻¹) = mNO
      -- LHS stays as (mNU * mDO) * mDU⁻¹
      simpa [mul_assoc, mul_left_comm, mul_comm,
        ENNReal.mul_inv_cancel hDU hDU_top] using this
    -- Step 2: multiply by mDO⁻¹ and cancel mDO on the LHS
    have h2 : ((mNU * mDO) * mDU⁻¹) * mDO⁻¹ = mNO * mDO⁻¹ := by
      exact congrArg (fun x => x * mDO⁻¹) h1
    -- Reassociate/commute: ((mNU*mDO)*mDU⁻¹)*mDO⁻¹ = (mNU*mDU⁻¹)*(mDO*mDO⁻¹) = mNU*mDU⁻¹
    have : mNU * mDU⁻¹ = mNO * mDO⁻¹ := by
      have h3 :
          ((mNU * mDO) * mDU⁻¹) * mDO⁻¹ = mNU * mDU⁻¹ := by
        calc
          ((mNU * mDO) * mDU⁻¹) * mDO⁻¹
              = (mNU * mDU⁻¹) * (mDO * mDO⁻¹) := by
                  ac_rfl
          _ = (mNU * mDU⁻¹) * 1 := by
                  simp [ENNReal.mul_inv_cancel hDO hDO_top]
          _ = mNU * mDU⁻¹ := by simp
      -- now rewrite h2 using h3
      simpa [h3] using h2
    exact this
  -- rewrite / as * inv
  simpa [div_eq_mul_inv, mNU, mDU, mNO, mDO] using this

end ConditioningCoord

-- ============================================================================
-- Product-measure independence for bind
-- ============================================================================

section BindIndep

variable {ι : Type uι}
variable {A : ι → Type uA}

open Classical in
/-- Replace coordinates in `K` of `x` by those of `y`. -/
noncomputable def replaceOn (K : Finset ι) (x y : ∀ i, A i) : (∀ i, A i) :=
  fun i => if i ∈ K then y i else x i

open Classical in
@[simp] lemma replaceOn_apply (K : Finset ι) (x y : ∀ i, A i) (i : ι) :
    replaceOn K x y i = (if i ∈ K then y i else x i) := rfl

@[simp] lemma replaceOn_empty (x y : ∀ i, A i) :
    replaceOn (A := A) (K := ∅) x y = x := by
  funext i
  simp [replaceOn]

open Classical in
lemma replaceOn_insert (K : Finset ι) (j : ι) (hj : j ∉ K)
    (x y : ∀ i, A i) :
    replaceOn (A := A) (K := insert j K) x y =
      Function.update (replaceOn (A := A) (K := K) x y) j (y j) := by
  funext i
  by_cases hi : i = j
  · subst hi
    simp [replaceOn]
  · simp [replaceOn, hi]

open Classical in
lemma ignores_replaceOn_eq
    {β : Type*}
    (h : (∀ i, A i) → β)
    (K : Finset ι)
    (hign : ∀ j, j ∈ K → Ignores j h)
    (x y : ∀ i, A i) :
    h (replaceOn (A := A) K x y) = h x := by
  induction K using Finset.induction with
  | empty =>
      simp [replaceOn_empty]
  | @insert j K hj ih =>
      have hignj : Ignores j h := hign j (by simp)
      have hignK : ∀ k, k ∈ K → Ignores k h := by
        intro k hk
        exact hign k (by simp [hk])
      rw [replaceOn_insert (A := A) K j hj x y]
      have hstep :
          h (@Function.update ι A (inferInstance) (replaceOn (A := A) (K := K) x y) j (y j))
            = h (replaceOn (A := A) (K := K) x y) := by
        simpa [update] using (hignj (replaceOn (A := A) (K := K) x y) (y j))
      rw [hstep]
      exact ih hignK

lemma replaceOn_univ_snd [Fintype ι] (x y : ∀ i, A i) :
    replaceOn (A := A) (K := Finset.univ) x y = y := by
  funext i
  simp [replaceOn]

open Classical in
lemma replaceOn_univ_diff [Fintype ι] (J : Finset ι) (x y : ∀ i, A i) :
    replaceOn (A := A) (K := Finset.univ \ J) x y =
      fun i => if i ∈ J then x i else y i := by
  funext i
  by_cases hi : i ∈ J
  · simp [replaceOn, hi]
  · simp [replaceOn, hi]

open Classical in
/-- **Product-measure independence for bind.**
    If `f` uses only `J`-coordinates (i.e., ignores all `j ∉ J`) and
    `g b` ignores `J`-coordinates, then drawing once from `pmfPi σ` and
    using the same sample for both `f` and `g` gives the same distribution
    as drawing independently for each. -/
theorem pmfPi_bind_indep [Fintype ι] [∀ i, Fintype (A i)]
    {β γ : Type*} [Finite β]
    (σ : ∀ i, PMF (A i))
    (f : (∀ i, A i) → PMF β)
    (g : β → (∀ i, A i) → PMF γ)
    (J : Finset ι)
    (hf : ∀ j, j ∉ J → Ignores j f)
    (hg : ∀ j, j ∈ J → ∀ b, Ignores j (g b)) :
    (pmfPi σ).bind (fun s => (f s).bind (fun b => g b s)) =
    (pmfPi σ).bind (fun s => (f s).bind (fun b =>
      (pmfPi σ).bind (fun t => g b t))) := by
  classical
  letI : Fintype β := Fintype.ofFinite β
  ext y
  simp only [PMF.bind_apply, pmfPi_apply, tsum_fintype]
  let P : (∀ i, A i) → ENNReal := fun s => ∏ i, σ i (s i)
  let Fsame : ((∀ i, A i) × (∀ i, A i)) → ENNReal :=
    fun p => (P p.1 * P p.2) * ∑ b : β, f p.1 b * g b p.1 y
  let Fcross : ((∀ i, A i) × (∀ i, A i)) → ENNReal :=
    fun p => (P p.1 * P p.2) * ∑ b : β, f p.1 b * g b p.2 y
  let e : ((∀ i, A i) × (∀ i, A i)) → ((∀ i, A i) × (∀ i, A i)) :=
    fun p => (replaceOn (A := A) (Finset.univ \ J) p.1 p.2,
              replaceOn (A := A) J p.1 p.2)
  have he : Function.Involutive e := by
    intro p
    rcases p with ⟨s, t⟩
    apply Prod.ext
    · funext i
      by_cases hiJ : i ∈ J
      · simp [e, replaceOn, hiJ]
      · simp [e, replaceOn, hiJ]
    · funext i
      by_cases hiJ : i ∈ J
      · simp [e, replaceOn, hiJ]
      · simp [e, replaceOn, hiJ]
  have hpoint : ∀ p, Fcross p = Fsame (e p) := by
    intro p
    rcases p with ⟨s, t⟩
    set s' : (∀ i, A i) := replaceOn (A := A) (Finset.univ \ J) s t
    set t' : (∀ i, A i) := replaceOn (A := A) J s t
    have hweight : P s * P t = P s' * P t' := by
      simp only [P]
      calc
        (∏ i, σ i (s i)) * (∏ i, σ i (t i))
            = ∏ i, (σ i (s i) * σ i (t i)) := by rw [← Finset.prod_mul_distrib]
        _ = ∏ i, (σ i (s' i) * σ i (t' i)) := by
            refine Finset.prod_congr rfl ?_
            intro i hi
            by_cases hiJ : i ∈ J
            · simp [s', t', hiJ]
            · simp [s', t', hiJ, mul_comm]
        _ = (∏ i, σ i (s' i)) * (∏ i, σ i (t' i)) := by rw [Finset.prod_mul_distrib]
    have hf' : f s' = f s := by
      have hignOut : ∀ j, j ∈ (Finset.univ \ J) → Ignores j f := by
        intro j hj
        exact hf j (by simpa using hj)
      simpa [s', replaceOn] using
        (ignores_replaceOn_eq (A := A) f (Finset.univ \ J) hignOut s t)
    have hg' : ∀ b : β, g b s' = g b t := by
      intro b
      have hignIn : ∀ j, j ∈ J → Ignores j (g b) := fun j hj => hg j hj b
      -- s' = replaceOn J t s
      have hs' : s' = replaceOn (A := A) J t s := by
        funext i
        by_cases hiJ : i ∈ J
        · simp [s', replaceOn, hiJ]
        · simp [s', replaceOn, hiJ]
      rw [hs']
      simpa using (ignores_replaceOn_eq (A := A) (g b) J hignIn t s)
    simp [Fcross, Fsame, e, s', t', hweight, hf', hg']
  have hpair : (∑ p, Fcross p) = ∑ p, Fsame p := by
    calc
      (∑ p, Fcross p) = ∑ p, Fsame (e p) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact hpoint p
      _ = ∑ p, Fsame p := sum_univ_eq_sum_univ_of_involutive e he Fsame
  have hsumP : (∑ t : (∀ i, A i), P t) = 1 := by
    simpa [P] using (pmf_sum_eq_one (pmfPi (A := A) σ))
  have hL :
      (∑ s : (∀ i, A i), (∏ i, σ i (s i)) * ∑ b : β, f s b * g b s y)
      = ∑ p : ((∀ i, A i) × (∀ i, A i)), Fsame p := by
    calc
      (∑ s : (∀ i, A i), (∏ i, σ i (s i)) * ∑ b : β, f s b * g b s y)
          = (∑ s : (∀ i, A i), (∏ i, σ i (s i)) * ∑ b : β, f s b * g b s y)
              * (∑ t : (∀ i, A i), P t) := by
              simp [hsumP]
      _ = ∑ p : ((∀ i, A i) × (∀ i, A i)), Fsame p := by
          simp [Fsame, P, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul,
            mul_assoc, mul_comm]
  have hR :
      (∑ s : (∀ i, A i),
          (∏ i, σ i (s i)) * ∑ b : β, f s b * ∑ t : (∀ i, A i), (∏ i, σ i (t i)) * g b t y)
      = ∑ p : ((∀ i, A i) × (∀ i, A i)), Fcross p := by
    calc
      (∑ s : (∀ i, A i),
          (∏ i, σ i (s i)) * ∑ b : β, f s b * ∑ t : (∀ i, A i), (∏ i, σ i (t i)) * g b t y)
          = ∑ s : (∀ i, A i), ∑ t : (∀ i, A i),
              (P s * P t) * ∑ b : β, f s b * g b t y := by
                apply Finset.sum_congr rfl
                intro s hs
                calc
                  (∏ i, σ i (s i)) * ∑ b : β, f s b * ∑ t : (∀ i, A i), (∏ i, σ i (t i)) * g b t y
                      = ∑ b : β, ∑ t : (∀ i, A i),
                          (P s) * (f s b * (P t * g b t y)) := by
                            simp [P, Finset.mul_sum, mul_comm]
                  _ = ∑ t : (∀ i, A i), ∑ b : β,
                        (P s) * (f s b * (P t * g b t y)) := by
                            simpa using
                              (Finset.sum_comm :
                                (∑ b : β, ∑ t : (∀ i, A i), (P s) * (f s b * (P t * g b t y)))
                                  = ∑ t : (∀ i, A i), ∑ b : β,
                                      (P s) * (f s b * (P t * g b t y)))
                  _ = ∑ t : (∀ i, A i), (P s * P t) * ∑ b : β, f s b * g b t y := by
                        apply Finset.sum_congr rfl
                        intro t ht
                        calc
                          ∑ b : β, (P s) * (f s b * (P t * g b t y))
                              = ∑ b : β, ((P s * P t) * (f s b * g b t y)) := by
                                  apply Finset.sum_congr rfl
                                  intro b hb
                                  ac_rfl
                          _ = (P s * P t) * ∑ b : β, f s b * g b t y := by
                                  rw [Finset.mul_sum]
      _ = ∑ p : ((∀ i, A i) × (∀ i, A i)), Fcross p := by
          simp [Fcross, Fintype.sum_prod_type]
  calc
    (∑ s : (∀ i, A i), (∏ i, σ i (s i)) * ∑ b : β, f s b * g b s y)
        = ∑ p : ((∀ i, A i) × (∀ i, A i)), Fsame p := hL
    _ = ∑ p : ((∀ i, A i) × (∀ i, A i)), Fcross p := by simpa using hpair.symm
    _ =
        (∑ s : (∀ i, A i),
          (∏ i, σ i (s i)) * ∑ b : β, f s b * ∑ t : (∀ i, A i), (∏ i, σ i (t i)) * g b t y) :=
      hR.symm

end BindIndep

end PMFProduct
end Math

