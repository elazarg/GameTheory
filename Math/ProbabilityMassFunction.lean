import Math.Probability
import Mathlib.Probability.ProbabilityMassFunction.Constructions

set_option autoImplicit false

/-!
# PMF Utilities

Canonical home for generic PMF utilities: pushforward, bind congruence, support
extensionality, conditioning (`condOn`), and sequential fold/bind composition.
Does not cover product structure (see `PMFProduct.lean`).
-/

namespace Math
namespace ProbabilityMassFunction

variable {α β γ : Type*}

noncomputable def pushforward (μ : PMF α) (f : α → β) : PMF β :=
  μ.bind (fun a => PMF.pure (f a))

theorem pushforward_comp
    (μ : PMF α) (f : α → β) (g : β → γ) :
    pushforward (pushforward μ f) g = pushforward μ (g ∘ f) := by
  simp [pushforward, PMF.bind_bind, Function.comp]

theorem pushforward_pushforward
    (μ : PMF α) (f : α → β) (g : β → γ) :
    pushforward (pushforward μ f) g = pushforward μ (g ∘ f) :=
  pushforward_comp μ f g

theorem pushforward_id (μ : PMF α) :
    pushforward μ id = μ := by
  simp [pushforward]

theorem pushforward_pure (a : α) (f : α → β) :
    pushforward (PMF.pure a) f = PMF.pure (f a) := by
  simp [pushforward]

theorem bind_pure_eq_pushforward
    (μ : PMF α) (f : α → β) :
    μ.bind (fun a => PMF.pure (f a)) = pushforward μ f := by
  rfl

theorem bind_assoc
    (μ : PMF α) (f : α → PMF β) (g : β → PMF γ) :
    (μ.bind f).bind g = μ.bind (fun a => (f a).bind g) := by
  exact PMF.bind_bind (p := μ) (f := f) (g := g)

theorem pushforward_bind
    (μ : PMF α) (k : α → PMF β) (f : β → γ) :
    pushforward (μ.bind k) f = μ.bind (fun a => pushforward (k a) f) := by
  simp [pushforward, PMF.bind_bind]

theorem bind_congr_on_support
    (μ : PMF α) (f g : α → PMF β)
    (hfg : ∀ a, a ∈ μ.support → f a = g a) :
    μ.bind f = μ.bind g := by
  ext b
  simp only [PMF.bind_apply]
  refine tsum_congr (fun a => ?_)
  by_cases ha0 : μ a = 0
  · simp [ha0]
  · have haS : a ∈ μ.support := by
      simpa [PMF.mem_support_iff] using ha0
    rw [hfg a haS]

theorem bind_congr_of_ne_zero
    (μ : PMF α) (f g : α → PMF β)
    (hfg : ∀ a, μ a ≠ 0 → f a = g a) :
    μ.bind f = μ.bind g := by
  exact bind_congr_on_support μ f g (fun a ha => hfg a (by simpa [PMF.mem_support_iff] using ha))

theorem expect_congr_on_support
    {Ω : Type*} (μ : PMF Ω) (f g : Ω → ℝ)
    (hfg : ∀ a, a ∈ μ.support → f a = g a) :
    Math.Probability.expect μ f = Math.Probability.expect μ g := by
  unfold Math.Probability.expect
  refine tsum_congr (fun a => ?_)
  by_cases ha0 : μ a = 0
  · simp [ha0]
  · have haS : a ∈ μ.support := by
      simpa [PMF.mem_support_iff] using ha0
    rw [hfg a haS]

theorem expect_congr_of_ne_zero
    {Ω : Type*} (μ : PMF Ω) (f g : Ω → ℝ)
    (hfg : ∀ a, μ a ≠ 0 → f a = g a) :
    Math.Probability.expect μ f = Math.Probability.expect μ g := by
  exact expect_congr_on_support μ f g (fun a ha => hfg a (by simpa [PMF.mem_support_iff] using ha))

theorem expect_pushforward
    {Ω Ξ : Type*} [Finite Ω] [Finite Ξ]
    (μ : PMF Ω) (f : Ω → Ξ) (φ : Ξ → ℝ) :
    Math.Probability.expect (pushforward μ f) φ =
      Math.Probability.expect μ (fun a => φ (f a)) := by
  classical
  letI : Fintype Ω := Fintype.ofFinite Ω
  letI : Fintype Ξ := Fintype.ofFinite Ξ
  simp [pushforward, Math.Probability.expect_bind]

theorem expect_bind_congr_on_support
    {Ω Ξ : Type*}
    (μ : PMF Ω) (k₁ k₂ : Ω → PMF Ξ) (φ : Ξ → ℝ)
    (hk : ∀ a, a ∈ μ.support → k₁ a = k₂ a) :
    Math.Probability.expect (μ.bind k₁) φ =
      Math.Probability.expect (μ.bind k₂) φ := by
  rw [bind_congr_on_support (μ := μ) (f := k₁) (g := k₂) hk]

set_option linter.unusedFintypeInType false in
open Classical in
theorem bind_apply_eq_sum_sum_fiber
    {β γ : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (proj : α → β) (g : α → PMF γ) (x : γ) :
    (μ.bind g) x =
      ∑ b : β, ∑ a : α, (if proj a = b then μ a else 0) * g a x := by
  simp only [PMF.bind_apply, tsum_fintype]
  rw [show ∑ a, μ a * g a x =
      ∑ a, ∑ b : β, if proj a = b then μ a * g a x else 0 from by
    congr 1
    funext a
    exact Eq.symm (Fintype.sum_ite_eq (proj a) (fun _ => μ a * (g a) x))]
  rw [Finset.sum_comm]
  congr 1
  funext b
  congr 1
  funext a
  split_ifs <;> ring

set_option linter.unusedFintypeInType false in
open Classical in
theorem le_pushforward_apply
    {β : Type*} [Fintype α]
    (μ : PMF α) (proj : α → β) (a : α) :
    μ a ≤ pushforward μ proj (proj a) := by
  have hle :
      (if proj a = proj a then (μ a : ENNReal) else 0) ≤
        ∑ t : α, if proj a = proj t then (μ t : ENNReal) else 0 := by
    exact Finset.single_le_sum
      (f := fun t : α => if proj a = proj t then (μ t : ENNReal) else 0)
      (fun _ _ => by positivity)
      (Finset.mem_univ a)
  simpa [pushforward, PMF.bind_apply, PMF.pure_apply, tsum_fintype] using hle

set_option linter.unusedFintypeInType false in
open Classical in
theorem eq_zero_of_pushforward_eq_zero
    {β : Type*} [Fintype α]
    (μ : PMF α) (proj : α → β) {b : β}
    (hb : pushforward μ proj b = 0)
    {a : α} (ha : proj a = b) :
    μ a = 0 := by
  have hle : μ a ≤ pushforward μ proj b := by
    simpa [ha] using le_pushforward_apply (μ := μ) (proj := proj) a
  rw [hb] at hle
  exact le_antisymm hle bot_le

set_option linter.unusedFintypeInType false in
open Classical in
noncomputable def condOn
    {β : Type*} [Fintype α]
    (μ : PMF α) (proj : α → β) (b : β) : PMF α :=
  let p_b := pushforward μ proj b
  if hb : p_b = 0 then μ
  else
    PMF.ofFintype
      (fun a => if proj a = b then μ a / p_b else 0)
      (by
        rw [show (∑ a, if proj a = b then μ a / p_b else (0 : ENNReal)) =
            (∑ a, (if proj a = b then (μ a : ENNReal) else 0) * p_b⁻¹) from
          Finset.sum_congr rfl (fun a _ => by split_ifs <;> simp [div_eq_mul_inv]),
          ← Finset.sum_mul]
        have h_sum : (∑ a : α, if proj a = b then (μ a : ENNReal) else 0) = p_b := by
          change _ = pushforward μ proj b
          simp [pushforward, PMF.bind_apply, PMF.pure_apply, tsum_fintype, eq_comm]
        rw [h_sum]
        exact ENNReal.mul_inv_cancel hb (PMF.apply_ne_top (pushforward μ proj) b))

set_option linter.unusedFintypeInType false in
open Classical in
theorem condOn_apply
    {β : Type*} [Fintype α]
    (μ : PMF α) (proj : α → β) (b : β)
    (a : α) (hb : pushforward μ proj b ≠ 0) :
    condOn μ proj b a = if proj a = b then μ a / pushforward μ proj b else 0 := by
  simp [condOn, hb, PMF.ofFintype_apply]

set_option linter.unusedFintypeInType false in
open Classical in
theorem bind_pushforward_condOn
    {β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (proj : α → β) (g : α → PMF γ) :
    μ.bind g = (pushforward μ proj).bind (fun b => (condOn μ proj b).bind g) := by
  ext x
  have hL :=
    bind_apply_eq_sum_sum_fiber (μ := μ) (proj := proj) (g := g) (x := x)
  rw [hL]
  simp only [PMF.bind_apply, tsum_fintype]
  apply Finset.sum_congr rfl
  intro b hb_mem
  by_cases hpb : pushforward μ proj b = 0
  · have hz : ∀ a : α, proj a = b → μ a = 0 := by
      intro a ha
      exact eq_zero_of_pushforward_eq_zero (μ := μ) (proj := proj) hpb ha
    have hinner_zero :
        ∑ a : α, (if proj a = b then μ a else 0) * g a x = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      by_cases hab : proj a = b
      · simp [hab, hz a hab]
      · simp [hab]
    have hrhs_zero :
        (pushforward μ proj b) *
            ∑ a : α, condOn μ proj b a * g a x = 0 := by
      simp [hpb]
    calc
      ∑ a : α, (if proj a = b then μ a else 0) * g a x = 0 := hinner_zero
      _ = (pushforward μ proj b) * ∑ a : α, condOn μ proj b a * g a x := by
        simp [hpb]
  · have hpb_top : pushforward μ proj b ≠ ⊤ :=
      PMF.apply_ne_top (pushforward μ proj) b
    have hterm :
        (pushforward μ proj b) *
            (∑ a : α, condOn μ proj b a * g a x)
          =
        ∑ a : α, (if proj a = b then μ a else 0) * g a x := by
      simp_rw [condOn_apply (μ := μ) (proj := proj) (b := b) (hb := hpb)]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro a ha
      by_cases hab : proj a = b
      · simp [hab, div_eq_mul_inv, mul_left_comm, mul_comm,
          ENNReal.mul_inv_cancel hpb hpb_top]
      · simp [hab, mul_comm]
    exact hterm.symm

theorem foldl_bind_append
    {δ : Type*}
    (l₁ l₂ : List δ) (μ : PMF α) (k : δ → α → PMF α) :
    (l₁ ++ l₂).foldl (fun dist b => dist.bind (k b)) μ =
      l₂.foldl (fun dist b => dist.bind (k b))
        (l₁.foldl (fun dist b => dist.bind (k b)) μ) := by
  induction l₁ generalizing μ with
  | nil =>
      simp
  | cons b rest ih =>
      exact ih (μ.bind (k b))

theorem foldl_bind_congr
    {δ : Type*}
    (l : List δ) (μ : PMF α) (k₁ k₂ : δ → α → PMF α)
    (hk : ∀ b a, k₁ b a = k₂ b a) :
    l.foldl (fun dist b => dist.bind (k₁ b)) μ =
      l.foldl (fun dist b => dist.bind (k₂ b)) μ := by
  induction l generalizing μ with
  | nil =>
      simp
  | cons b rest ih =>
      have hbind : μ.bind (k₁ b) = μ.bind (k₂ b) := by
        exact bind_congr_on_support μ (k₁ b) (k₂ b) (fun a _ => hk b a)
      simpa [hbind] using ih (μ.bind (k₁ b))

theorem foldl_bind_eq_bind_foldl_pure
    {δ : Type*}
    (l : List δ) (μ : PMF α) (k : δ → α → PMF α) :
    l.foldl (fun dist b => dist.bind (k b)) μ =
      μ.bind (fun a => l.foldl (fun dist b => dist.bind (k b)) (PMF.pure a)) := by
  induction l generalizing μ with
  | nil =>
      simp [PMF.bind_pure]
  | cons b rest ih =>
      simp only [List.foldl]
      rw [ih, PMF.bind_bind]
      congr 1
      funext a
      simpa using (ih (k b a)).symm

set_option linter.unusedFintypeInType false in
theorem expect_mono_of_pointwise
    {Ω : Type*} [Fintype Ω]
    (d : PMF Ω) (f g : Ω → ℝ)
    (hfg : ∀ ω, f ω ≤ g ω) :
    Math.Probability.expect d f ≤ Math.Probability.expect d g := by
  simpa [Math.Probability.expect_eq_sum] using
    (Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) ENNReal.toReal_nonneg))

-- ============================================================================
-- HEq lemmas for PMF
-- ============================================================================

universe u in
theorem pure_heq {α β : Type u} {a : α} {b : β} (h : HEq a b) :
    HEq (PMF.pure a) (PMF.pure b) := by
  cases h; exact HEq.rfl

universe u in
theorem bind_heq {α : Type*} {β γ : Type u} (μ : PMF α)
    {f : α → PMF β} {g : α → PMF γ}
    (htype : β = γ) (h : ∀ a, HEq (f a) (g a)) :
    HEq (μ.bind f) (μ.bind g) := by
  subst htype
  exact heq_of_eq (congrArg (μ.bind ·) (funext fun a => eq_of_heq (h a)))

end ProbabilityMassFunction
end Math
