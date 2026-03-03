import Math.Probability

set_option autoImplicit false

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

end ProbabilityMassFunction
end Math
