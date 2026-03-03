import Math.FunctionUpdate
import Math.FinsetUpdate
import Math.PMFProduct
import Math.ProbabilityMassFunction

set_option autoImplicit false

namespace Math
namespace Promotion

/-!
Promotion queue of reusable abstractions observed in `GameTheory`.
Theorem statements are added first, then discharged from easy to hard.
-/

namespace Function

variable {α α' β : Type*}

-- Already in Mathlib as `Function.update_comp_equiv`.
theorem update_comp_equiv_alias
    [DecidableEq α] [DecidableEq α']
    (f : α → β) (e : α ≃ α') (a' : α') (v : β) :
    Function.update (f ∘ e.symm) a' v =
      Function.update f (e.symm a') v ∘ e.symm := by
  simpa using
    (_root_.Function.update_comp_equiv
      (α := α) (α' := α') f e.symm (e.symm a') v).symm

theorem update_eq_update_of_decEq_alias
    {β' : α → Type*}
    (dec₁ dec₂ : DecidableEq α) (f : (a : α) → β' a) (a : α) (v : β' a) :
    @Function.update α β' dec₁ f a v = @Function.update α β' dec₂ f a v :=
  Math.Function.Update.update_eq_update_of_decEq dec₁ dec₂ f a v

end Function

namespace Finset

variable {ι α : Type*}

theorem sup'_update_eq_of_not_mem
    [DecidableEq ι] [SemilatticeSup α]
    (S : _root_.Finset ι) (hS : S.Nonempty)
    (j : ι) (hj : j ∉ S)
    (x : ι → α) (a : α) :
    S.sup' hS (Function.update x j a) = S.sup' hS x :=
  Math.Finset.Update.sup'_update_eq_of_not_mem S hS j hj x a

end Finset

namespace ProbabilityMassFunction

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

set_option linter.unusedFintypeInType false in
theorem bind_disintegrate
    [Fintype α] [Fintype β]
    (μ : PMF α) (proj : α → β) (g : α → PMF γ) :
    μ.bind g =
      (Math.PMFProduct.pushforward μ proj).bindOnSupport (fun b hb =>
        (μ.filter {a | proj a = b}
          (Math.PMFProduct.pushforward_support_fibre μ proj b hb)).bind g) := by
  exact Math.PMFProduct.pmf_bind_disintegrate μ proj g

theorem bind_congr_support
    {α β : Type*}
    (μ : PMF α) (f g : α → PMF β)
    (h : ∀ a, μ a ≠ 0 → f a = g a) :
    μ.bind f = μ.bind g :=
  Math.ProbabilityMassFunction.bind_congr_of_ne_zero μ f g h

theorem expect_le_of_pointwise
    {Ω : Type*} [Finite Ω]
    (d : PMF Ω) (f g : Ω → ℝ)
    (hfg : ∀ ω, f ω ≤ g ω) :
    Math.Probability.expect d f ≤ Math.Probability.expect d g := by
  classical
  letI : Fintype Ω := Fintype.ofFinite Ω
  exact Math.ProbabilityMassFunction.expect_mono_of_pointwise d f g hfg

end ProbabilityMassFunction

namespace PMFProduct

universe uι uA uβ
variable {ι : Type uι} [Fintype ι]
variable {A : ι → Type uA} [∀ i, Fintype (A i)]
variable {β : Type uβ}

open Classical in
theorem pmfPi_bind_irrelevant_coord
    (σ : ∀ i, PMF (A i)) (j : ι) (d : PMF (A j))
    (f : (∀ i, A i) → PMF β)
    (hf : Math.PMFProduct.Ignores (A := A) j f) :
    (Math.PMFProduct.pmfPi (A := A) (Function.update σ j d)).bind f =
      (Math.PMFProduct.pmfPi (A := A) σ).bind f := by
  exact Math.PMFProduct.pmfPi_bind_ignores_coord σ j d f hf

end PMFProduct

namespace Iteration

variable {α : Type*}

noncomputable def pmfIter (k : α → PMF α) : Nat → α → PMF α
  | 0 => PMF.pure
  | n + 1 => fun s => (pmfIter k n s).bind k

theorem pmfIter_succ
    (k : α → PMF α) (n : Nat) (s : α) :
    pmfIter k (n + 1) s = (pmfIter k n s).bind k := rfl

theorem pmfIter_congr
    (k₁ k₂ : α → PMF α) (hk : ∀ a, k₁ a = k₂ a) (n : Nat) (s : α) :
    pmfIter k₁ n s = pmfIter k₂ n s := by
  induction n generalizing s with
  | zero =>
      simp [pmfIter]
  | succ n ih =>
      have hbind : (pmfIter k₂ n s).bind k₁ = (pmfIter k₂ n s).bind k₂ := by
        exact Math.ProbabilityMassFunction.bind_congr_on_support
          (pmfIter k₂ n s) k₁ k₂ (fun a _ => hk a)
      simp [pmfIter, ih, hbind]

theorem pmfIter_add
    (k : α → PMF α) (m n : Nat) (s : α) :
    pmfIter k (m + n) s = (pmfIter k m s).bind (pmfIter k n) := by
  induction n generalizing s with
  | zero =>
      simp [pmfIter]
  | succ n ih =>
      simpa [pmfIter, Nat.add_assoc] using congrArg (fun p => p.bind k) (ih s)

end Iteration

end Promotion
end Math
