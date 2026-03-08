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

theorem sup'_update_eq_of_forall_ne
    [DecidableEq ι] [SemilatticeSup α]
    (S : _root_.Finset ι) (hS : S.Nonempty)
    (j : ι)
    (hneq : ∀ i, i ∈ S → i ≠ j)
    (x : ι → α) (a : α) :
    S.sup' hS (Function.update x j a) = S.sup' hS x :=
  Math.Finset.Update.sup'_update_eq_of_forall_ne S hS j hneq x a

theorem sup'_update_eq_of_mem
    [DecidableEq ι] [SemilatticeSup α]
    (S : _root_.Finset ι) (hS : S.Nonempty)
    (j : ι) (hj : j ∈ S)
    (hE : (S.erase j).Nonempty)
    (x : ι → α) (a : α) :
    S.sup' hS (Function.update x j a) = a ⊔ (S.erase j).sup' hE x :=
  Math.Finset.Update.sup'_update_eq_of_mem S hS j hj hE x a

end Finset

namespace ProbabilityMassFunction

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

set_option linter.unusedFintypeInType false in
theorem bind_disintegrate
    [Fintype α] [Fintype β]
    (μ : PMF α) (proj : α → β) (g : α → PMF γ) :
    μ.bind g =
      (Math.ProbabilityMassFunction.pushforward μ proj).bindOnSupport (fun b hb =>
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

theorem pmfIter_bind
    (k : α → PMF α) (m n : Nat) (s : α) :
    pmfIter k (m + n) s = (pmfIter k m s).bind (pmfIter k n) :=
  pmfIter_add k m n s

theorem pmfIter_eq_of_step_eqOn_reachable
    (k₁ k₂ : α → PMF α) (s : α)
    (hreach : ∀ n, Set.EqOn k₁ k₂ (pmfIter k₁ n s).support) :
    ∀ n, pmfIter k₁ n s = pmfIter k₂ n s := by
  intro n
  induction n with
  | zero =>
      simp [pmfIter]
  | succ n ih =>
      calc
        pmfIter k₁ (n + 1) s = (pmfIter k₁ n s).bind k₁ := by simp [pmfIter]
        _ = (pmfIter k₁ n s).bind k₂ := by
              exact Math.ProbabilityMassFunction.bind_congr_on_support
                (pmfIter k₁ n s) k₁ k₂ (fun a ha => hreach n ha)
        _ = (pmfIter k₂ n s).bind k₂ := by simp [ih]
        _ = pmfIter k₂ (n + 1) s := by simp [pmfIter]

set_option linter.unusedFintypeInType false in
theorem pmfIter_apply_le_of_step_le
    [Fintype α]
    (k₁ k₂ : α → PMF α)
    (hstep : ∀ x y, k₁ x y ≤ k₂ x y) :
    ∀ n s t, pmfIter k₁ n s t ≤ pmfIter k₂ n s t := by
  intro n
  induction n with
  | zero =>
      intro s t
      simp [pmfIter]
  | succ n ih =>
      intro s t
      simp only [pmfIter, PMF.bind_apply, tsum_fintype]
      refine Finset.sum_le_sum (fun a _ => ?_)
      exact mul_le_mul' (ih s a) (hstep a t)

set_option linter.unusedFintypeInType false in
open Classical in
theorem pmfIter_event_mono_of_step_le
    [Fintype α]
    (k₁ k₂ : α → PMF α)
    (hstep : ∀ x y, k₁ x y ≤ k₂ x y)
    (E : α → Prop) :
    ∀ n s,
      (∑ t : α, if E t then pmfIter k₁ n s t else 0)
        ≤
      (∑ t : α, if E t then pmfIter k₂ n s t else 0) := by
  intro n s
  refine Finset.sum_le_sum (fun t _ => ?_)
  by_cases hE : E t
  · simp [hE, pmfIter_apply_le_of_step_le (k₁ := k₁) (k₂ := k₂) hstep n s t]
  · simp [hE]

end Iteration

end Promotion
end Math
