import Mathlib

namespace Shadow
namespace ProtoKuhnEssentials

set_option autoImplicit false

section Function

section UpdateAlgebra

variable {ι : Type*} [DecidableEq ι]
variable {A : ι → Type*}

end UpdateAlgebra

section UpdateFold

variable {ι : Type*} [DecidableEq ι]
variable {A : ι → Type*} {X : Type*}

/-- Definition-free update-fold invariance:
if `F` is invariant under every update from a list, then folding those updates
does not change `F`. -/
theorem foldl_update_invariant
    (F : (∀ i, A i) → X)
    (l : List ι)
    (hF : ∀ j, j ∈ l → ∀ s a, F (Function.update s j a) = F s)
    (base : ∀ i, A i)
    (vals : ∀ i, A i) :
    F (l.foldl (fun s j => Function.update s j (vals j)) base) = F base := by
  induction l generalizing base with
  | nil =>
      simp
  | cons j rest ih =>
      have hHead : ∀ s a, F (Function.update s j a) = F s := hF j (by simp)
      have hTail : ∀ k, k ∈ rest → ∀ s a, F (Function.update s k a) = F s := by
        intro k hk
        exact hF k (by simp [hk])
      simp only [List.foldl]
      calc
        F (rest.foldl (fun s j => Function.update s j (vals j))
            (Function.update base j (vals j)))
            =
          F (Function.update base j (vals j)) := ih hTail _ _
        _ = F base := hHead _ _

end UpdateFold

end Function

section PMF

open scoped BigOperators

variable {α β γ : Type*}

/-- Pushforward composition in a theorem-prover-friendly normal form. -/
theorem pushforward_comp'
    (μ : PMF α) (f : α → β) (g : β → γ) :
    pushforward (pushforward μ f) g = pushforward μ (g ∘ f) := by
  simpa [pushforward, Function.comp] using
    (show (μ.bind (fun a => PMF.pure (f a))).bind (fun b => PMF.pure (g b))
      = μ.bind (fun a => PMF.pure (g (f a))) by
        simpa using (PMF.bind_bind μ (fun a => PMF.pure (f a)) (fun b => PMF.pure (g b))))

/-- Bind extensionality on the support of the source PMF. -/
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

end PMF

end ProtoKuhnEssentials
end Shadow
