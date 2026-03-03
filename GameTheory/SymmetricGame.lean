import GameTheory.SolutionConcepts
import Math.Probability

/-!
# Symmetric Games

A game with uniform strategy type is symmetric if payoffs are invariant
under permutation of player identities.

## Main definitions

* `IsSymmetricEU` — symmetry of an EU function under player permutations
* `symmetricProfile` — a profile where all players use the same strategy

## Main results

* `isSymmetricEU_nash_perm` — permuting a Nash profile in a symmetric game yields Nash
* `isSymmetricEU_eu_eq` — all players get equal EU under a symmetric profile
-/

namespace GameTheory

open Math.Probability

variable {ι : Type} {S : Type}

/-- An EU function `u : (ι → S) → ι → ℝ` is symmetric if for every
    permutation of players, payoffs permute accordingly:
    `u (σ ∘ π⁻¹) (π i) = u σ i` for all `π`, `σ`, `i`. -/
def IsSymmetricEU (u : (ι → S) → ι → ℝ) : Prop :=
  ∀ (π : Equiv.Perm ι) (σ : ι → S) (i : ι),
    u (σ ∘ ⇑π⁻¹) (π i) = u σ i

/-- Derived form: `u (σ ∘ π⁻¹) j = u σ (π⁻¹ j)`. -/
theorem IsSymmetricEU.apply_perm (hu : IsSymmetricEU u) (π : Equiv.Perm ι) (σ : ι → S) (j : ι) :
    u (σ ∘ ⇑π⁻¹) j = u σ (π⁻¹ j) := by
  have h1 := hu π σ (π⁻¹ j)
  have h2 : π (π⁻¹ j) = j := Equiv.apply_symm_apply π j
  rw [h2] at h1
  exact h1

/-- A symmetric profile: every player uses strategy `s`. -/
def symmetricProfile (s : S) : ι → S := fun _ => s

/-- A symmetric profile is invariant under precomposition with any function. -/
theorem symmetricProfile_comp (s : S) (f : ι → ι) :
    symmetricProfile s ∘ f = symmetricProfile (ι := ι) s := by
  ext; simp [symmetricProfile]

/-- In a symmetric game, all players receive the same EU under a symmetric profile. -/
theorem isSymmetricEU_eu_eq (u : (ι → S) → ι → ℝ) (hsym : IsSymmetricEU u)
    (s : S) (i j : ι) : u (symmetricProfile s) i = u (symmetricProfile s) j := by
  classical
  have h := hsym (Equiv.swap i j) (symmetricProfile s) i
  rw [symmetricProfile_comp, Equiv.swap_apply_left] at h
  linarith

open Classical in
/-- In a symmetric `ofEU` game, permuting a Nash profile yields Nash. -/
theorem isSymmetricEU_nash_perm (u : (ι → S) → ι → ℝ) (hsym : IsSymmetricEU u)
    (π : Equiv.Perm ι) (σ : ι → S) (hN : (KernelGame.ofEU (fun _ => S) u).IsNash σ) :
    (KernelGame.ofEU (fun _ => S) u).IsNash (σ ∘ ⇑π⁻¹) := by
  intro j s'
  simp only [KernelGame.eu, KernelGame.ofEU, expect_pure, ge_iff_le, id]
  -- u (σ ∘ π⁻¹) j = u σ (π⁻¹ j)
  have hlhs := hsym.apply_perm π σ j
  -- update (σ ∘ π⁻¹) j s' = (update σ (π⁻¹ j) s') ∘ π⁻¹
  have hupd :
      Function.update (σ ∘ ⇑π⁻¹) j s' =
        Function.update σ (π⁻¹ j) s' ∘ ⇑π⁻¹ := by
    simpa using (Function.update_comp_equiv (f := σ) (g := π.symm) (a := π⁻¹ j) (v := s')).symm
  have hrhs : u (Function.update (σ ∘ ⇑π⁻¹) j s') j =
      u (Function.update σ (π⁻¹ j) s') (π⁻¹ j) := by
    rw [hupd]
    exact hsym.apply_perm π (Function.update σ (π⁻¹ j) s') j
  rw [hlhs, hrhs]
  have := hN (π⁻¹ j) s'
  simp only [KernelGame.eu, KernelGame.ofEU, expect_pure, ge_iff_le, id] at this
  exact this

end GameTheory
