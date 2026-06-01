/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability
import Math.PMFProduct
import GameTheory.Concepts.SolutionConcepts
import GameTheory.Theorems.NashExistenceMixed

/-!
# Symmetric Games

A game with uniform strategy type is symmetric if payoffs are invariant
under permutation of player identities.

## Main definitions

* `IsSymmetricEU` — symmetry of an EU function under player permutations
* `symmetricProfile` — a profile where all players use the same strategy
* `symmetric_mixed_nash_exists` — finite symmetric games have symmetric mixed Nash equilibria

## Main results

* `isSymmetricEU_nash_perm` — permuting a Nash profile in a symmetric game yields Nash
* `isSymmetricEU_eu_eq` — all players get equal EU under a symmetric profile
* `IsSymmetricEU.ofPureEU_mixed` — symmetry lifts to the mixed extension
* `symmetric_mixed_nash_exists` — Nash's symmetric-equilibrium theorem for finite games
-/

open scoped BigOperators

namespace Math.PMFProduct

variable {ι S : Type} [Fintype ι]

open Classical in
/-- Product distributions with a uniform coordinate type are invariant under
permuting coordinates, pointwise at the correspondingly permuted profile. -/
theorem pmfPi_const_perm_apply
    (σ : ι → PMF S) (π : Equiv.Perm ι) (s : ι → S) :
    pmfPi (A := fun _ : ι => S) (σ ∘ ⇑π.symm) (s ∘ ⇑π.symm) =
      pmfPi (A := fun _ : ι => S) σ s := by
  classical
  simpa [pmfPi_apply, Function.comp_def] using
    (Equiv.prod_comp π.symm (g := fun i : ι => σ i (s i)))

end Math.PMFProduct

namespace GameTheory

open Math.Probability
open Math.PMFProduct

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

/-- Permute a uniform-strategy profile by relabeling player coordinates. -/
def profilePerm (π : Equiv.Perm ι) : (ι → S) ≃ (ι → S) where
  toFun σ := σ ∘ ⇑π.symm
  invFun σ := σ ∘ ⇑π
  left_inv := by
    intro σ
    ext i
    simp [Function.comp_def]
  right_inv := by
    intro σ
    ext i
    simp [Function.comp_def]

/-- In a symmetric game, all players receive the same EU under a symmetric profile. -/
theorem isSymmetricEU_eu_eq (u : (ι → S) → ι → ℝ) (hsym : IsSymmetricEU u)
    (s : S) (i j : ι) : u (symmetricProfile s) i = u (symmetricProfile s) j := by
  classical
  have h := hsym (Equiv.swap i j) (symmetricProfile s) i
  rw [symmetricProfile_comp, Equiv.swap_apply_left] at h
  linarith

namespace KernelGame

variable {Sdep : ι → Type}

open Classical in
/-- The direct-EU and deterministic-profile encodings have the same mixed
expected utilities when pure strategy profiles are finite. -/
theorem ofEU_mixedExtension_eu_eq_ofPureEU
    [Fintype ι] [∀ i, Finite (Sdep i)]
    (u : (∀ i, Sdep i) → Payoff ι)
    (σ : ∀ i, PMF (Sdep i)) (who : ι) :
    (KernelGame.ofEU Sdep u).mixedExtension.eu σ who =
      (KernelGame.ofPureEU Sdep u).mixedExtension.eu σ who := by
  classical
  letI : ∀ i, Fintype (Sdep i) := fun i => Fintype.ofFinite (Sdep i)
  have hleft :
      (KernelGame.ofEU Sdep u).mixedExtension.eu σ who =
        ∑ s : (∀ i, Sdep i), ((pmfPi (A := Sdep) σ s).toReal) * u s who := by
    change expect ((pmfPi (A := Sdep) σ).bind (fun s => PMF.pure (u s)))
        (fun p : Payoff ι => p who) =
      ∑ s : (∀ i, Sdep i), ((pmfPi (A := Sdep) σ s).toReal) * u s who
    rw [show (pmfPi (A := Sdep) σ).bind (fun s => PMF.pure (u s)) =
        PMF.map u (pmfPi (A := Sdep) σ) from PMF.bind_pure_comp u (pmfPi (A := Sdep) σ)]
    exact expect_map_fintype_source (pmfPi (A := Sdep) σ) u (fun p : Payoff ι => p who)
  have hright :
      (KernelGame.ofPureEU Sdep u).mixedExtension.eu σ who =
        ∑ s : (∀ i, Sdep i), ((pmfPi (A := Sdep) σ s).toReal) * u s who := by
    change expect ((pmfPi (A := Sdep) σ).bind (fun s => PMF.pure s))
        (fun s => u s who) =
      ∑ s : (∀ i, Sdep i), ((pmfPi (A := Sdep) σ s).toReal) * u s who
    rw [PMF.bind_pure]
    rw [expect_eq_sum]
  rw [hleft, hright]

end KernelGame

open Classical in
/-- Symmetry of a finite deterministic strategic-form game lifts to symmetry
of its mixed-extension payoff function. -/
theorem IsSymmetricEU.ofPureEU_mixed
    [Fintype ι] [Finite S]
    {u : (ι → S) → ι → ℝ} (hsym : IsSymmetricEU u) :
    IsSymmetricEU
      (fun σ : ι → PMF S =>
        (KernelGame.ofPureEU (fun _ : ι => S) u).mixedExtension.eu σ) := by
  classical
  letI : Fintype S := Fintype.ofFinite S
  intro π σ i
  let G : KernelGame ι := KernelGame.ofPureEU (fun _ : ι => S) u
  let e : (ι → S) ≃ (ι → S) := profilePerm (S := S) π
  have hleft :
      G.mixedExtension.eu (σ ∘ ⇑π.symm) (π i) =
        ∑ s : ι → S,
          ((pmfPi (A := fun _ : ι => S) (σ ∘ ⇑π.symm) s).toReal) * u s (π i) := by
    change expect
        ((pmfPi (A := fun _ : ι => S) (σ ∘ ⇑π.symm)).bind (fun s => PMF.pure s))
        (fun s => u s (π i)) =
      ∑ s : ι → S,
        ((pmfPi (A := fun _ : ι => S) (σ ∘ ⇑π.symm) s).toReal) * u s (π i)
    rw [PMF.bind_pure]
    rw [expect_eq_sum]
  have hright :
      G.mixedExtension.eu σ i =
        ∑ s : ι → S,
          ((pmfPi (A := fun _ : ι => S) σ s).toReal) * u s i := by
    change expect
        ((pmfPi (A := fun _ : ι => S) σ).bind (fun s => PMF.pure s))
        (fun s => u s i) =
      ∑ s : ι → S,
        ((pmfPi (A := fun _ : ι => S) σ s).toReal) * u s i
    rw [PMF.bind_pure]
    rw [expect_eq_sum]
  change G.mixedExtension.eu (σ ∘ ⇑π.symm) (π i) = G.mixedExtension.eu σ i
  rw [hleft, hright]
  rw [← Equiv.sum_comp e
    (g := fun s : ι → S =>
      ((pmfPi (A := fun _ : ι => S) (σ ∘ ⇑π.symm) s).toReal) * u s (π i))]
  refine Finset.sum_congr rfl ?_
  intro s _
  have hprob :
      pmfPi (A := fun _ : ι => S) (σ ∘ ⇑π.symm) (s ∘ ⇑π.symm) =
        pmfPi (A := fun _ : ι => S) σ s :=
    Math.PMFProduct.pmfPi_const_perm_apply σ π s
  have hutil : u (s ∘ ⇑π.symm) (π i) = u s i := hsym π s i
  simp [e, profilePerm, hprob, hutil]

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

open Classical in
/-- **Symmetric mixed Nash existence**, deterministic-profile encoding.

For a finite nonempty symmetric game with a uniform strategy type, there is a
mixed strategy `μ` such that every player using `μ` is a Nash equilibrium of
the mixed extension. -/
theorem symmetric_mixed_nash_exists_ofPureEU
    [Fintype ι] [DecidableEq ι] [Nonempty ι] [Finite S] [Nonempty S]
    (u : (ι → S) → ι → ℝ) (hsym : IsSymmetricEU u) :
    ∃ μ : PMF S,
      (KernelGame.ofPureEU (fun _ : ι => S) u).mixedExtension.IsNash
        (symmetricProfile (ι := ι) μ) := by
  classical
  letI : Fintype S := Fintype.ofFinite S
  let G : KernelGame ι := KernelGame.ofPureEU (fun _ : ι => S) u
  letI : ∀ i, Fintype (G.Strategy i) := by
    intro i
    dsimp [G, KernelGame.ofPureEU]
    infer_instance
  letI : Finite G.Outcome := by
    dsimp [G, KernelGame.ofPureEU]
    infer_instance
  let i₀ : ι := Classical.arbitrary ι
  let diag : MixedSimplex Unit (fun _ : Unit => S) → MixedSimplex ι (fun _ : ι => S) :=
    fun x _ => x ()
  let f : MixedSimplex Unit (fun _ : Unit => S) → MixedSimplex Unit (fun _ : Unit => S) :=
    fun x _ => G.nashMapOnMixedSimplex (diag x) i₀
  have hdiag : Continuous diag := by
    exact continuous_pi (fun _ => continuous_apply ())
  have hcont : Continuous f := by
    have hcoord :
        Continuous (fun x : MixedSimplex Unit (fun _ : Unit => S) =>
          G.nashMapOnMixedSimplex (diag x) i₀) :=
      (continuous_apply i₀).comp (G.continuous_nashMapOnMixedSimplex.comp hdiag)
    exact continuous_pi (fun _ => hcoord)
  rcases brouwer_mixedSimplex f hcont with ⟨x, hx⟩
  let xdiag : MixedSimplex ι (fun _ : ι => S) := diag x
  let σ : ∀ i, PMF S := G.profileFromMixedSimplex xdiag
  let μ : PMF S := σ i₀
  have hσ_toReal : ∀ (i : ι) (a : S), (σ i a).toReal = x () a := by
    intro i a
    simp [σ, xdiag, diag, G, KernelGame.profileFromMixedSimplex,
      KernelGame.profileFromWeights, KernelGame.realToPmf_toReal]
    rfl
  have hσ_symm : σ = symmetricProfile (ι := ι) μ := by
    ext i a
    exact (ENNReal.toReal_eq_toReal_iff'
      (PMF.apply_ne_top (σ i) a) (PMF.apply_ne_top μ a)).mp (by
        rw [hσ_toReal i a, hσ_toReal i₀ a])
  have hrep_nonpos : ∀ a : S, G.mixedGain σ i₀ a ≤ 0 := by
    have hxcoord := congrArg Subtype.val (congr_fun hx ())
    have hfp_all :
        ∀ b : S,
          (σ i₀ b).toReal * (1 + G.gainSum σ i₀) =
            (σ i₀ b).toReal + KernelGame.pospart (G.mixedGain σ i₀ b) := by
      intro b
      have hxb := congr_fun hxcoord b
      have hmap :
          (x () b + KernelGame.pospart (G.mixedGain σ i₀ b)) /
              (1 + G.gainSum σ i₀) =
            x () b := by
        simpa [f, xdiag, σ, diag, KernelGame.nashMapOnMixedSimplex_apply,
          KernelGame.mixedGainOnMixedSimplex, KernelGame.gainSumOnMixedSimplex] using hxb
      have hden_pos : 0 < 1 + G.gainSum σ i₀ := by
        have hnonneg := G.gainSum_nonneg σ i₀
        linarith
      have hden_ne : (1 + G.gainSum σ i₀) ≠ 0 := ne_of_gt hden_pos
      have hfp_x :
          x () b * (1 + G.gainSum σ i₀) =
            x () b + KernelGame.pospart (G.mixedGain σ i₀ b) := by
        have hmul := congrArg (fun y => y * (1 + G.gainSum σ i₀)) hmap
        change
          ((x () b + KernelGame.pospart (G.mixedGain σ i₀ b)) /
                (1 + G.gainSum σ i₀)) * (1 + G.gainSum σ i₀) =
            x () b * (1 + G.gainSum σ i₀) at hmul
        rw [div_mul_cancel₀ _ hden_ne] at hmul
        exact hmul.symm
      rw [hσ_toReal i₀ b]
      exact hfp_x
    have hwg := G.weighted_gain_sum_zero σ i₀
    change expect (σ i₀) (fun a => G.mixedGain σ i₀ a) = 0 at hwg
    rw [expect_eq_sum] at hwg
    intro a
    exact Math.Optimization.LocalGlobal.all_nonpos_of_weighted_pospart_fixedPoint
      (w := fun a : S => (σ i₀ a).toReal)
      (g := fun a : S => G.mixedGain σ i₀ a)
      (fun a => by simpa [KernelGame.pospart, KernelGame.gainSum] using hfp_all a) hwg a
  have hmixedSymm :
      IsSymmetricEU
        (fun τ : ι → PMF S =>
          (KernelGame.ofPureEU (fun _ : ι => S) u).mixedExtension.eu τ) :=
    hsym.ofPureEU_mixed
  have hall_nonpos : ∀ who (a : S), G.mixedGain σ who a ≤ 0 := by
    intro who a
    have hbase : G.mixedExtension.eu σ who = G.mixedExtension.eu σ i₀ := by
      rw [hσ_symm]
      exact isSymmetricEU_eu_eq
        (fun τ : ι → PMF S => G.mixedExtension.eu τ) hmixedSymm μ who i₀
    let π : Equiv.Perm ι := Equiv.swap i₀ who
    have hprofile :
        Function.update σ who (PMF.pure a) =
          Function.update σ i₀ (PMF.pure a) ∘ ⇑π.symm := by
      rw [hσ_symm]
      ext j
      have hswap : (Equiv.swap i₀ who j = i₀) ↔ j = who := by
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
      simp [π, symmetricProfile, Function.update, hswap]
    have hdev : G.mixedExtension.eu (Function.update σ who (PMF.pure a)) who =
        G.mixedExtension.eu (Function.update σ i₀ (PMF.pure a)) i₀ := by
      have h := hmixedSymm π (Function.update σ i₀ (PMF.pure a)) i₀
      have hπ : π i₀ = who := by simp [π]
      change G.mixedExtension.eu
          ((Function.update σ i₀ (PMF.pure a)) ∘ ⇑π.symm) (π i₀) =
        G.mixedExtension.eu (Function.update σ i₀ (PMF.pure a)) i₀ at h
      rw [hπ, ← hprofile] at h
      exact h
    have hrep := hrep_nonpos a
    unfold KernelGame.mixedGain at hrep ⊢
    rw [hdev, hbase]
    exact hrep
  have hNσ : G.mixedExtension.IsNash σ := by
    exact (G.isNash_iff_gains_nonpos σ).2 hall_nonpos
  refine ⟨μ, ?_⟩
  simpa [hσ_symm] using hNσ

open Classical in
/-- **Symmetric mixed Nash existence** for the direct-EU strategic-form encoding. -/
theorem symmetric_mixed_nash_exists
    [Fintype ι] [DecidableEq ι] [Nonempty ι] [Finite S] [Nonempty S]
    (u : (ι → S) → ι → ℝ) (hsym : IsSymmetricEU u) :
    ∃ μ : PMF S,
      (KernelGame.ofEU (fun _ : ι => S) u).mixedExtension.IsNash
        (symmetricProfile (ι := ι) μ) := by
  classical
  letI : Fintype S := Fintype.ofFinite S
  rcases symmetric_mixed_nash_exists_ofPureEU (ι := ι) (S := S) u hsym with ⟨μ, hN⟩
  refine ⟨μ, ?_⟩
  intro who τ
  have h := hN who τ
  simpa [KernelGame.ofEU_mixedExtension_eu_eq_ofPureEU]
    using h

end GameTheory
