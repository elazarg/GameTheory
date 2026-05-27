/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.MixedExtension
import GameTheory.Languages.NFG.Examples
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Mixed Matching Pennies

This file proves the exact mixed Nash equilibrium of the normal-form matching
pennies example: both players assign probability `1 / 2` to heads.
-/

open scoped BigOperators
open Math.Probability
open Math.PMFProduct

namespace NFG

noncomputable section

open MPAction

private instance : Nonempty MPAction := ⟨heads⟩

private instance matchingPenniesOutcomeFintype :
    Fintype matchingPennies.toKernelGame.Outcome := by
  change Fintype (∀ _ : Bool, MPAction)
  infer_instance

private instance matchingPenniesOutcomeFinite :
    Finite matchingPennies.toKernelGame.Outcome :=
  @Fintype.finite matchingPennies.toKernelGame.Outcome matchingPenniesOutcomeFintype

private instance matchingPenniesStrategyNonempty :
    ∀ i : Bool, Nonempty (matchingPennies.toKernelGame.Strategy i) :=
  fun _ => ⟨heads⟩

private instance matchingPenniesStrategyFintype :
    ∀ i : Bool, Fintype (matchingPennies.toKernelGame.Strategy i) :=
  fun _ => by
    change Fintype MPAction
    infer_instance

private def mpHH : Bool → MPAction := fun _ => heads
private def mpHT : Bool → MPAction := fun b => if b then heads else tails
private def mpTH : Bool → MPAction := fun b => if b then tails else heads
private def mpTT : Bool → MPAction := fun _ => tails

private lemma mpHH_ne_mpHT : mpHH ≠ mpHT := by
  intro h
  have := congrFun h false
  simp [mpHH, mpHT] at this

private lemma mpHH_ne_mpTH : mpHH ≠ mpTH := by
  intro h
  have := congrFun h true
  simp [mpHH, mpTH] at this

private lemma mpHH_ne_mpTT : mpHH ≠ mpTT := by
  intro h
  have := congrFun h true
  simp [mpHH, mpTT] at this

private lemma mpHT_ne_mpTH : mpHT ≠ mpTH := by
  intro h
  have := congrFun h true
  simp [mpHT, mpTH] at this

private lemma mpHT_ne_mpTT : mpHT ≠ mpTT := by
  intro h
  have := congrFun h true
  simp [mpHT, mpTT] at this

private lemma mpTH_ne_mpTT : mpTH ≠ mpTT := by
  intro h
  have := congrFun h false
  simp [mpTH, mpTT] at this

private lemma univ_bool_mp_profile :
    (Finset.univ : Finset (Bool → MPAction)) = {mpHH, mpHT, mpTH, mpTT} := by
  ext f
  constructor
  · intro _
    cases hf : f true <;> cases ht : f false
    · simp [mpHH, hf, ht, funext_iff]
    · simp [mpHT, hf, ht, funext_iff]
    · simp [mpTH, hf, ht, funext_iff]
    · simp [mpTT, hf, ht, funext_iff]
  · intro _
    simp

private lemma mp_tails_toReal (μ : PMF MPAction) :
    (μ tails).toReal = 1 - (μ heads).toReal := by
  have h := Math.Probability.pmf_toReal_sum_one μ
  have hfin : (Finset.univ : Finset MPAction) = {heads, tails} := by
    ext a
    cases a <;> simp
  rw [hfin] at h
  simp at h
  linarith

private lemma matchingPennies_mixedEu_true (σ : ∀ _ : Bool, PMF MPAction) :
    matchingPennies.toKernelGame.mixedExtension.eu σ true =
      (2 * (σ true heads).toReal - 1) * (2 * (σ false heads).toReal - 1) := by
  rw [GameTheory.KernelGame.mixedExtension_eu]
  simp [GameTheory.KernelGame.eu, NFGGame.toKernelGame, matchingPennies,
    Math.Probability.expect_eq_sum, Math.PMFProduct.pmfPi_apply,
    univ_bool_mp_profile, mpHH, mpHT, mpTH, mpTT, mp_tails_toReal,
    mpHH_ne_mpHT, mpHH_ne_mpTH, mpHH_ne_mpTT,
    mpHT_ne_mpTH, mpHT_ne_mpTT, mpTH_ne_mpTT,
    Ne.symm mpHH_ne_mpHT, Ne.symm mpHH_ne_mpTH, Ne.symm mpHH_ne_mpTT,
    Ne.symm mpHT_ne_mpTH, Ne.symm mpHT_ne_mpTT, Ne.symm mpTH_ne_mpTT]
  ring_nf

private lemma matchingPennies_mixedEu_false (σ : ∀ _ : Bool, PMF MPAction) :
    matchingPennies.toKernelGame.mixedExtension.eu σ false =
      -((2 * (σ true heads).toReal - 1) * (2 * (σ false heads).toReal - 1)) := by
  rw [GameTheory.KernelGame.mixedExtension_eu]
  simp [GameTheory.KernelGame.eu, NFGGame.toKernelGame, matchingPennies,
    Math.Probability.expect_eq_sum, Math.PMFProduct.pmfPi_apply,
    univ_bool_mp_profile, mpHH, mpHT, mpTH, mpTT, mp_tails_toReal,
    mpHH_ne_mpHT, mpHH_ne_mpTH, mpHH_ne_mpTT,
    mpHT_ne_mpTH, mpHT_ne_mpTT, mpTH_ne_mpTT,
    Ne.symm mpHH_ne_mpHT, Ne.symm mpHH_ne_mpTH, Ne.symm mpHH_ne_mpTT,
    Ne.symm mpHT_ne_mpTH, Ne.symm mpHT_ne_mpTT, Ne.symm mpTH_ne_mpTT]
  ring_nf

private lemma matchingPennies_mixedGain_true_heads (σ : ∀ _ : Bool, PMF MPAction) :
    matchingPennies.toKernelGame.mixedGain σ true heads =
      2 * (1 - (σ true heads).toReal) * (2 * (σ false heads).toReal - 1) := by
  unfold GameTheory.KernelGame.mixedGain
  rw [matchingPennies_mixedEu_true, matchingPennies_mixedEu_true]
  rw [Function.update_self, Function.update_of_ne (by decide : false ≠ true)]
  change (2 * ((PMF.pure heads : PMF MPAction) heads).toReal - 1) *
        (2 * ((σ false) heads).toReal - 1) -
      (2 * ((σ true) heads).toReal - 1) * (2 * ((σ false) heads).toReal - 1) =
    2 * (1 - ((σ true) heads).toReal) * (2 * ((σ false) heads).toReal - 1)
  simp [PMF.pure_apply]
  ring_nf

private lemma matchingPennies_mixedGain_true_tails (σ : ∀ _ : Bool, PMF MPAction) :
    matchingPennies.toKernelGame.mixedGain σ true tails =
      -2 * (σ true heads).toReal * (2 * (σ false heads).toReal - 1) := by
  unfold GameTheory.KernelGame.mixedGain
  rw [matchingPennies_mixedEu_true, matchingPennies_mixedEu_true]
  rw [Function.update_self, Function.update_of_ne (by decide : false ≠ true)]
  change (2 * ((PMF.pure tails : PMF MPAction) heads).toReal - 1) *
        (2 * ((σ false) heads).toReal - 1) -
      (2 * ((σ true) heads).toReal - 1) * (2 * ((σ false) heads).toReal - 1) =
    -2 * ((σ true) heads).toReal * (2 * ((σ false) heads).toReal - 1)
  simp [PMF.pure_apply]
  ring_nf

private lemma matchingPennies_mixedGain_false_heads (σ : ∀ _ : Bool, PMF MPAction) :
    matchingPennies.toKernelGame.mixedGain σ false heads =
      -2 * (1 - (σ false heads).toReal) * (2 * (σ true heads).toReal - 1) := by
  unfold GameTheory.KernelGame.mixedGain
  rw [matchingPennies_mixedEu_false, matchingPennies_mixedEu_false]
  rw [Function.update_self, Function.update_of_ne (by decide : true ≠ false)]
  change -((2 * ((σ true) heads).toReal - 1) *
        (2 * ((PMF.pure heads : PMF MPAction) heads).toReal - 1)) -
      -((2 * ((σ true) heads).toReal - 1) * (2 * ((σ false) heads).toReal - 1)) =
    -2 * (1 - ((σ false) heads).toReal) * (2 * ((σ true) heads).toReal - 1)
  simp [PMF.pure_apply]
  ring_nf

private lemma matchingPennies_mixedGain_false_tails (σ : ∀ _ : Bool, PMF MPAction) :
    matchingPennies.toKernelGame.mixedGain σ false tails =
      2 * (σ false heads).toReal * (2 * (σ true heads).toReal - 1) := by
  unfold GameTheory.KernelGame.mixedGain
  rw [matchingPennies_mixedEu_false, matchingPennies_mixedEu_false]
  rw [Function.update_self, Function.update_of_ne (by decide : true ≠ false)]
  change -((2 * ((σ true) heads).toReal - 1) *
        (2 * ((PMF.pure tails : PMF MPAction) heads).toReal - 1)) -
      -((2 * ((σ true) heads).toReal - 1) * (2 * ((σ false) heads).toReal - 1)) =
    2 * ((σ false) heads).toReal * (2 * ((σ true) heads).toReal - 1)
  simp [PMF.pure_apply]
  ring_nf

/-- The fair mixed profile for matching pennies. -/
def matchingPenniesFairMixed : MixedProfile (fun _ : Bool => MPAction) :=
  fun _ => PMF.uniformOfFintype MPAction

/-- Matching pennies is balanced at the uniform mixed profile: every pure
deviation has zero gain when both players are uniform. -/
theorem matchingPennies_uniform_mixed_balanced :
    matchingPennies.toKernelGame.IsUniformMixedBalanced := by
  rw [GameTheory.KernelGame.isUniformMixedBalanced_iff_mixedGain_eq_zero]
  intro who a
  cases who
  · cases a
    · rw [matchingPennies_mixedGain_false_heads]
      simp only [GameTheory.KernelGame.uniformMixedProfile]
      change -2 * (1 - ((PMF.uniformOfFintype MPAction) heads).toReal) *
        (2 * ((PMF.uniformOfFintype MPAction) heads).toReal - 1) = 0
      rw [PMF.uniformOfFintype_apply]
      have hcard : Fintype.card MPAction = 2 := by rfl
      rw [hcard]
      norm_num
    · rw [matchingPennies_mixedGain_false_tails]
      simp only [GameTheory.KernelGame.uniformMixedProfile]
      change 2 * ((PMF.uniformOfFintype MPAction) heads).toReal *
        (2 * ((PMF.uniformOfFintype MPAction) heads).toReal - 1) = 0
      rw [PMF.uniformOfFintype_apply]
      have hcard : Fintype.card MPAction = 2 := by rfl
      rw [hcard]
      norm_num
  · cases a
    · rw [matchingPennies_mixedGain_true_heads]
      simp only [GameTheory.KernelGame.uniformMixedProfile]
      change 2 * (1 - ((PMF.uniformOfFintype MPAction) heads).toReal) *
        (2 * ((PMF.uniformOfFintype MPAction) heads).toReal - 1) = 0
      rw [PMF.uniformOfFintype_apply]
      have hcard : Fintype.card MPAction = 2 := by rfl
      rw [hcard]
      norm_num
    · rw [matchingPennies_mixedGain_true_tails]
      simp only [GameTheory.KernelGame.uniformMixedProfile]
      change -2 * ((PMF.uniformOfFintype MPAction) heads).toReal *
        (2 * ((PMF.uniformOfFintype MPAction) heads).toReal - 1) = 0
      rw [PMF.uniformOfFintype_apply]
      have hcard : Fintype.card MPAction = 2 := by rfl
      rw [hcard]
      norm_num

/-- In the mixed matching-pennies game, Nash equilibrium is exactly the profile
where both players assign probability `1 / 2` to heads. -/
theorem matchingPennies_mixed_nash_iff_half (σ : MixedProfile (fun _ : Bool => MPAction)) :
    IsNashMixed matchingPennies σ ↔
      (σ true heads).toReal = (1 / 2 : ℝ) ∧
        (σ false heads).toReal = (1 / 2 : ℝ) := by
  constructor
  · intro hN
    have hg := (GameTheory.KernelGame.isNash_iff_gains_nonpos
      (G := matchingPennies.toKernelGame) σ).mp hN
    have hth := hg true heads
    have htt := hg true tails
    have hfh := hg false heads
    have hft := hg false tails
    rw [matchingPennies_mixedGain_true_heads] at hth
    rw [matchingPennies_mixedGain_true_tails] at htt
    rw [matchingPennies_mixedGain_false_heads] at hfh
    rw [matchingPennies_mixedGain_false_tails] at hft
    constructor <;> nlinarith
  · rintro ⟨htrue, hfalse⟩
    change matchingPennies.toKernelGame.mixedExtension.IsNash σ
    rw [GameTheory.KernelGame.isNash_iff_gains_nonpos]
    intro who a
    cases who <;> cases a <;>
      simp [matchingPennies_mixedGain_true_heads, matchingPennies_mixedGain_true_tails,
        matchingPennies_mixedGain_false_heads, matchingPennies_mixedGain_false_tails,
        htrue, hfalse]

/-- The fair mixed profile is a mixed Nash equilibrium of matching pennies. -/
theorem matchingPennies_fair_mixed_nash :
    IsNashMixed matchingPennies matchingPenniesFairMixed := by
  change matchingPennies.toKernelGame.mixedExtension.IsNash matchingPenniesFairMixed
  simpa [matchingPenniesFairMixed, GameTheory.KernelGame.uniformMixedProfile] using
    matchingPennies_uniform_mixed_balanced.uniformMixedProfile_isNash

end

end NFG
