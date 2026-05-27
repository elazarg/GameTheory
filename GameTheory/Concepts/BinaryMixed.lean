/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.MixedExtension
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Binary Mixed Strategy Calculus

Reusable facts for two-player games whose player set is `Bool` and whose pure
strategy sets are labeled by `Bool`.

The main application is matching-pennies-style games.  The results are stated
over `KernelGame`, so an NFG, FOSG, MAID, or any other language can compile to a
kernel game and then use the same mixed-equilibrium theorem after proving the
small semantic payoff predicate.
-/

noncomputable section

open scoped BigOperators

namespace GameTheory
namespace KernelGame

open Math.Probability
open Math.PMFProduct

/-- Boolean labels for each player's two pure strategies in a two-player
`KernelGame Bool`.  The labels are semantic: they can name heads/tails,
match/mismatch, left/right, or any other two alternatives. -/
structure BinaryActionLabels (G : KernelGame Bool) where
  toBool : ∀ i : Bool, G.Strategy i ≃ Bool

namespace BinaryActionLabels

variable {G : KernelGame Bool} (L : BinaryActionLabels G)

/-- The pure strategy with label `b` for player `i`. -/
def action (i : Bool) (b : Bool) : G.Strategy i :=
  (L.toBool i).symm b

/-- The pure profile whose `true` player has label `a` and whose `false`
player has label `b`. -/
def profile (a b : Bool) : Profile G
  | true => L.action true a
  | false => L.action false b

@[simp] theorem profile_true (a b : Bool) :
    L.profile a b true = L.action true a := rfl

@[simp] theorem profile_false (a b : Bool) :
    L.profile a b false = L.action false b := rfl

@[simp] theorem action_left_inverse (i b) :
    L.toBool i (L.action i b) = b := by
  simp [action]

@[simp] theorem action_right_inverse (i) (s : G.Strategy i) :
    L.action i (L.toBool i s) = s := by
  simp [action]

@[simp] theorem action_inj {i a b} :
    L.action i a = L.action i b ↔ a = b := by
  constructor
  · intro h
    simpa using congrArg (L.toBool i) h
  · intro h
    simp [h]

/-- The fintype instance induced by binary labels.  Theorems in this file use
this locally instead of asking callers for redundant `Fintype` instances. -/
@[reducible] def fintypeStrategy (i : Bool) : Fintype (G.Strategy i) :=
  Fintype.ofEquiv Bool (L.toBool i).symm

/-- The nonemptiness instance induced by binary labels. -/
@[reducible] def nonemptyStrategy (i : Bool) : Nonempty (G.Strategy i) :=
  ⟨L.action i true⟩

/-- The decidable equality instance induced by binary labels. -/
def decidableEqStrategy (i : Bool) : DecidableEq (G.Strategy i) :=
  Equiv.decidableEq (L.toBool i)

/-- Pure profiles are equivalent to Boolean label profiles. -/
def profileBoolEquiv : Profile G ≃ (Bool → Bool) where
  toFun s := fun i => L.toBool i (s i)
  invFun b := fun i => L.action i (b i)
  left_inv s := by
    funext i
    simp
  right_inv b := by
    funext i
    simp

@[simp] theorem profileBoolEquiv_apply (s : Profile G) (i : Bool) :
    L.profileBoolEquiv s i = L.toBool i (s i) := rfl

@[simp] theorem profileBoolEquiv_symm_apply (b : Bool → Bool) (i : Bool) :
    L.profileBoolEquiv.symm b i = L.action i (b i) := rfl

@[simp] theorem profile_const_true :
    (fun i => L.action i true) = L.profile true true := by
  funext i
  cases i <;> rfl

@[simp] theorem profile_const_false :
    (fun i => L.action i false) = L.profile false false := by
  funext i
  cases i <;> rfl

@[simp] theorem profile_self :
    (fun i => L.action i i) = L.profile true false := by
  funext i
  cases i <;> rfl

@[simp] theorem profile_not :
    (fun i => L.action i (!i)) = L.profile false true := by
  funext i
  cases i <;> rfl

/-- Every binary-labeled action is one of the two labeled actions. -/
theorem action_eq_true_or_false (i : Bool) (s : G.Strategy i) :
    s = L.action i true ∨ s = L.action i false := by
  have h : s = L.action i (L.toBool i s) := by
    simp
  cases hb : L.toBool i s
  · right
    simpa [hb] using h
  · left
    simpa [hb] using h

/-- Probability assigned to the action labeled `true`. -/
def probTrue (σ : ∀ i, PMF (G.Strategy i)) (i : Bool) : ℝ :=
  ((σ i) (L.action i true)).toReal

theorem probTrue_nonneg (σ : ∀ i, PMF (G.Strategy i)) (i : Bool) :
    0 ≤ L.probTrue σ i := by
  exact ENNReal.toReal_nonneg

theorem probTrue_le_one (σ : ∀ i, PMF (G.Strategy i)) (i : Bool) :
    L.probTrue σ i ≤ 1 := by
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by
    simpa using PMF.coe_le_one (σ i) (L.action i true))

/-- In a binary strategy set, the probability of the action labeled `false` is
`1 - probTrue`. -/
theorem prob_false_toReal (σ : ∀ i, PMF (G.Strategy i)) (i : Bool) :
    ((σ i) (L.action i false)).toReal = 1 - L.probTrue σ i := by
  letI : ∀ i : Bool, Fintype (G.Strategy i) := fun i => L.fintypeStrategy i
  have h0 := Math.Probability.pmf_toReal_sum_one (σ i)
  have hsum : ∑ b : Bool, ((σ i) (L.action i b)).toReal = 1 := by
    have h := Fintype.sum_equiv (L.toBool i)
      (fun s : G.Strategy i => ((σ i) s).toReal)
      (fun b : Bool => ((σ i) (L.action i b)).toReal)
      (by intro s; simp [action])
    exact h.symm.trans h0
  rw [show (∑ b : Bool, ((σ i) (L.action i b)).toReal) =
      ((σ i) (L.action i false)).toReal + ((σ i) (L.action i true)).toReal by
    simp [add_comm]] at hsum
  simp [probTrue]
  linarith

/-- The independent uniform mixed profile induced by the binary labels.  This
does not require callers to provide separate `Fintype` or `Nonempty` instances
for the strategy sets. -/
def uniformMixedProfile : Profile G.mixedExtension :=
  fun i => @PMF.uniformOfFintype (G.Strategy i) (L.fintypeStrategy i) (L.nonemptyStrategy i)

/-- The label-induced uniform mixed profile puts probability `1 / 2` on each
binary label. -/
theorem probTrue_labeledUniformMixedProfile (i : Bool) :
    L.probTrue L.uniformMixedProfile i = (1 / 2 : ℝ) := by
  letI : Fintype (G.Strategy i) := L.fintypeStrategy i
  letI : Nonempty (G.Strategy i) := L.nonemptyStrategy i
  change ((PMF.uniformOfFintype (G.Strategy i)) (L.action i true)).toReal = (1 / 2 : ℝ)
  rw [PMF.uniformOfFintype_apply]
  have hcard : Fintype.card (G.Strategy i) = 2 := by
    rw [← Fintype.card_bool]
    exact Fintype.card_congr (L.toBool i)
  rw [hcard]
  norm_num

/-- The uniform mixed profile puts probability `1 / 2` on each binary label. -/
theorem probTrue_uniformMixedProfile
    [∀ i : Bool, Fintype (G.Strategy i)]
    [∀ i : Bool, Nonempty (G.Strategy i)] (i : Bool) :
    L.probTrue G.uniformMixedProfile i = (1 / 2 : ℝ) := by
  change ((PMF.uniformOfFintype (G.Strategy i)) (L.action i true)).toReal = (1 / 2 : ℝ)
  rw [PMF.uniformOfFintype_apply]
  have hcard : Fintype.card (G.Strategy i) = 2 := by
    rw [← Fintype.card_bool]
    exact Fintype.card_congr (L.toBool i)
  rw [hcard]
  norm_num

/-- Finite expansion of mixed-extension EU for a binary-labeled game, under a
bounded-utility hypothesis. -/
theorem mixedExtension_eu_binary_of_bounded
    (σ : ∀ i, PMF (G.Strategy i)) (who : Bool)
    {C : ℝ} (hbd : ∀ ω, |G.utility ω who| ≤ C) :
    G.mixedExtension.eu σ who =
      ∑ b : Bool → Bool,
        (((σ true) (L.action true (b true))).toReal *
          ((σ false) (L.action false (b false))).toReal) *
          G.eu (fun i => L.action i (b i)) who := by
  letI : ∀ i : Bool, Fintype (G.Strategy i) := fun i => L.fintypeStrategy i
  rw [G.mixedExtension_eu_of_bounded σ who hbd]
  rw [Math.Probability.expect_eq_sum]
  trans ∑ x : Profile G, ((pmfPi σ) x).toReal * G.eu x who
  · rfl
  rw [Fintype.sum_equiv (L.profileBoolEquiv) _ _]
  simp [Math.PMFProduct.pmfPi_apply]

/-- Finite-outcome wrapper for `mixedExtension_eu_binary_of_bounded`. -/
theorem mixedExtension_eu_binary [Finite G.Outcome]
    (σ : ∀ i, PMF (G.Strategy i)) (who : Bool) :
    G.mixedExtension.eu σ who =
      ∑ b : Bool → Bool,
        (((σ true) (L.action true (b true))).toReal *
          ((σ false) (L.action false (b false))).toReal) *
          G.eu (fun i => L.action i (b i)) who := by
  obtain ⟨C, hC⟩ : BddAbove (Set.range fun ω => |G.utility ω who|) :=
    Finite.bddAbove_range _
  exact L.mixedExtension_eu_binary_of_bounded σ who (C := C) (fun ω => hC ⟨ω, rfl⟩)

end BinaryActionLabels

private def boolProfileHH : Bool → Bool := fun _ => true
private def boolProfileHT : Bool → Bool := fun b => if b then true else false
private def boolProfileTH : Bool → Bool := fun b => if b then false else true
private def boolProfileTT : Bool → Bool := fun _ => false

private lemma boolProfileHH_ne_HT : boolProfileHH ≠ boolProfileHT := by
  intro h
  have := congrFun h false
  simp [boolProfileHH, boolProfileHT] at this

private lemma boolProfileHH_ne_TH : boolProfileHH ≠ boolProfileTH := by
  intro h
  have := congrFun h true
  simp [boolProfileHH, boolProfileTH] at this

private lemma boolProfileHH_ne_TT : boolProfileHH ≠ boolProfileTT := by
  intro h
  have := congrFun h true
  simp [boolProfileHH, boolProfileTT] at this

private lemma boolProfileHT_ne_TH : boolProfileHT ≠ boolProfileTH := by
  intro h
  have := congrFun h true
  simp [boolProfileHT, boolProfileTH] at this

private lemma boolProfileHT_ne_TT : boolProfileHT ≠ boolProfileTT := by
  intro h
  have := congrFun h true
  simp [boolProfileHT, boolProfileTT] at this

private lemma boolProfileTH_ne_TT : boolProfileTH ≠ boolProfileTT := by
  intro h
  have := congrFun h false
  simp [boolProfileTH, boolProfileTT] at this

private lemma boolProfile_univ :
    (Finset.univ : Finset (Bool → Bool)) =
      {boolProfileHH, boolProfileHT, boolProfileTH, boolProfileTT} := by
  ext f
  constructor
  · intro _
    cases hf : f true <;> cases ht : f false
    · simp [boolProfileTT, hf, ht, funext_iff]
    · simp [boolProfileTH, hf, ht, funext_iff]
    · simp [boolProfileHT, hf, ht, funext_iff]
    · simp [boolProfileHH, hf, ht, funext_iff]
  · intro _
    simp

/-- A semantic matching-pennies pattern on a binary-labeled two-player kernel
game: the `true` player receives `scale` for matching labels and `-scale` for
mismatching labels, while the `false` player receives the negative payoff.

This is intentionally language-independent.  Any concrete language only has to
compile to `KernelGame Bool`, provide binary action labels, and prove these four
payoff equations. -/
structure MatchingPenniesLike (G : KernelGame Bool) (L : BinaryActionLabels G) where
  scale : ℝ
  scale_pos : 0 < scale
  eu_true : ∀ a b : Bool,
    G.eu (L.profile a b) true = if a = b then scale else -scale
  eu_false : ∀ a b : Bool,
    G.eu (L.profile a b) false = -(if a = b then scale else -scale)

/-- Prop-valued version of `MatchingPenniesLike` for users who only need the
semantic concept and not the bundled payoff scale. -/
def IsMatchingPenniesLike (G : KernelGame Bool) (L : BinaryActionLabels G) : Prop :=
  Nonempty (G.MatchingPenniesLike L)

namespace MatchingPenniesLike

variable {G : KernelGame Bool} {L : BinaryActionLabels G}
variable (h : G.MatchingPenniesLike L)

theorem isMatchingPenniesLike (h : G.MatchingPenniesLike L) : G.IsMatchingPenniesLike L :=
  ⟨h⟩

theorem mixedEu_true_formula_of_bounded
    (σ : ∀ i, PMF (G.Strategy i))
    {C : ℝ} (hbd : ∀ ω, |G.utility ω true| ≤ C) :
    G.mixedExtension.eu σ true =
      h.scale * ((2 * L.probTrue σ true - 1) *
        (2 * L.probTrue σ false - 1)) := by
  rw [L.mixedExtension_eu_binary_of_bounded σ true hbd]
  simp [boolProfile_univ, boolProfileHH, boolProfileHT, boolProfileTH, boolProfileTT,
    boolProfileHH_ne_HT, boolProfileHH_ne_TH, boolProfileHH_ne_TT,
    boolProfileHT_ne_TH, boolProfileHT_ne_TT, boolProfileTH_ne_TT,
    h.eu_true, BinaryActionLabels.prob_false_toReal, BinaryActionLabels.probTrue]
  ring_nf

theorem mixedEu_false_formula_of_bounded
    (σ : ∀ i, PMF (G.Strategy i))
    {C : ℝ} (hbd : ∀ ω, |G.utility ω false| ≤ C) :
    G.mixedExtension.eu σ false =
      -h.scale * ((2 * L.probTrue σ true - 1) *
        (2 * L.probTrue σ false - 1)) := by
  rw [L.mixedExtension_eu_binary_of_bounded σ false hbd]
  simp [boolProfile_univ, boolProfileHH, boolProfileHT, boolProfileTH, boolProfileTT,
    boolProfileHH_ne_HT, boolProfileHH_ne_TH, boolProfileHH_ne_TT,
    boolProfileHT_ne_TH, boolProfileHT_ne_TT, boolProfileTH_ne_TT,
    h.eu_false, BinaryActionLabels.prob_false_toReal, BinaryActionLabels.probTrue]
  ring_nf

theorem mixedEu_true_formula [Finite G.Outcome]
    (σ : ∀ i, PMF (G.Strategy i)) :
    G.mixedExtension.eu σ true =
      h.scale * ((2 * L.probTrue σ true - 1) *
        (2 * L.probTrue σ false - 1)) := by
  obtain ⟨C, hC⟩ : BddAbove (Set.range fun ω => |G.utility ω true|) :=
    Finite.bddAbove_range _
  exact h.mixedEu_true_formula_of_bounded σ (C := C) (fun ω => hC ⟨ω, rfl⟩)

theorem mixedEu_false_formula [Finite G.Outcome]
    (σ : ∀ i, PMF (G.Strategy i)) :
    G.mixedExtension.eu σ false =
      -h.scale * ((2 * L.probTrue σ true - 1) *
        (2 * L.probTrue σ false - 1)) := by
  obtain ⟨C, hC⟩ : BddAbove (Set.range fun ω => |G.utility ω false|) :=
    Finite.bddAbove_range _
  exact h.mixedEu_false_formula_of_bounded σ (C := C) (fun ω => hC ⟨ω, rfl⟩)

theorem deviationGain_true_true_formula_of_bounded
    (σ : ∀ i, PMF (G.Strategy i))
    {C : ℝ} (hbd : ∀ ω, |G.utility ω true| ≤ C) :
    G.mixedExtension.eu (Function.update σ true (PMF.pure (L.action true true))) true -
      G.mixedExtension.eu σ true =
        2 * h.scale * (1 - L.probTrue σ true) *
          (2 * L.probTrue σ false - 1) := by
  letI : ∀ i : Bool, DecidableEq (G.Strategy i) := fun i => L.decidableEqStrategy i
  have hdev := h.mixedEu_true_formula_of_bounded
    (Function.update σ true (PMF.pure (L.action true true))) (C := C) hbd
  have hbase := h.mixedEu_true_formula_of_bounded σ (C := C) hbd
  calc
    G.mixedExtension.eu (Function.update σ true (PMF.pure (L.action true true))) true -
        G.mixedExtension.eu σ true
        = h.scale *
            ((2 * L.probTrue (Function.update σ true (PMF.pure (L.action true true)))
                  true - 1) *
              (2 * L.probTrue (Function.update σ true (PMF.pure (L.action true true)))
                  false - 1)) -
            h.scale * ((2 * L.probTrue σ true - 1) *
              (2 * L.probTrue σ false - 1)) := by
          exact congrArg₂ (fun x y : ℝ => x - y) hdev hbase
    _ = 2 * h.scale * (1 - L.probTrue σ true) *
          (2 * L.probTrue σ false - 1) := by
        simp [BinaryActionLabels.probTrue, Function.update_self,
          PMF.pure_apply]
        ring_nf

theorem deviationGain_true_false_formula_of_bounded
    (σ : ∀ i, PMF (G.Strategy i))
    {C : ℝ} (hbd : ∀ ω, |G.utility ω true| ≤ C) :
    G.mixedExtension.eu (Function.update σ true (PMF.pure (L.action true false))) true -
      G.mixedExtension.eu σ true =
        -2 * h.scale * L.probTrue σ true *
          (2 * L.probTrue σ false - 1) := by
  letI : ∀ i : Bool, DecidableEq (G.Strategy i) := fun i => L.decidableEqStrategy i
  have hdev := h.mixedEu_true_formula_of_bounded
    (Function.update σ true (PMF.pure (L.action true false))) (C := C) hbd
  have hbase := h.mixedEu_true_formula_of_bounded σ (C := C) hbd
  calc
    G.mixedExtension.eu (Function.update σ true (PMF.pure (L.action true false))) true -
        G.mixedExtension.eu σ true
        = h.scale *
            ((2 * L.probTrue (Function.update σ true (PMF.pure (L.action true false)))
                  true - 1) *
              (2 * L.probTrue (Function.update σ true (PMF.pure (L.action true false)))
                  false - 1)) -
            h.scale * ((2 * L.probTrue σ true - 1) *
              (2 * L.probTrue σ false - 1)) := by
          exact congrArg₂ (fun x y : ℝ => x - y) hdev hbase
    _ = -2 * h.scale * L.probTrue σ true *
          (2 * L.probTrue σ false - 1) := by
        simp [BinaryActionLabels.probTrue, Function.update_self,
          PMF.pure_apply]
        ring_nf

theorem deviationGain_false_true_formula_of_bounded
    (σ : ∀ i, PMF (G.Strategy i))
    {C : ℝ} (hbd : ∀ ω, |G.utility ω false| ≤ C) :
    G.mixedExtension.eu (Function.update σ false (PMF.pure (L.action false true))) false -
      G.mixedExtension.eu σ false =
        -2 * h.scale * (1 - L.probTrue σ false) *
          (2 * L.probTrue σ true - 1) := by
  letI : ∀ i : Bool, DecidableEq (G.Strategy i) := fun i => L.decidableEqStrategy i
  have hdev := h.mixedEu_false_formula_of_bounded
    (Function.update σ false (PMF.pure (L.action false true))) (C := C) hbd
  have hbase := h.mixedEu_false_formula_of_bounded σ (C := C) hbd
  calc
    G.mixedExtension.eu (Function.update σ false (PMF.pure (L.action false true))) false -
        G.mixedExtension.eu σ false
        = -h.scale *
            ((2 * L.probTrue (Function.update σ false (PMF.pure (L.action false true)))
                  true - 1) *
              (2 * L.probTrue (Function.update σ false (PMF.pure (L.action false true)))
                  false - 1)) -
            (-h.scale * ((2 * L.probTrue σ true - 1) *
              (2 * L.probTrue σ false - 1))) := by
          exact congrArg₂ (fun x y : ℝ => x - y) hdev hbase
    _ = -2 * h.scale * (1 - L.probTrue σ false) *
          (2 * L.probTrue σ true - 1) := by
        simp [BinaryActionLabels.probTrue, Function.update_self,
          PMF.pure_apply]
        ring_nf

theorem deviationGain_false_false_formula_of_bounded
    (σ : ∀ i, PMF (G.Strategy i))
    {C : ℝ} (hbd : ∀ ω, |G.utility ω false| ≤ C) :
    G.mixedExtension.eu (Function.update σ false (PMF.pure (L.action false false))) false -
      G.mixedExtension.eu σ false =
        2 * h.scale * L.probTrue σ false *
          (2 * L.probTrue σ true - 1) := by
  letI : ∀ i : Bool, DecidableEq (G.Strategy i) := fun i => L.decidableEqStrategy i
  have hdev := h.mixedEu_false_formula_of_bounded
    (Function.update σ false (PMF.pure (L.action false false))) (C := C) hbd
  have hbase := h.mixedEu_false_formula_of_bounded σ (C := C) hbd
  calc
    G.mixedExtension.eu (Function.update σ false (PMF.pure (L.action false false))) false -
        G.mixedExtension.eu σ false
        = -h.scale *
            ((2 * L.probTrue (Function.update σ false (PMF.pure (L.action false false)))
                  true - 1) *
              (2 * L.probTrue (Function.update σ false (PMF.pure (L.action false false)))
                  false - 1)) -
            (-h.scale * ((2 * L.probTrue σ true - 1) *
              (2 * L.probTrue σ false - 1))) := by
          exact congrArg₂ (fun x y : ℝ => x - y) hdev hbase
    _ = 2 * h.scale * L.probTrue σ false *
          (2 * L.probTrue σ true - 1) := by
        simp [BinaryActionLabels.probTrue, Function.update_self,
          PMF.pure_apply]
        ring_nf

theorem mixedGain_true_true_formula [Finite G.Outcome]
    (σ : ∀ i, PMF (G.Strategy i)) :
    G.mixedGain σ true (L.action true true) =
      2 * h.scale * (1 - L.probTrue σ true) *
        (2 * L.probTrue σ false - 1) := by
  unfold mixedGain
  obtain ⟨C, hC⟩ : BddAbove (Set.range fun ω => |G.utility ω true|) :=
    Finite.bddAbove_range _
  exact h.deviationGain_true_true_formula_of_bounded σ (C := C) (fun ω => hC ⟨ω, rfl⟩)

theorem mixedGain_true_false_formula [Finite G.Outcome]
    (σ : ∀ i, PMF (G.Strategy i)) :
    G.mixedGain σ true (L.action true false) =
      -2 * h.scale * L.probTrue σ true *
        (2 * L.probTrue σ false - 1) := by
  unfold mixedGain
  obtain ⟨C, hC⟩ : BddAbove (Set.range fun ω => |G.utility ω true|) :=
    Finite.bddAbove_range _
  exact h.deviationGain_true_false_formula_of_bounded σ (C := C) (fun ω => hC ⟨ω, rfl⟩)

theorem mixedGain_false_true_formula [Finite G.Outcome]
    (σ : ∀ i, PMF (G.Strategy i)) :
    G.mixedGain σ false (L.action false true) =
      -2 * h.scale * (1 - L.probTrue σ false) *
        (2 * L.probTrue σ true - 1) := by
  unfold mixedGain
  obtain ⟨C, hC⟩ : BddAbove (Set.range fun ω => |G.utility ω false|) :=
    Finite.bddAbove_range _
  exact h.deviationGain_false_true_formula_of_bounded σ (C := C) (fun ω => hC ⟨ω, rfl⟩)

theorem mixedGain_false_false_formula [Finite G.Outcome]
    (σ : ∀ i, PMF (G.Strategy i)) :
    G.mixedGain σ false (L.action false false) =
      2 * h.scale * L.probTrue σ false *
        (2 * L.probTrue σ true - 1) := by
  unfold mixedGain
  obtain ⟨C, hC⟩ : BddAbove (Set.range fun ω => |G.utility ω false|) :=
    Finite.bddAbove_range _
  exact h.deviationGain_false_false_formula_of_bounded σ (C := C) (fun ω => hC ⟨ω, rfl⟩)

/-- Bounded-utility exact mixed Nash characterization for matching-pennies-like
binary games.  Each player must put probability `1 / 2` on the action labeled
`true`, and conversely that profile is Nash. -/
theorem mixed_nash_iff_half_of_bounded
    (h : G.MatchingPenniesLike L)
    (σ : ∀ i, PMF (G.Strategy i))
    {C : Bool → ℝ} (hbd : ∀ who ω, |G.utility ω who| ≤ C who) :
    G.mixedExtension.IsNash σ ↔
      L.probTrue σ true = (1 / 2 : ℝ) ∧
        L.probTrue σ false = (1 / 2 : ℝ) := by
  letI : ∀ i : Bool, Fintype (G.Strategy i) := fun i => L.fintypeStrategy i
  letI : ∀ i : Bool, Nonempty (G.Strategy i) := fun i => L.nonemptyStrategy i
  constructor
  · intro hN
    have hg := (G.isNash_iff_gains_nonpos_of_bounded σ (C := C) hbd).mp hN
    have hTT := hg true (L.action true true)
    have hTF := hg true (L.action true false)
    have hFT := hg false (L.action false true)
    have hFF := hg false (L.action false false)
    rw [deviationGain_true_true_formula_of_bounded h σ (hbd true)] at hTT
    rw [deviationGain_true_false_formula_of_bounded h σ (hbd true)] at hTF
    rw [deviationGain_false_true_formula_of_bounded h σ (hbd false)] at hFT
    rw [deviationGain_false_false_formula_of_bounded h σ (hbd false)] at hFF
    have hp0 := L.probTrue_nonneg σ true
    have hp1 := L.probTrue_le_one σ true
    have hq0 := L.probTrue_nonneg σ false
    have hq1 := L.probTrue_le_one σ false
    constructor <;> nlinarith [h.scale_pos]
  · rintro ⟨htrue, hfalse⟩
    rw [G.isNash_iff_gains_nonpos_of_bounded σ (C := C) hbd]
    intro who a
    have ha := BinaryActionLabels.action_eq_true_or_false L who a
    cases who
    · rcases ha with rfl | rfl
      · rw [deviationGain_false_true_formula_of_bounded h σ (hbd false)]
        rw [htrue, hfalse]
        norm_num
      · rw [deviationGain_false_false_formula_of_bounded h σ (hbd false)]
        rw [htrue, hfalse]
        norm_num
    · rcases ha with rfl | rfl
      · rw [deviationGain_true_true_formula_of_bounded h σ (hbd true)]
        rw [htrue, hfalse]
        norm_num
      · rw [deviationGain_true_false_formula_of_bounded h σ (hbd true)]
        rw [htrue, hfalse]
        norm_num

/-- Finite-outcome exact mixed Nash characterization for matching-pennies-like
binary games. -/
theorem mixed_nash_iff_half [Finite G.Outcome]
    (h : G.MatchingPenniesLike L)
    (σ : ∀ i, PMF (G.Strategy i)) :
    G.mixedExtension.IsNash σ ↔
      L.probTrue σ true = (1 / 2 : ℝ) ∧
        L.probTrue σ false = (1 / 2 : ℝ) := by
  let hbd : ∀ who, ∃ C : ℝ, ∀ ω, |G.utility ω who| ≤ C := fun who =>
    let ⟨C, hC⟩ := (Finite.bddAbove_range fun ω => |G.utility ω who|)
    ⟨C, fun ω => hC ⟨ω, rfl⟩⟩
  choose C hC using hbd
  exact mixed_nash_iff_half_of_bounded h σ (C := C) (fun who => hC who)

/-- A matching-pennies-like game is balanced at the uniform mixed profile. -/
theorem uniformMixed_balanced
    (h : G.MatchingPenniesLike L)
    [∀ i : Bool, Fintype (G.Strategy i)]
    [∀ i : Bool, Nonempty (G.Strategy i)]
    [Finite G.Outcome] :
    G.IsUniformMixedBalanced := by
  rw [G.isUniformMixedBalanced_iff_mixedGain_eq_zero]
  intro who a
  have ha := BinaryActionLabels.action_eq_true_or_false L who a
  cases who
  · rcases ha with rfl | rfl
    · rw [mixedGain_false_true_formula h]
      rw [L.probTrue_uniformMixedProfile true, L.probTrue_uniformMixedProfile false]
      ring
    · rw [mixedGain_false_false_formula h]
      rw [L.probTrue_uniformMixedProfile true, L.probTrue_uniformMixedProfile false]
      ring
  · rcases ha with rfl | rfl
    · rw [mixedGain_true_true_formula h]
      rw [L.probTrue_uniformMixedProfile true, L.probTrue_uniformMixedProfile false]
      ring
    · rw [mixedGain_true_false_formula h]
      rw [L.probTrue_uniformMixedProfile true, L.probTrue_uniformMixedProfile false]
      ring

/-- The uniform mixed profile is Nash in any finite-outcome
matching-pennies-like binary game. -/
theorem uniformMixedProfile_isNash
    (h : G.MatchingPenniesLike L)
    [∀ i : Bool, Fintype (G.Strategy i)]
    [∀ i : Bool, Nonempty (G.Strategy i)]
    [Finite G.Outcome] :
    G.mixedExtension.IsNash G.uniformMixedProfile := by
  exact (uniformMixed_balanced h).uniformMixedProfile_isNash

/-- The label-induced uniform mixed profile is Nash in any finite-outcome
matching-pennies-like binary game.  Unlike `uniformMixedProfile_isNash`, this
does not need external `Fintype` or `Nonempty` instances for the strategy sets. -/
theorem labeledUniformMixedProfile_isNash
    (h : G.MatchingPenniesLike L)
    [Finite G.Outcome] :
    G.mixedExtension.IsNash L.uniformMixedProfile := by
  rw [mixed_nash_iff_half h]
  exact ⟨L.probTrue_labeledUniformMixedProfile true,
    L.probTrue_labeledUniformMixedProfile false⟩

end MatchingPenniesLike

namespace IsMatchingPenniesLike

variable {G : KernelGame Bool} {L : BinaryActionLabels G}

/-- Prop-valued wrapper for the bounded-utility exact mixed Nash
characterization. -/
theorem mixed_nash_iff_half_of_bounded
    (h : G.IsMatchingPenniesLike L)
    (σ : ∀ i, PMF (G.Strategy i))
    {C : Bool → ℝ} (hbd : ∀ who ω, |G.utility ω who| ≤ C who) :
    G.mixedExtension.IsNash σ ↔
      L.probTrue σ true = (1 / 2 : ℝ) ∧
        L.probTrue σ false = (1 / 2 : ℝ) := by
  rcases h with ⟨w⟩
  exact MatchingPenniesLike.mixed_nash_iff_half_of_bounded w σ hbd

/-- Prop-valued wrapper for the finite-outcome exact mixed Nash
characterization. -/
theorem mixed_nash_iff_half [Finite G.Outcome]
    (h : G.IsMatchingPenniesLike L)
    (σ : ∀ i, PMF (G.Strategy i)) :
    G.mixedExtension.IsNash σ ↔
      L.probTrue σ true = (1 / 2 : ℝ) ∧
        L.probTrue σ false = (1 / 2 : ℝ) := by
  rcases h with ⟨w⟩
  exact MatchingPenniesLike.mixed_nash_iff_half w σ

/-- Prop-valued wrapper for uniform mixed balance. -/
theorem uniformMixed_balanced
    (h : G.IsMatchingPenniesLike L)
    [∀ i : Bool, Fintype (G.Strategy i)]
    [∀ i : Bool, Nonempty (G.Strategy i)]
    [Finite G.Outcome] :
    G.IsUniformMixedBalanced := by
  rcases h with ⟨w⟩
  exact MatchingPenniesLike.uniformMixed_balanced w

/-- Prop-valued wrapper for uniform-profile Nash. -/
theorem uniformMixedProfile_isNash
    (h : G.IsMatchingPenniesLike L)
    [∀ i : Bool, Fintype (G.Strategy i)]
    [∀ i : Bool, Nonempty (G.Strategy i)]
    [Finite G.Outcome] :
    G.mixedExtension.IsNash G.uniformMixedProfile := by
  rcases h with ⟨w⟩
  exact MatchingPenniesLike.uniformMixedProfile_isNash w

/-- Prop-valued wrapper for the label-induced uniform-profile Nash theorem. -/
theorem labeledUniformMixedProfile_isNash
    (h : G.IsMatchingPenniesLike L)
    [Finite G.Outcome] :
    G.mixedExtension.IsNash L.uniformMixedProfile := by
  rcases h with ⟨w⟩
  exact MatchingPenniesLike.labeledUniformMixedProfile_isNash w

end IsMatchingPenniesLike

end KernelGame
end GameTheory
