/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.OpenGame.Mixed
import GameTheory.Languages.OpenGame.Compile
import GameTheory.Concepts.Mixed.MixedExtension
import GameTheory.Languages.NFG.Compile

/-!
# Probabilistic Open Games and Mixed Normal Form

This bridge identifies the two-player `GProb` decision tensor with the
repository's existing mixed extension of a Bool-indexed normal-form game.
Finite support disappears at the boundary when the action carrier is finite:
every Mathlib `PMF` on that carrier has finite support.
-/

noncomputable section

namespace OpenGames.ProbOpenGame

open GameTheory Math

variable {A : Type}

/-- Assemble two finite marginals into the library's Bool-indexed mixed
profile, in `(false, true)` order. -/
def boolMixedProfile (μfalse μtrue : FinPMF A) :
    NFG.MixedProfile (fun _ : Bool => A)
  | false => μfalse.toPMF
  | true => μtrue.toPMF

@[simp] theorem boolMixedProfile_false (μfalse μtrue : FinPMF A) :
    boolMixedProfile μfalse μtrue false = μfalse.toPMF :=
  rfl

@[simp] theorem boolMixedProfile_true (μfalse μtrue : FinPMF A) :
    boolMixedProfile μfalse μtrue true = μtrue.toPMF :=
  rfl

@[simp] theorem boolMixedProfile_update_false [Finite A]
    (μfalse μtrue : FinPMF A)
    (τ : PMF A) :
    Function.update (boolMixedProfile μfalse μtrue) false τ =
      boolMixedProfile (FinPMF.ofPMF τ) μtrue := by
  funext i
  cases i <;> simp [boolMixedProfile, Function.update]

@[simp] theorem boolMixedProfile_update_true [Finite A]
    (μfalse μtrue : FinPMF A)
    (τ : PMF A) :
    Function.update (boolMixedProfile μfalse μtrue) true τ =
      boolMixedProfile μfalse (FinPMF.ofPMF τ) := by
  funext i
  cases i <;> simp [boolMixedProfile, Function.update]

/-- The independent Bool-indexed product law becomes the binary independent
product after the canonical Π-to-pair equivalence. -/
theorem map_pmfPi_bool_eq_product (μfalse μtrue : FinPMF A) :
    (Math.PMFProduct.pmfPi (boolMixedProfile μfalse μtrue)).map
        (ShapeN.boolPiEquiv fun _ : Bool => A) =
      (FinPMF.product μfalse μtrue).toPMF := by
  ext p
  rcases p with ⟨a, b⟩
  rw [Math.ProbabilityMassFunction.map_equiv_apply]
  simp [Math.PMFProduct.pmfPi_apply, boolMixedProfile, mul_comm]

/-- Pair-valued payoff table associated to a Bool-indexed NFG, in
`(false, true)` player order. -/
def boolPayoffPair (G : NFG.NFGGame Bool (fun _ => A)) (p : A × A) :
    ℝ × ℝ :=
  let σ := (ShapeN.boolPiEquiv fun _ : Bool => A).symm p
  (G.utility (G.outcome σ) false, G.utility (G.outcome σ) true)

private theorem mixed_eu_false_eq_pair_expect
    (G : NFG.NFGGame Bool (fun _ => A)) [Finite G.Outcome]
    (μfalse μtrue : FinPMF A) :
    G.toKernelGame.mixedExtension.eu
        (boolMixedProfile μfalse μtrue) false =
      expect (FinPMF.product μfalse μtrue)
        (fun p => (boolPayoffPair G p).1) := by
  letI : Finite G.toKernelGame.Outcome := ‹Finite G.Outcome›
  rw [G.toKernelGame.mixedExtension_eu]
  unfold expect
  rw [← map_pmfPi_bool_eq_product μfalse μtrue,
    Math.Probability.expect_map]
  simp only [GameTheory.KernelGame.eu, NFG.NFGGame.toKernelGame,
    Math.Probability.expect_pure, boolPayoffPair]
  apply Math.ProbabilityMassFunction.expect_congr_on_support
  intro σ _hσ
  congr 2
  funext i
  cases i <;> rfl

private theorem mixed_eu_true_eq_pair_expect
    (G : NFG.NFGGame Bool (fun _ => A)) [Finite G.Outcome]
    (μfalse μtrue : FinPMF A) :
    G.toKernelGame.mixedExtension.eu
        (boolMixedProfile μfalse μtrue) true =
      expect (FinPMF.product μfalse μtrue)
        (fun p => (boolPayoffPair G p).2) := by
  letI : Finite G.toKernelGame.Outcome := ‹Finite G.Outcome›
  rw [G.toKernelGame.mixedExtension_eu]
  unfold expect
  rw [← map_pmfPi_bool_eq_product μfalse μtrue,
    Math.Probability.expect_map]
  simp only [GameTheory.KernelGame.eu, NFG.NFGGame.toKernelGame,
    Math.Probability.expect_pure, boolPayoffPair]
  apply Math.ProbabilityMassFunction.expect_congr_on_support
  intro σ _hσ
  congr 2
  funext i
  cases i <;> rfl

/-- The generic two-player mixed predicate recovered by the probabilistic
decision tensor is exactly the library's `NFG.IsNashMixed`. -/
theorem isMixedNash2_iff_isNashMixed
    (G : NFG.NFGGame Bool (fun _ => A)) [Finite A] [Finite G.Outcome]
    (μfalse μtrue : FinPMF A) :
    IsMixedNash2 (boolPayoffPair G) μfalse μtrue ↔
      NFG.IsNashMixed G (boolMixedProfile μfalse μtrue) := by
  unfold IsMixedNash2
  constructor
  · rintro ⟨hfalse, htrue⟩
    change G.toKernelGame.mixedExtension.IsNash
      (boolMixedProfile μfalse μtrue)
    intro who τ
    cases who
    · change PMF A at τ
      calc
        G.toKernelGame.mixedExtension.eu
            (boolMixedProfile μfalse μtrue) false =
            expect (FinPMF.product μfalse μtrue)
              (fun p => (boolPayoffPair G p).1) :=
          mixed_eu_false_eq_pair_expect G μfalse μtrue
        _ ≥ expect (FinPMF.product (FinPMF.ofPMF τ) μtrue)
              (fun p => (boolPayoffPair G p).1) := hfalse (FinPMF.ofPMF τ)
        _ = G.toKernelGame.mixedExtension.eu
              (boolMixedProfile (FinPMF.ofPMF τ) μtrue) false :=
          (mixed_eu_false_eq_pair_expect G (FinPMF.ofPMF τ) μtrue).symm
        _ = G.toKernelGame.mixedExtension.eu
              (Function.update (boolMixedProfile μfalse μtrue) false τ) false := by
          exact congrArg
            (fun σ : NFG.MixedProfile (fun _ : Bool => A) =>
              G.toKernelGame.mixedExtension.eu σ false)
            (boolMixedProfile_update_false μfalse μtrue τ).symm
    · change PMF A at τ
      calc
        G.toKernelGame.mixedExtension.eu
            (boolMixedProfile μfalse μtrue) true =
            expect (FinPMF.product μfalse μtrue)
              (fun p => (boolPayoffPair G p).2) :=
          mixed_eu_true_eq_pair_expect G μfalse μtrue
        _ ≥ expect (FinPMF.product μfalse (FinPMF.ofPMF τ))
              (fun p => (boolPayoffPair G p).2) := htrue (FinPMF.ofPMF τ)
        _ = G.toKernelGame.mixedExtension.eu
              (boolMixedProfile μfalse (FinPMF.ofPMF τ)) true :=
          (mixed_eu_true_eq_pair_expect G μfalse (FinPMF.ofPMF τ)).symm
        _ = G.toKernelGame.mixedExtension.eu
              (Function.update (boolMixedProfile μfalse μtrue) true τ) true := by
          exact congrArg
            (fun σ : NFG.MixedProfile (fun _ : Bool => A) =>
              G.toKernelGame.mixedExtension.eu σ true)
            (boolMixedProfile_update_true μfalse μtrue τ).symm
  · intro h
    change G.toKernelGame.mixedExtension.IsNash
      (boolMixedProfile μfalse μtrue) at h
    constructor
    · intro μ'
      calc
        expect (FinPMF.product μ' μtrue)
            (fun p => (boolPayoffPair G p).1) =
            G.toKernelGame.mixedExtension.eu
              (boolMixedProfile μ' μtrue) false :=
          (mixed_eu_false_eq_pair_expect G μ' μtrue).symm
        _ = G.toKernelGame.mixedExtension.eu
              (Function.update (boolMixedProfile μfalse μtrue) false μ'.toPMF) false := by
          exact congrArg
            (fun σ : NFG.MixedProfile (fun _ : Bool => A) =>
              G.toKernelGame.mixedExtension.eu σ false)
            (boolMixedProfile_update_false μfalse μtrue μ'.toPMF).symm
        _ ≤ G.toKernelGame.mixedExtension.eu
              (boolMixedProfile μfalse μtrue) false := h false μ'.toPMF
        _ = expect (FinPMF.product μfalse μtrue)
              (fun p => (boolPayoffPair G p).1) :=
          mixed_eu_false_eq_pair_expect G μfalse μtrue
    · intro ν'
      calc
        expect (FinPMF.product μfalse ν')
            (fun p => (boolPayoffPair G p).2) =
            G.toKernelGame.mixedExtension.eu
              (boolMixedProfile μfalse ν') true :=
          (mixed_eu_true_eq_pair_expect G μfalse ν').symm
        _ = G.toKernelGame.mixedExtension.eu
              (Function.update (boolMixedProfile μfalse μtrue) true ν'.toPMF) true := by
          exact congrArg
            (fun σ : NFG.MixedProfile (fun _ : Bool => A) =>
              G.toKernelGame.mixedExtension.eu σ true)
            (boolMixedProfile_update_true μfalse μtrue ν'.toPMF).symm
        _ ≤ G.toKernelGame.mixedExtension.eu
              (boolMixedProfile μfalse μtrue) true := h true ν'.toPMF
        _ = expect (FinPMF.product μfalse μtrue)
              (fun p => (boolPayoffPair G p).2) :=
          mixed_eu_true_eq_pair_expect G μfalse μtrue

/-- End-to-end recovery: equilibrium of the tensor of two probabilistic
decisions is mixed Nash in the existing NFG semantics. -/
theorem actionDecision_tensor_isEquilibriumIn_iff_isNashMixed
    (G : NFG.NFGGame Bool (fun _ => A)) [Finite A] [Finite G.Outcome]
    (μfalse μtrue : FinPMF A) :
    (actionDecision A ⊗ₚ actionDecision A).IsEquilibriumIn ((), ())
        (boolPayoffPair G) (FinPMF.product μfalse μtrue) ↔
      NFG.IsNashMixed G (boolMixedProfile μfalse μtrue) :=
  (actionDecision_tensor_isEquilibriumIn_iff_isMixedNash2
    (boolPayoffPair G) μfalse μtrue).trans
      (isMixedNash2_iff_isNashMixed G μfalse μtrue)

end OpenGames.ProbOpenGame
