/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.OpenGame.Compile

/-!
# Finite-Horizon Sequential Open-Game Shapes

`ShapeSeq n A` is the direct perfect-information shape for `n` ordered
decisions with a common action type `A` and one decision owner per stage.
The strategy of stage `i` is a contingent plan `(Fin i → A) → A`, so it sees
exactly the preceding action history.  Playing a profile recursively realizes
the complete `Fin n → A` path.

The equilibrium predicate is the strategic-form Nash predicate on contingent
plans.  In particular, a deviation at an early stage is followed by the fixed
later plans reacting to the changed history.  It is deliberately the plain
sequential/agent-form notion, not subgame-perfect equilibrium; a future
extension can impose optimality at every counterfactual history.

The homogeneous action type keeps this first n-stage API small while already
covering arbitrary finite horizons.  Heterogeneous actions require dependent
prefix histories and are left as a separate generalization.
-/

namespace OpenGames

namespace ShapeSeq

/-- Histories available at stage `i`. -/
abbrev History (A : Type) (i : Nat) := Fin i → A

/-- A contingent plan at stage `i`. -/
abbrev StageStrategy (A : Type) (i : Nat) := History A i → A

/-- A profile containing one contingent plan for every stage. -/
abbrev Strategy (n : Nat) (A : Type) :=
  ∀ i : Fin n, StageStrategy A i.val

/-- Realize a complete path from an ordered profile of contingent plans. -/
def realize {A : Type} : (n : Nat) → Strategy n A → Fin n → A
  | 0, _ => Fin.elim0
  | n + 1, σ =>
      let prior := realize n (fun i => σ i.castSucc)
      Fin.snoc prior (σ (Fin.last n) prior)

end ShapeSeq

/-- The direct finite-horizon sequential shape. -/
def ShapeSeq (n : Nat) (A : Type) :
    OpenGame Unit Unit (Fin n → A) (Fin n → ℝ) where
  Strategy := ShapeSeq.Strategy n A
  play := fun σ _ => ShapeSeq.realize n σ
  coplay := fun _ _ _ => ()
  IsEquilibriumIn := fun _ k σ =>
    ∀ i (deviation : ShapeSeq.StageStrategy A i.val),
      k (ShapeSeq.realize n (Function.update σ i deviation)) i ≤
        k (ShapeSeq.realize n σ) i

namespace ShapeSeq

@[simp] theorem realize_succ_castSucc {A : Type} {n : Nat}
    (σ : Strategy (n + 1) A) (i : Fin n) :
    realize (n + 1) σ i.castSucc =
      realize n (fun j => σ j.castSucc) i := by
  simp [realize]

@[simp] theorem realize_succ_last {A : Type} {n : Nat}
    (σ : Strategy (n + 1) A) :
    realize (n + 1) σ (Fin.last n) =
      σ (Fin.last n) (realize n fun j => σ j.castSucc) := by
  simp [realize]

/-- The strategic-form game induced by an n-stage closing continuation. -/
def actionNFG (n : Nat) (A : Type) (k : (Fin n → A) → Fin n → ℝ) :
    NFG.NFGGame (Fin n) (fun i => StageStrategy A i.val) where
  Outcome := Fin n → A
  outcome := realize n
  utility := k

/-- Compile the n-stage strategic form through the existing NFG bridge. -/
noncomputable def compileAction (n : Nat) (A : Type)
    (k : (Fin n → A) → Fin n → ℝ) : GameTheory.KernelGame (Fin n) :=
  (actionNFG n A k).toKernelGame

/-- Plain n-stage equilibrium is exactly pure Nash equilibrium of the induced
strategic form. -/
theorem isEquilibriumIn_iff_isNashPure {n : Nat} {A : Type}
    (k : (Fin n → A) → Fin n → ℝ) (σ : Strategy n A) :
    (ShapeSeq n A).IsEquilibriumIn () k σ ↔
      NFG.IsNashPure (actionNFG n A k) σ := by
  rfl

/-- Kernel-level correctness of n-stage compilation. -/
theorem isEquilibriumIn_iff_isNash {n : Nat} {A : Type}
    (k : (Fin n → A) → Fin n → ℝ) (σ : Strategy n A) :
    (ShapeSeq n A).IsEquilibriumIn () k σ ↔
      (compileAction n A k).IsNash σ := by
  rw [isEquilibriumIn_iff_isNashPure]
  exact NFG.IsNashPure_iff_kernelGame (actionNFG n A k) σ

/-! ## Compatibility with the direct two-stage shape -/

/-- A two-coordinate finite function as a binary product. -/
def finTwoEquiv (A : Type) : (Fin 2 → A) ≃ A × A where
  toFun f := (f 0, f 1)
  invFun p := Fin.cases p.1 fun _ => p.2
  left_inv f := by
    funext i
    fin_cases i <;> rfl
  right_inv _ := rfl

@[simp] theorem finTwoEquiv_apply_fst (f : Fin 2 → A) :
    (finTwoEquiv A f).1 = f 0 := rfl

@[simp] theorem finTwoEquiv_apply_snd (f : Fin 2 → A) :
    (finTwoEquiv A f).2 = f 1 := rfl

@[simp] theorem finTwoEquiv_symm_zero (p : A × A) :
    (finTwoEquiv A).symm p 0 = p.1 := rfl

@[simp] theorem finTwoEquiv_symm_one (p : A × A) :
    (finTwoEquiv A).symm p 1 = p.2 := rfl

@[simp] theorem finTwoEquiv_snoc (f : Fin 1 → A) (a : A) :
    finTwoEquiv A (Fin.snoc f a) = (f 0, a) := by
  rfl

@[simp] theorem snoc_empty {A : Type} (a : A) :
    (Fin.snoc Fin.elim0 a : Fin 1 → A) = fun _ => a := by
  funext i
  fin_cases i
  rfl

/-- Two ordered contingent plans are a leader action and a follower plan. -/
def twoStrategyEquiv (A : Type) : Strategy 2 A ≃ A × (A → A) where
  toFun σ := (σ 0 Fin.elim0, fun a => σ 1 fun _ => a)
  invFun p := fun i =>
    Fin.cases (fun _ => p.1)
      (fun j h => p.2 (h (Fin.last j.val))) i
  left_inv σ := by
    apply funext
    intro i
    apply funext
    intro h
    fin_cases i
    · change σ 0 Fin.elim0 = σ 0 h
      apply congrArg (σ 0)
      funext j
      exact Fin.elim0 j
    · change σ 1 (fun _ => h (Fin.last 0)) = σ 1 h
      apply congrArg (σ 1)
      funext j
      fin_cases j
      rfl
  right_inv p := by
    apply Prod.ext
    · rfl
    · funext a
      rfl

@[simp] theorem twoStrategyEquiv_apply_fst (σ : Strategy 2 A) :
    (twoStrategyEquiv A σ).1 = σ 0 Fin.elim0 := rfl

@[simp] theorem twoStrategyEquiv_apply_snd (σ : Strategy 2 A) (a : A) :
    (twoStrategyEquiv A σ).2 a = σ 1 (fun _ => a) := rfl

/-- At horizon two, `ShapeSeq` is the existing direct two-stage shape, up to
the canonical function/product presentations of outcomes and cooutcomes. -/
def twoStageIso (A : Type) :
    OpenGameIso (ShapeSeq 2 A) (ShapeS A A) where
  eX := Equiv.refl _
  eS := Equiv.refl _
  eY := finTwoEquiv A
  eR := finTwoEquiv ℝ
  stratEquiv := twoStrategyEquiv A
  play_preserved := by
    intro σ x
    cases x
    rfl
  coplay_preserved := by
    intro σ x r
    cases x
    rfl
  equilibrium_preserved := by
    intro x k σ
    cases x
    change
      ((∀ a,
          (k (a, σ 1 (fun _ => a))).1 ≤
            (k (σ 0 Fin.elim0,
              σ 1 (fun _ => σ 0 Fin.elim0))).1) ∧
        ∀ a,
          (k (σ 0 Fin.elim0, a)).2 ≤
            (k (σ 0 Fin.elim0,
              σ 1 (fun _ => σ 0 Fin.elim0))).2) ↔
        ∀ i (deviation : StageStrategy A i.val),
          (finTwoEquiv ℝ).symm
              (k (finTwoEquiv A
                (realize 2 (Function.update σ i deviation)))) i ≤
            (finTwoEquiv ℝ).symm
              (k (finTwoEquiv A (realize 2 σ))) i
    constructor
    · rintro ⟨hleader, hfollower⟩ i deviation
      fin_cases i
      · simpa [realize, Function.update, Fin.snoc] using
          hleader (deviation Fin.elim0)
      · simpa [realize, Function.update, Fin.snoc] using
          hfollower (deviation fun _ => σ 0 Fin.elim0)
    · intro hn
      constructor
      · intro a
        let deviation : StageStrategy A 0 := fun _ => a
        simpa [realize, Function.update, Fin.snoc, deviation] using
          hn 0 deviation
      · intro a
        let deviation : StageStrategy A 1 := fun _ => a
        simpa [realize, Function.update, Fin.snoc, deviation] using
          hn 1 deviation

end ShapeSeq

end OpenGames
