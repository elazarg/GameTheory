/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.OpenGame.Compile

/-!
# Finite Tensors of Decisions

This file quarantines the ordered, right-associated product representation of
an iterated binary tensor.  The canonical simultaneous shape remains
Π-typed; `finTensorIso` is the single translation boundary between the two.
-/

namespace OpenGames.ShapeN

open scoped OpenGames

/-- Right-associated product of a `Fin n`-indexed type family. -/
def FinTuple : (n : Nat) → (Fin n → Type) → Type
  | 0, _ => Unit
  | n + 1, T => T 0 × FinTuple n (fun i => T i.succ)

/-- Dependent functions over `Fin n` are equivalent to right-associated
products in the enumeration order `0, ..., n-1`. -/
def finPiEquiv : {n : Nat} → (T : Fin n → Type) →
    (∀ i, T i) ≃ FinTuple n T
  | 0, T =>
      { toFun := fun _ => ()
        invFun := fun _ i => Fin.elim0 i
        left_inv := fun f => by funext i; exact Fin.elim0 i
        right_inv := fun x => by cases x; rfl }
  | n + 1, T =>
      let tail := finPiEquiv (fun i : Fin n => T i.succ)
      { toFun := fun f => (f 0, tail (fun i => f i.succ))
        invFun := fun p => Fin.cases p.1 (tail.symm p.2)
        left_inv := fun f => by
          funext i
          refine Fin.cases ?_ (fun j => ?_) i
          · rfl
          · exact congrFun (tail.symm_apply_apply (fun j => f j.succ)) j
        right_inv := fun p => by
          apply Prod.ext
          · rfl
          · exact tail.apply_symm_apply p.2 }

@[simp] theorem finPiEquiv_zero_apply (T : Fin 0 → Type) (f : ∀ i, T i) :
    finPiEquiv T f = () := rfl

@[simp] theorem finPiEquiv_succ_apply {n : Nat} (T : Fin (n + 1) → Type)
    (f : ∀ i, T i) :
    finPiEquiv T f =
      (f 0, finPiEquiv (fun i : Fin n => T i.succ) (fun i => f i.succ)) :=
  rfl

@[simp] theorem finPiEquiv_succ_symm_zero {n : Nat}
    (T : Fin (n + 1) → Type) (p : FinTuple (n + 1) T) :
    (finPiEquiv T).symm p 0 = p.1 := rfl

@[simp] theorem finPiEquiv_succ_symm_succ {n : Nat}
    (T : Fin (n + 1) → Type) (p : FinTuple (n + 1) T) (i : Fin n) :
    (finPiEquiv T).symm p i.succ =
      (finPiEquiv (fun j : Fin n => T j.succ)).symm p.2 i :=
  rfl

@[simp] theorem update_fin_succ_zero {n : Nat}
    (T : Fin (n + 1) → Type) (f : ∀ i, T i) (j : Fin n) (x : T j.succ) :
    Function.update f j.succ x 0 = f 0 := by
  have hzero : (0 : Fin (n + 1)) ≠ j.succ := (Fin.succ_ne_zero j).symm
  simp [Function.update, hzero]

@[simp] theorem update_fin_succ_succ {n : Nat}
    (T : Fin (n + 1) → Type) (f : ∀ i, T i) (j i : Fin n) (x : T j.succ) :
    Function.update f j.succ x i.succ =
      Function.update (fun q => f q.succ) j x i := by
  by_cases hij : i = j
  · subst j
    simp
  · have hsucc : i.succ ≠ j.succ := by
      intro h
      exact hij (Fin.succ_injective n h)
    simp [Function.update, hij, hsucc]

@[simp] theorem finPiEquiv_update_zero {n : Nat}
    (T : Fin (n + 1) → Type) (f : ∀ i, T i) (x : T 0) :
    finPiEquiv T (Function.update f 0 x) =
      (x, finPiEquiv (fun i : Fin n => T i.succ) (fun i => f i.succ)) := by
  apply Prod.ext
  · simp
  · change
      finPiEquiv (fun i : Fin n => T i.succ)
          (fun i => Function.update f 0 x i.succ) =
        finPiEquiv (fun i : Fin n => T i.succ) (fun i => f i.succ)
    rw [Equiv.apply_eq_iff_eq]
    funext i
    simp

@[simp] theorem finPiEquiv_update_succ {n : Nat}
    (T : Fin (n + 1) → Type) (f : ∀ i, T i) (j : Fin n) (x : T j.succ) :
    finPiEquiv T (Function.update f j.succ x) =
      (f 0, finPiEquiv (fun i : Fin n => T i.succ)
        (Function.update (fun i => f i.succ) j x)) := by
  apply Prod.ext
  · exact update_fin_succ_zero T f j x
  · change
      finPiEquiv (fun i : Fin n => T i.succ)
          (fun i => Function.update f j.succ x i.succ) =
        finPiEquiv (fun i : Fin n => T i.succ)
          (Function.update (fun i => f i.succ) j x)
    rw [Equiv.apply_eq_iff_eq]
    funext i
    exact update_fin_succ_succ T f j i x

/-- Ordered right-associated tensor of one decision per `Fin n` player. -/
def tensorDecisions : {n : Nat} → (X Y : Fin n → Type) →
    OpenGame (FinTuple n X) (FinTuple n fun _ => Unit)
      (FinTuple n Y) (FinTuple n fun _ => ℝ)
  | 0, _, _ => OpenGame.idWire Unit Unit
  | n + 1, X, Y =>
      OpenGame.decision (X 0) (Y 0) ⊗ₒ
        tensorDecisions (fun i : Fin n => X i.succ)
          (fun i : Fin n => Y i.succ)

/-- Strategy translation from Π-shaped contingent plans to the ordered tensor. -/
def tensorStrategyEquiv : {n : Nat} → (X Y : Fin n → Type) →
    (∀ i, X i → Y i) ≃ (tensorDecisions X Y).Strategy
  | 0, _, _ =>
      { toFun := fun _ => ()
        invFun := fun _ i => Fin.elim0 i
        left_inv := fun σ => by funext i; exact Fin.elim0 i
        right_inv := fun u => by cases u; rfl }
  | n + 1, X, Y =>
      let tail := tensorStrategyEquiv
        (fun i : Fin n => X i.succ) (fun i : Fin n => Y i.succ)
      { toFun := fun σ => (σ 0, tail (fun i => σ i.succ))
        invFun := fun p => Fin.cases p.1 (tail.symm p.2)
        left_inv := fun σ => by
          funext i
          refine Fin.cases ?_ (fun j => ?_) i
          · rfl
          · exact congrFun (tail.symm_apply_apply (fun j => σ j.succ)) j
        right_inv := fun p => by
          apply Prod.ext
          · rfl
          · exact tail.apply_symm_apply p.2 }

/-- Iterated tensor play is componentwise play after Π-to-product transport. -/
theorem tensorDecisions_play : {n : Nat} →
    ∀ (X Y : Fin n → Type) (σ : ∀ i, X i → Y i) (h : ∀ i, X i),
      (tensorDecisions X Y).play (tensorStrategyEquiv X Y σ)
          (finPiEquiv X h) =
        finPiEquiv Y (fun i => σ i (h i))
  | 0, X, Y, σ, h => rfl
  | n + 1, X, Y, σ, h => by
      apply Prod.ext
      · rfl
      · exact tensorDecisions_play
          (fun i : Fin n => X i.succ) (fun i : Fin n => Y i.succ)
          (fun i => σ i.succ) (fun i => h i.succ)

/-- Every decision has unit coplay; the iterated tensor preserves the nested
unit tuple. -/
theorem tensorDecisions_coplay : {n : Nat} →
    ∀ (X Y : Fin n → Type) (σ : ∀ i, X i → Y i) (h : ∀ i, X i)
      (r : FinTuple n fun _ => ℝ),
      (tensorDecisions X Y).coplay (tensorStrategyEquiv X Y σ)
          (finPiEquiv X h) r =
        finPiEquiv (fun _ : Fin n => Unit) (fun _ => ())
  | 0, X, Y, σ, h, r => rfl
  | n + 1, X, Y, σ, h, r => by
      apply Prod.ext
      · rfl
      · exact tensorDecisions_coplay
          (fun i : Fin n => X i.succ) (fun i : Fin n => Y i.succ)
          (fun i => σ i.succ) (fun i => h i.succ) r.2

/-- Equilibrium is preserved by the Π-to-ordered-tensor translation. -/
theorem tensorDecisions_equilibrium : {n : Nat} →
    ∀ (X Y : Fin n → Type) (h : ∀ i, X i)
      (k : FinTuple n Y → FinTuple n fun _ => ℝ)
      (σ : ∀ i, X i → Y i),
      (tensorDecisions X Y).IsEquilibriumIn (finPiEquiv X h) k
          (tensorStrategyEquiv X Y σ) ↔
        (ShapeN X Y).IsEquilibriumIn h
          (fun ys => (finPiEquiv (fun _ : Fin n => ℝ)).symm
            (k (finPiEquiv Y ys))) σ
  | 0, X, Y, h, k, σ => by
      simp [ShapeN, tensorDecisions, tensorStrategyEquiv, OpenGame.idWire,
        OpenGame.ofLens, Lens.toOpenGame]
  | n + 1, X, Y, h, k, σ => by
      let Xtail : Fin n → Type := fun i => X i.succ
      let Ytail : Fin n → Type := fun i => Y i.succ
      change
        ((∀ y : Y 0,
            (k (y, (tensorDecisions Xtail Ytail).play
              (tensorStrategyEquiv Xtail Ytail (fun i => σ i.succ))
              (finPiEquiv Xtail (fun i => h i.succ)))).1 ≤
            (k (σ 0 (h 0),
              (tensorDecisions Xtail Ytail).play
                (tensorStrategyEquiv Xtail Ytail (fun i => σ i.succ))
                (finPiEquiv Xtail (fun i => h i.succ)))).1) ∧
          (tensorDecisions Xtail Ytail).IsEquilibriumIn
            (finPiEquiv Xtail (fun i => h i.succ))
            (fun ys => (k (σ 0 (h 0), ys)).2)
            (tensorStrategyEquiv Xtail Ytail (fun i => σ i.succ))) ↔
          (ShapeN X Y).IsEquilibriumIn h
            (fun ys => (finPiEquiv (fun _ : Fin (n + 1) => ℝ)).symm
              (k (finPiEquiv Y ys))) σ
      rw [tensorDecisions_play Xtail Ytail]
      rw [tensorDecisions_equilibrium Xtail Ytail]
      constructor
      · rintro ⟨hhead, htail⟩ i
        refine Fin.cases ?_ (fun j => ?_) i
        · intro y
          simpa [ShapeN, Xtail, Ytail] using hhead y
        · intro y
          simpa [ShapeN, Xtail, Ytail] using htail j y
      · intro hall
        constructor
        · intro y
          simpa [ShapeN, Xtail, Ytail] using hall 0 y
        · intro j y
          simpa [ShapeN, Xtail, Ytail] using hall j.succ y

/-- The Π-shaped simultaneous game is isomorphic to the ordered iterated
binary tensor for every finite number of players. -/
def finTensorIso {n : Nat} (X Y : Fin n → Type) :
    OpenGameIso (ShapeN X Y) (tensorDecisions X Y) where
  eX := finPiEquiv X
  eS := finPiEquiv fun _ => Unit
  eY := finPiEquiv Y
  eR := finPiEquiv fun _ => ℝ
  stratEquiv := tensorStrategyEquiv X Y
  play_preserved := tensorDecisions_play X Y
  coplay_preserved := tensorDecisions_coplay X Y
  equilibrium_preserved := tensorDecisions_equilibrium X Y

end OpenGames.ShapeN
