/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.OpenGame.Syntax
import GameTheory.Languages.NFG.Compile

/-!
# Compiling Simultaneous Open-Game Shapes

`ShapeN` is the canonical simultaneous open game with one decision per player.
Its histories, actions, cooutcomes, and strategies are all Π-shaped; no
arbitrary nesting of binary products leaks into compilation.

Compilation is context-indexed by the continuation `k`.  It deliberately goes
through the existing NFG bridge, so deterministic strategic-form semantics has
one implementation in the library.
-/

namespace OpenGames

open scoped OpenGames

/-- The canonical simultaneous shape with one decision per player.

At a context `(h, k)`, each player compares its realized action with every
unilateral alternative, holding the other realized actions fixed. -/
def ShapeN {ι : Type} [DecidableEq ι] (X Y : ι → Type) :
    OpenGame (∀ i, X i) (∀ _i : ι, Unit) (∀ i, Y i) (∀ _i : ι, ℝ) where
  Strategy := ∀ i, X i → Y i
  play σ h i := σ i (h i)
  coplay _ _ _ _ := ()
  IsEquilibriumIn h k σ :=
    ∀ i (y : Y i),
      k (Function.update (fun j => σ j (h j)) i y) i ≤
        k (fun j => σ j (h j)) i

namespace ShapeN

variable {ι : Type} [DecidableEq ι]
variable {X Y : ι → Type}

/-- Realize a contingent open-game strategy at a history profile. -/
def realize (h : ∀ i, X i) (σ : ∀ i, X i → Y i) : ∀ i, Y i :=
  fun i => σ i (h i)

/-- The action-level NFG induced by a continuation. -/
def actionNFG (Y : ι → Type) (k : (∀ i, Y i) → (∀ _i : ι, ℝ)) :
    NFG.NFGGame ι Y where
  Outcome := ∀ i, Y i
  outcome := id
  utility := k

/-- Compile the simultaneous shape's action game for continuation `k`.

The history type is absent because histories affect only the translation from
contingent strategies to their realized action profile. -/
noncomputable def compileAction (Y : ι → Type)
    (k : (∀ i, Y i) → (∀ _i : ι, ℝ)) : GameTheory.KernelGame ι :=
  (actionNFG Y k).toKernelGame

/-- Open-game equilibrium for the simultaneous shape is exactly pure NFG Nash
at the realized action profile. -/
theorem isEquilibriumIn_iff_isNashPure
    (h : ∀ i, X i) (k : (∀ i, Y i) → (∀ _i : ι, ℝ))
    (σ : ∀ i, X i → Y i) :
    (ShapeN X Y).IsEquilibriumIn h k σ ↔
      NFG.IsNashPure (actionNFG Y k) (realize h σ) := by
  rfl

/-- Context-parametric correctness of compilation to `KernelGame`. -/
theorem isEquilibriumIn_iff_isNash
    (h : ∀ i, X i) (k : (∀ i, Y i) → (∀ _i : ι, ℝ))
    (σ : ∀ i, X i → Y i) :
    (ShapeN X Y).IsEquilibriumIn h k σ ↔
      (compileAction Y k).IsNash (realize h σ) := by
  rw [isEquilibriumIn_iff_isNashPure]
  exact NFG.IsNashPure_iff_kernelGame (actionNFG Y k) (realize h σ)

/-- Simultaneous-shape equilibrium depends on a contingent strategy only
through its action profile at the current history. -/
theorem equilibrium_congr_realize
    (h : ∀ i, X i) (k : (∀ i, Y i) → (∀ _i : ι, ℝ))
    {σ τ : ∀ i, X i → Y i} (hst : realize h σ = realize h τ) :
    (ShapeN X Y).IsEquilibriumIn h k σ ↔
      (ShapeN X Y).IsEquilibriumIn h k τ := by
  change (∀ i (y : Y i),
      k (Function.update (realize h σ) i y) i ≤ k (realize h σ) i) ↔
    ∀ i (y : Y i),
      k (Function.update (realize h τ) i y) i ≤ k (realize h τ) i
  rw [hst]

/-- Closed simultaneous contingent strategies are equivalent to action
profiles; the only history available at each decision is `Unit`. -/
def closedStrategyEquiv (A : ι → Type) :
    (∀ i, Unit → A i) ≃ (∀ i, A i) where
  toFun σ i := σ i ()
  invFun a _ _ := a _
  left_inv σ := by
    funext i u
    cases u
    rfl
  right_inv _ := rfl

/-- A Bool-indexed dependent function is equivalently a binary product. -/
def boolPiEquiv (T : Bool → Type*) : (∀ i, T i) ≃ T false × T true where
  toFun f := (f false, f true)
  invFun p
    | false => p.1
    | true => p.2
  left_inv f := by
    funext i
    cases i <;> rfl
  right_inv _ := rfl

@[simp]
theorem boolPiEquiv_apply (T : Bool → Type*) (f : ∀ i, T i) :
    boolPiEquiv T f = (f false, f true) := rfl

@[simp]
theorem boolPiEquiv_apply_fst (T : Bool → Type*) (f : ∀ i, T i) :
    (boolPiEquiv T f).1 = f false := rfl

@[simp]
theorem boolPiEquiv_apply_snd (T : Bool → Type*) (f : ∀ i, T i) :
    (boolPiEquiv T f).2 = f true := rfl

@[simp]
theorem boolPiEquiv_symm_apply_false (T : Bool → Type*)
    (p : T false × T true) :
    (boolPiEquiv T).symm p false = p.1 := rfl

@[simp]
theorem boolPiEquiv_symm_apply_true (T : Bool → Type*)
    (p : T false × T true) :
    (boolPiEquiv T).symm p true = p.2 := rfl

/-- For two players, the direct Π-shaped simultaneous game is isomorphic to
the tensor of its two decisions.  This quarantines all product reindexing at
the boundary between the clean aggregate representation and the calculus. -/
def boolTensorIso (X Y : Bool → Type) :
    OpenGameIso (ShapeN X Y)
      (OpenGame.decision (X false) (Y false) ⊗ₒ
        OpenGame.decision (X true) (Y true)) where
  eX := boolPiEquiv X
  eS := boolPiEquiv fun _i => Unit
  eY := boolPiEquiv Y
  eR := boolPiEquiv fun _i => ℝ
  stratEquiv := boolPiEquiv fun i => X i → Y i
  play_preserved := by intro σ h; rfl
  coplay_preserved := by intro σ h r; rfl
  equilibrium_preserved := by
    intro h k σ
    change (∀ i, X i → Y i) at σ
    simp [ShapeN, OpenGame.tensor, OpenGame.decision, Function.update]
    rfl

/-- Nash recovery specialized to a closed simultaneous shape. -/
theorem closed_isEquilibriumIn_iff_isNash
    (k : (∀ i, Y i) → (∀ _i : ι, ℝ)) (σ : ∀ i, Unit → Y i) :
    (ShapeN (fun _i => Unit) Y).IsEquilibriumIn (fun _i => ()) k σ ↔
      (compileAction Y k).IsNash (closedStrategyEquiv Y σ) :=
  isEquilibriumIn_iff_isNash (fun _i => ()) k σ

end ShapeN

end OpenGames
