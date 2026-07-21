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

/-! ## Two-stage sequential shapes -/

/-- The direct two-stage sequential shape with one decision per player.

The follower chooses a contingent plan `A → B`, but plain open-game
composition checks that plan only at the leader's realized action. -/
def ShapeS (A B : Type) : OpenGame Unit Unit (A × B) (ℝ × ℝ) where
  Strategy := A × (A → B)
  play σ _ := (σ.1, σ.2 σ.1)
  coplay _ _ _ := ()
  IsEquilibriumIn _ k σ :=
    (∀ a, (k (a, σ.2 a)).1 ≤ (k (σ.1, σ.2 σ.1)).1) ∧
    (∀ b, (k (σ.1, b)).2 ≤ (k (σ.1, σ.2 σ.1)).2)

namespace ShapeS

open scoped OpenGames

/-- The two-stage shape expressed entirely in the core wiring calculus. -/
def wiring (A B : Type) : OpenGame Unit Unit (A × B) (ℝ × ℝ) :=
  OpenGame.decision Unit A ;ₒ
    OpenGame.copyWire A ℝ ;ₒ
    (OpenGame.idWire A ℝ ⊗ₒ OpenGame.decision A B)

/-- Remove the strategically trivial witnesses introduced by `wiring`. -/
def wiringStrategyEquiv (A B : Type) :
    (A × (A → B)) ≃ (wiring A B).Strategy where
  toFun σ := (fun _u => σ.1, ((), ((), σ.2)))
  invFun σ := (σ.1 (), σ.2.2.2)
  left_inv _ := rfl
  right_inv σ := by
    rcases σ with ⟨first, u, v, second⟩
    cases u
    cases v
    congr

/-- The direct two-stage representation is isomorphic to its typed wiring
diagram. -/
def wiringIso (A B : Type) : OpenGameIso (ShapeS A B) (wiring A B) :=
  OpenGameIso.ofStrat (wiringStrategyEquiv A B)
    (by rintro σ ⟨⟩; rfl)
    (by rintro σ ⟨⟩ r; rfl)
    (by
      rintro ⟨⟩ k σ
      simp [wiring, wiringStrategyEquiv, ShapeS, OpenGame.seq,
        OpenGame.tensor, OpenGame.decision, OpenGame.copyWire,
        OpenGame.idWire, OpenGame.ofLens, Lens.toOpenGame]
      rfl)

/-- Strategic-form strategy family for the two players. -/
def PlayerStrategy (A B : Type) : Bool → Type
  | false => A
  | true => A → B

/-- Translate the direct pair presentation into a player-indexed profile. -/
def toProfile {A B : Type} (σ : A × (A → B)) :
    ∀ i, PlayerStrategy A B i
  | false => σ.1
  | true => σ.2

/-- Translate a player-indexed sequential profile back to a pair. -/
def ofProfile {A B : Type} (σ : ∀ i, PlayerStrategy A B i) :
    A × (A → B) :=
  (σ false, σ true)

/-- Pair and player-indexed presentations of sequential strategies agree. -/
def profileEquiv (A B : Type) :
    (A × (A → B)) ≃ (∀ i, PlayerStrategy A B i) where
  toFun := toProfile
  invFun := ofProfile
  left_inv _ := rfl
  right_inv σ := by
    funext i
    cases i <;> rfl

/-- Convert a utility pair into the Bool-indexed payoff convention. -/
def pairUtility {A B : Type} (k : A × B → ℝ × ℝ)
    (outcome : A × B) (i : Bool) : ℝ :=
  if i then (k outcome).2 else (k outcome).1

/-- Strategic-form NFG for the two-stage shape. -/
def actionNFG (A B : Type) (k : A × B → ℝ × ℝ) :
    NFG.NFGGame Bool (PlayerStrategy A B) where
  Outcome := A × B
  outcome σ := (σ false, σ true (σ false))
  utility := pairUtility k

/-- Compile a two-stage shape for a closing continuation. -/
noncomputable def compileAction (A B : Type) (k : A × B → ℝ × ℝ) :
    GameTheory.KernelGame Bool :=
  (actionNFG A B k).toKernelGame

/-- Plain sequential equilibrium is exactly Nash equilibrium in the strategic
form with a contingent follower plan. -/
theorem isEquilibriumIn_iff_isNashPure {A B : Type}
    (k : A × B → ℝ × ℝ) (σ : A × (A → B)) :
    (ShapeS A B).IsEquilibriumIn () k σ ↔
      NFG.IsNashPure (actionNFG A B k) (toProfile σ) := by
  constructor
  · rintro ⟨hleader, hfollower⟩ i deviation
    cases i with
    | false =>
        simpa [NFG.IsNashPure, actionNFG, pairUtility, NFG.deviate,
          toProfile, Function.update] using hleader deviation
    | true =>
        simpa [NFG.IsNashPure, actionNFG, pairUtility, NFG.deviate,
          toProfile, Function.update] using hfollower (deviation σ.1)
  · intro hn
    constructor
    · intro a
      simpa [NFG.IsNashPure, actionNFG, pairUtility, NFG.deviate,
        toProfile, Function.update] using hn false a
    · intro b
      let deviation : A → B := fun _a => b
      simpa [NFG.IsNashPure, actionNFG, pairUtility, NFG.deviate,
        toProfile, Function.update, deviation] using hn true deviation

/-- Kernel-level Nash recovery for a two-stage sequential shape. -/
theorem isEquilibriumIn_iff_isNash {A B : Type}
    (k : A × B → ℝ × ℝ) (σ : A × (A → B)) :
    (ShapeS A B).IsEquilibriumIn () k σ ↔
      (compileAction A B k).IsNash (toProfile σ) := by
  rw [isEquilibriumIn_iff_isNashPure]
  exact NFG.IsNashPure_iff_kernelGame (actionNFG A B k) (toProfile σ)

end ShapeS

end OpenGames
