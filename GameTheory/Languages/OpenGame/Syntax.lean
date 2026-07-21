/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod

/-!
# Deterministic Open Games

This file defines the deterministic open-game calculus.  An open game from
`(X, S)` to `(Y, R)` has a forward play map, a backward coplay map, and an
equilibrium predicate indexed by a history `x : X` and continuation
`k : Y → R`.

The backward values `S` and `R` are called **cooutcomes** here.  They are often
called *coutilities* in the open-games literature, but need not be utilities.
The literature's established name `coplay` is retained for the map propagating
a cooutcome backwards.

The calculus is intentionally independent of category-theory infrastructure:
composition laws are witnessed by `OpenGameIso`, using ordinary `Equiv`s for
boundaries and strategies.
-/

namespace OpenGames

/-- A deterministic open game from boundary `(X, S)` to boundary `(Y, R)`.

`R` and `S` are backward-flowing cooutcomes (often called *coutilities*).
The equilibrium predicate is carried as data, as is standard for open games. -/
structure OpenGame (X S Y R : Type*) where
  /-- Strategy witnesses internal to the component. -/
  Strategy : Type*
  /-- Forward behavior of the component. -/
  play : Strategy → X → Y
  /-- Backward propagation of a cooutcome (called coplay in the literature). -/
  coplay : Strategy → X → R → S
  /-- Strategies selected by a history and continuation. -/
  IsEquilibriumIn : X → (Y → R) → Strategy → Prop

/-- A deterministic context: a history paired with a continuation. -/
abbrev Context (X Y R : Type*) := X × (Y → R)

namespace OpenGame

variable {X S Y R Z Q W T : Type*}

/-- Evaluate the equilibrium predicate on a bundled context. -/
def IsEquilibriumAt (g : OpenGame X S Y R) (c : Context X Y R)
    (σ : g.Strategy) : Prop :=
  g.IsEquilibriumIn c.1 c.2 σ

/-- Sequential composition.  The continuation seen by the first component is
computed by playing and coplaying the second component. -/
def seq (g : OpenGame X S Y R) (h : OpenGame Y R Z Q) :
    OpenGame X S Z Q where
  Strategy := g.Strategy × h.Strategy
  play σ x := h.play σ.2 (g.play σ.1 x)
  coplay σ x q := g.coplay σ.1 x (h.coplay σ.2 (g.play σ.1 x) q)
  IsEquilibriumIn x k σ :=
    g.IsEquilibriumIn x
        (fun y => h.coplay σ.2 y (k (h.play σ.2 y))) σ.1 ∧
      h.IsEquilibriumIn (g.play σ.1 x) k σ.2

/-- Parallel (monoidal) composition.  Each component sees the other
component's realized play through the joint continuation. -/
def tensor {X' S' Y' R' : Type*}
    (g : OpenGame X S Y R) (h : OpenGame X' S' Y' R') :
    OpenGame (X × X') (S × S') (Y × Y') (R × R') where
  Strategy := g.Strategy × h.Strategy
  play σ x := (g.play σ.1 x.1, h.play σ.2 x.2)
  coplay σ x r := (g.coplay σ.1 x.1 r.1, h.coplay σ.2 x.2 r.2)
  IsEquilibriumIn x k σ :=
    g.IsEquilibriumIn x.1
        (fun y => (k (y, h.play σ.2 x.2)).1) σ.1 ∧
      h.IsEquilibriumIn x.2
        (fun y' => (k (g.play σ.1 x.1, y')).2) σ.2

end OpenGame

scoped[OpenGames] infixr:90 " ;ₒ " => OpenGame.seq
scoped[OpenGames] infixr:88 " ⊗ₒ " => OpenGame.tensor

/-! ## Strategically trivial lenses and atomic games -/

/-- A pure lens between open-game boundaries.  Its backward map propagates a
cooutcome (the value called *coutility* in much of the literature). -/
structure Lens (X S Y R : Type*) where
  /-- Forward observation. -/
  view : X → Y
  /-- Backward cooutcome update. -/
  update : X → R → S

namespace Lens

variable {X S Y R : Type*}

/-- Regard a pure lens as a strategically trivial open game. -/
def toOpenGame (l : Lens X S Y R) : OpenGame X S Y R where
  Strategy := Unit
  play _ := l.view
  coplay _ := l.update
  IsEquilibriumIn _ _ _ := True

end Lens

namespace OpenGame

variable {X S Y R : Type*}

/-- Lift forward and backward wiring maps to a strategically trivial game. -/
def ofLens (view : X → Y) (update : X → R → S) : OpenGame X S Y R :=
  (Lens.mk view update).toOpenGame

/-- Identity wiring. -/
def idWire (X S : Type*) : OpenGame X S X S :=
  ofLens id fun _ s => s

/-- Swap two parallel wires. -/
def swapWire (X X' S S' : Type*) :
    OpenGame (X × X') (S × S') (X' × X) (S' × S) :=
  ofLens Prod.swap fun _ s => s.swap

/-- Reassociate three parallel wires to the right. -/
def assocWire (X X' X'' S S' S'' : Type*) :
    OpenGame ((X × X') × X'') ((S × S') × S'')
      (X × (X' × X'')) (S × (S' × S'')) :=
  ofLens (fun x => (x.1.1, x.1.2, x.2))
    fun _ s => ((s.1, s.2.1), s.2.2)

/-- Reassociate three parallel wires to the left. -/
def unassocWire (X X' X'' S S' S'' : Type*) :
    OpenGame (X × (X' × X'')) (S × (S' × S''))
      ((X × X') × X'') ((S × S') × S'') :=
  ofLens (fun x => ((x.1, x.2.1), x.2.2))
    fun _ s => (s.1.1, s.1.2, s.2)

/-- Copy a forward value while routing one cooutcome backwards. -/
def copyWire (X R : Type*) : OpenGame X R (X × X) (R × Unit) :=
  ofLens (fun x => (x, x)) fun _ r => r.1

/-- Project the first forward wire and discard the second backward wire. -/
def fstWire (X X' R : Type*) : OpenGame (X × X') (R × Unit) X R :=
  ofLens Prod.fst fun _ r => (r, ())

/-- Project the second forward wire and discard the first backward wire. -/
def sndWire (X X' R : Type*) : OpenGame (X × X') (Unit × R) X' R :=
  ofLens Prod.snd fun _ r => ((), r)

/-- A decision observing `X` and choosing `Y`, evaluated by a real-valued
continuation.  Its strategies are contingent plans `X → Y`. -/
def decision (X Y : Type*) : OpenGame X Unit Y ℝ where
  Strategy := X → Y
  play σ x := σ x
  coplay _ _ _ := ()
  IsEquilibriumIn x k σ := ∀ y, k (σ x) ≥ k y

/-- Close an output with a cooutcome-producing function.  In utility examples
this is the utility costate; generically it may deliver any cooutcome. -/
def costate (c : Y → R) : OpenGame Y R Unit Unit where
  Strategy := Unit
  play _ _ := ()
  coplay _ y _ := c y
  IsEquilibriumIn _ _ _ := True

end OpenGame

/-! ## Isomorphisms -/

/-- Isomorphism of open games, including boundary relabelings.

The cooutcome boundaries are contravariant in the coplay equation. -/
structure OpenGameIso
    {X S Y R X' S' Y' R' : Type*}
    (g : OpenGame X S Y R) (g' : OpenGame X' S' Y' R') where
  eX : X ≃ X'
  eS : S ≃ S'
  eY : Y ≃ Y'
  eR : R ≃ R'
  stratEquiv : g.Strategy ≃ g'.Strategy
  play_preserved : ∀ σ x,
    g'.play (stratEquiv σ) (eX x) = eY (g.play σ x)
  coplay_preserved : ∀ σ x r',
    g'.coplay (stratEquiv σ) (eX x) r' =
      eS (g.coplay σ x (eR.symm r'))
  equilibrium_preserved : ∀ x k' σ,
    g'.IsEquilibriumIn (eX x) k' (stratEquiv σ) ↔
      g.IsEquilibriumIn x (fun y => eR.symm (k' (eY y))) σ

namespace OpenGameIso

variable {X S Y R Z Q W T : Type*}
variable {g : OpenGame X S Y R} {g' : OpenGame X S Y R}

/-- Concrete left-unit equivalence used by the coherence witnesses. -/
def unitProdEquiv (A : Type*) : Unit × A ≃ A where
  toFun x := x.2
  invFun a := ((), a)
  left_inv := by rintro ⟨u, a⟩; cases u; rfl
  right_inv _ := rfl

/-- Concrete right-unit equivalence used by the coherence witnesses. -/
def prodUnitEquiv (A : Type*) : A × Unit ≃ A where
  toFun x := x.1
  invFun a := (a, ())
  left_inv := by rintro ⟨a, u⟩; cases u; rfl
  right_inv _ := rfl

/-- Concrete product reassociation used by the coherence witnesses. -/
def prodAssocEquiv (A B C : Type*) : (A × B) × C ≃ A × (B × C) where
  toFun x := (x.1.1, x.1.2, x.2)
  invFun x := ((x.1, x.2.1), x.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem unitProdEquiv_apply (A : Type*) (x : Unit × A) :
    unitProdEquiv A x = x.2 := rfl

@[simp]
theorem unitProdEquiv_symm_apply (A : Type*) (x : A) :
    (unitProdEquiv A).symm x = ((), x) := rfl

@[simp]
theorem prodUnitEquiv_apply (A : Type*) (x : A × Unit) :
    prodUnitEquiv A x = x.1 := rfl

@[simp]
theorem prodUnitEquiv_symm_apply (A : Type*) (x : A) :
    (prodUnitEquiv A).symm x = (x, ()) := rfl

/-- Construct an isomorphism when only the strategy presentation changes. -/
def ofStrat (e : g.Strategy ≃ g'.Strategy)
    (hplay : ∀ σ x, g'.play (e σ) x = g.play σ x)
    (hcoplay : ∀ σ x r, g'.coplay (e σ) x r = g.coplay σ x r)
    (heq : ∀ x k σ,
      g'.IsEquilibriumIn x k (e σ) ↔ g.IsEquilibriumIn x k σ) :
    OpenGameIso g g' where
  eX := Equiv.refl _
  eS := Equiv.refl _
  eY := Equiv.refl _
  eR := Equiv.refl _
  stratEquiv := e
  play_preserved := hplay
  coplay_preserved := hcoplay
  equilibrium_preserved := heq

/-- Reflexivity of open-game isomorphism. -/
def refl (g : OpenGame X S Y R) : OpenGameIso g g :=
  ofStrat (Equiv.refl _) (fun _ _ => rfl) (fun _ _ _ => rfl)
    fun _ _ _ => Iff.rfl

/-- Symmetry of open-game isomorphism. -/
def symm
    {X' S' Y' R' : Type*}
    {g : OpenGame X S Y R} {g' : OpenGame X' S' Y' R'}
    (e : OpenGameIso g g') : OpenGameIso g' g where
  eX := e.eX.symm
  eS := e.eS.symm
  eY := e.eY.symm
  eR := e.eR.symm
  stratEquiv := e.stratEquiv.symm
  play_preserved := by
    intro σ x
    have h := e.play_preserved (e.stratEquiv.symm σ) (e.eX.symm x)
    simpa using (congrArg e.eY.symm h).symm
  coplay_preserved := by
    intro σ x r
    have h := e.coplay_preserved (e.stratEquiv.symm σ) (e.eX.symm x) (e.eR r)
    simpa using (congrArg e.eS.symm h).symm
  equilibrium_preserved := by
    intro x k σ
    simpa using (e.equilibrium_preserved (e.eX.symm x)
      (fun y => e.eR (k (e.eY.symm y))) (e.stratEquiv.symm σ)).symm

/-- Transitivity of open-game isomorphism. -/
def trans
    {X' S' Y' R' X'' S'' Y'' R'' : Type*}
    {g : OpenGame X S Y R} {g' : OpenGame X' S' Y' R'}
    {g'' : OpenGame X'' S'' Y'' R''}
    (e : OpenGameIso g g') (f : OpenGameIso g' g'') : OpenGameIso g g'' where
  eX := e.eX.trans f.eX
  eS := e.eS.trans f.eS
  eY := e.eY.trans f.eY
  eR := e.eR.trans f.eR
  stratEquiv := e.stratEquiv.trans f.stratEquiv
  play_preserved := by
    intro σ x
    calc
      g''.play (f.stratEquiv (e.stratEquiv σ)) (f.eX (e.eX x))
          = f.eY (g'.play (e.stratEquiv σ) (e.eX x)) :=
            f.play_preserved (e.stratEquiv σ) (e.eX x)
      _ = f.eY (e.eY (g.play σ x)) := congrArg f.eY (e.play_preserved σ x)
  coplay_preserved := by
    intro σ x r
    calc
      g''.coplay (f.stratEquiv (e.stratEquiv σ)) (f.eX (e.eX x)) r
          = f.eS (g'.coplay (e.stratEquiv σ) (e.eX x) (f.eR.symm r)) :=
            f.coplay_preserved (e.stratEquiv σ) (e.eX x) r
      _ = f.eS (e.eS (g.coplay σ x (e.eR.symm (f.eR.symm r)))) :=
            congrArg f.eS (e.coplay_preserved σ x (f.eR.symm r))
  equilibrium_preserved := by
    intro x k σ
    exact (f.equilibrium_preserved (e.eX x) k (e.stratEquiv σ)).trans
      (e.equilibrium_preserved x (fun y => f.eR.symm (k (f.eY y))) σ)

/-- Left identity for sequential composition. -/
def seqIdLeft (g : OpenGame X S Y R) :
    OpenGameIso (OpenGame.idWire X S ;ₒ g) g :=
  ofStrat (unitProdEquiv g.Strategy)
    (by rintro ⟨⟨⟩, σ⟩ x; rfl)
    (by rintro ⟨⟨⟩, σ⟩ x r; rfl)
    (by
      rintro x k ⟨⟨⟩, σ⟩
      change g.IsEquilibriumIn x k (unitProdEquiv g.Strategy ((), σ)) ↔
        True ∧ g.IsEquilibriumIn x k σ
      rw [unitProdEquiv_apply]
      simp only [true_and])

/-- Right identity for sequential composition. -/
def seqIdRight (g : OpenGame X S Y R) :
    OpenGameIso (g ;ₒ OpenGame.idWire Y R) g :=
  ofStrat (prodUnitEquiv g.Strategy)
    (by rintro ⟨σ, ⟨⟩⟩ x; rfl)
    (by rintro ⟨σ, ⟨⟩⟩ x r; rfl)
    (by
      rintro x k ⟨σ, ⟨⟩⟩
      change g.IsEquilibriumIn x k (prodUnitEquiv g.Strategy (σ, ())) ↔
        g.IsEquilibriumIn x k σ ∧ True
      rw [prodUnitEquiv_apply]
      simp only [and_true])

/-- Associativity of sequential composition, up to strategy reassociation. -/
def seqAssoc (g : OpenGame X S Y R) (h : OpenGame Y R Z Q)
    (k : OpenGame Z Q W T) :
    OpenGameIso ((g ;ₒ h) ;ₒ k) (g ;ₒ (h ;ₒ k)) :=
  ofStrat (prodAssocEquiv g.Strategy h.Strategy k.Strategy)
    (by rintro ⟨⟨σ, τ⟩, υ⟩ x; rfl)
    (by rintro ⟨⟨σ, τ⟩, υ⟩ x r; rfl)
    (by
      rintro x c ⟨⟨σ, τ⟩, υ⟩
      dsimp [OpenGame.seq, prodAssocEquiv]
      exact and_assoc.symm)

/-- Associativity of tensor, including all four boundary reassociations. -/
def tensorAssoc {X' S' Y' R' X'' S'' Y'' R'' : Type*}
    (g : OpenGame X S Y R) (h : OpenGame X' S' Y' R')
    (k : OpenGame X'' S'' Y'' R'') :
    OpenGameIso ((g ⊗ₒ h) ⊗ₒ k) (g ⊗ₒ (h ⊗ₒ k)) where
  eX := prodAssocEquiv _ _ _
  eS := prodAssocEquiv _ _ _
  eY := prodAssocEquiv _ _ _
  eR := prodAssocEquiv _ _ _
  stratEquiv := prodAssocEquiv _ _ _
  play_preserved := by rintro ⟨⟨σ, τ⟩, υ⟩ ⟨⟨x, x'⟩, x''⟩; rfl
  coplay_preserved := by
    rintro ⟨⟨σ, τ⟩, υ⟩ ⟨⟨x, x'⟩, x''⟩ ⟨r, r', r''⟩
    rfl
  equilibrium_preserved := by
    rintro ⟨⟨x, x'⟩, x''⟩ c ⟨⟨σ, τ⟩, υ⟩
    dsimp [OpenGame.tensor, prodAssocEquiv]
    exact and_assoc.symm

/-- The tensor unit is a left unitor. -/
def tensorUnitLeft (g : OpenGame X S Y R) :
    OpenGameIso (OpenGame.idWire Unit Unit ⊗ₒ g) g where
  eX := unitProdEquiv X
  eS := unitProdEquiv S
  eY := unitProdEquiv Y
  eR := unitProdEquiv R
  stratEquiv := unitProdEquiv g.Strategy
  play_preserved := by rintro ⟨⟨⟩, σ⟩ ⟨⟨⟩, x⟩; rfl
  coplay_preserved := by rintro ⟨⟨⟩, σ⟩ ⟨⟨⟩, x⟩ r; rfl
  equilibrium_preserved := by
    rintro ⟨⟨⟩, x⟩ k ⟨⟨⟩, σ⟩
    change g.IsEquilibriumIn x k (unitProdEquiv g.Strategy ((), σ)) ↔
      True ∧ g.IsEquilibriumIn x k σ
    rw [unitProdEquiv_apply]
    simp only [true_and]

/-- The tensor unit is a right unitor. -/
def tensorUnitRight (g : OpenGame X S Y R) :
    OpenGameIso (g ⊗ₒ OpenGame.idWire Unit Unit) g where
  eX := prodUnitEquiv X
  eS := prodUnitEquiv S
  eY := prodUnitEquiv Y
  eR := prodUnitEquiv R
  stratEquiv := prodUnitEquiv g.Strategy
  play_preserved := by rintro ⟨σ, ⟨⟩⟩ ⟨x, ⟨⟩⟩; rfl
  coplay_preserved := by rintro ⟨σ, ⟨⟩⟩ ⟨x, ⟨⟩⟩ r; rfl
  equilibrium_preserved := by
    rintro ⟨x, ⟨⟩⟩ k ⟨σ, ⟨⟩⟩
    change g.IsEquilibriumIn x k (prodUnitEquiv g.Strategy (σ, ())) ↔
      g.IsEquilibriumIn x k σ ∧ True
    rw [prodUnitEquiv_apply]
    simp only [and_true]

/-- Tensor is symmetric up to swapping boundaries and strategies. -/
def tensorComm {X' S' Y' R' : Type*}
    (g : OpenGame X S Y R) (h : OpenGame X' S' Y' R') :
    OpenGameIso (g ⊗ₒ h) (h ⊗ₒ g) where
  eX := Equiv.prodComm _ _
  eS := Equiv.prodComm _ _
  eY := Equiv.prodComm _ _
  eR := Equiv.prodComm _ _
  stratEquiv := Equiv.prodComm _ _
  play_preserved := by rintro ⟨σ, τ⟩ ⟨x, x'⟩; rfl
  coplay_preserved := by rintro ⟨σ, τ⟩ ⟨x, x'⟩ ⟨r', r⟩; rfl
  equilibrium_preserved := by
    rintro ⟨x, x'⟩ k ⟨σ, τ⟩
    simp only [OpenGame.tensor]
    exact and_comm

/-- Sequential composition distributes over tensor (the interchange law). -/
def interchange
    {X' S' Y' R' Z' Q' : Type*}
    (g : OpenGame X S Y R) (h : OpenGame X' S' Y' R')
    (g' : OpenGame Y R Z Q) (h' : OpenGame Y' R' Z' Q') :
    OpenGameIso ((g ⊗ₒ h) ;ₒ (g' ⊗ₒ h'))
      ((g ;ₒ g') ⊗ₒ (h ;ₒ h')) :=
  ofStrat (Equiv.prodProdProdComm _ _ _ _)
    (by rintro ⟨⟨σ, τ⟩, ⟨σ', τ'⟩⟩ ⟨x, x'⟩; rfl)
    (by rintro ⟨⟨σ, τ⟩, ⟨σ', τ'⟩⟩ ⟨x, x'⟩ ⟨q, q'⟩; rfl)
    (by
      rintro ⟨x, x'⟩ c ⟨⟨σ, τ⟩, ⟨σ', τ'⟩⟩
      simp only [OpenGame.seq, OpenGame.tensor]
      aesop)

end OpenGameIso

end OpenGames
