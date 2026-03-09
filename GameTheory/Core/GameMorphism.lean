import GameTheory.Core.GameIsomorphism
import Math.Probability
import GameTheory.Concepts.SolutionConcepts

/-!
# Game Morphisms

Morphisms between kernel-based games: structure-preserving maps that relate the
strategic structure of different games.

This file is distribution-first:
- morphisms preserve utility distributions (`udist`) under profile mapping;
- EU-based corollaries (Nash, dominance) are stated in explicitly EU-specialized
  structures.

## Main definitions

* `KernelGame.Morphism` -- strategy map preserving `udist`
* `KernelGame.EUMorphism` -- morphism with additional EU preservation
* `KernelGame.EUGameIsomorphism` -- game isomorphism with additional EU preservation

## Main EU corollaries

* `KernelGame.EUMorphism.nash_of_nash`
* `KernelGame.EUGameIsomorphism.nash_iff`
* `KernelGame.EUGameIsomorphism.dominant_iff`
-/

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type}

-- ============================================================================
-- Game morphisms (distribution-preserving)
-- ============================================================================

/-- A morphism from game `G` to game `H`: per-player strategy maps that preserve
    the induced joint utility distribution. -/
structure Morphism (G H : KernelGame ι) where
  /-- Per-player strategy map. -/
  stratMap : ∀ i, G.Strategy i → H.Strategy i
  /-- Utility-distribution preservation under mapped profiles. -/
  udist_preserved : ∀ (σ : Profile G),
    H.udist (fun i => stratMap i (σ i)) = G.udist σ

namespace Morphism

/-- Identity morphism. -/
def id (G : KernelGame ι) : Morphism G G where
  stratMap := fun _i => _root_.id
  udist_preserved := by intro σ; rfl

/-- Composition of morphisms. -/
def comp {G H K : KernelGame ι} (g : Morphism H K) (f : Morphism G H) : Morphism G K where
  stratMap := fun i => g.stratMap i ∘ f.stratMap i
  udist_preserved := by
    intro σ
    let τ : Profile H := fun i => f.stratMap i (σ i)
    have hg : K.udist (fun i => g.stratMap i (τ i)) = H.udist τ := g.udist_preserved τ
    have hf : H.udist τ = G.udist σ := by simpa [τ] using f.udist_preserved σ
    simpa [τ, Function.comp] using hg.trans hf

@[simp] theorem id_comp {G H : KernelGame ι} (f : Morphism G H) :
    comp (id H) f = f := by
  cases f
  rfl

@[simp] theorem comp_id {G H : KernelGame ι} (f : Morphism G H) :
    comp f (id G) = f := by
  cases f
  rfl

theorem comp_assoc {G H K L : KernelGame ι}
    (h : Morphism K L) (g : Morphism H K) (f : Morphism G H) :
    comp h (comp g f) = comp (comp h g) f := by
  cases h; cases g; cases f
  rfl

end Morphism

/-- `udist` preservation implies per-player utility-distribution preservation. -/
theorem Morphism.udistPlayer_preserved {G H : KernelGame ι} (f : Morphism G H)
    (σ : Profile G) (who : ι) :
    H.udistPlayer (fun i => f.stratMap i (σ i)) who = G.udistPlayer σ who := by
  have h :=
    congrArg (fun d : PMF (Payoff ι) => d.bind (fun u => PMF.pure (u who))) (f.udist_preserved σ)
  simpa [KernelGame.udistPlayer_eq_udist_bind] using h

-- ============================================================================
-- EU-specialized morphisms
-- ============================================================================

/-- A morphism that additionally preserves expected utility values. -/
structure EUMorphism (G H : KernelGame ι) extends Morphism G H where
  /-- Expected-utility preservation under mapped profiles. -/
  eu_preserved : ∀ (σ : Profile G) (who : ι),
    H.eu (fun i => stratMap i (σ i)) who = G.eu σ who

namespace EUMorphism

/-- Identity EU morphism. -/
def id (G : KernelGame ι) : EUMorphism G G where
  toMorphism := Morphism.id G
  eu_preserved := by intro σ who; rfl

/-- Composition of EU morphisms. -/
def comp {G H K : KernelGame ι} (g : EUMorphism H K) (f : EUMorphism G H) : EUMorphism G K where
  toMorphism := Morphism.comp g.toMorphism f.toMorphism
  eu_preserved := by
    intro σ who
    let τ : Profile H := fun i => f.stratMap i (σ i)
    have hg : K.eu (fun i => g.stratMap i (τ i)) who = H.eu τ who := g.eu_preserved τ who
    have hf : H.eu τ who = G.eu σ who := by simpa [τ] using f.eu_preserved σ who
    simpa [τ, Function.comp] using hg.trans hf

@[simp] theorem id_comp {G H : KernelGame ι} (f : EUMorphism G H) :
    comp (id H) f = f := by
  cases f
  rfl

@[simp] theorem comp_id {G H : KernelGame ι} (f : EUMorphism G H) :
    comp f (id G) = f := by
  cases f
  rfl

theorem comp_assoc {G H K L : KernelGame ι}
    (h : EUMorphism K L) (g : EUMorphism H K) (f : EUMorphism G H) :
    comp h (comp g f) = comp (comp h g) f := by
  cases h; cases g; cases f
  rfl

end EUMorphism

open Classical in
/-- EU corollary: if a morphism preserves EU values, Nash pulls back. -/
theorem EUMorphism.nash_of_nash {G H : KernelGame ι} (f : EUMorphism G H)
    {σ : Profile G}
    (hN : H.IsNash (fun i => f.stratMap i (σ i))) :
    G.IsNash σ := by
  intro who s'
  have h := hN who (f.stratMap who s')
  have h1 := f.eu_preserved σ who
  have h2 : H.eu (Function.update (fun i => f.stratMap i (σ i)) who (f.stratMap who s')) who =
      G.eu (Function.update σ who s') who := by
    rw [← f.eu_preserved (Function.update σ who s') who]
    congr 2
    funext j
    simpa using
      (Function.apply_update
        (f := f.stratMap) (g := σ) (i := who) (v := s') (j := j)).symm
  linarith

-- ============================================================================
-- EU-specialized game isomorphisms
-- ============================================================================

/-- A game isomorphism with additional EU preservation. -/
structure EUGameIsomorphism (G H : KernelGame ι) extends GameIsomorphism G H where
  /-- Expected-utility preservation under the isomorphism. -/
  eu_preserved : ∀ (σ : Profile G) (who : ι),
    H.eu (fun i => stratEquiv i (σ i)) who = G.eu σ who

namespace EUGameIsomorphism

variable {G H : KernelGame ι}

/-- An EU-preserving game isomorphism induces an EU-preserving morphism. -/
def toEUMorphism (e : EUGameIsomorphism G H) : EUMorphism G H where
  stratMap := fun i => e.stratEquiv i
  udist_preserved := e.udist_preserved
  eu_preserved := e.eu_preserved

/-- Inverse EU-preserving game isomorphism. -/
def symm (e : EUGameIsomorphism G H) : EUGameIsomorphism H G where
  toGameIsomorphism := e.toGameIsomorphism.symm
  eu_preserved := by
    intro σ who
    have h := e.eu_preserved (fun i => (e.stratEquiv i).symm (σ i)) who
    simpa using h.symm

open Classical in
/-- EU corollary: Nash is preserved in both directions. -/
theorem nash_iff (e : EUGameIsomorphism G H) (σ : Profile G) :
    G.IsNash σ ↔ H.IsNash (fun i => e.stratEquiv i (σ i)) := by
  constructor
  · intro hN who s'
    suffices H.eu (Function.update (fun i => e.stratEquiv i (σ i)) who s') who =
        H.eu (fun i => e.stratEquiv i
          (Function.update σ who ((e.stratEquiv who).symm s') i)) who by
      have h := hN who ((e.stratEquiv who).symm s')
      have h1 := e.eu_preserved σ who
      have h2 := e.eu_preserved (Function.update σ who ((e.stratEquiv who).symm s')) who
      linarith
    congr 2
    funext j
    simpa using
      (Function.apply_update
        (f := fun i => e.stratEquiv i) (g := σ) (i := who)
        (v := (e.stratEquiv who).symm s') (j := j)).symm
  · exact e.toEUMorphism.nash_of_nash

open Classical in
/-- EU corollary: dominance is preserved in both directions. -/
theorem dominant_iff (e : EUGameIsomorphism G H)
    (who : ι) (s : G.Strategy who) :
    G.IsDominant who s ↔ H.IsDominant who (e.stratEquiv who s) := by
  constructor
  · intro hdom σ s'
    set τ := fun i => (e.stratEquiv i).symm (σ i) with hτ
    have key1 : Function.update σ who (e.stratEquiv who s) =
        fun i => e.stratEquiv i (Function.update τ who s i) := by
      funext j
      simpa [hτ] using
        (Function.apply_update (f := fun i => e.stratEquiv i) (g := τ)
          (i := who) (v := s) (j := j)).symm
    have key2 : Function.update σ who s' =
        fun i => e.stratEquiv i (Function.update τ who ((e.stratEquiv who).symm s') i) := by
      funext j
      simpa [hτ] using
        (Function.apply_update
          (f := fun i => e.stratEquiv i) (g := τ) (i := who)
          (v := (e.stratEquiv who).symm s') (j := j)).symm
    rw [key1, key2]
    have h1 := e.eu_preserved (Function.update τ who s) who
    have h2 := e.eu_preserved (Function.update τ who ((e.stratEquiv who).symm s')) who
    linarith [hdom τ ((e.stratEquiv who).symm s')]
  · intro hdom σ s'
    have h := hdom (fun i => e.stratEquiv i (σ i)) (e.stratEquiv who s')
    have h1 := e.eu_preserved (Function.update σ who s) who
    have h2 := e.eu_preserved (Function.update σ who s') who
    have hmap_s :
        (fun i => e.stratEquiv i (Function.update σ who s i)) =
          Function.update (fun i => e.stratEquiv i (σ i)) who (e.stratEquiv who s) := by
      funext j
      simpa using
        (Function.apply_update (f := fun i => e.stratEquiv i) (g := σ)
          (i := who) (v := s) (j := j))
    have hmap_s' :
        (fun i => e.stratEquiv i (Function.update σ who s' i)) =
          Function.update (fun i => e.stratEquiv i (σ i)) who (e.stratEquiv who s') := by
      funext j
      simpa using
        (Function.apply_update (f := fun i => e.stratEquiv i) (g := σ)
          (i := who) (v := s') (j := j))
    rw [hmap_s] at h1
    rw [hmap_s'] at h2
    linarith

end EUGameIsomorphism

end KernelGame

end GameTheory
