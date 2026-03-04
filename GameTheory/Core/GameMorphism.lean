import GameTheory.Concepts.SolutionConcepts
import Math.Probability

/-!
# Game Morphisms

Morphisms between kernel-based games: structure-preserving maps that relate the
strategic structure of different games.

This file is distribution-first:
- morphisms preserve utility distributions (`udist`) under profile mapping;
- EU-based corollaries (Nash, dominance) are stated with explicit EU-compatibility
  assumptions, since those concepts are genuinely EU-functional.

## Main definitions

* `KernelGame.Morphism` -- strategy map preserving `udist`
* `KernelGame.StratEquiv` -- strategy bijection preserving `udist`
* `KernelGame.EUMorphism` -- morphism with additional EU preservation
* `KernelGame.EUStratEquiv` -- strategy equivalence with additional EU preservation

## Main EU corollaries

* `KernelGame.EUMorphism.nash_of_nash`
* `KernelGame.EUStratEquiv.nash_iff`
* `KernelGame.EUStratEquiv.dominant_iff`
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

/-- `udist` preservation implies per-player utility-distribution preservation. -/
theorem Morphism.udistPlayer_preserved {G H : KernelGame ι} (f : Morphism G H)
    (σ : Profile G) (who : ι) :
    H.udistPlayer (fun i => f.stratMap i (σ i)) who = G.udistPlayer σ who := by
  have h :=
    congrArg (fun d : PMF (Payoff ι) => d.bind (fun u => PMF.pure (u who))) (f.udist_preserved σ)
  simpa [KernelGame.udistPlayer_eq_udist_bind] using h

end KernelGame

namespace KernelGame

variable {ι : Type}

-- ============================================================================
-- EU-specialized morphisms
-- ============================================================================

/-- A morphism that additionally preserves expected utility values. -/
structure EUMorphism (G H : KernelGame ι) extends Morphism G H where
  /-- Expected-utility preservation under mapped profiles. -/
  eu_preserved : ∀ (σ : Profile G) (who : ι),
    H.eu (fun i => stratMap i (σ i)) who = G.eu σ who

open Classical in
/-- EU corollary: if a morphism also preserves EU values, Nash pulls back. -/
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
-- Strategy equivalences (distribution-preserving bijections)
-- ============================================================================

/-- A strategy equivalence between games `G` and `H`: per-player bijections on
    strategy spaces preserving joint utility distribution exactly. -/
structure StratEquiv (G H : KernelGame ι) where
  /-- Per-player strategy bijection (forward). -/
  toFun : ∀ i, G.Strategy i → H.Strategy i
  /-- Per-player strategy bijection (inverse). -/
  invFun : ∀ i, H.Strategy i → G.Strategy i
  /-- Left inverse. -/
  left_inv : ∀ i s, invFun i (toFun i s) = s
  /-- Right inverse. -/
  right_inv : ∀ i s, toFun i (invFun i s) = s
  /-- Utility-distribution preservation under the bijection. -/
  udist_preserved : ∀ (σ : Profile G),
    H.udist (fun i => toFun i (σ i)) = G.udist σ

/-- A strategy equivalence with additional EU preservation. -/
structure EUStratEquiv (G H : KernelGame ι) extends StratEquiv G H where
  /-- Expected-utility preservation under the bijection. -/
  eu_preserved : ∀ (σ : Profile G) (who : ι),
    H.eu (fun i => toFun i (σ i)) who = G.eu σ who

namespace StratEquiv

variable {G H : KernelGame ι}

/-- A strategy equivalence is a morphism. -/
def toMorphism (e : StratEquiv G H) : Morphism G H where
  stratMap := e.toFun
  udist_preserved := e.udist_preserved

/-- The inverse equivalence. -/
def symm (e : StratEquiv G H) : StratEquiv H G where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv
  udist_preserved := by
    intro σ
    have h := e.udist_preserved (fun i => e.invFun i (σ i))
    simpa [e.right_inv] using h.symm

end StratEquiv

namespace EUStratEquiv

variable {G H : KernelGame ι}

/-- Forgetting EU preservation yields a distribution-preserving strategy equivalence. -/
def toBase (e : EUStratEquiv G H) : StratEquiv G H :=
  { toFun := e.toFun
    invFun := e.invFun
    left_inv := e.left_inv
    right_inv := e.right_inv
    udist_preserved := e.udist_preserved }

/-- A EU-preserving strategy equivalence induces a EU-preserving morphism. -/
def toEUMorphism (e : EUStratEquiv G H) : EUMorphism G H where
  stratMap := e.toFun
  udist_preserved := e.udist_preserved
  eu_preserved := e.eu_preserved

/-- Inverse EU-preserving strategy equivalence. -/
def symm (e : EUStratEquiv G H) : EUStratEquiv H G where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv
  udist_preserved := by
    intro σ
    have h := e.udist_preserved (fun i => e.invFun i (σ i))
    simpa [e.right_inv] using h.symm
  eu_preserved := by
    intro σ who
    have h := e.eu_preserved (fun i => e.invFun i (σ i)) who
    simpa [e.right_inv] using h.symm

open Classical in
/-- EU corollary: if a strategy equivalence also preserves EU values, Nash is
    preserved in both directions. -/
theorem nash_iff (e : EUStratEquiv G H)
    (σ : Profile G) :
    G.IsNash σ ↔ H.IsNash (fun i => e.toFun i (σ i)) := by
  constructor
  · intro hN who s'
    suffices H.eu (Function.update (fun i => e.toFun i (σ i)) who s') who =
        H.eu (fun i => e.toFun i (Function.update σ who (e.invFun who s') i)) who by
      have h := hN who (e.invFun who s')
      have h1 := e.eu_preserved σ who
      have h2 := e.eu_preserved (Function.update σ who (e.invFun who s')) who
      linarith
    congr 2
    funext j
    simpa [e.right_inv] using
      (Function.apply_update
        (f := e.toFun) (g := σ) (i := who) (v := e.invFun who s') (j := j)).symm
  · exact e.toEUMorphism.nash_of_nash

open Classical in
/-- EU corollary: if a strategy equivalence also preserves EU values, dominance
    is preserved in both directions. -/
theorem dominant_iff (e : EUStratEquiv G H)
    (who : ι) (s : G.Strategy who) :
    G.IsDominant who s ↔ H.IsDominant who (e.toFun who s) := by
  constructor
  · intro hdom σ s'
    set τ := fun i => e.invFun i (σ i) with hτ
    have key1 : Function.update σ who (e.toFun who s) =
        fun i => e.toFun i (Function.update τ who s i) := by
      funext j
      simpa [hτ, e.right_inv] using
        (Function.apply_update (f := e.toFun) (g := τ) (i := who) (v := s) (j := j)).symm
    have key2 : Function.update σ who s' =
        fun i => e.toFun i (Function.update τ who (e.invFun who s') i) := by
      funext j
      simpa [hτ, e.right_inv] using
        (Function.apply_update
          (f := e.toFun) (g := τ) (i := who) (v := e.invFun who s') (j := j)).symm
    rw [key1, key2]
    have h1 := e.eu_preserved (Function.update τ who s) who
    have h2 := e.eu_preserved (Function.update τ who (e.invFun who s')) who
    linarith [hdom τ (e.invFun who s')]
  · intro hdom σ s'
    have h := hdom (fun i => e.toFun i (σ i)) (e.toFun who s')
    have h1 := e.eu_preserved (Function.update σ who s) who
    have h2 := e.eu_preserved (Function.update σ who s') who
    have hmap_s :
        (fun i => e.toFun i (Function.update σ who s i)) =
          Function.update (fun i => e.toFun i (σ i)) who (e.toFun who s) := by
      funext j
      simpa using (Function.apply_update (f := e.toFun) (g := σ) (i := who) (v := s) (j := j))
    have hmap_s' :
        (fun i => e.toFun i (Function.update σ who s' i)) =
          Function.update (fun i => e.toFun i (σ i)) who (e.toFun who s') := by
      funext j
      simpa using (Function.apply_update (f := e.toFun) (g := σ) (i := who) (v := s') (j := j))
    rw [hmap_s] at h1
    rw [hmap_s'] at h2
    linarith

end EUStratEquiv

end KernelGame

end GameTheory
