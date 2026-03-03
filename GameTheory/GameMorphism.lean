import GameTheory.SolutionConcepts
import Math.Probability

/-!
# Game Morphisms

Morphisms between kernel-based games: structure-preserving maps that
relate the strategic structure of different games.

A **game morphism** from `G` to `H` maps strategy profiles in `G` to
strategy profiles in `H` while preserving each player's utility ordering.
This captures when one game "embeds into" or "reduces to" another.

## Main definitions

* `KernelGame.Morphism` — a strategy-preserving map between games
* `KernelGame.StratEquiv` — a strategy bijection that preserves EU exactly

## Main results

* `KernelGame.Morphism.nash_of_nash` — morphisms pull back Nash equilibria
* `KernelGame.StratEquiv.nash_iff` — strategy equivalences reflect Nash
* `KernelGame.StratEquiv.dominant_iff` — strategy equivalences reflect dominance
-/

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type}

-- ============================================================================
-- Game morphisms (preserve utility ordering)
-- ============================================================================

open Classical in
/-- A morphism from game `G` to game `H`: per-player strategy maps that
    preserve utility comparisons under unilateral deviation.

    If `f` maps strategies of `G` into strategies of `H`, and player `who`
    weakly prefers `σ` over deviating to `s'` in `H`, then the same holds
    for the pre-image in `G`. -/
structure Morphism (G H : KernelGame ι) where
  /-- Per-player strategy map. -/
  stratMap : ∀ i, G.Strategy i → H.Strategy i
  /-- The map preserves EU: player utilities are the same in both games
      after mapping strategies. -/
  eu_preserved : ∀ (σ : Profile G) (who : ι),
    H.eu (fun i => stratMap i (σ i)) who = G.eu σ who

open Classical in
/-- Morphisms pull back Nash equilibria: if the image of `σ` is Nash in `H`,
    then `σ` is Nash in `G`. -/
theorem Morphism.nash_of_nash {G H : KernelGame ι} (f : Morphism G H)
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
-- Strategy equivalences (EU-preserving bijections)
-- ============================================================================

open Classical in
/-- A strategy equivalence between games `G` and `H`: per-player bijections
    on strategy spaces that preserve expected utility exactly.

    This is the natural notion of "same game up to relabeling strategies." -/
structure StratEquiv (G H : KernelGame ι) where
  /-- Per-player strategy bijection (forward). -/
  toFun : ∀ i, G.Strategy i → H.Strategy i
  /-- Per-player strategy bijection (inverse). -/
  invFun : ∀ i, H.Strategy i → G.Strategy i
  /-- Left inverse. -/
  left_inv : ∀ i s, invFun i (toFun i s) = s
  /-- Right inverse. -/
  right_inv : ∀ i s, toFun i (invFun i s) = s
  /-- EU is preserved under the bijection. -/
  eu_preserved : ∀ (σ : Profile G) (who : ι),
    H.eu (fun i => toFun i (σ i)) who = G.eu σ who

namespace StratEquiv

variable {G H : KernelGame ι}

/-- A strategy equivalence is a morphism. -/
def toMorphism (e : StratEquiv G H) : Morphism G H where
  stratMap := e.toFun
  eu_preserved := e.eu_preserved

/-- The inverse equivalence. -/
def symm (e : StratEquiv G H) : StratEquiv H G where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv
  eu_preserved := by
    intro σ who
    have h := e.eu_preserved (fun i => e.invFun i (σ i)) who
    simp only [e.right_inv] at h
    exact h.symm

open Classical in
/-- Strategy equivalences preserve Nash equilibria in both directions. -/
theorem nash_iff (e : StratEquiv G H) (σ : Profile G) :
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
  · exact e.toMorphism.nash_of_nash

open Classical in
/-- Strategy equivalences preserve dominance. -/
theorem dominant_iff (e : StratEquiv G H) (who : ι) (s : G.Strategy who) :
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

end StratEquiv

end KernelGame

end GameTheory
