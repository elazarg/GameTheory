/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Core.GameMorphism
import GameTheory.Concepts.SolutionConcepts

/-!
# Solution-Concept Corollaries for Game Morphisms

The morphism structures live in `GameTheory.Core.GameMorphism`. This file adds
Nash and dominance transport theorems, which depend on solution concepts.
-/

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type}

/-- EU corollary: if a morphism preserves EU values, Nash pulls back. -/
theorem EUMorphism.nash_of_nash [DecidableEq ι]
    {G H : KernelGame ι} (f : EUMorphism G H)
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

namespace EUGameIsomorphism

variable {G H : KernelGame ι}

/-- EU corollary: Nash is preserved in both directions. -/
theorem nash_iff [DecidableEq ι] (e : EUGameIsomorphism G H) (σ : Profile G) :
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
