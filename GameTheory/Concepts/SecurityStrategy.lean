/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability
import GameTheory.Concepts.SolutionConcepts

/-!
# Security Strategies and Maximin Values

A player's security level (maximin value) is the best EU they can
guarantee regardless of opponents' play. A security (maximin) strategy
achieves this guarantee.

## Main definitions

* `worstCaseEUInf` — infimum EU over opponent profiles for a fixed strategy
* `securityLevelSup` — supremum over own strategies of `worstCaseEUInf`
* `worstCaseEU` — minimum EU over opponent profiles for a fixed strategy
* `securityLevel` — the max over own strategies of `worstCaseEU`

## Main results

* `nash_eu_ge_securityLevel` — Nash equilibrium EU ≥ security level
* `IsDominant.eu_ge_securityLevel` — a dominant strategy guarantees ≥ security level
-/

open scoped BigOperators

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type}

section Order

variable (G : KernelGame ι)

open Classical in
/-- Worst-case EU as an order-theoretic infimum over opponent profiles.

Unlike `worstCaseEU`, this definition does not enumerate the profile space.
Useful bounds require the displayed payoff range to be bounded below. -/
noncomputable def worstCaseEUInf (who : ι) (s : G.Strategy who) : ℝ :=
  ⨅ σ : Profile G, G.eu (Function.update σ who s) who

open Classical in
/-- Security level as an order-theoretic supremum over own strategies.

Unlike `securityLevel`, this definition does not enumerate the strategy space.
Upper-bound lemmas require the strategy range to be nonempty. Lower-bound
lemmas additionally require the displayed range to be bounded above. -/
noncomputable def securityLevelSup (who : ι) : ℝ :=
  ⨆ s : G.Strategy who, G.worstCaseEUInf who s

open Classical in
/-- The infimum worst-case EU is below every profile payoff when the payoff
    range is bounded below. -/
theorem worstCaseEUInf_le (who : ι) (s : G.Strategy who)
    (hbdd : BddBelow (Set.range (fun σ : Profile G =>
      G.eu (Function.update σ who s) who)))
    (σ : Profile G) :
    G.worstCaseEUInf who s ≤ G.eu (Function.update σ who s) who := by
  exact ciInf_le hbdd σ

open Classical in
/-- The infimum worst case is a guaranteed payoff against every profile, under
    the same bounded-below hypothesis needed to use `iInf` as a lower bound. -/
theorem worstCaseEUInf_guarantees (who : ι) (s : G.Strategy who)
    (hbdd : BddBelow (Set.range (fun σ : Profile G =>
      G.eu (Function.update σ who s) who))) :
    ∀ σ : Profile G, G.eu (Function.update σ who s) who ≥
      G.worstCaseEUInf who s :=
  fun σ => G.worstCaseEUInf_le who s hbdd σ

open Classical in
/-- In a Nash equilibrium, each player's EU is at least their order-theoretic
    security level, assuming each pure-deviation worst-case range is bounded
    below. -/
theorem nash_eu_ge_securityLevelSup {σ : Profile G} (hN : G.IsNash σ)
    (who : ι) [Nonempty (G.Strategy who)]
    (hbddWorst : ∀ s : G.Strategy who,
      BddBelow (Set.range (fun τ : Profile G =>
        G.eu (Function.update τ who s) who))) :
    G.eu σ who ≥ G.securityLevelSup who := by
  simp only [securityLevelSup]
  apply ciSup_le
  intro s
  calc G.worstCaseEUInf who s
      ≤ G.eu (Function.update σ who s) who := G.worstCaseEUInf_le who s (hbddWorst s) σ
    _ ≤ G.eu σ who := by have := hN who s; linarith

open Classical in
/-- A dominant strategy guarantees at least the order-theoretic security level
    against any profile, under bounded-below worst-case ranges. -/
theorem IsDominant.eu_ge_securityLevelSup
    {who : ι} [Nonempty (G.Strategy who)]
    {s : G.Strategy who} (hdom : G.IsDominant who s)
    (σ : Profile G)
    (hbddWorst : ∀ t : G.Strategy who,
      BddBelow (Set.range (fun τ : Profile G =>
        G.eu (Function.update τ who t) who))) :
    G.eu (Function.update σ who s) who ≥ G.securityLevelSup who := by
  simp only [securityLevelSup]
  apply ciSup_le
  intro t
  calc G.worstCaseEUInf who t
      ≤ G.eu (Function.update σ who t) who := G.worstCaseEUInf_le who t (hbddWorst t) σ
    _ ≤ G.eu (Function.update σ who s) who := by
        have := hdom σ t; linarith

open Classical in
/-- The order-theoretic security level is the best guaranteed payoff, provided
    the chosen strategy's profile range is nonempty/bounded below and the
    strategy-level worst-case range is bounded above. -/
theorem le_securityLevelSup_of_forall_eu_ge (who : ι) [Nonempty (Profile G)]
    (s : G.Strategy who) (v : ℝ)
    (hg : ∀ σ : Profile G, G.eu (Function.update σ who s) who ≥ v)
    (hbddSec : BddAbove (Set.range (fun t : G.Strategy who =>
      G.worstCaseEUInf who t))) :
    v ≤ G.securityLevelSup who := by
  calc v ≤ G.worstCaseEUInf who s := by
          exact le_ciInf hg
     _ ≤ G.securityLevelSup who :=
          le_ciSup hbddSec s

end Order

section Finite

variable (G : KernelGame ι) [Fintype (Profile G)] [Nonempty (Profile G)]

open Classical in
/-- Worst-case EU for player `who` when they play `s`:
    the minimum EU over all possible opponent profiles. -/
noncomputable def worstCaseEU (who : ι) (s : G.Strategy who) : ℝ :=
  Finset.inf' Finset.univ ⟨Classical.arbitrary _, Finset.mem_univ _⟩
    (fun σ => G.eu (Function.update σ who s) who)

open Classical in
/-- The worst-case EU is a lower bound on EU for any profile. -/
theorem worstCaseEU_le (who : ι) (s : G.Strategy who) (σ : Profile G) :
    G.worstCaseEU who s ≤ G.eu (Function.update σ who s) who :=
  Finset.inf'_le _ (Finset.mem_univ σ)

open Classical in
/-- The worst-case EU is a lower bound: a strategy guarantees at least
    its worst-case EU against any opponents. -/
theorem worstCaseEU_guarantees (who : ι) (s : G.Strategy who) :
    ∀ σ : Profile G, G.eu (Function.update σ who s) who ≥ G.worstCaseEU who s :=
  fun σ => worstCaseEU_le G who s σ

variable [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]

open Classical in
/-- The security level (maximin value) of player `who`:
    the best worst-case EU they can guarantee. -/
noncomputable def securityLevel (who : ι) : ℝ :=
  Finset.sup' Finset.univ ⟨Classical.arbitrary _, Finset.mem_univ _⟩
    (fun s => G.worstCaseEU who s)

open Classical in
/-- In a Nash equilibrium, each player's EU is at least their security level. -/
theorem nash_eu_ge_securityLevel {σ : Profile G} (hN : G.IsNash σ) (who : ι) :
    G.eu σ who ≥ G.securityLevel who := by
  simp only [securityLevel]
  apply Finset.sup'_le
  intro s _
  calc G.worstCaseEU who s
      ≤ G.eu (Function.update σ who s) who := worstCaseEU_le G who s σ
    _ ≤ G.eu σ who := by have := hN who s; linarith

open Classical in
/-- A dominant strategy guarantees at least the security level
    against any opponent profile. -/
theorem IsDominant.eu_ge_securityLevel
    {who : ι} {s : G.Strategy who} (hdom : G.IsDominant who s)
    (σ : Profile G) :
    G.eu (Function.update σ who s) who ≥ G.securityLevel who := by
  simp only [securityLevel]
  apply Finset.sup'_le
  intro t _
  calc G.worstCaseEU who t
      ≤ G.eu (Function.update σ who t) who := worstCaseEU_le G who t σ
    _ ≤ G.eu (Function.update σ who s) who := by
        have := hdom σ t; linarith

open Classical in
/-- The security level is the best guarantee: if a strategy guarantees
    at least `v` against all opponent profiles, then `v ≤ securityLevel`. -/
theorem le_securityLevel_of_forall_eu_ge (who : ι) (s : G.Strategy who) (v : ℝ)
    (hg : ∀ σ : Profile G, G.eu (Function.update σ who s) who ≥ v) :
    v ≤ G.securityLevel who := by
  calc v ≤ G.worstCaseEU who s := by
          apply Finset.le_inf'
          intro σ _
          exact hg σ
     _ ≤ G.securityLevel who :=
          Finset.le_sup' _ (Finset.mem_univ s)

open Classical in
/-- A security strategy exists: some strategy achieves the security level. -/
theorem exists_securityStrategy (who : ι) :
    ∃ s : G.Strategy who, G.worstCaseEU who s = G.securityLevel who := by
  obtain ⟨s, _, hs⟩ := Finset.exists_max_image Finset.univ
    (fun s => G.worstCaseEU who s) ⟨Classical.arbitrary _, Finset.mem_univ _⟩
  exact ⟨s, le_antisymm (Finset.le_sup' _ (Finset.mem_univ s))
    (Finset.sup'_le _ _ (fun t _ => hs t (Finset.mem_univ t)))⟩

end Finite

end KernelGame

end GameTheory
