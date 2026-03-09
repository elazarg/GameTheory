import Math.Probability
import GameTheory.Concepts.SolutionConcepts

/-!
# Security Strategies and Maximin Values

A player's security level (maximin value) is the best EU they can
guarantee regardless of opponents' play. A security (maximin) strategy
achieves this guarantee.

## Main definitions

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

section Finite

variable (G : KernelGame ι) [Fintype (Profile G)]
  [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
  [Nonempty (Profile G)]

open Classical in
/-- Worst-case EU for player `who` when they play `s`:
    the minimum EU over all possible opponent profiles. -/
noncomputable def worstCaseEU (who : ι) (s : G.Strategy who) : ℝ :=
  Finset.inf' Finset.univ ⟨Classical.arbitrary _, Finset.mem_univ _⟩
    (fun σ => G.eu (Function.update σ who s) who)

open Classical in
/-- The security level (maximin value) of player `who`:
    the best worst-case EU they can guarantee. -/
noncomputable def securityLevel (who : ι) : ℝ :=
  Finset.sup' Finset.univ ⟨Classical.arbitrary _, Finset.mem_univ _⟩
    (fun s => G.worstCaseEU who s)

set_option linter.unusedFintypeInType false in
omit [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)] in
open Classical in
/-- The worst-case EU is a lower bound on EU for any profile. -/
theorem worstCaseEU_le (who : ι) (s : G.Strategy who) (σ : Profile G) :
    G.worstCaseEU who s ≤ G.eu (Function.update σ who s) who :=
  Finset.inf'_le _ (Finset.mem_univ σ)

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

set_option linter.unusedFintypeInType false in
omit [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)] in
open Classical in
/-- The worst-case EU is a lower bound: a strategy guarantees at least
    its worst-case EU against any opponents. -/
theorem worstCaseEU_guarantees (who : ι) (s : G.Strategy who) :
    ∀ σ : Profile G, G.eu (Function.update σ who s) who ≥ G.worstCaseEU who s :=
  fun σ => worstCaseEU_le G who s σ

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
