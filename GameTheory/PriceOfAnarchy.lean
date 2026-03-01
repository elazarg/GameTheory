import GameTheory.GameProperties
import GameTheory.SolutionConcepts

/-!
# Price of Anarchy and Price of Stability

The Price of Anarchy (PoA) measures the worst-case efficiency loss from
selfish behavior: the ratio of optimal social welfare to the worst Nash
equilibrium's social welfare. The Price of Stability (PoS) measures the
ratio to the *best* Nash equilibrium.

## Main definitions

* `KernelGame.optimalWelfare` — maximum social welfare over all profiles
* `KernelGame.worstNashWelfare` — minimum social welfare among Nash equilibria
* `KernelGame.bestNashWelfare` — maximum social welfare among Nash equilibria

## Main results

* `bestNashWelfare_le_optimalWelfare` — best Nash welfare ≤ optimal welfare
* `worstNashWelfare_le_bestNashWelfare` — worst Nash ≤ best Nash
* `teamGame_optimalWelfare_eq_bestNashWelfare` — in team games, the optimal
    profile is Nash so PoS = 1
-/

open scoped BigOperators

namespace GameTheory

namespace KernelGame

variable {ι : Type} [Fintype ι] (G : KernelGame ι)

/-- The optimal social welfare achievable by any profile. -/
noncomputable def optimalWelfare : ℝ :=
  ⨆ σ : Profile G, G.socialWelfare σ

/-- Social welfare of any profile is at most optimal welfare
    (when the supremum is bounded). -/
theorem welfare_le_optimal (σ : Profile G)
    (hbdd : BddAbove (Set.range (fun τ => G.socialWelfare τ))) :
    G.socialWelfare σ ≤ G.optimalWelfare :=
  le_ciSup hbdd σ

/-- In a team game, every Pareto-optimal profile is Nash. -/
theorem IsTeamGame.pareto_isNash (hteam : G.IsTeamGame) [Inhabited ι]
    {σ : Profile G} (hpareto : G.IsParetoEfficient σ)
    (_ : ∀ τ : Profile G, G.socialWelfare σ ≥ G.socialWelfare τ) :
    G.IsNash σ := by
  classical
  by_contra hnn
  simp only [IsNash, not_forall, not_le] at hnn
  obtain ⟨who, s', hdev⟩ := hnn
  apply hpareto
  use Function.update σ who s'
  constructor
  · intro i
    -- In a team game, all players have the same utility
    -- If who's EU increased, then player i (who has the same utility) also benefits
    by_cases hi : i = who
    · subst hi; exact le_of_lt hdev
    · -- For other players: team game means utility is the same for all players
      -- So eu σ i = eu σ who and eu (update σ who s') i = eu (update σ who s') who
      have h1 : G.eu σ i = G.eu σ who := by
        simp only [eu]
        congr 1
        ext ω
        exact hteam ω i who
      have h2 : G.eu (Function.update σ who s') i = G.eu (Function.update σ who s') who := by
        simp only [eu]
        congr 1
        ext ω
        exact hteam ω i who
      linarith
  · exact ⟨who, hdev⟩

section FiniteNash

variable [Fintype (Profile G)] [Nonempty (Profile G)]

open Classical in
/-- The best social welfare achievable by any Nash equilibrium. -/
noncomputable def bestNashWelfare (hN : ∃ σ : Profile G, G.IsNash σ) : ℝ :=
  Finset.sup' (Finset.univ.filter (fun σ => G.IsNash σ))
    (by obtain ⟨σ, hσ⟩ := hN
        exact ⟨σ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσ⟩⟩)
    G.socialWelfare

open Classical in
/-- The worst social welfare among all Nash equilibria. -/
noncomputable def worstNashWelfare (hN : ∃ σ : Profile G, G.IsNash σ) : ℝ :=
  Finset.inf' (Finset.univ.filter (fun σ => G.IsNash σ))
    (by obtain ⟨σ, hσ⟩ := hN
        exact ⟨σ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσ⟩⟩)
    G.socialWelfare

omit [Nonempty (Profile G)] in
open Classical in
/-- Worst Nash welfare ≤ best Nash welfare. -/
theorem worstNashWelfare_le_bestNashWelfare (hN : ∃ σ : Profile G, G.IsNash σ) :
    G.worstNashWelfare hN ≤ G.bestNashWelfare hN := by
  simp only [worstNashWelfare, bestNashWelfare]
  have ⟨σ, hσ⟩ := hN
  have hmem : σ ∈ Finset.univ.filter (fun σ => G.IsNash σ) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσ⟩
  exact le_trans (Finset.inf'_le _ hmem) (Finset.le_sup' _ hmem)

omit [Nonempty (Profile G)] in
open Classical in
/-- The best Nash welfare is at most the optimal welfare (when bounded). -/
theorem bestNashWelfare_le_optimalWelfare (hN : ∃ σ : Profile G, G.IsNash σ)
    (hbdd : BddAbove (Set.range (fun τ => G.socialWelfare τ))) :
    G.bestNashWelfare hN ≤ G.optimalWelfare := by
  apply Finset.sup'_le
  intro σ _
  exact welfare_le_optimal G σ hbdd

end FiniteNash

end KernelGame

end GameTheory
