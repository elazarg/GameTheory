import GameTheory.SolutionConcepts

/-!
# Two-Player Game Properties

Specialized results for 2-player games (`KernelGame (Fin 2)`).

## Main results

* `two_player_update_comm` — updating different players commutes
* `two_player_profile_ext` — a profile is determined by its two components
* `two_player_profile_decompose` — any profile equals its component updates
-/

namespace GameTheory

namespace KernelGame

open Classical in
/-- In a 2-player game, updating players 0 and 1 commutes. -/
theorem two_player_update_comm {G : KernelGame (Fin 2)}
    (σ : Profile G) (s₀ : G.Strategy 0) (s₁ : G.Strategy 1) :
    Function.update (Function.update σ 0 s₀) 1 s₁ =
    Function.update (Function.update σ 1 s₁) 0 s₀ := by
  simpa using (Function.update_comm (f := σ) (a := (0 : Fin 2)) (b := (1 : Fin 2))
    (v := s₀) (w := s₁) (by decide))

open Classical in
/-- A 2-player profile is determined by its two components. -/
theorem two_player_profile_ext {G : KernelGame (Fin 2)}
    {σ τ : Profile G} (h0 : σ 0 = τ 0) (h1 : σ 1 = τ 1) :
    σ = τ := by
  funext i; fin_cases i
  · exact h0
  · exact h1

open Classical in
/-- Any 2-player profile can be decomposed as updates from any base profile. -/
theorem two_player_profile_decompose {G : KernelGame (Fin 2)}
    (σ τ : Profile G) :
    Function.update (Function.update τ 0 (σ 0)) 1 (σ 1) = σ := by
  calc
    Function.update (Function.update τ 0 (σ 0)) 1 (σ 1)
        = Function.update (Function.update σ 1 (τ 1)) 1 (σ 1) := by
            simpa using congrArg (fun p => Function.update p 1 (σ 1)) (fin2_update_comm σ τ)
    _ = Function.update σ 1 (σ 1) := by simp [Function.update_idem]
    _ = σ := Function.update_eq_self 1 σ

open Classical in
/-- In a 2-player game, a profile where player 0 updates to their current
    strategy is unchanged. -/
theorem two_player_update_same_0 {G : KernelGame (Fin 2)}
    (σ : Profile G) : Function.update σ 0 (σ 0) = σ := by
  exact Function.update_eq_self 0 σ

open Classical in
/-- In a 2-player game, if σ is Nash and we fix player 1's strategy,
    then player 0 is playing a best response to player 1. -/
theorem two_player_nash_best_response_0 {G : KernelGame (Fin 2)}
    {σ : Profile G} (hN : G.IsNash σ) (s₀ : G.Strategy 0) :
    G.eu σ 0 ≥ G.eu (Function.update σ 0 s₀) 0 := by
  convert hN 0 s₀

open Classical in
/-- Similarly for player 1. -/
theorem two_player_nash_best_response_1 {G : KernelGame (Fin 2)}
    {σ : Profile G} (hN : G.IsNash σ) (s₁ : G.Strategy 1) :
    G.eu σ 1 ≥ G.eu (Function.update σ 1 s₁) 1 := by
  convert hN 1 s₁

end KernelGame

end GameTheory
