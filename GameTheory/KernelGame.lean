import GameTheory.Probability

/-!
# GameTheory.KernelGame

Kernel-based game structure: the semantic core for finite/discrete game models.

Provides:
- `KernelGame` — a game with player-indexed strategies, stochastic outcome kernel, and utility
- `eu` — expected utility for a player under a strategy profile
- `Profile`, `correlatedOutcome` — standard game-theoretic notions
- `KernelGame.ofEU` — constructs a kernel game from a direct EU function
-/

namespace GameTheory

/-- A payoff vector for `ι` players. -/
abbrev Payoff (ι : Type) : Type := ι → ℝ

-- ============================================================================
-- Kernel-based game (strategies + outcome kernel → EU)
-- ============================================================================

/-- A kernel-based game with explicit outcome type.
    - `Outcome` is the type of game outcomes (e.g. terminal nodes, action profiles)
    - `utility` maps outcomes to player payoffs
    - `outcomeKernel` maps strategy profiles to outcome distributions -/
structure KernelGame (ι : Type) where
  Strategy : ι → Type
  Outcome : Type
  utility : Outcome → Payoff ι
  outcomeKernel : Kernel (∀ i, Strategy i) Outcome

namespace KernelGame

variable {ι : Type}

abbrev Profile (G : KernelGame ι) := ∀ i, G.Strategy i

/-- Expected utility of player `who` under strategy profile `σ`. -/
noncomputable def eu (G : KernelGame ι) (σ : Profile G) (who : ι) : ℝ :=
  expect (G.outcomeKernel σ) (fun ω => G.utility ω who)

/-- Outcome distribution under a correlated profile distribution (correlation device). -/
noncomputable def correlatedOutcome (G : KernelGame ι)
    (μ : PMF (Profile G)) : PMF G.Outcome :=
  Kernel.pushforward G.outcomeKernel μ

/-- A point-mass profile distribution induces the same outcome distribution
    as direct evaluation at that profile. -/
@[simp] theorem correlatedOutcome_pure (G : KernelGame ι) (σ : Profile G) :
    G.correlatedOutcome (PMF.pure σ) = G.outcomeKernel σ := by
  simp [correlatedOutcome]

/-- Joint utility distribution: pushforward of the outcome distribution through `utility`. -/
noncomputable def udist (G : KernelGame ι) (σ : Profile G) : PMF (Payoff ι) :=
  (G.outcomeKernel σ).bind (fun ω => PMF.pure (G.utility ω))

/-- Per-player utility distribution: pushforward projected to a single player. -/
noncomputable def udistPlayer (G : KernelGame ι) (σ : Profile G) (who : ι) : PMF ℝ :=
  (G.outcomeKernel σ).bind (fun ω => PMF.pure (G.utility ω who))

/-- Player-`who` utility distribution is the pushforward of the joint utility
    distribution along coordinate projection. -/
theorem udistPlayer_eq_udist_bind (G : KernelGame ι) (σ : Profile G) (who : ι) :
    G.udistPlayer σ who =
      (G.udist σ).bind (fun u : Payoff ι => PMF.pure (u who)) := by
  simp [udistPlayer, udist, PMF.bind_bind]

/-- `udist` under a deterministic (point-mass) outcome collapses to a point mass. -/
@[simp] theorem udist_pure (G : KernelGame ι) (σ : Profile G) (ω : G.Outcome)
    (h : G.outcomeKernel σ = PMF.pure ω) :
    G.udist σ = PMF.pure (G.utility ω) := by
  simp [udist, h]

/-- `udistPlayer` under a deterministic outcome collapses to a point mass. -/
@[simp] theorem udistPlayer_pure (G : KernelGame ι) (σ : Profile G) (ω : G.Outcome)
    (who : ι) (h : G.outcomeKernel σ = PMF.pure ω) :
    G.udistPlayer σ who = PMF.pure (G.utility ω who) := by
  simp [udistPlayer, h]

open Classical in
theorem fin2_update_comm {α : Fin 2 → Type} (σ τ : ∀ i, α i) :
    Function.update τ 0 (σ 0) = Function.update σ 1 (τ 1) := by
  funext i; fin_cases i <;> simp [Function.update]

end KernelGame

end GameTheory
