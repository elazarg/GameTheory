/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Core.GameForm
import Math.Probability

/-!
# GameTheory.Core.KernelGame

Kernel-based game structure: the semantic core for finite/discrete game models.

Provides:
- `KernelGame` — a game with player-indexed strategies, stochastic outcome kernel, and utility
- `GameForm.withUtility`, `KernelGame.toGameForm` — bridge to raw semantics
- `KernelGame.mixedExtension` — utility-preserving lift of `GameForm.mixedExtension`
- `eu` — expected utility for a player under a strategy profile
- `Profile`, `correlatedOutcome` — standard game-theoretic notions
- `KernelGame.ofEU` — constructs a kernel game from a direct EU function
- `KernelGame.ofPureEU` — deterministic strategic-form kernel whose outcomes are pure profiles
-/

namespace GameTheory

open Math.Probability

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

end KernelGame

namespace GameForm

variable {ι : Type}

/-- Attach a utility function to a game form to get a full kernel game. -/
def withUtility (F : GameForm ι) (u : F.Outcome → Payoff ι) : KernelGame ι where
  Strategy := F.Strategy
  Outcome := F.Outcome
  utility := u
  outcomeKernel := F.outcomeKernel

@[simp] theorem withUtility_Strategy (F : GameForm ι) (u : F.Outcome → Payoff ι) :
    (F.withUtility u).Strategy = F.Strategy := rfl

@[simp] theorem withUtility_Outcome (F : GameForm ι) (u : F.Outcome → Payoff ι) :
    (F.withUtility u).Outcome = F.Outcome := rfl

@[simp] theorem withUtility_outcomeKernel (F : GameForm ι) (u : F.Outcome → Payoff ι) :
    (F.withUtility u).outcomeKernel = F.outcomeKernel := rfl

@[simp] theorem withUtility_utility (F : GameForm ι) (u : F.Outcome → Payoff ι) :
    (F.withUtility u).utility = u := rfl

end GameForm

namespace KernelGame

variable {ι : Type}

/-- Strip utility from a kernel game to get its underlying game form. -/
@[reducible] def toGameForm (G : KernelGame ι) : GameForm ι where
  Strategy := G.Strategy
  Outcome := G.Outcome
  outcomeKernel := G.outcomeKernel

@[simp] theorem toGameForm_Strategy (G : KernelGame ι) :
    G.toGameForm.Strategy = G.Strategy := rfl

@[simp] theorem toGameForm_Outcome (G : KernelGame ι) :
    G.toGameForm.Outcome = G.Outcome := rfl

@[simp] theorem toGameForm_outcomeKernel (G : KernelGame ι) :
    G.toGameForm.outcomeKernel = G.outcomeKernel := rfl

/-- Round-trip: stripping utility then reattaching recovers the original game. -/
@[simp] theorem toGameForm_withUtility (G : KernelGame ι) :
    G.toGameForm.withUtility G.utility = G := by
  cases G; rfl

end KernelGame

namespace GameForm

@[simp] theorem withUtility_toGameForm
    (F : GameForm ι) (u : F.Outcome → Payoff ι) :
    (F.withUtility u).toGameForm = F := by
  cases F; rfl

end GameForm

namespace KernelGame

open Classical in
/-- Lift the utility-free mixed extension to a kernel game, retaining the
original utility function. -/
noncomputable def mixedExtension (G : KernelGame ι) [Fintype ι] : KernelGame ι :=
  G.toGameForm.mixedExtension.withUtility G.utility

/-- The Strategy field of `G.mixedExtension` is `fun i => PMF (G.Strategy i)`.
Marked `@[simp]` so `Function.update` terms reduce uniformly (see `ofEU_Strategy`
in `SolutionConcepts` for background on why v4.29 needs this). -/
@[simp] theorem mixedExtension_Strategy (G : KernelGame ι) [Fintype ι] :
    G.mixedExtension.Strategy = fun i => PMF (G.Strategy i) := rfl

@[simp] theorem mixedExtension_toGameForm (G : KernelGame ι) [Fintype ι] :
    G.mixedExtension.toGameForm = G.toGameForm.mixedExtension :=
  GameForm.withUtility_toGameForm _ _

/-- Reindex the player type of a kernel game along an equivalence.

This is presentation bookkeeping: bridges often choose a canonical finite
player type, such as `Fin (Fintype.card ι)`, while the source game is indexed by
some equivalent type `ι`. -/
noncomputable def reindex {ι κ : Type} (e : ι ≃ κ)
    (G : KernelGame κ) : KernelGame ι where
  Strategy := fun i => G.Strategy (e i)
  Outcome := G.Outcome
  utility := fun ω i => G.utility ω (e i)
  outcomeKernel := fun σ =>
    G.outcomeKernel fun k =>
      cast (congrArg G.Strategy (e.apply_symm_apply k)) (σ (e.symm k))

/-- Expected utility of player `who` under strategy profile `σ`. -/
noncomputable def eu (G : KernelGame ι) (σ : Profile G) (who : ι) : ℝ :=
  expect (G.outcomeKernel σ) (fun ω => G.utility ω who)

open Classical in
/-- Deterministic strategic-form kernel from a direct payoff function.

Unlike `KernelGame.ofEU`, this keeps the realized pure profile as the outcome.
For finite strategy spaces this gives a finite outcome carrier, which is useful
for mixed-extension existence theorems. -/
noncomputable def ofPureEU
    (Strategy : ι → Type) (u : (∀ i, Strategy i) → Payoff ι) : KernelGame ι where
  Strategy := Strategy
  Outcome := ∀ i, Strategy i
  utility := fun σ i => u σ i
  outcomeKernel := fun σ => PMF.pure σ

/-- EU of `ofPureEU` is just the supplied payoff function. -/
@[simp] theorem eu_ofPureEU
    (S : ι → Type) (u : (∀ i, S i) → Payoff ι) (σ : ∀ i, S i) (i : ι) :
    (ofPureEU S u).eu σ i = u σ i := by
  simp [eu, ofPureEU, expect_pure]

/-- The Strategy field of `ofPureEU S u` is `S` by definition. -/
@[simp] theorem ofPureEU_Strategy
    (S : ι → Type) (u : (∀ i, S i) → Payoff ι) :
    (ofPureEU S u).Strategy = S := rfl

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

end KernelGame

end GameTheory
