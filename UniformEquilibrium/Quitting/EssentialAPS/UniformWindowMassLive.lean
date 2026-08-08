/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.EssentialAPS.CompactFixedPointLive
import UniformEquilibrium.Quitting.EssentialAPS.UniformWindowMass

/-!
# Uniform APS window mass with unique live successors

The quantitative active-face separation argument only uses compactness of the
initial greatest-family fiber.  Combining it with the unique-live closure
bootstrap removes graph-theoretic successor uniqueness from the `nu`-lemma.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type}

/-- **Uniform positive finite-window mass with unique live successors.**
Face avoidance is required only on the initial greatest-family fiber. -/
theorem
    exists_uniform_quittingEssentialAPS_windowMass_of_greatest_faceAvoidance_unique_live
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : ι → Set (Payoff ι))
    (hcarrierCompact : ∀ player, IsCompact (carrier player))
    (hcarrierConvex : ∀ player, Convex ℝ (carrier player))
    (successor : ι → ι)
    (hedge : ∀ player,
      QuittingFleschSuccessor reward player (successor player))
    (huniqueLive : ∀ player candidate,
      QuittingFleschSuccessor reward player candidate →
        candidate ≠ successor player →
          quittingEssentialAPSGreatestFamily reward carrier candidate = ∅)
    (owner : ℕ → ι) (horizon : ℕ)
    (hgreatestNonempty :
      (quittingEssentialAPSGreatestFamily reward carrier (owner 0)).Nonempty)
    (hfaceAvoidance : ∀ current,
      current ∈
          quittingEssentialAPSGreatestFamily reward carrier (owner 0) →
        ¬ IsQuittingEssentialAPSActiveAlong
          reward owner current horizon)
    {bound : ℝ} (hbound : 0 < bound)
    (hrootBound : ∀ time who,
      |quittingSoloReward reward (owner time) who| ≤ bound) :
    ∃ nu : ℝ, 0 < nu ∧
      ∀ (mass : ℕ → ℝ) (value : ℕ → Payoff ι),
        value 0 ∈
            quittingEssentialAPSGreatestFamily reward carrier (owner 0) →
        (∀ time, 0 ≤ mass time) →
        (∀ time,
          value time = quittingSingletonArcPayoff (mass time)
            (quittingSoloReward reward (owner time))
            (value (time + 1))) →
        (∀ time,
          value time (owner time) =
            quittingSoloReward reward (owner time) (owner time)) →
        (∀ time who, |value time who| ≤ bound) →
        nu ≤ ∑ time ∈ Finset.range horizon, mass time := by
  let greatest := quittingEssentialAPSGreatestFamily reward carrier
  have hgreatestCompact : IsCompact (greatest (owner 0)) :=
    isCompact_quittingEssentialAPSGreatestFamily_of_compact_convex_unique_live
      reward carrier hcarrierCompact hcarrierConvex
        successor hedge huniqueLive (owner 0)
  obtain ⟨delta, hdeltaPos, hdeltaLower⟩ :=
    exists_uniform_quittingEssentialAPSActiveGap
      reward owner horizon hgreatestCompact hgreatestNonempty
        hfaceAvoidance
  let coefficient : ℝ :=
    ((horizon + 1 : ℕ) : ℝ) * (2 * bound)
  have hcoefficientPos : 0 < coefficient := by
    dsimp only [coefficient]
    positivity
  refine ⟨delta / coefficient,
    div_pos hdeltaPos hcoefficientPos, ?_⟩
  intro mass value hvalue0 hmass harc hactive hvalueBound
  have hdeltaLe := hdeltaLower (value 0) hvalue0
  have hgapLe :=
    quittingEssentialAPSActiveGapSum_le_windowMass
      reward owner horizon mass value hbound.le hmass harc hactive
        hrootBound hvalueBound
  have hscaled :
      delta ≤ coefficient *
        (∑ time ∈ Finset.range horizon, mass time) := by
    exact hdeltaLe.trans (by
      simpa only [coefficient] using hgapLe)
  exact (div_le_iff₀ hcoefficientPos).2 (by
    simpa only [mul_comm] using hscaled)

/-- Carrier-level corollary of the unique-live greatest-fiber theorem. -/
theorem exists_uniform_quittingEssentialAPS_windowMass_unique_live
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : ι → Set (Payoff ι))
    (hcarrierCompact : ∀ player, IsCompact (carrier player))
    (hcarrierConvex : ∀ player, Convex ℝ (carrier player))
    (successor : ι → ι)
    (hedge : ∀ player,
      QuittingFleschSuccessor reward player (successor player))
    (huniqueLive : ∀ player candidate,
      QuittingFleschSuccessor reward player candidate →
        candidate ≠ successor player →
          quittingEssentialAPSGreatestFamily reward carrier candidate = ∅)
    (owner : ℕ → ι) (horizon : ℕ)
    (hgreatestNonempty :
      (quittingEssentialAPSGreatestFamily reward carrier (owner 0)).Nonempty)
    (hfaceAvoidance : ∀ current,
      current ∈ carrier (owner 0) →
        ¬ IsQuittingEssentialAPSActiveAlong
          reward owner current horizon)
    {bound : ℝ} (hbound : 0 < bound)
    (hrootBound : ∀ time who,
      |quittingSoloReward reward (owner time) who| ≤ bound) :
    ∃ nu : ℝ, 0 < nu ∧
      ∀ (mass : ℕ → ℝ) (value : ℕ → Payoff ι),
        value 0 ∈
            quittingEssentialAPSGreatestFamily reward carrier (owner 0) →
        (∀ time, 0 ≤ mass time) →
        (∀ time,
          value time = quittingSingletonArcPayoff (mass time)
            (quittingSoloReward reward (owner time))
            (value (time + 1))) →
        (∀ time,
          value time (owner time) =
            quittingSoloReward reward (owner time) (owner time)) →
        (∀ time who, |value time who| ≤ bound) →
        nu ≤ ∑ time ∈ Finset.range horizon, mass time := by
  exact
    exists_uniform_quittingEssentialAPS_windowMass_of_greatest_faceAvoidance_unique_live
      reward carrier hcarrierCompact hcarrierConvex successor hedge
        huniqueLive owner horizon hgreatestNonempty
        (fun current hcurrent ↦ by
          have hwithin :=
            quittingEssentialAPSGreatestFamily_subinvariant
              reward carrier (owner 0) hcurrent
          exact hfaceAvoidance current hwithin.1)
        hbound hrootBound

end GameTheory
