/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Foundations.DeviationSimulation

/-!
# GameTheory.Concepts.Foundations.StrategicEquivalence

A *strategic equivalence* between two game forms: a per-player bijection on
strategies that preserves the observed outcome law.

This is the strongest and most reusable bridge between two presentations of the
"same" game.  Unlike a `NashDeviationBisimulation`, which only matches unilateral
deviations, a strategic equivalence relabels each player's strategy set by a
bijection.  From that single datum, *every* deviation-based solution concept
transports — Nash, correlated, and coarse-correlated equilibrium are instances —
because a deviation by player `i` on one side maps through the player-`i`
bijection to a deviation on the other side with the same observed law.
-/

namespace GameTheory

open Math.Probability

namespace GameForm

variable {ι Ω : Type}

/-- A per-player strategy bijection preserving the observed outcome law. -/
structure StrategicEquivalence (G H : GameForm ι) (Ω : Type) where
  viewG : ViewFamily G ι (fun _ => Ω)
  viewH : ViewFamily H ι (fun _ => Ω)
  equivStrategy : (i : ι) → G.Strategy i ≃ H.Strategy i
  law_eq :
    ∀ (σ : G.Profile) (i : ι),
      viewG.plaw i σ = viewH.plaw i (fun j => equivStrategy j (σ j))

namespace StrategicEquivalence

variable {G H : GameForm ι}

/-- Forward profile realization induced by the per-player bijection. -/
def realize (E : StrategicEquivalence G H Ω) (σ : G.Profile) : H.Profile :=
  fun i => E.equivStrategy i (σ i)

/-- Backward profile realization induced by the inverse bijections. -/
def realizeSymm (E : StrategicEquivalence G H Ω) (τ : H.Profile) : G.Profile :=
  fun i => (E.equivStrategy i).symm (τ i)

@[simp] theorem realizeSymm_realize (E : StrategicEquivalence G H Ω)
    (σ : G.Profile) : E.realizeSymm (E.realize σ) = σ := by
  funext i; simp [realize, realizeSymm]

@[simp] theorem realize_realizeSymm (E : StrategicEquivalence G H Ω)
    (τ : H.Profile) : E.realize (E.realizeSymm τ) = τ := by
  funext i; simp [realize, realizeSymm]

theorem law_eq_realize (E : StrategicEquivalence G H Ω) (σ : G.Profile) (i : ι) :
    E.viewG.plaw i σ = E.viewH.plaw i (E.realize σ) :=
  E.law_eq σ i

theorem law_eq_realizeSymm (E : StrategicEquivalence G H Ω) (τ : H.Profile) (i : ι) :
    E.viewG.plaw i (E.realizeSymm τ) = E.viewH.plaw i τ := by
  rw [E.law_eq (E.realizeSymm τ) i]
  congr 1
  funext j
  simp [realizeSymm]

variable [DecidableEq ι]

theorem realize_update (E : StrategicEquivalence G H Ω) (σ : G.Profile)
    (i : ι) (s : G.Strategy i) :
    E.realize (Function.update σ i s) =
      Function.update (E.realize σ) i (E.equivStrategy i s) := by
  funext j
  by_cases h : j = i
  · subst h; simp [realize]
  · simp [realize, Function.update_of_ne h]

theorem realizeSymm_update (E : StrategicEquivalence G H Ω) (τ : H.Profile)
    (i : ι) (s : H.Strategy i) :
    E.realizeSymm (Function.update τ i s) =
      Function.update (E.realizeSymm τ) i ((E.equivStrategy i).symm s) := by
  funext j
  by_cases h : j = i
  · subst h; simp [realizeSymm]
  · simp [realizeSymm, Function.update_of_ne h]

/-- The forward deviation-matching law: a target deviation `sH` by player `who`
is matched by the source deviation `(equivStrategy who).symm sH`. -/
theorem law_update_realizeSymm (E : StrategicEquivalence G H Ω) (σ : G.Profile)
    (who : ι) (sH : H.Strategy who) :
    E.viewG.plaw who (Function.update σ who ((E.equivStrategy who).symm sH)) =
      E.viewH.plaw who (Function.update (E.realize σ) who sH) := by
  rw [E.law_eq (Function.update σ who ((E.equivStrategy who).symm sH)) who]
  congr 1
  funext i
  by_cases h : i = who
  · subst h; simp [Equiv.apply_symm_apply]
  · simp [realize, Function.update_of_ne h]

/-- The backward deviation-matching law: a source deviation `sG` by player `who`
is matched by the target deviation `equivStrategy who sG`. -/
theorem law_update_realize (E : StrategicEquivalence G H Ω) (σ : G.Profile)
    (who : ι) (sG : G.Strategy who) :
    E.viewG.plaw who (Function.update σ who sG) =
      E.viewH.plaw who (Function.update (E.realize σ) who (E.equivStrategy who sG)) := by
  rw [E.law_eq (Function.update σ who sG) who]
  congr 1
  funext i
  by_cases h : i = who
  · subst h; simp
  · simp [realize, Function.update_of_ne h]

/-- A strategic equivalence induces a two-way Nash-deviation bisimulation. -/
def toNashDeviationBisimulation (E : StrategicEquivalence G H Ω) :
    NashDeviationBisimulation G H Ω where
  viewG := E.viewG
  viewH := E.viewH
  rel := fun σ τ => τ = E.realize σ
  law_eq := by
    intro σ τ h i; subst h; exact E.law_eq σ i
  simulate_target_deviation := by
    intro σ τ h who sH; subst h
    exact ⟨(E.equivStrategy who).symm sH, E.law_update_realizeSymm σ who sH⟩
  simulate_source_deviation := by
    intro σ τ h who sG; subst h
    exact ⟨E.equivStrategy who sG, E.law_update_realize σ who sG⟩

/-- A source profile is related to its canonical realization. -/
theorem rel_realize (E : StrategicEquivalence G H Ω) (σ : G.Profile) :
    E.toNashDeviationBisimulation.rel σ (E.realize σ) := rfl

/-- **Nash transport.** Nash equilibrium is invariant across a strategic
equivalence, for any common observed-outcome preference. -/
theorem nash_iff (E : StrategicEquivalence G H Ω) (σ : G.Profile)
    {prefΩ : ι → PMF Ω → PMF Ω → Prop} :
    G.IsNashFor (observedPref E.viewG prefΩ) σ ↔
      H.IsNashFor (observedPref E.viewH prefΩ) (E.realize σ) :=
  E.toNashDeviationBisimulation.nash_iff (E.rel_realize σ)

/-- The inverse strategic equivalence (swap the two games, invert each
per-player bijection). -/
def symm (E : StrategicEquivalence G H Ω) : StrategicEquivalence H G Ω where
  viewG := E.viewH
  viewH := E.viewG
  equivStrategy := fun i => (E.equivStrategy i).symm
  law_eq := fun τ i => (E.law_eq_realizeSymm τ i).symm

/-- Forward constant-deviation-family transport: matches a target constant
deviation by player `who` with the source deviation through `(equivStrategy who).symm`. -/
noncomputable def toCoarseCorrelatedSimulation (E : StrategicEquivalence G H Ω) :
    Transport G H E.viewG E.viewH
      G.constantDeviationProfileFamily H.constantDeviationProfileFamily :=
  Transport.ofConstantProfileMap E.viewG E.viewH E.realize
    (fun i σ => E.law_eq_realize σ i)
    (fun who sH =>
      ⟨(E.equivStrategy who).symm sH, fun σ => E.law_update_realizeSymm σ who sH⟩)

/-- Forward recommendation-deviation-family transport: matches a target
recommendation deviation by player `who` with the conjugated source deviation. -/
noncomputable def toCorrelatedSimulation (E : StrategicEquivalence G H Ω) :
    Transport G H E.viewG E.viewH
      G.recommendationDeviationFamily H.recommendationDeviationFamily :=
  Transport.ofRecommendationProfileMap E.viewG E.viewH E.realize
    (fun i σ => E.law_eq_realize σ i)
    (fun who dH =>
      ⟨fun s => (E.equivStrategy who).symm (dH (E.equivStrategy who s)),
        fun σ => by
          have h := E.law_update_realizeSymm σ who (dH (E.realize σ who))
          simpa [GameForm.deviateProfileFn, realize] using h⟩)

/-- **Coarse-correlated-equilibrium transport.** -/
theorem target_coarseCorrelatedEq (E : StrategicEquivalence G H Ω)
    (μ : PMF G.Profile) {prefΩ : ι → PMF Ω → PMF Ω → Prop}
    (h : G.IsCoarseCorrelatedEqFor (observedPref E.viewG prefΩ) μ) :
    H.IsCoarseCorrelatedEqFor (observedPref E.viewH prefΩ) (PMF.map E.realize μ) :=
  E.toCoarseCorrelatedSimulation.target_coarseCorrelatedEq_of_source_coarseCorrelatedEq
    rfl h

/-- **Correlated-equilibrium transport.** -/
theorem target_correlatedEq (E : StrategicEquivalence G H Ω)
    (μ : PMF G.Profile) {prefΩ : ι → PMF Ω → PMF Ω → Prop}
    (h : G.IsCorrelatedEqFor (observedPref E.viewG prefΩ) μ) :
    H.IsCorrelatedEqFor (observedPref E.viewH prefΩ) (PMF.map E.realize μ) :=
  E.toCorrelatedSimulation.target_correlatedEq_of_source_correlatedEq rfl h

end StrategicEquivalence

end GameForm

end GameTheory
