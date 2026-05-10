import GameTheory.Concepts.SolutionConcepts

/-!
# GameTheory.Core.DeviationSimulation

Distribution-level transport of equilibrium across game presentations.

The core idea is that matching the realized outcome law at a profile is not
enough to transport equilibrium: every target-side deviation must also be
matched by a source-side deviation with the same observed outcome law.

This file keeps the transport theorem at the `GameForm`/preference level.
Expected utility corollaries are downstream conveniences.
-/

namespace GameTheory

open Math.Probability

namespace GameForm

variable {ι Ω : Type}

/-- A view of a game form's outcomes into a common observed carrier. -/
structure OutcomeView (F : GameForm ι) (Ω : Type) where
  observe : F.Outcome → Ω

namespace OutcomeView

/-- Observed outcome law at a pure profile. -/
noncomputable def law {F : GameForm ι} (V : OutcomeView F Ω) (σ : F.Profile) : PMF Ω :=
  PMF.map V.observe (F.outcomeKernel σ)

/-- Observed outcome law induced by a profile distribution. -/
noncomputable def correlatedLaw {F : GameForm ι}
    (V : OutcomeView F Ω) (μ : PMF F.Profile) : PMF Ω :=
  PMF.map V.observe (F.correlatedOutcome μ)

@[simp] theorem law_eq_correlatedLaw_pure {F : GameForm ι}
    (V : OutcomeView F Ω) (σ : F.Profile) :
    V.law σ = V.correlatedLaw (PMF.pure σ) := by
  simp [law, correlatedLaw]

end OutcomeView

/-- Equality of observed outcome laws through two views. -/
def sameObservedLaw {G H : GameForm ι}
    (VG : OutcomeView G Ω) (VH : OutcomeView H Ω)
    (σ : G.Profile) (τ : H.Profile) : Prop :=
  VG.law σ = VH.law τ

/-- Lift preferences on observed outcome laws to preferences on a game form's
native outcome laws. -/
def observedPref {F : GameForm ι} (V : OutcomeView F Ω)
    (prefΩ : ι → PMF Ω → PMF Ω → Prop) :
    ι → PMF F.Outcome → PMF F.Outcome → Prop :=
  fun who d e => prefΩ who (PMF.map V.observe d) (PMF.map V.observe e)

/-- A relation saying that target profiles realize source profiles up to an
observed outcome law. The relation is intentionally not functional: many game
presentation bridges, including Kuhn-style realization relations, are
existential or many-to-many. -/
structure ProfileRealization (G H : GameForm ι) (Ω : Type) where
  viewG : OutcomeView G Ω
  viewH : OutcomeView H Ω
  rel : G.Profile → H.Profile → Prop
  law_eq : ∀ {σ : G.Profile} {τ : H.Profile}, rel σ τ →
    viewG.law σ = viewH.law τ

section Nash

variable [DecidableEq ι]

/-- One-way unilateral-deviation simulation.

To transfer Nash equilibrium from `G` to `H`, every unilateral deviation in
the target game `H` must be matched by some unilateral deviation in the source
game `G` with the same observed outcome law. -/
structure NashDeviationSimulation (G H : GameForm ι) (Ω : Type)
    extends ProfileRealization G H Ω where
  simulate_target_deviation :
    ∀ {σ : G.Profile} {τ : H.Profile}, rel σ τ →
    ∀ (who : ι) (sH : H.Strategy who),
      ∃ sG : G.Strategy who,
        viewG.law (Function.update σ who sG) =
          viewH.law (Function.update τ who sH)

/-- Transport Nash equilibrium along a one-way deviation simulation. -/
theorem NashDeviationSimulation.target_nash_of_source_nash
    {G H : GameForm ι} {Ω : Type}
    (S : NashDeviationSimulation G H Ω)
    {σ : G.Profile} {τ : H.Profile}
    (hrel : S.rel σ τ)
    {prefΩ : ι → PMF Ω → PMF Ω → Prop}
    (hN : G.IsNashFor (observedPref S.viewG prefΩ) σ) :
    H.IsNashFor (observedPref S.viewH prefΩ) τ := by
  classical
  refine (H.isNashFor_iff (observedPref S.viewH prefΩ) τ).2 ?_
  intro who sH
  rcases S.simulate_target_deviation hrel who sH with ⟨sG, hdev⟩
  have hsrc :=
    (G.isNashFor_iff (observedPref S.viewG prefΩ) σ).1 hN who sG
  have hsrc' :
      prefΩ who (S.viewG.law σ)
        (S.viewG.law (Function.update σ who sG)) := by
    simpa [observedPref, OutcomeView.law] using hsrc
  have hbase := S.law_eq hrel
  rw [hbase, hdev] at hsrc'
  simpa [observedPref, OutcomeView.law] using hsrc'

/-- Two-way unilateral-deviation simulation using a single profile-realization
relation and a single pair of observed views. -/
structure NashDeviationBisimulation (G H : GameForm ι) (Ω : Type)
    extends ProfileRealization G H Ω where
  simulate_target_deviation :
    ∀ {σ : G.Profile} {τ : H.Profile}, rel σ τ →
    ∀ (who : ι) (sH : H.Strategy who),
      ∃ sG : G.Strategy who,
        viewG.law (Function.update σ who sG) =
          viewH.law (Function.update τ who sH)
  simulate_source_deviation :
    ∀ {σ : G.Profile} {τ : H.Profile}, rel σ τ →
    ∀ (who : ι) (sG : G.Strategy who),
      ∃ sH : H.Strategy who,
        viewG.law (Function.update σ who sG) =
          viewH.law (Function.update τ who sH)

namespace NashDeviationBisimulation

/-- Forget a two-way simulation to the forward one-way simulation. -/
def toForwardSimulation {G H : GameForm ι} {Ω : Type}
    (S : NashDeviationBisimulation G H Ω) :
    NashDeviationSimulation G H Ω where
  toProfileRealization := S.toProfileRealization
  simulate_target_deviation := S.simulate_target_deviation

/-- Reverse a two-way simulation. -/
def toReverseSimulation {G H : GameForm ι} {Ω : Type}
    (S : NashDeviationBisimulation G H Ω) :
    NashDeviationSimulation H G Ω where
  viewG := S.viewH
  viewH := S.viewG
  rel := fun τ σ => S.rel σ τ
  law_eq := by
    intro τ σ hrel
    exact (S.law_eq hrel).symm
  simulate_target_deviation := by
    intro τ σ hrel who sG
    rcases S.simulate_source_deviation hrel who sG with ⟨sH, hdev⟩
    exact ⟨sH, hdev.symm⟩

/-- Nash equilibrium is invariant across a two-way deviation simulation. -/
theorem nash_iff {G H : GameForm ι} {Ω : Type}
    (S : NashDeviationBisimulation G H Ω)
    {σ : G.Profile} {τ : H.Profile}
    (hrel : S.rel σ τ)
    {prefΩ : ι → PMF Ω → PMF Ω → Prop} :
    G.IsNashFor (observedPref S.viewG prefΩ) σ ↔
      H.IsNashFor (observedPref S.viewH prefΩ) τ := by
  constructor
  · intro hN
    exact S.toForwardSimulation.target_nash_of_source_nash hrel hN
  · intro hN
    exact S.toReverseSimulation.target_nash_of_source_nash hrel hN

end NashDeviationBisimulation

end Nash

end GameForm

end GameTheory
