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

/-- A relation saying that target profile distributions realize source profile
distributions up to an observed outcome law. This is the right level for
deviation-family equilibrium notions such as correlated and coarse correlated
equilibrium. -/
structure ProfileDistributionRealization (G H : GameForm ι) (Ω : Type) where
  viewG : OutcomeView G Ω
  viewH : OutcomeView H Ω
  rel : PMF G.Profile → PMF H.Profile → Prop
  law_eq : ∀ {μG : PMF G.Profile} {μH : PMF H.Profile}, rel μG μH →
    viewG.correlatedLaw μG = viewH.correlatedLaw μH

/-- One-way simulation for arbitrary profile-deviation families.

To transport a deviation-family equilibrium from `G` to `H`, every allowed
target-side deviation in `H` must be matched by some allowed source-side
deviation in `G` with the same observed post-deviation outcome law. -/
structure DeviationFamilySimulation
    (G H : GameForm ι) (Ω : Type)
    (ΔG : ProfileDeviationFamily G) (ΔH : ProfileDeviationFamily H)
    extends ProfileDistributionRealization G H Ω where
  simulate_target_deviation :
    ∀ {μG : PMF G.Profile} {μH : PMF H.Profile}, rel μG μH →
    ∀ (who : ι) (dH : ΔH.Dev who),
      ∃ dG : ΔG.Dev who,
        viewG.correlatedLaw (ΔG.deviate μG who dG) =
          viewH.correlatedLaw (ΔH.deviate μH who dH)

/-- Transport a generic deviation-family equilibrium along a one-way
deviation-family simulation. -/
theorem DeviationFamilySimulation.target_eq_of_source_eq
    {G H : GameForm ι} {Ω : Type}
    {ΔG : ProfileDeviationFamily G} {ΔH : ProfileDeviationFamily H}
    (S : DeviationFamilySimulation G H Ω ΔG ΔH)
    {μG : PMF G.Profile} {μH : PMF H.Profile}
    (hrel : S.rel μG μH)
    {prefΩ : ι → PMF Ω → PMF Ω → Prop}
    (hEq : G.IsDeviationEqFamilyFor (observedPref S.viewG prefΩ) μG ΔG) :
    H.IsDeviationEqFamilyFor (observedPref S.viewH prefΩ) μH ΔH := by
  intro who dH
  rcases S.simulate_target_deviation hrel who dH with ⟨dG, hdev⟩
  have hsrc := hEq who dG
  have hsrc' :
      prefΩ who (S.viewG.correlatedLaw μG)
        (S.viewG.correlatedLaw (ΔG.deviate μG who dG)) := by
    simpa [observedPref, OutcomeView.correlatedLaw,
      NoProfitableProfileDeviationFor, NoProfitableDeviationFor] using hsrc
  have hbase := S.law_eq hrel
  rw [hbase, hdev] at hsrc'
  simpa [observedPref, OutcomeView.correlatedLaw,
    NoProfitableProfileDeviationFor, NoProfitableDeviationFor] using hsrc'

/-- Two-way simulation for arbitrary profile-deviation families. -/
structure DeviationFamilyBisimulation
    (G H : GameForm ι) (Ω : Type)
    (ΔG : ProfileDeviationFamily G) (ΔH : ProfileDeviationFamily H)
    extends ProfileDistributionRealization G H Ω where
  simulate_target_deviation :
    ∀ {μG : PMF G.Profile} {μH : PMF H.Profile}, rel μG μH →
    ∀ (who : ι) (dH : ΔH.Dev who),
      ∃ dG : ΔG.Dev who,
        viewG.correlatedLaw (ΔG.deviate μG who dG) =
          viewH.correlatedLaw (ΔH.deviate μH who dH)
  simulate_source_deviation :
    ∀ {μG : PMF G.Profile} {μH : PMF H.Profile}, rel μG μH →
    ∀ (who : ι) (dG : ΔG.Dev who),
      ∃ dH : ΔH.Dev who,
        viewG.correlatedLaw (ΔG.deviate μG who dG) =
          viewH.correlatedLaw (ΔH.deviate μH who dH)

namespace DeviationFamilyBisimulation

/-- Forget a two-way deviation-family simulation to the forward direction. -/
def toForwardSimulation
    {G H : GameForm ι} {Ω : Type}
    {ΔG : ProfileDeviationFamily G} {ΔH : ProfileDeviationFamily H}
    (S : DeviationFamilyBisimulation G H Ω ΔG ΔH) :
    DeviationFamilySimulation G H Ω ΔG ΔH where
  toProfileDistributionRealization := S.toProfileDistributionRealization
  simulate_target_deviation := S.simulate_target_deviation

/-- Reverse a two-way deviation-family simulation. -/
def toReverseSimulation
    {G H : GameForm ι} {Ω : Type}
    {ΔG : ProfileDeviationFamily G} {ΔH : ProfileDeviationFamily H}
    (S : DeviationFamilyBisimulation G H Ω ΔG ΔH) :
    DeviationFamilySimulation H G Ω ΔH ΔG where
  viewG := S.viewH
  viewH := S.viewG
  rel := fun μH μG => S.rel μG μH
  law_eq := by
    intro μH μG hrel
    exact (S.law_eq hrel).symm
  simulate_target_deviation := by
    intro μH μG hrel who dG
    rcases S.simulate_source_deviation hrel who dG with ⟨dH, hdev⟩
    exact ⟨dH, hdev.symm⟩

/-- A deviation-family equilibrium is invariant across a two-way
deviation-family simulation. -/
theorem eq_iff
    {G H : GameForm ι} {Ω : Type}
    {ΔG : ProfileDeviationFamily G} {ΔH : ProfileDeviationFamily H}
    (S : DeviationFamilyBisimulation G H Ω ΔG ΔH)
    {μG : PMF G.Profile} {μH : PMF H.Profile}
    (hrel : S.rel μG μH)
    {prefΩ : ι → PMF Ω → PMF Ω → Prop} :
    G.IsDeviationEqFamilyFor (observedPref S.viewG prefΩ) μG ΔG ↔
      H.IsDeviationEqFamilyFor (observedPref S.viewH prefΩ) μH ΔH := by
  constructor
  · intro hEq
    exact S.toForwardSimulation.target_eq_of_source_eq hrel hEq
  · intro hEq
    exact S.toReverseSimulation.target_eq_of_source_eq hrel hEq

end DeviationFamilyBisimulation

section CanonicalFamilies

variable [DecidableEq ι]

/-- View a Nash-specific deviation simulation as a simulation between the
constant-deviation profile families, restricted to point-mass profile
distributions. -/
noncomputable def NashDeviationSimulation.toConstantDeviationFamilySimulation
    {G H : GameForm ι} {Ω : Type}
    (S : NashDeviationSimulation G H Ω) :
    DeviationFamilySimulation G H Ω
      G.constantDeviationProfileFamily H.constantDeviationProfileFamily where
  viewG := S.viewG
  viewH := S.viewH
  rel := fun μG μH =>
    ∃ σ : G.Profile, ∃ τ : H.Profile,
      S.rel σ τ ∧ μG = PMF.pure σ ∧ μH = PMF.pure τ
  law_eq := by
    intro μG μH hrel
    rcases hrel with ⟨σ, τ, hστ, rfl, rfl⟩
    simpa [OutcomeView.correlatedLaw] using S.law_eq hστ
  simulate_target_deviation := by
    intro μG μH hrel who sH
    rcases hrel with ⟨σ, τ, hστ, rfl, rfl⟩
    rcases S.simulate_target_deviation hστ who sH with ⟨sG, hdev⟩
    refine ⟨sG, ?_⟩
    simpa [OutcomeView.correlatedLaw] using hdev

/-- Correlated-equilibrium transport as the recommendation-deviation-family
instance of the generic theorem. -/
theorem DeviationFamilySimulation.target_correlatedEq_of_source_correlatedEq
    {G H : GameForm ι} {Ω : Type}
    (S : DeviationFamilySimulation G H Ω
      G.recommendationDeviationFamily H.recommendationDeviationFamily)
    {μG : PMF G.Profile} {μH : PMF H.Profile}
    (hrel : S.rel μG μH)
    {prefΩ : ι → PMF Ω → PMF Ω → Prop}
    (hCE : G.IsCorrelatedEqFor (observedPref S.viewG prefΩ) μG) :
    H.IsCorrelatedEqFor (observedPref S.viewH prefΩ) μH :=
  S.target_eq_of_source_eq hrel hCE

/-- Coarse-correlated-equilibrium transport as the constant-deviation-family
instance of the generic theorem. -/
theorem DeviationFamilySimulation.target_coarseCorrelatedEq_of_source_coarseCorrelatedEq
    {G H : GameForm ι} {Ω : Type}
    (S : DeviationFamilySimulation G H Ω
      G.constantDeviationProfileFamily H.constantDeviationProfileFamily)
    {μG : PMF G.Profile} {μH : PMF H.Profile}
    (hrel : S.rel μG μH)
    {prefΩ : ι → PMF Ω → PMF Ω → Prop}
    (hCCE : G.IsCoarseCorrelatedEqFor (observedPref S.viewG prefΩ) μG) :
    H.IsCoarseCorrelatedEqFor (observedPref S.viewH prefΩ) μH :=
  S.target_eq_of_source_eq hrel hCCE

end CanonicalFamilies

end GameForm

end GameTheory
