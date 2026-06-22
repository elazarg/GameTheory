/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Equilibrium.SolutionConcepts

/-!
# GameTheory.Concepts.Foundations.DeviationSimulation

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

/-- Pointwise equal observed laws lift through a common recommendation distribution. -/
theorem correlatedLaw_map_eq_map_of_law_eq {α : Type} {G H : GameForm ι}
    (VG : OutcomeView G Ω) (VH : OutcomeView H Ω)
    (μ : PMF α) (source : α → G.Profile) (target : α → H.Profile)
    (law_eq : ∀ a, VG.law (source a) = VH.law (target a)) :
    VG.correlatedLaw (PMF.map source μ) = VH.correlatedLaw (PMF.map target μ) := by
  simpa [correlatedLaw, law, GameForm.correlatedOutcome,
    Math.Probability.Kernel.pushforward, PMF.map_bind, PMF.bind_map] using
    Math.ProbabilityMassFunction.bind_congr_on_support μ
      (fun a => PMF.map VG.observe (G.outcomeKernel (source a)))
      (fun a => PMF.map VH.observe (H.outcomeKernel (target a)))
      (fun a _ => law_eq a)

/-- A pointwise profile realization induces the same correlated observed law. -/
theorem correlatedLaw_map_of_law {G H : GameForm ι}
    (VG : OutcomeView G Ω) (VH : OutcomeView H Ω)
    (realize : G.Profile → H.Profile)
    (law_eq : ∀ σ, VG.law σ = VH.law (realize σ))
    (μ : PMF G.Profile) :
    VG.correlatedLaw μ = VH.correlatedLaw (PMF.map realize μ) := by
  have h := correlatedLaw_map_eq_map_of_law_eq VG VH μ id realize law_eq
  rwa [PMF.map_id] at h

/-- Pointwise law equality after profile transforms lifts to correlated laws. -/
theorem correlatedLaw_bind_profile_map_of_law {G H : GameForm ι}
    (VG : OutcomeView G Ω) (VH : OutcomeView H Ω)
    (realize : G.Profile → H.Profile)
    (source : G.Profile → G.Profile) (target : H.Profile → H.Profile)
    (law_eq : ∀ σ, VG.law (source σ) = VH.law (target (realize σ)))
    (μ : PMF G.Profile) :
    VG.correlatedLaw (μ.bind (fun σ => PMF.pure (source σ))) =
      VH.correlatedLaw ((PMF.map realize μ).bind (fun τ => PMF.pure (target τ))) := by
  change VG.correlatedLaw (μ.bind (PMF.pure ∘ source)) =
    VH.correlatedLaw ((PMF.map realize μ).bind (PMF.pure ∘ target))
  have hsource :
      μ.bind (PMF.pure ∘ source) = PMF.map source μ :=
    PMF.bind_pure_comp source μ
  have htarget :
      (PMF.map realize μ).bind (PMF.pure ∘ target) =
        PMF.map (target ∘ realize) μ := by
    calc
      (PMF.map realize μ).bind (PMF.pure ∘ target)
          = PMF.map target (PMF.map realize μ) := by
              exact PMF.bind_pure_comp target (PMF.map realize μ)
      _ = PMF.map (target ∘ realize) μ := by
              exact PMF.map_comp realize μ target
  calc
    VG.correlatedLaw (μ.bind (PMF.pure ∘ source))
        = VG.correlatedLaw (PMF.map source μ) := by rw [hsource]
    _ = VH.correlatedLaw (PMF.map (target ∘ realize) μ) :=
        correlatedLaw_map_eq_map_of_law_eq VG VH μ source (target ∘ realize) law_eq
    _ = VH.correlatedLaw ((PMF.map realize μ).bind (PMF.pure ∘ target)) := by
        rw [htarget]

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

/-- Expected-utility preference over a common observed outcome carrier. -/
noncomputable def observedEuPref (uΩ : Ω → Payoff ι) :
    ι → PMF Ω → PMF Ω → Prop :=
  fun who d e =>
    expect d (fun ω => uΩ ω who) ≥ expect e (fun ω => uΩ ω who)

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

namespace ProfileRealization

/-- Build a profile-realization relation from a functional realization map. -/
def ofFunctionalRealization
    {G H : GameForm ι} {Ω : Type}
    (viewG : OutcomeView G Ω) (viewH : OutcomeView H Ω)
    (realize : G.Profile → H.Profile)
    (law_eq : ∀ σ, viewG.law σ = viewH.law (realize σ)) :
    ProfileRealization G H Ω where
  viewG := viewG
  viewH := viewH
  rel := fun σ τ => τ = realize σ
  law_eq := by
    intro σ τ hrel
    subst τ
    exact law_eq σ

end ProfileRealization

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

namespace NashDeviationSimulation

/-- Reflexive deviation simulation for a fixed observed view. -/
def refl {G : GameForm ι} (view : OutcomeView G Ω) :
    NashDeviationSimulation G G Ω where
  viewG := view
  viewH := view
  rel := fun σ τ => σ = τ
  law_eq := by
    intro σ τ hrel
    subst τ
    rfl
  simulate_target_deviation := by
    intro σ τ hrel who sG
    subst τ
    exact ⟨sG, rfl⟩

/-- Identity deviation simulation for a fixed observed view. -/
abbrev id {G : GameForm ι} (view : OutcomeView G Ω) :
    NashDeviationSimulation G G Ω :=
  refl view

/-- Compose one-way deviation simulations whose middle observed views induce
the same laws on every middle-game profile. Applies `S` first, then `T`. -/
def comp {G H K : GameForm ι}
    (T : NashDeviationSimulation H K Ω) (S : NashDeviationSimulation G H Ω)
    (hmid : ∀ τ : H.Profile, S.viewH.law τ = T.viewG.law τ) :
    NashDeviationSimulation G K Ω where
  viewG := S.viewG
  viewH := T.viewH
  rel := fun σ ρ => ∃ τ : H.Profile, S.rel σ τ ∧ T.rel τ ρ
  law_eq := by
    intro σ ρ hrel
    rcases hrel with ⟨τ, hS, hT⟩
    exact (S.law_eq hS).trans ((hmid τ).trans (T.law_eq hT))
  simulate_target_deviation := by
    intro σ ρ hrel who sK
    rcases hrel with ⟨τ, hS, hT⟩
    rcases T.simulate_target_deviation hT who sK with ⟨sH, hdevT⟩
    rcases S.simulate_target_deviation hS who sH with ⟨sG, hdevS⟩
    exact ⟨sG, hdevS.trans ((hmid (Function.update τ who sH)).trans hdevT)⟩

/-- Build a one-way deviation simulation from a functional realization map.

This is the common case for compiler and language bridges: every source
profile has a canonical target realization, and target-side unilateral
deviations can be matched by source-side unilateral deviations. -/
def ofFunctionalRealization
    {G H : GameForm ι} {Ω : Type}
    (viewG : OutcomeView G Ω) (viewH : OutcomeView H Ω)
    (realize : G.Profile → H.Profile)
    (law_eq : ∀ σ, viewG.law σ = viewH.law (realize σ))
    (simulate_target_deviation :
      ∀ (σ : G.Profile) (who : ι) (sH : H.Strategy who),
        ∃ sG : G.Strategy who,
          viewG.law (Function.update σ who sG) =
            viewH.law (Function.update (realize σ) who sH)) :
    NashDeviationSimulation G H Ω where
  toProfileRealization :=
    ProfileRealization.ofFunctionalRealization viewG viewH realize law_eq
  simulate_target_deviation := by
    intro σ τ hrel who sH
    subst τ
    exact simulate_target_deviation σ who sH

end NashDeviationSimulation

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

/-- Reflexive two-way deviation simulation for a fixed observed view. -/
def refl {G : GameForm ι} (view : OutcomeView G Ω) :
    NashDeviationBisimulation G G Ω where
  viewG := view
  viewH := view
  rel := fun σ τ => σ = τ
  law_eq := by
    intro σ τ hrel
    subst τ
    rfl
  simulate_target_deviation := by
    intro σ τ hrel who sG
    subst τ
    exact ⟨sG, rfl⟩
  simulate_source_deviation := by
    intro σ τ hrel who sG
    subst τ
    exact ⟨sG, rfl⟩

/-- Identity two-way deviation simulation for a fixed observed view. -/
abbrev id {G : GameForm ι} (view : OutcomeView G Ω) :
    NashDeviationBisimulation G G Ω :=
  refl view

/-- Forget a two-way simulation to the forward one-way simulation. -/
def toForwardSimulation {G H : GameForm ι} {Ω : Type}
    (S : NashDeviationBisimulation G H Ω) :
    NashDeviationSimulation G H Ω where
  toProfileRealization := S.toProfileRealization
  simulate_target_deviation := S.simulate_target_deviation

/-- Reverse a two-way deviation simulation. -/
def symm {G H : GameForm ι} {Ω : Type}
    (S : NashDeviationBisimulation G H Ω) :
    NashDeviationBisimulation H G Ω where
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
  simulate_source_deviation := by
    intro τ σ hrel who sH
    rcases S.simulate_target_deviation hrel who sH with ⟨sG, hdev⟩
    exact ⟨sG, hdev.symm⟩

/-- Reverse a two-way simulation. -/
def toReverseSimulation {G H : GameForm ι} {Ω : Type}
    (S : NashDeviationBisimulation G H Ω) :
    NashDeviationSimulation H G Ω :=
  (S.symm).toForwardSimulation

/-- Compose two-way deviation simulations whose middle observed views induce
the same laws on every middle-game profile. Applies `S` first, then `T`. -/
def comp {G H K : GameForm ι} {Ω : Type}
    (T : NashDeviationBisimulation H K Ω) (S : NashDeviationBisimulation G H Ω)
    (hmid : ∀ τ : H.Profile, S.viewH.law τ = T.viewG.law τ) :
    NashDeviationBisimulation G K Ω where
  viewG := S.viewG
  viewH := T.viewH
  rel := fun σ ρ => ∃ τ : H.Profile, S.rel σ τ ∧ T.rel τ ρ
  law_eq := by
    intro σ ρ hrel
    rcases hrel with ⟨τ, hS, hT⟩
    exact (S.law_eq hS).trans ((hmid τ).trans (T.law_eq hT))
  simulate_target_deviation := by
    intro σ ρ hrel who sK
    rcases hrel with ⟨τ, hS, hT⟩
    rcases T.simulate_target_deviation hT who sK with ⟨sH, hdevT⟩
    rcases S.simulate_target_deviation hS who sH with ⟨sG, hdevS⟩
    exact ⟨sG, hdevS.trans ((hmid (Function.update τ who sH)).trans hdevT)⟩
  simulate_source_deviation := by
    intro σ ρ hrel who sG
    rcases hrel with ⟨τ, hS, hT⟩
    rcases S.simulate_source_deviation hS who sG with ⟨sH, hdevS⟩
    rcases T.simulate_source_deviation hT who sH with ⟨sK, hdevT⟩
    exact ⟨sK, hdevS.trans ((hmid (Function.update τ who sH)).trans hdevT)⟩

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

namespace ProfileDistributionRealization

/-- Build a profile-distribution realization relation from a functional
realization map on profile distributions. -/
def ofFunctionalRealization
    {G H : GameForm ι} {Ω : Type}
    (viewG : OutcomeView G Ω) (viewH : OutcomeView H Ω)
    (realize : PMF G.Profile → PMF H.Profile)
    (law_eq : ∀ μ, viewG.correlatedLaw μ = viewH.correlatedLaw (realize μ)) :
    ProfileDistributionRealization G H Ω where
  viewG := viewG
  viewH := viewH
  rel := fun μG μH => μH = realize μG
  law_eq := by
    intro μG μH hrel
    subst μH
    exact law_eq μG

/-- Build a profile-distribution realization from a pointwise profile map. -/
noncomputable def ofProfileMap
    {G H : GameForm ι} {Ω : Type}
    (viewG : OutcomeView G Ω) (viewH : OutcomeView H Ω)
    (realize : G.Profile → H.Profile)
    (law_eq : ∀ σ, viewG.law σ = viewH.law (realize σ)) :
    ProfileDistributionRealization G H Ω :=
  ofFunctionalRealization viewG viewH (PMF.map realize)
    (OutcomeView.correlatedLaw_map_of_law viewG viewH realize law_eq)

end ProfileDistributionRealization

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

namespace DeviationFamilySimulation

/-- Build a one-way deviation-family simulation from a functional realization
map on profile distributions. -/
def ofFunctionalRealization
    {G H : GameForm ι} {Ω : Type}
    {ΔG : ProfileDeviationFamily G} {ΔH : ProfileDeviationFamily H}
    (viewG : OutcomeView G Ω) (viewH : OutcomeView H Ω)
    (realize : PMF G.Profile → PMF H.Profile)
    (law_eq : ∀ μ, viewG.correlatedLaw μ = viewH.correlatedLaw (realize μ))
    (simulate_target_deviation :
      ∀ (μG : PMF G.Profile) (who : ι) (dH : ΔH.Dev who),
        ∃ dG : ΔG.Dev who,
          viewG.correlatedLaw (ΔG.deviate μG who dG) =
            viewH.correlatedLaw (ΔH.deviate (realize μG) who dH)) :
    DeviationFamilySimulation G H Ω ΔG ΔH where
  toProfileDistributionRealization :=
    ProfileDistributionRealization.ofFunctionalRealization viewG viewH realize law_eq
  simulate_target_deviation := by
    intro μG μH hrel who dH
    subst μH
    exact simulate_target_deviation μG who dH

end DeviationFamilySimulation

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

/-- Build a constant-deviation-family simulation from a pointwise profile map. -/
noncomputable def DeviationFamilySimulation.ofConstantProfileMap
    {G H : GameForm ι} {Ω : Type}
    (viewG : OutcomeView G Ω) (viewH : OutcomeView H Ω)
    (realize : G.Profile → H.Profile)
    (law_eq : ∀ σ, viewG.law σ = viewH.law (realize σ))
    (simulate_target_deviation :
      ∀ (who : ι) (sH : H.Strategy who),
        ∃ sG : G.Strategy who,
          ∀ σ : G.Profile,
            viewG.law (Function.update σ who sG) =
              viewH.law (Function.update (realize σ) who sH)) :
    DeviationFamilySimulation G H Ω
      G.constantDeviationProfileFamily H.constantDeviationProfileFamily where
  toProfileDistributionRealization :=
    ProfileDistributionRealization.ofProfileMap viewG viewH realize law_eq
  simulate_target_deviation := by
    intro μG μH hrel who sH
    subst μH
    rcases simulate_target_deviation who sH with ⟨sG, hdev⟩
    refine ⟨sG, ?_⟩
    simpa [ProfileDistributionRealization.ofProfileMap,
      ProfileDistributionRealization.ofFunctionalRealization,
      GameForm.constantDeviationProfileFamily_deviate,
      GameForm.constDeviateDistributionFn] using
      OutcomeView.correlatedLaw_bind_profile_map_of_law
        viewG viewH realize
        (fun σ => Function.update σ who sG)
        (fun τ => Function.update τ who sH) hdev μG

/-- Build a recommendation-deviation-family simulation from a pointwise profile map. -/
noncomputable def DeviationFamilySimulation.ofRecommendationProfileMap
    {G H : GameForm ι} {Ω : Type}
    (viewG : OutcomeView G Ω) (viewH : OutcomeView H Ω)
    (realize : G.Profile → H.Profile)
    (law_eq : ∀ σ, viewG.law σ = viewH.law (realize σ))
    (simulate_target_deviation :
      ∀ (who : ι) (dH : H.Strategy who → H.Strategy who),
        ∃ dG : G.Strategy who → G.Strategy who,
          ∀ σ : G.Profile,
            viewG.law (G.deviateProfileFn σ who dG) =
              viewH.law (H.deviateProfileFn (realize σ) who dH)) :
    DeviationFamilySimulation G H Ω
      G.recommendationDeviationFamily H.recommendationDeviationFamily where
  toProfileDistributionRealization :=
    ProfileDistributionRealization.ofProfileMap viewG viewH realize law_eq
  simulate_target_deviation := by
    intro μG μH hrel who dH
    subst μH
    rcases simulate_target_deviation who dH with ⟨dG, hdev⟩
    refine ⟨dG, ?_⟩
    simpa [ProfileDistributionRealization.ofProfileMap,
      ProfileDistributionRealization.ofFunctionalRealization,
      GameForm.recommendationDeviationFamily_deviate,
      GameForm.deviateDistributionFn] using
      OutcomeView.correlatedLaw_bind_profile_map_of_law
        viewG viewH realize
        (fun σ => G.deviateProfileFn σ who dG)
        (fun τ => H.deviateProfileFn τ who dH) hdev μG

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

namespace KernelGame

variable {ι Ω : Type}

/-- Kernel-game convenience alias for outcome views on the underlying game form. -/
abbrev OutcomeView (G : KernelGame ι) (Ω : Type) :=
  GameForm.OutcomeView G.toGameForm Ω

/-- Kernel-game convenience alias for profile realizations on underlying game forms. -/
abbrev ProfileRealization (G H : KernelGame ι) (Ω : Type) :=
  GameForm.ProfileRealization G.toGameForm H.toGameForm Ω

/-- Kernel-game wrapper for the functional profile-realization constructor. -/
def ProfileRealization.ofFunctionalRealization
    {G H : KernelGame ι} {Ω : Type}
    (viewG : OutcomeView G Ω) (viewH : OutcomeView H Ω)
    (realize : G.Profile → H.Profile)
    (law_eq : ∀ σ, viewG.law σ = viewH.law (realize σ)) :
    ProfileRealization G H Ω :=
  GameForm.ProfileRealization.ofFunctionalRealization viewG viewH realize law_eq

/-- Kernel-game convenience alias for Nash deviation simulations on underlying
game forms. -/
abbrev NashDeviationSimulation (G H : KernelGame ι) (Ω : Type) [DecidableEq ι] :=
  GameForm.NashDeviationSimulation G.toGameForm H.toGameForm Ω

/-- Kernel-game convenience alias for Nash deviation bisimulations on
underlying game forms. -/
abbrev NashDeviationBisimulation (G H : KernelGame ι) (Ω : Type) [DecidableEq ι] :=
  GameForm.NashDeviationBisimulation G.toGameForm H.toGameForm Ω

/-- Kernel-game convenience alias for profile-deviation families on the
underlying game form. -/
abbrev ProfileDeviationFamily (G : KernelGame ι) :=
  GameForm.ProfileDeviationFamily G.toGameForm

/-- Kernel-game convenience wrapper for generic deviation-family equilibrium. -/
def IsDeviationEqFamilyFor (G : KernelGame ι)
    (pref : ι → PMF G.Outcome → PMF G.Outcome → Prop)
    (μ : PMF G.Profile) (Δ : ProfileDeviationFamily G) : Prop :=
  G.toGameForm.IsDeviationEqFamilyFor pref μ Δ

/-- Kernel-game convenience alias for profile-distribution realizations on
underlying game forms. -/
abbrev ProfileDistributionRealization (G H : KernelGame ι) (Ω : Type) :=
  GameForm.ProfileDistributionRealization G.toGameForm H.toGameForm Ω

/-- Kernel-game wrapper for the functional profile-distribution realization
constructor. -/
def ProfileDistributionRealization.ofFunctionalRealization
    {G H : KernelGame ι} {Ω : Type}
    (viewG : OutcomeView G Ω) (viewH : OutcomeView H Ω)
    (realize : PMF G.Profile → PMF H.Profile)
    (law_eq : ∀ μ, viewG.correlatedLaw μ = viewH.correlatedLaw (realize μ)) :
    ProfileDistributionRealization G H Ω :=
  GameForm.ProfileDistributionRealization.ofFunctionalRealization
    viewG viewH realize law_eq

/-- Kernel-game convenience alias for deviation-family simulations on
underlying game forms. -/
abbrev DeviationFamilySimulation
    (G H : KernelGame ι) (Ω : Type)
    (ΔG : ProfileDeviationFamily G) (ΔH : ProfileDeviationFamily H) :=
  GameForm.DeviationFamilySimulation G.toGameForm H.toGameForm Ω ΔG ΔH

section Nash

variable [DecidableEq ι]

/-- Kernel-game reflexive deviation simulation for a fixed observed view. -/
def NashDeviationSimulation.refl
    {G : KernelGame ι} {Ω : Type} (view : OutcomeView G Ω) :
    NashDeviationSimulation G G Ω :=
  GameForm.NashDeviationSimulation.refl view

/-- Kernel-game identity deviation simulation for a fixed observed view. -/
abbrev NashDeviationSimulation.id
    {G : KernelGame ι} {Ω : Type} (view : OutcomeView G Ω) :
    NashDeviationSimulation G G Ω :=
  GameForm.NashDeviationSimulation.id view

/-- Kernel-game composition of one-way deviation simulations whose middle
observed views induce the same laws on every middle-game profile. Applies `S`
first, then `T`. -/
def NashDeviationSimulation.comp
    {G H K : KernelGame ι} {Ω : Type}
    (T : NashDeviationSimulation H K Ω) (S : NashDeviationSimulation G H Ω)
    (hmid : ∀ τ : H.Profile, S.viewH.law τ = T.viewG.law τ) :
    NashDeviationSimulation G K Ω :=
  GameForm.NashDeviationSimulation.comp T S hmid

/-- Kernel-game wrapper for the functional-realization constructor. -/
def NashDeviationSimulation.ofFunctionalRealization
    {G H : KernelGame ι} {Ω : Type}
    (viewG : OutcomeView G Ω) (viewH : OutcomeView H Ω)
    (realize : G.Profile → H.Profile)
    (law_eq : ∀ σ, viewG.law σ = viewH.law (realize σ))
    (simulate_target_deviation :
      ∀ (σ : G.Profile) (who : ι) (sH : H.Strategy who),
        ∃ sG : G.Strategy who,
          viewG.law (Function.update σ who sG) =
            viewH.law (Function.update (realize σ) who sH)) :
    NashDeviationSimulation G H Ω :=
  GameForm.NashDeviationSimulation.ofFunctionalRealization
    viewG viewH realize law_eq simulate_target_deviation

/-- Kernel-game reflexive two-way deviation simulation for a fixed observed
view. -/
def NashDeviationBisimulation.refl
    {G : KernelGame ι} {Ω : Type} (view : OutcomeView G Ω) :
    NashDeviationBisimulation G G Ω :=
  GameForm.NashDeviationBisimulation.refl view

/-- Kernel-game identity two-way deviation simulation for a fixed observed
view. -/
abbrev NashDeviationBisimulation.id
    {G : KernelGame ι} {Ω : Type} (view : OutcomeView G Ω) :
    NashDeviationBisimulation G G Ω :=
  GameForm.NashDeviationBisimulation.id view

/-- Forget a kernel-game two-way deviation simulation to the forward direction. -/
def NashDeviationBisimulation.toForwardSimulation
    {G H : KernelGame ι} {Ω : Type}
    (S : NashDeviationBisimulation G H Ω) :
    NashDeviationSimulation G H Ω :=
  GameForm.NashDeviationBisimulation.toForwardSimulation S

/-- Reverse a kernel-game two-way deviation simulation. -/
def NashDeviationBisimulation.symm
    {G H : KernelGame ι} {Ω : Type}
    (S : NashDeviationBisimulation G H Ω) :
    NashDeviationBisimulation H G Ω :=
  GameForm.NashDeviationBisimulation.symm S

/-- Forget a kernel-game two-way deviation simulation to the reverse
direction. -/
def NashDeviationBisimulation.toReverseSimulation
    {G H : KernelGame ι} {Ω : Type}
    (S : NashDeviationBisimulation G H Ω) :
    NashDeviationSimulation H G Ω :=
  GameForm.NashDeviationBisimulation.toReverseSimulation S

/-- Kernel-game composition of two-way deviation simulations whose middle
observed views induce the same laws on every middle-game profile. Applies `S`
first, then `T`. -/
def NashDeviationBisimulation.comp
    {G H K : KernelGame ι} {Ω : Type}
    (T : NashDeviationBisimulation H K Ω) (S : NashDeviationBisimulation G H Ω)
    (hmid : ∀ τ : H.Profile, S.viewH.law τ = T.viewG.law τ) :
    NashDeviationBisimulation G K Ω :=
  GameForm.NashDeviationBisimulation.comp T S hmid

/-- Kernel-game wrapper for preference-parametric Nash transport. -/
theorem NashDeviationSimulation.target_nashFor_of_source_nashFor
    {G H : KernelGame ι} {Ω : Type}
    (S : NashDeviationSimulation G H Ω)
    {σ : G.Profile} {τ : H.Profile}
    (hrel : S.rel σ τ)
    {prefΩ : ι → PMF Ω → PMF Ω → Prop}
    (hN : G.IsNashFor (GameForm.observedPref S.viewG prefΩ) σ) :
    H.IsNashFor (GameForm.observedPref S.viewH prefΩ) τ :=
  GameForm.NashDeviationSimulation.target_nash_of_source_nash S hrel hN

/-- Kernel-game preference-parametric Nash invariance across a two-way
deviation simulation. -/
theorem NashDeviationBisimulation.nashFor_iff
    {G H : KernelGame ι} {Ω : Type}
    (S : NashDeviationBisimulation G H Ω)
    {σ : G.Profile} {τ : H.Profile}
    (hrel : S.rel σ τ)
    {prefΩ : ι → PMF Ω → PMF Ω → Prop} :
    G.IsNashFor (GameForm.observedPref S.viewG prefΩ) σ ↔
      H.IsNashFor (GameForm.observedPref S.viewH prefΩ) τ :=
  GameForm.NashDeviationBisimulation.nash_iff S hrel

/-- EU Nash transport when both games' EU preferences are compatible with the
same observed-law preference. The compatibility assumptions are intentionally
explicit, so the distribution-level transport theorem itself remains independent
of finiteness or expected-utility representation choices. -/
theorem NashDeviationSimulation.target_isNash_of_source_isNash
    {G H : KernelGame ι} {Ω : Type}
    (S : NashDeviationSimulation G H Ω)
    {σ : G.Profile} {τ : H.Profile}
    (hrel : S.rel σ τ)
    {prefΩ : ι → PMF Ω → PMF Ω → Prop}
    (hprefG : ∀ who d e,
      G.euPref who d e → GameForm.observedPref S.viewG prefΩ who d e)
    (hprefH : ∀ who d e,
      GameForm.observedPref S.viewH prefΩ who d e → H.euPref who d e)
    (hN : G.IsNash σ) :
    H.IsNash τ := by
  have hNForEu : G.IsNashFor G.euPref σ :=
    (G.IsNash_iff_IsNashFor_eu σ).1 hN
  have hNForObserved :
      G.IsNashFor (GameForm.observedPref S.viewG prefΩ) σ :=
    GameForm.IsNashFor.mono
      (F := G.toGameForm)
      (pref₁ := GameForm.observedPref S.viewG prefΩ)
      (pref₂ := G.euPref)
      hprefG hNForEu
  have hTargetObserved :
      H.IsNashFor (GameForm.observedPref S.viewH prefΩ) τ :=
    S.target_nashFor_of_source_nashFor hrel hNForObserved
  have hTargetEu : H.IsNashFor H.euPref τ :=
    GameForm.IsNashFor.mono
      (F := H.toGameForm)
      (pref₁ := H.euPref)
      (pref₂ := GameForm.observedPref S.viewH prefΩ)
      hprefH hTargetObserved
  exact (H.IsNash_iff_IsNashFor_eu τ).2 hTargetEu

end Nash

section DeviationFamilies

/-- Kernel-game wrapper for the functional deviation-family simulation
constructor. -/
def DeviationFamilySimulation.ofFunctionalRealization
    {G H : KernelGame ι} {Ω : Type}
    {ΔG : ProfileDeviationFamily G} {ΔH : ProfileDeviationFamily H}
    (viewG : OutcomeView G Ω) (viewH : OutcomeView H Ω)
    (realize : PMF G.Profile → PMF H.Profile)
    (law_eq : ∀ μ, viewG.correlatedLaw μ = viewH.correlatedLaw (realize μ))
    (simulate_target_deviation :
      ∀ (μG : PMF G.Profile) (who : ι) (dH : ΔH.Dev who),
        ∃ dG : ΔG.Dev who,
          viewG.correlatedLaw (ΔG.deviate μG who dG) =
            viewH.correlatedLaw (ΔH.deviate (realize μG) who dH)) :
    DeviationFamilySimulation G H Ω ΔG ΔH :=
  GameForm.DeviationFamilySimulation.ofFunctionalRealization
    viewG viewH realize law_eq simulate_target_deviation

/-- Kernel-game wrapper for generic deviation-family equilibrium transport. -/
theorem DeviationFamilySimulation.target_eqFor_of_source_eqFor
    {G H : KernelGame ι} {Ω : Type}
    {ΔG : ProfileDeviationFamily G} {ΔH : ProfileDeviationFamily H}
    (S : DeviationFamilySimulation G H Ω ΔG ΔH)
    {μG : PMF G.Profile} {μH : PMF H.Profile}
    (hrel : S.rel μG μH)
    {prefΩ : ι → PMF Ω → PMF Ω → Prop}
    (hEq : G.IsDeviationEqFamilyFor (GameForm.observedPref S.viewG prefΩ) μG ΔG) :
    H.IsDeviationEqFamilyFor (GameForm.observedPref S.viewH prefΩ) μH ΔH :=
  GameForm.DeviationFamilySimulation.target_eq_of_source_eq S hrel hEq

variable [DecidableEq ι]

/-- Kernel-game wrapper for correlated-equilibrium transport. -/
theorem DeviationFamilySimulation.target_correlatedEqFor_of_source_correlatedEqFor
    {G H : KernelGame ι} {Ω : Type}
    (S : DeviationFamilySimulation G H Ω
      G.toGameForm.recommendationDeviationFamily H.toGameForm.recommendationDeviationFamily)
    {μG : PMF G.Profile} {μH : PMF H.Profile}
    (hrel : S.rel μG μH)
    {prefΩ : ι → PMF Ω → PMF Ω → Prop}
    (hCE : G.IsCorrelatedEqFor (GameForm.observedPref S.viewG prefΩ) μG) :
    H.IsCorrelatedEqFor (GameForm.observedPref S.viewH prefΩ) μH :=
  GameForm.DeviationFamilySimulation.target_correlatedEq_of_source_correlatedEq S hrel hCE

/-- Kernel-game wrapper for coarse-correlated-equilibrium transport. -/
theorem DeviationFamilySimulation.target_coarseCorrelatedEqFor_of_source_coarseCorrelatedEqFor
    {G H : KernelGame ι} {Ω : Type}
    (S : DeviationFamilySimulation G H Ω
      G.toGameForm.constantDeviationProfileFamily H.toGameForm.constantDeviationProfileFamily)
    {μG : PMF G.Profile} {μH : PMF H.Profile}
    (hrel : S.rel μG μH)
    {prefΩ : ι → PMF Ω → PMF Ω → Prop}
    (hCCE : G.IsCoarseCorrelatedEqFor (GameForm.observedPref S.viewG prefΩ) μG) :
    H.IsCoarseCorrelatedEqFor (GameForm.observedPref S.viewH prefΩ) μH :=
  GameForm.DeviationFamilySimulation.target_coarseCorrelatedEq_of_source_coarseCorrelatedEq
    S hrel hCCE

end DeviationFamilies

end KernelGame

namespace GameForm

namespace DeviationSimulationExamples

/-- A one-player toy form whose outcome is the chosen Boolean strategy. -/
noncomputable def boolOutcomeForm : GameForm Unit where
  Strategy := fun _ => Bool
  Outcome := Bool
  outcomeKernel := fun σ => PMF.pure (σ ())

/-- The same observed behavior with a richer trace-like outcome carrier. -/
noncomputable def tracedOutcomeForm : GameForm Unit where
  Strategy := fun _ => Bool
  Outcome := Bool × Unit
  outcomeKernel := fun σ => PMF.pure (σ (), ())

/-- Observe the direct Boolean outcome. -/
def boolOutcomeView : OutcomeView boolOutcomeForm Bool where
  observe := id

/-- Observe only the Boolean component of the richer trace outcome. -/
def tracedOutcomeView : OutcomeView tracedOutcomeForm Bool where
  observe := Prod.fst

/-- The richer-trace form simulates the direct form for unilateral deviations:
target deviations are matched by the same Boolean source deviation. -/
def boolToTracedNashSimulation :
    NashDeviationSimulation boolOutcomeForm tracedOutcomeForm Bool where
  viewG := boolOutcomeView
  viewH := tracedOutcomeView
  rel := fun σ τ => σ () = τ ()
  law_eq := by
    intro σ τ hrel
    simp [OutcomeView.law, boolOutcomeView, tracedOutcomeView,
      boolOutcomeForm, tracedOutcomeForm, hrel, PMF.pure_map]
  simulate_target_deviation := by
    intro σ τ hrel who sH
    refine ⟨sH, ?_⟩
    cases who
    simp [OutcomeView.law, boolOutcomeView, tracedOutcomeView,
      boolOutcomeForm, tracedOutcomeForm, PMF.pure_map]

example {σ : boolOutcomeForm.Profile} {τ : tracedOutcomeForm.Profile}
    (hrel : boolToTracedNashSimulation.rel σ τ) :
    sameObservedLaw boolOutcomeView tracedOutcomeView σ τ :=
  boolToTracedNashSimulation.law_eq hrel

example {σ : boolOutcomeForm.Profile} {τ : tracedOutcomeForm.Profile}
    (hrel : boolToTracedNashSimulation.rel σ τ)
    {prefΩ : Unit → PMF Bool → PMF Bool → Prop}
    (hN : boolOutcomeForm.IsNashFor
      (observedPref boolToTracedNashSimulation.viewG prefΩ) σ) :
    tracedOutcomeForm.IsNashFor
      (observedPref boolToTracedNashSimulation.viewH prefΩ) τ :=
  boolToTracedNashSimulation.target_nash_of_source_nash hrel hN

end DeviationSimulationExamples

end GameForm

end GameTheory
