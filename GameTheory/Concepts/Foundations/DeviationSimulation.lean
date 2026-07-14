/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Equilibrium.SolutionConcepts
import GameTheory.Concepts.Foundations.Transport.Transfer

/-!
# The pure-profile Nash corner of transport

The general transport theory lives in `Concepts/Foundations/Transport/`:
`ViewFamily` and `observedPref` in `Transport.View`, `Realization`/`Simulates`/
`Transport` in `Transport.Simulation`, and the generic transfer theorem in
`Transport.Transfer`.

This file specializes that theory to the corners phrased over pure strategy
profiles and unilateral replacement, where they read most naturally:

* `NashDeviationSimulation` — a constant-view realization on point-mass profile
  distributions with the constant-deviation family, matching every target-side
  unilateral pure replacement. Nash transport (`target_nash_of_source_nash`) is
  an instantiation of the generic transfer theorem at the constant-deviation
  family evaluated at a point mass, since `IsNashFor` unfolds to exactly that.
* `Transport.ofConstantProfileMap` / `ofRecommendationProfileMap` — the
  coarse-correlated and correlated corners, building a `Transport` at the
  constant- and recommendation-deviation families from a pointwise profile map.
-/

namespace GameTheory

open Math.Probability

namespace GameForm

variable {ι : Type}

section Nash

variable [DecidableEq ι] {Ω : Type}

/-- One-way unilateral-deviation simulation on a constant observed view.

To transfer Nash equilibrium from `G` to `H`, every unilateral deviation in the
target game `H` must be matched by some unilateral deviation in the source game
`G` with the same observed outcome law. -/
structure NashDeviationSimulation (G H : GameForm ι) (Ω : Type) where
  /-- The source game's observed view (a single carrier shared across players). -/
  viewG : ViewFamily G ι (fun _ => Ω)
  /-- The target game's observed view. -/
  viewH : ViewFamily H ι (fun _ => Ω)
  /-- Which source profiles are matched to which target profiles. -/
  rel : G.Profile → H.Profile → Prop
  /-- Related profiles share the observed outcome law at every player. -/
  law_eq : ∀ {σ : G.Profile} {τ : H.Profile}, rel σ τ →
    ∀ i, viewG.plaw i σ = viewH.plaw i τ
  /-- Every target-side unilateral deviation is matched by a source-side one. -/
  simulate_target_deviation :
    ∀ {σ : G.Profile} {τ : H.Profile}, rel σ τ →
    ∀ (who : ι) (sH : H.Strategy who),
      ∃ sG : G.Strategy who,
        viewG.plaw who (Function.update σ who sG) =
          viewH.plaw who (Function.update τ who sH)

namespace NashDeviationSimulation

variable {G H : GameForm ι}

/-- The transport of a Nash simulation: a constant-deviation-family transport on
the point-mass profile distributions. -/
noncomputable def toTransport (S : NashDeviationSimulation G H Ω) :
    Transport G H S.viewG S.viewH
      G.constantDeviationProfileFamily H.constantDeviationProfileFamily where
  rel := fun μG μH => ∃ σ τ, S.rel σ τ ∧ μG = PMF.pure σ ∧ μH = PMF.pure τ
  law_eq := by
    rintro μG μH ⟨σ, τ, hστ, rfl, rfl⟩ i
    simpa using S.law_eq hστ i
  simulate := by
    rintro μG μH ⟨σ, τ, hστ, rfl, rfl⟩ who sH
    obtain ⟨sG, hd⟩ := S.simulate_target_deviation hστ who sH
    refine ⟨sG, ?_⟩
    simpa [constantDeviationProfileFamily_deviate, constDeviateDistributionFn_pure]
      using hd

/-- Build a one-way Nash simulation from a functional realization map.

This is the common case for compiler and language bridges: every source profile
has a canonical target realization, and target-side unilateral deviations can be
matched by source-side unilateral deviations. -/
def ofFunctionalRealization
    (viewG : ViewFamily G ι (fun _ => Ω)) (viewH : ViewFamily H ι (fun _ => Ω))
    (realize : G.Profile → H.Profile)
    (law_eq : ∀ (i : ι) (σ : G.Profile), viewG.plaw i σ = viewH.plaw i (realize σ))
    (simulate_target_deviation :
      ∀ (σ : G.Profile) (who : ι) (sH : H.Strategy who),
        ∃ sG : G.Strategy who,
          viewG.plaw who (Function.update σ who sG) =
            viewH.plaw who (Function.update (realize σ) who sH)) :
    NashDeviationSimulation G H Ω where
  viewG := viewG
  viewH := viewH
  rel := fun σ τ => τ = realize σ
  law_eq := by intro σ τ h i; subst h; exact law_eq i σ
  simulate_target_deviation := by
    intro σ τ h who sH; subst h
    exact simulate_target_deviation σ who sH

/-- Transport Nash equilibrium along a one-way Nash simulation, as an
instantiation of the generic transfer theorem. -/
theorem target_nash_of_source_nash
    (S : NashDeviationSimulation G H Ω)
    {σ : G.Profile} {τ : H.Profile} (hrel : S.rel σ τ)
    {prefΩ : ι → PMF Ω → PMF Ω → Prop}
    (hN : G.IsNashFor (observedPref S.viewG prefΩ) σ) :
    H.IsNashFor (observedPref S.viewH prefΩ) τ := by
  have hEq : G.IsDeviationEqFor (observedPref S.viewG prefΩ) (PMF.pure σ)
      G.constantDeviationProfileFamily := hN
  exact S.toTransport.target_eq_of_source_eq ⟨σ, τ, hrel, rfl, rfl⟩ hEq

end NashDeviationSimulation

/-- Two-way unilateral-deviation simulation on a constant observed view. -/
structure NashDeviationBisimulation (G H : GameForm ι) (Ω : Type) where
  /-- The source game's observed view. -/
  viewG : ViewFamily G ι (fun _ => Ω)
  /-- The target game's observed view. -/
  viewH : ViewFamily H ι (fun _ => Ω)
  /-- Which source profiles are matched to which target profiles. -/
  rel : G.Profile → H.Profile → Prop
  /-- Related profiles share the observed outcome law at every player. -/
  law_eq : ∀ {σ : G.Profile} {τ : H.Profile}, rel σ τ →
    ∀ i, viewG.plaw i σ = viewH.plaw i τ
  /-- Every target-side unilateral deviation is matched by a source-side one. -/
  simulate_target_deviation :
    ∀ {σ : G.Profile} {τ : H.Profile}, rel σ τ →
    ∀ (who : ι) (sH : H.Strategy who),
      ∃ sG : G.Strategy who,
        viewG.plaw who (Function.update σ who sG) =
          viewH.plaw who (Function.update τ who sH)
  /-- Every source-side unilateral deviation is matched by a target-side one. -/
  simulate_source_deviation :
    ∀ {σ : G.Profile} {τ : H.Profile}, rel σ τ →
    ∀ (who : ι) (sG : G.Strategy who),
      ∃ sH : H.Strategy who,
        viewG.plaw who (Function.update σ who sG) =
          viewH.plaw who (Function.update τ who sH)

namespace NashDeviationBisimulation

variable {G H : GameForm ι}

/-- Forget a two-way simulation to the forward one-way simulation. -/
def toForwardSimulation (S : NashDeviationBisimulation G H Ω) :
    NashDeviationSimulation G H Ω where
  viewG := S.viewG
  viewH := S.viewH
  rel := S.rel
  law_eq := S.law_eq
  simulate_target_deviation := S.simulate_target_deviation

/-- Reverse a two-way simulation. -/
def symm (S : NashDeviationBisimulation G H Ω) :
    NashDeviationBisimulation H G Ω where
  viewG := S.viewH
  viewH := S.viewG
  rel := fun τ σ => S.rel σ τ
  law_eq := by intro τ σ h i; exact (S.law_eq h i).symm
  simulate_target_deviation := by
    intro τ σ h who sG
    obtain ⟨sH, hd⟩ := S.simulate_source_deviation h who sG
    exact ⟨sH, hd.symm⟩
  simulate_source_deviation := by
    intro τ σ h who sH
    obtain ⟨sG, hd⟩ := S.simulate_target_deviation h who sH
    exact ⟨sG, hd.symm⟩

/-- Nash equilibrium is invariant across a two-way Nash simulation. -/
theorem nash_iff (S : NashDeviationBisimulation G H Ω)
    {σ : G.Profile} {τ : H.Profile} (hrel : S.rel σ τ)
    {prefΩ : ι → PMF Ω → PMF Ω → Prop} :
    G.IsNashFor (observedPref S.viewG prefΩ) σ ↔
      H.IsNashFor (observedPref S.viewH prefΩ) τ := by
  constructor
  · intro hN
    exact S.toForwardSimulation.target_nash_of_source_nash hrel hN
  · intro hN
    exact S.symm.toForwardSimulation.target_nash_of_source_nash hrel hN

end NashDeviationBisimulation

end Nash

section CanonicalFamilies

variable [DecidableEq ι] {Ω : Type}

/-- Build a coarse-correlated-family transport from a pointwise profile map:
`realize` sends each source profile to a target profile preserving the observed
law, and each target constant deviation is matched by a source one. -/
noncomputable def Transport.ofConstantProfileMap {G H : GameForm ι}
    (viewG : ViewFamily G ι (fun _ => Ω)) (viewH : ViewFamily H ι (fun _ => Ω))
    (realize : G.Profile → H.Profile)
    (law_eq : ∀ (i : ι) (σ : G.Profile), viewG.plaw i σ = viewH.plaw i (realize σ))
    (simulate_target_deviation :
      ∀ (who : ι) (sH : H.Strategy who),
        ∃ sG : G.Strategy who,
          ∀ σ : G.Profile,
            viewG.plaw who (Function.update σ who sG) =
              viewH.plaw who (Function.update (realize σ) who sH)) :
    Transport G H viewG viewH
      G.constantDeviationProfileFamily H.constantDeviationProfileFamily where
  rel := fun μG μH => μH = PMF.map realize μG
  law_eq := by
    intro μG μH h u; subst h
    exact ViewFamily.claw_map_of_plaw viewG viewH u realize (law_eq u) μG
  simulate := by
    intro μG μH h u sH; subst h
    obtain ⟨sG, hd⟩ := simulate_target_deviation u sH
    refine ⟨sG, ?_⟩
    have hbind :=
      ViewFamily.claw_bind_profile_map_of_plaw viewG viewH u realize
        (fun σ => Function.update σ u sG) (fun τ => Function.update τ u sH) hd μG
    simpa [constantDeviationProfileFamily_deviate, constDeviateDistributionFn]
      using hbind

/-- Build a correlated-family transport from a pointwise profile map: `realize`
preserves the observed law, and each target recommendation deviation is matched
by a source one. -/
noncomputable def Transport.ofRecommendationProfileMap {G H : GameForm ι}
    (viewG : ViewFamily G ι (fun _ => Ω)) (viewH : ViewFamily H ι (fun _ => Ω))
    (realize : G.Profile → H.Profile)
    (law_eq : ∀ (i : ι) (σ : G.Profile), viewG.plaw i σ = viewH.plaw i (realize σ))
    (simulate_target_deviation :
      ∀ (who : ι) (dH : H.Strategy who → H.Strategy who),
        ∃ dG : G.Strategy who → G.Strategy who,
          ∀ σ : G.Profile,
            viewG.plaw who (G.deviateProfileFn σ who dG) =
              viewH.plaw who (H.deviateProfileFn (realize σ) who dH)) :
    Transport G H viewG viewH
      G.recommendationDeviationFamily H.recommendationDeviationFamily where
  rel := fun μG μH => μH = PMF.map realize μG
  law_eq := by
    intro μG μH h u; subst h
    exact ViewFamily.claw_map_of_plaw viewG viewH u realize (law_eq u) μG
  simulate := by
    intro μG μH h u dH; subst h
    obtain ⟨dG, hd⟩ := simulate_target_deviation u dH
    refine ⟨dG, ?_⟩
    have hbind :=
      ViewFamily.claw_bind_profile_map_of_plaw viewG viewH u realize
        (fun σ => G.deviateProfileFn σ u dG) (fun τ => H.deviateProfileFn τ u dH) hd μG
    simpa [recommendationDeviationFamily_deviate, deviateDistributionFn]
      using hbind

/-- Correlated-equilibrium transport as the recommendation-family instance of the
generic transfer theorem. -/
theorem Transport.target_correlatedEq_of_source_correlatedEq {G H : GameForm ι}
    {viewG : ViewFamily G ι (fun _ => Ω)} {viewH : ViewFamily H ι (fun _ => Ω)}
    (T : Transport G H viewG viewH
      G.recommendationDeviationFamily H.recommendationDeviationFamily)
    {μG : PMF G.Profile} {μH : PMF H.Profile} (hrel : T.rel μG μH)
    {prefΩ : ι → PMF Ω → PMF Ω → Prop}
    (hCE : G.IsCorrelatedEqFor (observedPref viewG prefΩ) μG) :
    H.IsCorrelatedEqFor (observedPref viewH prefΩ) μH :=
  T.target_eq_of_source_eq hrel hCE

/-- Coarse-correlated-equilibrium transport as the constant-family instance of the
generic transfer theorem. -/
theorem Transport.target_coarseCorrelatedEq_of_source_coarseCorrelatedEq
    {G H : GameForm ι}
    {viewG : ViewFamily G ι (fun _ => Ω)} {viewH : ViewFamily H ι (fun _ => Ω)}
    (T : Transport G H viewG viewH
      G.constantDeviationProfileFamily H.constantDeviationProfileFamily)
    {μG : PMF G.Profile} {μH : PMF H.Profile} (hrel : T.rel μG μH)
    {prefΩ : ι → PMF Ω → PMF Ω → Prop}
    (hCCE : G.IsCoarseCorrelatedEqFor (observedPref viewG prefΩ) μG) :
    H.IsCoarseCorrelatedEqFor (observedPref viewH prefΩ) μH :=
  T.target_eq_of_source_eq hrel hCCE

/-- A constant unilateral deviation is the recommendation deviation that ignores
its recommendation. This morphism embeds the coarse-correlated (constant) family
into the correlated (recommendation) family. -/
def constantToRecommendationHom (F : GameForm ι) :
    DeviationFamily.Hom id F.constantDeviationProfileFamily F.recommendationDeviationFamily where
  map := fun _who s' => fun _ => s'
  deviate_eq := fun _μ _who _s' => rfl

/-- **Mixed corollary (correlated ⇒ coarse-correlated across a transport).** A
transport of the correlated (recommendation) family on both sides also simulates
the mixed pair `(recommendation, constant)` — by restricting only the target
family along `constantToRecommendationHom` — so a source correlated equilibrium
transports to a target *coarse*-correlated equilibrium.

Moving both sides of the transport along the same morphism is *not* a theorem: a
constant target deviation may only have recommendation-dependent source witnesses,
so a correlated-equilibrium transport does not entail a coarse-correlated one. The
target-only restriction here is what does hold. -/
theorem Transport.target_coarseCorrelatedEq_of_source_correlatedEq {G H : GameForm ι}
    {viewG : ViewFamily G ι (fun _ => Ω)} {viewH : ViewFamily H ι (fun _ => Ω)}
    (T : Transport G H viewG viewH
      G.recommendationDeviationFamily H.recommendationDeviationFamily)
    {μG : PMF G.Profile} {μH : PMF H.Profile} (hrel : T.rel μG μH)
    {prefΩ : ι → PMF Ω → PMF Ω → Prop}
    (hCE : G.IsCorrelatedEqFor (observedPref viewG prefΩ) μG) :
    H.IsCoarseCorrelatedEqFor (observedPref viewH prefΩ) μH :=
  let T' : Transport G H viewG viewH
      G.recommendationDeviationFamily H.constantDeviationProfileFamily :=
    { toRealization := T.toRealization
      simulate := Realization.Simulates.mono_target (constantToRecommendationHom H) T.simulate }
  T'.target_eq_of_source_eq hrel hCE

end CanonicalFamilies

end GameForm

/-- **Expectation preference** on real-valued outcome laws: `ν₁` is weakly
preferred to `ν₂` when its expectation is at least as large. This is the preference
on `PMF ℝ` that turns the utility-law view into the expected-utility corner. -/
noncomputable def expectationPref : PMF ℝ → PMF ℝ → Prop :=
  fun ν₁ ν₂ => expect ν₁ id ≥ expect ν₂ id

/-- **Strict expectation preference** on real-valued outcome laws. -/
noncomputable def expectationStrictPref : PMF ℝ → PMF ℝ → Prop :=
  fun ν₁ ν₂ => expect ν₁ id > expect ν₂ id

namespace KernelGame

variable {ι : Type}

/-- Kernel-game convenience alias for view families on the underlying game form. -/
abbrev ViewFamily (G : KernelGame ι) (U : Type) (Ω : U → Type) :=
  GameForm.ViewFamily G.toGameForm U Ω

/-- The **utility-law view**: each player observes the real-valued utility of the
outcome. Under `expectationPref` its observed preference is exactly the
expected-utility preference `euPref` (`observedPref_utilityView`), so it is the
corner at which observed-preference transport specializes to expected-utility
transport (`NashDeviationSimulation.target_isNash_of_source_isNash`). It lives at
the `KernelGame` level because a `GameForm` carries no utility. -/
def utilityView (G : KernelGame ι) : ViewFamily G ι (fun _ => ℝ) where
  observe := fun i o => G.utility o i

/-- The observed-preference relation of the utility-law view under
`expectationPref` is exactly the expected-utility preference `euPref`: this is the
change of variables `expect (PMF.map (G.utility · i) d) id = expect d (G.utility · i)`
(`Math.Probability.expect_map`). It is the bridge that makes `utilityView` the
expected-utility corner of transport. -/
theorem observedPref_utilityView (G : KernelGame ι) :
    GameForm.observedPref G.utilityView (fun _ => expectationPref) = G.euPref := by
  funext i d e
  simp only [GameForm.observedPref, utilityView, expectationPref, KernelGame.euPref,
    expect_map, id_eq]
  rfl

/-- The strict analogue of `observedPref_utilityView`: the utility-law view under
`expectationStrictPref` is exactly the strict expected-utility preference. -/
theorem observedStrictPref_utilityView (G : KernelGame ι) :
    GameForm.observedPref G.utilityView (fun _ => expectationStrictPref) = G.euStrictPref := by
  funext i d e
  simp only [GameForm.observedPref, utilityView, expectationStrictPref, KernelGame.euStrictPref,
    expect_map, id_eq]
  rfl

/-- Kernel-game convenience alias for deviation families over a unit type `U`. -/
abbrev DeviationFamily (G : KernelGame ι) (U : Type) :=
  GameForm.DeviationFamily G.toGameForm U

/-- Kernel-game convenience wrapper for deviation-family equilibrium. -/
def IsDeviationEqFor (G : KernelGame ι) {U : Type}
    (pref : U → PMF G.Outcome → PMF G.Outcome → Prop)
    (μ : PMF G.Profile) (Δ : DeviationFamily G U) : Prop :=
  G.toGameForm.IsDeviationEqFor pref μ Δ

/-- Kernel-game convenience alias for realizations on underlying game forms. -/
abbrev Realization (G H : KernelGame ι) {U : Type} {Ω : U → Type}
    (VG : GameForm.ViewFamily G.toGameForm U Ω) (VH : GameForm.ViewFamily H.toGameForm U Ω) :=
  GameForm.Realization G.toGameForm H.toGameForm VG VH

/-- Kernel-game convenience alias for transports on underlying game forms. -/
abbrev Transport (G H : KernelGame ι) {U : Type} {Ω : U → Type}
    (VG : GameForm.ViewFamily G.toGameForm U Ω) (VH : GameForm.ViewFamily H.toGameForm U Ω)
    (ΔG : DeviationFamily G U) (ΔH : DeviationFamily H U) :=
  GameForm.Transport G.toGameForm H.toGameForm VG VH ΔG ΔH

variable [DecidableEq ι]

/-- Kernel-game convenience alias for Nash deviation simulations. -/
abbrev NashDeviationSimulation (G H : KernelGame ι) (Ω : Type) :=
  GameForm.NashDeviationSimulation G.toGameForm H.toGameForm Ω

/-- Kernel-game convenience alias for Nash deviation bisimulations. -/
abbrev NashDeviationBisimulation (G H : KernelGame ι) (Ω : Type) :=
  GameForm.NashDeviationBisimulation G.toGameForm H.toGameForm Ω

/-- **Expected-utility Nash transport at the `KernelGame` level.** Along a Nash
deviation simulation whose views are the two games' utility-law views, the
`eu`-based `IsNash` of a source profile transfers to the target. This is the
expected-utility corner of `target_nash_of_source_nash`, obtained by instantiating
the observed preference at `expectationPref` via `observedPref_utilityView`. -/
theorem NashDeviationSimulation.target_isNash_of_source_isNash
    {G H : KernelGame ι} (S : NashDeviationSimulation G H ℝ)
    (hViewG : S.viewG = G.utilityView) (hViewH : S.viewH = H.utilityView)
    {σ : KernelGame.Profile G} {τ : KernelGame.Profile H} (hrel : S.rel σ τ)
    (hN : G.IsNash σ) : H.IsNash τ := by
  have hG : G.euPref = GameForm.observedPref S.viewG (fun _ => expectationPref) := by
    rw [hViewG]; exact (observedPref_utilityView G).symm
  have hH : H.euPref = GameForm.observedPref S.viewH (fun _ => expectationPref) := by
    rw [hViewH]; exact (observedPref_utilityView H).symm
  rw [KernelGame.IsNash_iff_IsNashFor_eu] at hN
  rw [KernelGame.IsNash_iff_IsNashFor_eu, hH]
  rw [hG] at hN
  exact S.target_nash_of_source_nash hrel hN

/-- **Expected-utility Nash invariance across a bisimulation.** When both views are
the utility-law views, `eu`-based `IsNash` is invariant across a two-way Nash
simulation. -/
theorem NashDeviationBisimulation.isNash_iff
    {G H : KernelGame ι} (S : NashDeviationBisimulation G H ℝ)
    (hViewG : S.viewG = G.utilityView) (hViewH : S.viewH = H.utilityView)
    {σ : KernelGame.Profile G} {τ : KernelGame.Profile H} (hrel : S.rel σ τ) :
    G.IsNash σ ↔ H.IsNash τ := by
  have hG : G.euPref = GameForm.observedPref S.viewG (fun _ => expectationPref) := by
    rw [hViewG]; exact (observedPref_utilityView G).symm
  have hH : H.euPref = GameForm.observedPref S.viewH (fun _ => expectationPref) := by
    rw [hViewH]; exact (observedPref_utilityView H).symm
  rw [KernelGame.IsNash_iff_IsNashFor_eu, KernelGame.IsNash_iff_IsNashFor_eu, hG, hH]
  exact S.nash_iff hrel

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
noncomputable def boolOutcomeView : ViewFamily boolOutcomeForm Unit (fun _ => Bool) :=
  ViewFamily.const id

/-- Observe only the Boolean component of the richer trace outcome. -/
noncomputable def tracedOutcomeView : ViewFamily tracedOutcomeForm Unit (fun _ => Bool) :=
  ViewFamily.const Prod.fst

/-- The richer-trace form simulates the direct form for unilateral deviations:
target deviations are matched by the same Boolean source deviation. -/
noncomputable def boolToTracedNashSimulation :
    NashDeviationSimulation boolOutcomeForm tracedOutcomeForm Bool where
  viewG := boolOutcomeView
  viewH := tracedOutcomeView
  rel := fun σ τ => σ () = τ ()
  law_eq := by
    intro σ τ hrel i
    simp [ViewFamily.plaw, boolOutcomeView, tracedOutcomeView, ViewFamily.const,
      boolOutcomeForm, tracedOutcomeForm, hrel, PMF.pure_map]
  simulate_target_deviation := by
    intro σ τ hrel who sH
    refine ⟨sH, ?_⟩
    cases who
    simp [ViewFamily.plaw, boolOutcomeView, tracedOutcomeView, ViewFamily.const,
      boolOutcomeForm, tracedOutcomeForm, PMF.pure_map]

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
