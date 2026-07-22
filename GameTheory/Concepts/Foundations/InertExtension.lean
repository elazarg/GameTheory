/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Core.InertExtension
import GameTheory.Concepts.Equilibrium.SolutionConcepts
import GameTheory.Concepts.Transport.Pref

/-!
# Solution-Concept Transport for Inert Extensions

The inert-extension structure and projection identities live in
`GameTheory.Core.InertExtension`. This file contains the preference- and
solution-concept consequences.
-/

namespace GameTheory

open Math.Probability

namespace GameForm

variable {ι : Type}

namespace InertExtension

variable {F : GameForm ι} (E : F.InertExtension)

/-- One-way compatibility of deviation families: every enriched deviation
projects to some allowed base deviation at the projected distribution. -/
def ProjectsDeviationFamily
    (Δ' : DeviationFamily E.form ι) (Δ : DeviationFamily F ι) : Prop :=
  ∀ (μ' : PMF E.form.Profile) (who : ι) (d' : Δ'.Dev who),
    ∃ d : Δ.Dev who,
      E.projectDistribution (Δ'.deviate μ' who d') =
        Δ.deviate (E.projectDistribution μ') who d

/-- One-way lift compatibility of deviation families: every base deviation can
be represented by some enriched deviation after projection. -/
def LiftsDeviationFamily
    (Δ' : DeviationFamily E.form ι) (Δ : DeviationFamily F ι) : Prop :=
  ∀ (μ' : PMF E.form.Profile) (who : ι) (d : Δ.Dev who),
    ∃ d' : Δ'.Dev who,
      E.projectDistribution (Δ'.deviate μ' who d') =
        Δ.deviate (E.projectDistribution μ') who d

/-- Projection compatibility is a preference-level backtranslation from the base
game into the inert extension: over the projection relation, each enriched
deviation is matched by the base deviation it projects to, and since the inert
extension leaves outcomes fixed the two games share the preference and the
verdict carries verbatim. -/
theorem prefSimulates_of_projects
    {Δ' : DeviationFamily E.form ι} {Δ : DeviationFamily F ι}
    (hΔ : E.ProjectsDeviationFamily Δ' Δ)
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop) :
    GameForm.PrefSimulates (fun μF μ' => μF = E.projectDistribution μ') pref pref Δ Δ' := by
  intro μF μ' hrel u d'
  obtain ⟨d, hd⟩ := hΔ μ' u d'
  refine ⟨d, ?_⟩
  subst hrel
  intro h
  rw [E.correlatedOutcome_projectDistribution μ',
    E.correlatedOutcome_projectDistribution (Δ'.deviate μ' u d'), hd]
  exact h

/-- Lift compatibility is the opposite preference-level backtranslation, from the
inert extension into the base game: over the projection relation, each base
deviation is matched by an enriched deviation lifting it, and the shared
preference carries the verdict verbatim. -/
theorem prefSimulates_of_lifts
    {Δ' : DeviationFamily E.form ι} {Δ : DeviationFamily F ι}
    (hΔ : E.LiftsDeviationFamily Δ' Δ)
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop) :
    GameForm.PrefSimulates (fun μ' μF => μF = E.projectDistribution μ') pref pref Δ' Δ := by
  intro μ' μF hrel u d
  obtain ⟨d', hd⟩ := hΔ μ' u d
  refine ⟨d', ?_⟩
  subst hrel
  intro h
  rw [E.correlatedOutcome_projectDistribution μ'] at h
  rw [E.correlatedOutcome_projectDistribution (Δ'.deviate μ' u d')] at h
  rw [hd] at h
  exact h

/-- If every enriched deviation projects to an allowed base deviation, then any
base deviation-family equilibrium pulls back to the inert extension. An
instantiation of the preference-level transfer along `prefSimulates_of_projects`. -/
theorem isDeviationEqFor_of_projected_isDeviationEqFor
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    {μ' : PMF E.form.Profile}
    {Δ' : DeviationFamily E.form ι} {Δ : DeviationFamily F ι}
    (hΔ : E.ProjectsDeviationFamily Δ' Δ)
    (hEq : F.IsDeviationEqFor pref (E.projectDistribution μ') Δ) :
    E.form.IsDeviationEqFor pref μ' Δ' :=
  GameForm.PrefSimulates.transfer (E.prefSimulates_of_projects hΔ pref) rfl hEq

/-- If every base deviation lifts to an enriched deviation, then any enriched
deviation-family equilibrium projects to the base game form. An instantiation of
the preference-level transfer along `prefSimulates_of_lifts`. -/
theorem projected_isDeviationEqFor_of_isDeviationEqFor
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    {μ' : PMF E.form.Profile}
    {Δ' : DeviationFamily E.form ι} {Δ : DeviationFamily F ι}
    (hΔ : E.LiftsDeviationFamily Δ' Δ)
    (hEq : E.form.IsDeviationEqFor pref μ' Δ') :
    F.IsDeviationEqFor pref (E.projectDistribution μ') Δ :=
  GameForm.PrefSimulates.transfer (E.prefSimulates_of_lifts hΔ pref) rfl hEq

/-- Deviation-family equilibria are equivalent across an inert extension when
the enriched and base deviation families project to each other. The two
directions are the opposite preference-level backtranslations assembled by
`PrefSimulates.transfer_iff`. -/
theorem isDeviationEqFor_iff
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    {μ' : PMF E.form.Profile}
    {Δ' : DeviationFamily E.form ι} {Δ : DeviationFamily F ι}
    (hproj : E.ProjectsDeviationFamily Δ' Δ)
    (hlift : E.LiftsDeviationFamily Δ' Δ) :
    E.form.IsDeviationEqFor pref μ' Δ' ↔
      F.IsDeviationEqFor pref (E.projectDistribution μ') Δ :=
  GameForm.PrefSimulates.transfer_iff
    (E.prefSimulates_of_lifts hlift pref)
    (E.prefSimulates_of_projects hproj pref) rfl

section PreferenceUpdate

variable [DecidableEq ι]

/-- Constant unilateral deviations are projection-compatible. This covers
Nash-style and coarse-correlated-equilibrium-style deviation families. -/
theorem projects_constantDeviationProfileFamily :
    E.ProjectsDeviationFamily E.form.constantDeviationProfileFamily
      F.constantDeviationProfileFamily := by
  intro μ' who s'
  refine ⟨E.proj who s', ?_⟩
  change E.projectDistribution (μ'.bind fun σ =>
      PMF.pure (Function.update σ who s')) =
    (E.projectDistribution μ').bind fun σ =>
      PMF.pure (Function.update σ who (E.proj who s'))
  exact E.projectDistribution_bind_pure μ'
    (fun σ => Function.update σ who s')
    (fun σ => Function.update σ who (E.proj who s'))
    (fun σ => E.projectProfile_update σ who s')

/-- Constant base deviations lift to constant enriched deviations via `embed`. -/
theorem lifts_constantDeviationProfileFamily :
    E.LiftsDeviationFamily E.form.constantDeviationProfileFamily
      F.constantDeviationProfileFamily := by
  intro μ' who s
  refine ⟨E.embed who s, ?_⟩
  change E.projectDistribution (μ'.bind fun σ =>
      PMF.pure (Function.update σ who (E.embed who s))) =
    (E.projectDistribution μ').bind fun σ =>
      PMF.pure (Function.update σ who s)
  exact E.projectDistribution_bind_pure μ'
    (fun σ => Function.update σ who (E.embed who s))
    (fun σ => Function.update σ who s)
    (fun σ => by
      rw [E.projectProfile_update σ who (E.embed who s)]
      simp [E.section_proj who s])

/-- Coarse-correlated equilibria pull back along inert extensions. -/
theorem coarseCorrelatedEqFor_of_projected_coarseCorrelatedEqFor
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    {μ' : PMF E.form.Profile}
    (hEq : F.IsCoarseCorrelatedEqFor pref (E.projectDistribution μ')) :
    E.form.IsCoarseCorrelatedEqFor pref μ' :=
  E.isDeviationEqFor_of_projected_isDeviationEqFor pref
    E.projects_constantDeviationProfileFamily hEq

/-- Coarse-correlated equilibria project along inert extensions. -/
theorem projected_coarseCorrelatedEqFor_of_coarseCorrelatedEqFor
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    {μ' : PMF E.form.Profile}
    (hEq : E.form.IsCoarseCorrelatedEqFor pref μ') :
    F.IsCoarseCorrelatedEqFor pref (E.projectDistribution μ') :=
  E.projected_isDeviationEqFor_of_isDeviationEqFor pref
    E.lifts_constantDeviationProfileFamily hEq

/-- Coarse-correlated equilibrium is invariant under inert extensions. -/
theorem coarseCorrelatedEqFor_iff
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    {μ' : PMF E.form.Profile} :
    E.form.IsCoarseCorrelatedEqFor pref μ' ↔
      F.IsCoarseCorrelatedEqFor pref (E.projectDistribution μ') :=
  E.isDeviationEqFor_iff pref E.projects_constantDeviationProfileFamily
    E.lifts_constantDeviationProfileFamily

/-- A recommendation-dependent base deviation lifts to the enriched game by
projecting the enriched recommendation, applying the base deviation, and
embedding the result. The converse is intentionally not automatic: an enriched
recommendation-dependent deviation may condition on payoff-irrelevant
coordinates that the base recommendation does not contain. -/
theorem lifts_recommendationDeviationFamily :
    E.LiftsDeviationFamily E.form.recommendationDeviationFamily
      F.recommendationDeviationFamily := by
  intro μ' who dev
  refine ⟨fun s' => E.embed who (dev (E.proj who s')), ?_⟩
  change E.projectDistribution (μ'.bind fun σ =>
      PMF.pure (Function.update σ who
        (E.embed who (dev (E.proj who (σ who)))))) =
    (E.projectDistribution μ').bind fun σ =>
      PMF.pure (Function.update σ who (dev (σ who)))
  exact E.projectDistribution_bind_pure μ'
    (fun σ => Function.update σ who
      (E.embed who (dev (E.proj who (σ who)))))
    (fun σ => Function.update σ who (dev (σ who)))
    (fun σ => by
      rw [E.projectProfile_update σ who
        (E.embed who (dev (E.proj who (σ who))))]
      simp [E.section_proj who (dev (E.proj who (σ who)))])

/-- Correlated equilibria in the enriched recommendation game project to
correlated equilibria of the base game form. The reverse implication needs a
smaller, projection-measurable enriched deviation family or an additional
information condition. -/
theorem projected_correlatedEqFor_of_correlatedEqFor
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    {μ' : PMF E.form.Profile}
    (hEq : E.form.IsCorrelatedEqFor pref μ') :
    F.IsCorrelatedEqFor pref (E.projectDistribution μ') :=
  E.projected_isDeviationEqFor_of_isDeviationEqFor pref
    E.lifts_recommendationDeviationFamily hEq

/-- Preference-parameterized best responses pull back along inert extensions. -/
theorem bestResponseFor_of_projected_bestResponseFor
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    {who : ι} {σ' : E.form.Profile} {s : E.form.Strategy who}
    (hBR : F.IsBestResponseFor pref who (E.projectProfile σ') (E.proj who s)) :
    E.form.IsBestResponseFor pref who σ' s := by
  intro t
  have h := hBR (E.proj who t)
  change pref who (E.outcomeKernel' (Function.update σ' who s))
    (E.outcomeKernel' (Function.update σ' who t))
  rw [E.outcome_inert (Function.update σ' who s)]
  rw [E.outcome_inert (Function.update σ' who t)]
  change pref who (F.outcomeKernel (E.projectProfile (Function.update σ' who s)))
    (F.outcomeKernel (E.projectProfile (Function.update σ' who t)))
  rw [E.projectProfile_update σ' who s]
  rw [E.projectProfile_update σ' who t]
  exact h

/-- Preference-parameterized Nash equilibria pull back along inert extensions. -/
theorem isNashFor_of_projected_isNashFor
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    {σ' : E.form.Profile}
    (hN : F.IsNashFor pref (E.projectProfile σ')) :
    E.form.IsNashFor pref σ' := by
  refine (E.form.isNashFor_iff pref σ').2 ?_
  intro who s'
  have h := (F.isNashFor_iff pref (E.projectProfile σ')).1 hN
    who (E.proj who s')
  change pref who (E.outcomeKernel' σ')
    (E.outcomeKernel' (Function.update σ' who s'))
  rw [E.outcome_inert σ']
  rw [E.outcome_inert (Function.update σ' who s')]
  change pref who (F.outcomeKernel (E.projectProfile σ'))
    (F.outcomeKernel (E.projectProfile (Function.update σ' who s')))
  rw [E.projectProfile_update σ' who s']
  exact h

/-- Preference-parameterized Nash equilibria project along inert extensions. -/
theorem projected_isNashFor_of_isNashFor
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    {σ' : E.form.Profile}
    (hN : E.form.IsNashFor pref σ') :
    F.IsNashFor pref (E.projectProfile σ') := by
  refine (F.isNashFor_iff pref (E.projectProfile σ')).2 ?_
  intro who s
  have h := (E.form.isNashFor_iff pref σ').1 hN who (E.embed who s)
  change pref who (E.outcomeKernel' σ')
    (E.outcomeKernel' (Function.update σ' who (E.embed who s))) at h
  rw [E.outcome_inert σ'] at h
  rw [E.outcome_inert (Function.update σ' who (E.embed who s))] at h
  change pref who (F.outcomeKernel (E.projectProfile σ'))
    (F.outcomeKernel (E.projectProfile
      (Function.update σ' who (E.embed who s)))) at h
  rw [E.projectProfile_update σ' who (E.embed who s)] at h
  simpa [E.section_proj who s] using h

/-- Nash-for is invariant under inert extensions at projected profiles. -/
theorem isNashFor_iff
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    {σ' : E.form.Profile} :
    E.form.IsNashFor pref σ' ↔ F.IsNashFor pref (E.projectProfile σ') :=
  ⟨E.projected_isNashFor_of_isNashFor pref,
    E.isNashFor_of_projected_isNashFor pref⟩

/-- Canonically embedding a base preference-parameterized Nash equilibrium into
an inert extension yields a preference-parameterized Nash equilibrium of the
extension. -/
theorem isNashFor_embedProfile
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    {σ : F.Profile}
    (hN : F.IsNashFor pref σ) :
    E.form.IsNashFor pref (E.embedProfile σ) :=
  E.isNashFor_of_projected_isNashFor pref (by simpa using hN)

/-- Preference-parameterized dominant strategies pull back along inert
extensions. -/
theorem dominantFor_of_projected_dominantFor
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    {who : ι} {s : E.form.Strategy who}
    (hdom : F.IsDominantFor pref who (E.proj who s)) :
    E.form.IsDominantFor pref who s := by
  intro σ' t
  have h := hdom (E.projectProfile σ') (E.proj who t)
  change pref who (E.outcomeKernel' (Function.update σ' who s))
    (E.outcomeKernel' (Function.update σ' who t))
  rw [E.outcome_inert (Function.update σ' who s)]
  rw [E.outcome_inert (Function.update σ' who t)]
  change pref who (F.outcomeKernel (E.projectProfile (Function.update σ' who s)))
    (F.outcomeKernel (E.projectProfile (Function.update σ' who t)))
  rw [E.projectProfile_update σ' who s]
  rw [E.projectProfile_update σ' who t]
  exact h

/-- Preference-parameterized weak dominance pulls back along inert extensions. -/
theorem weaklyDominatesReflexiveFor_of_projected_weaklyDominatesReflexiveFor
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    {who : ι} {s t : E.form.Strategy who}
    (hdom : F.WeaklyDominatesReflexiveFor pref who (E.proj who s)
      (E.proj who t)) :
    E.form.WeaklyDominatesReflexiveFor pref who s t := by
  intro σ'
  have h := hdom (E.projectProfile σ')
  change pref who (E.outcomeKernel' (Function.update σ' who s))
    (E.outcomeKernel' (Function.update σ' who t))
  rw [E.outcome_inert (Function.update σ' who s)]
  rw [E.outcome_inert (Function.update σ' who t)]
  change pref who (F.outcomeKernel (E.projectProfile (Function.update σ' who s)))
    (F.outcomeKernel (E.projectProfile (Function.update σ' who t)))
  rw [E.projectProfile_update σ' who s]
  rw [E.projectProfile_update σ' who t]
  exact h

end PreferenceUpdate

end InertExtension

end GameForm

namespace KernelGame

variable {ι : Type}

namespace InertExtension

variable {G : KernelGame ι} (E : G.InertExtension)

section PreferenceUpdate

variable [DecidableEq ι]

/-- Any enriched profile whose projection is a Nash equilibrium of the base game
is a Nash equilibrium of the inert extension. -/
theorem nash_of_projected_nash
    {σ' : Profile E.game}
    (hN : G.IsNash (E.projectProfile σ')) :
    E.game.IsNash σ' := by
  rw [KernelGame.IsNash_iff_IsNashFor_eu] at hN ⊢
  have h := E.isNashFor_of_projected_isNashFor G.euPref hN
  exact h

/-- Nash equilibria in the inert extension project to Nash equilibria in the
base game. -/
theorem projected_nash_of_nash
    {σ' : Profile E.game}
    (hN : E.game.IsNash σ') :
    G.IsNash (E.projectProfile σ') := by
  rw [KernelGame.IsNash_iff_IsNashFor_eu] at hN ⊢
  have h := E.projected_isNashFor_of_isNashFor G.euPref
    (by exact hN)
  exact h

/-- Nash is invariant under inert extensions at projected profiles. -/
theorem nash_iff
    {σ' : Profile E.game} :
    E.game.IsNash σ' ↔ G.IsNash (E.projectProfile σ') :=
  ⟨E.projected_nash_of_nash, E.nash_of_projected_nash⟩

/-- Canonically embedding a base Nash equilibrium into an inert extension yields
a Nash equilibrium of the extension. This is the abstract babbling/pre-play
message theorem: the extra strategic coordinates are payoff-irrelevant. -/
theorem nash_embedProfile
    {σ : Profile G} (hN : G.IsNash σ) :
    E.game.IsNash (E.embedProfile σ) :=
  E.nash_of_projected_nash (by simpa using hN)

/-- Alias emphasizing the cheap-talk reading of `nash_embedProfile`. -/
theorem babbling_nash
    {σ : Profile G} (hN : G.IsNash σ) :
    E.game.IsNash (E.embedProfile σ) :=
  E.nash_embedProfile hN

end PreferenceUpdate

end InertExtension

end KernelGame

end GameTheory
