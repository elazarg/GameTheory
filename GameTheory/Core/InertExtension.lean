/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Core.GameMorphism

/-!
# Inert Extensions

An inert extension enriches each player's strategy space with extra choices
that do not affect outcome distributions except through a projection back to
the original strategy space. Pre-play cheap-talk messages and other
payoff-irrelevant protocol enrichments are instances of this pattern.

The primary construction is stated for `GameForm`, since inertness is a
protocol property: it mentions strategies and outcome kernels, but not utility.
The `KernelGame` namespace then provides the expected utility/Nash corollaries.

The central theorem is not Nash-specific. It transports any
`ProfileDeviationFamily` whose deviations are compatible with projection.
-/

namespace GameTheory

open Math.Probability

namespace GameForm

variable {ι : Type}

/-- An inert extension of a game form `F`.

Each enriched strategy projects to a base strategy. The enriched outcome kernel
is required to be exactly the base outcome kernel evaluated at the projected
profile. The section `embed` chooses a canonical enriched representative of
each base strategy; it is used to lift base deviations into the extension. -/
structure InertExtension (F : GameForm ι) where
  /-- Enriched strategy space for each player. -/
  Strategy' : ι → Type
  /-- Projection from enriched strategies to the base strategy. -/
  proj : ∀ i, Strategy' i → F.Strategy i
  /-- Canonical embedding of base strategies into enriched strategies. -/
  embed : ∀ i, F.Strategy i → Strategy' i
  /-- `embed` is a section of `proj`. -/
  section_proj : ∀ i s, proj i (embed i s) = s
  /-- Outcome kernel on enriched profiles. -/
  outcomeKernel' : Kernel (∀ i, Strategy' i) F.Outcome
  /-- The enriched kernel is inert: only projected base strategies matter. -/
  outcome_inert : ∀ σ',
    outcomeKernel' σ' = F.outcomeKernel (fun i => proj i (σ' i))

namespace InertExtension

variable {F : GameForm ι} (E : F.InertExtension)

/-- The game form induced by an inert extension. -/
def form : GameForm ι where
  Strategy := E.Strategy'
  Outcome := F.Outcome
  outcomeKernel := E.outcomeKernel'

/-- Project an enriched profile to the base game form. -/
def projectProfile (σ' : E.form.Profile) : F.Profile :=
  fun i => E.proj i (σ' i)

/-- Embed a base profile into the enriched game form using the chosen section. -/
def embedProfile (σ : F.Profile) : E.form.Profile :=
  fun i => E.embed i (σ i)

/-- Project a distribution over enriched profiles to a distribution over base
profiles. -/
noncomputable def projectDistribution (μ' : PMF E.form.Profile) : PMF F.Profile :=
  Math.ProbabilityMassFunction.pushforward μ' E.projectProfile

@[simp] theorem projectProfile_apply (σ' : E.form.Profile) (i : ι) :
    E.projectProfile σ' i = E.proj i (σ' i) := rfl

@[simp] theorem embedProfile_apply (σ : F.Profile) (i : ι) :
    E.embedProfile σ i = E.embed i (σ i) := rfl

/-- Projecting the canonical embedding recovers the original base profile. -/
@[simp] theorem project_embedProfile (σ : F.Profile) :
    E.projectProfile (E.embedProfile σ) = σ := by
  funext i
  exact E.section_proj i (σ i)

@[simp] theorem projectDistribution_pure (σ' : E.form.Profile) :
    E.projectDistribution (PMF.pure σ') = PMF.pure (E.projectProfile σ') := by
  simpa [projectDistribution, Math.ProbabilityMassFunction.pushforward] using
    (PMF.pure_map E.projectProfile σ')

/-- Projecting a deterministic profile-distribution transform commutes with
projection when the transform itself commutes with projection. -/
theorem projectDistribution_bind_pure
    (μ' : PMF E.form.Profile)
    (f : E.form.Profile → E.form.Profile) (g : F.Profile → F.Profile)
    (hfg : ∀ σ', E.projectProfile (f σ') = g (E.projectProfile σ')) :
    E.projectDistribution (μ'.bind fun σ' => PMF.pure (f σ')) =
      (E.projectDistribution μ').bind fun σ => PMF.pure (g σ) := by
  unfold projectDistribution Math.ProbabilityMassFunction.pushforward
  calc
    PMF.map E.projectProfile (μ'.bind fun σ' => PMF.pure (f σ')) =
        (μ'.bind fun σ' => PMF.pure (f σ')).bind
          (fun τ => PMF.pure (E.projectProfile τ)) := by
          rw [← PMF.bind_pure_comp]
          rfl
    _ = μ'.bind (fun σ' => PMF.pure (g (E.projectProfile σ'))) := by
          simp [PMF.bind_bind, hfg]
    _ = (μ'.bind fun σ' => PMF.pure (E.projectProfile σ')).bind
          (fun σ => PMF.pure (g σ)) := by
          simp [PMF.bind_bind]
    _ = (PMF.map E.projectProfile μ').bind (fun σ => PMF.pure (g σ)) := by
          have hmap :
              (μ'.bind fun σ' => PMF.pure (E.projectProfile σ')) =
                PMF.map E.projectProfile μ' := PMF.bind_pure_comp E.projectProfile μ'
          rw [hmap]

/-- Outcome kernels in the extension are the base kernels at projected profiles. -/
theorem outcomeKernel_form (σ' : E.form.Profile) :
    E.form.outcomeKernel σ' = F.outcomeKernel (E.projectProfile σ') := by
  exact E.outcome_inert σ'

/-- Correlated outcomes in an inert extension are exactly the correlated
outcomes of the projected profile distribution. -/
theorem correlatedOutcome_projectDistribution (μ' : PMF E.form.Profile) :
    E.form.correlatedOutcome μ' = F.correlatedOutcome (E.projectDistribution μ') := by
  calc
    E.form.correlatedOutcome μ' = μ'.bind E.form.outcomeKernel := rfl
    _ = μ'.bind (F.outcomeKernel ∘ E.projectProfile) := by
          congr 1
          funext σ'
          exact E.outcome_inert σ'
    _ = F.correlatedOutcome (E.projectDistribution μ') := by
          simp [GameForm.correlatedOutcome, projectDistribution,
            Math.Probability.Kernel.pushforward, Math.ProbabilityMassFunction.pushforward]

/-- Projecting an enriched unilateral deviation gives the corresponding base
deviation to the projected enriched strategy. -/
@[simp] theorem projectProfile_update [DecidableEq ι]
    (σ' : E.form.Profile) (who : ι) (s' : E.form.Strategy who) :
    E.projectProfile (Function.update σ' who s') =
      Function.update (E.projectProfile σ') who (E.proj who s') := by
  funext i
  by_cases h : i = who
  · subst h
    simp [projectProfile]
  · simp [projectProfile, Function.update, h]

/-- One-way compatibility of deviation families: every enriched deviation
projects to some allowed base deviation at the projected distribution. -/
def ProjectsDeviationFamily
    (Δ' : ProfileDeviationFamily E.form) (Δ : ProfileDeviationFamily F) : Prop :=
  ∀ (μ' : PMF E.form.Profile) (who : ι) (d' : Δ'.Dev who),
    ∃ d : Δ.Dev who,
      E.projectDistribution (Δ'.deviate μ' who d') =
        Δ.deviate (E.projectDistribution μ') who d

/-- One-way lift compatibility of deviation families: every base deviation can
be represented by some enriched deviation after projection. -/
def LiftsDeviationFamily
    (Δ' : ProfileDeviationFamily E.form) (Δ : ProfileDeviationFamily F) : Prop :=
  ∀ (μ' : PMF E.form.Profile) (who : ι) (d : Δ.Dev who),
    ∃ d' : Δ'.Dev who,
      E.projectDistribution (Δ'.deviate μ' who d') =
        Δ.deviate (E.projectDistribution μ') who d

/-- If every enriched deviation projects to an allowed base deviation, then any
base deviation-family equilibrium pulls back to the inert extension. -/
theorem isDeviationEqFamilyFor_of_projected_isDeviationEqFamilyFor
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    {μ' : PMF E.form.Profile}
    {Δ' : ProfileDeviationFamily E.form} {Δ : ProfileDeviationFamily F}
    (hΔ : E.ProjectsDeviationFamily Δ' Δ)
    (hEq : F.IsDeviationEqFamilyFor pref (E.projectDistribution μ') Δ) :
    E.form.IsDeviationEqFamilyFor pref μ' Δ' := by
  intro who d'
  obtain ⟨d, hd⟩ := hΔ μ' who d'
  have h := hEq who d
  change pref who (E.form.correlatedOutcome μ')
    (E.form.correlatedOutcome (Δ'.deviate μ' who d'))
  rw [E.correlatedOutcome_projectDistribution μ']
  rw [E.correlatedOutcome_projectDistribution (Δ'.deviate μ' who d')]
  rw [hd]
  exact h

/-- If every base deviation lifts to an enriched deviation, then any enriched
deviation-family equilibrium projects to the base game form. -/
theorem projected_isDeviationEqFamilyFor_of_isDeviationEqFamilyFor
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    {μ' : PMF E.form.Profile}
    {Δ' : ProfileDeviationFamily E.form} {Δ : ProfileDeviationFamily F}
    (hΔ : E.LiftsDeviationFamily Δ' Δ)
    (hEq : E.form.IsDeviationEqFamilyFor pref μ' Δ') :
    F.IsDeviationEqFamilyFor pref (E.projectDistribution μ') Δ := by
  intro who d
  obtain ⟨d', hd⟩ := hΔ μ' who d
  have h := hEq who d'
  change pref who (E.form.correlatedOutcome μ')
    (E.form.correlatedOutcome (Δ'.deviate μ' who d')) at h
  rw [E.correlatedOutcome_projectDistribution μ'] at h
  rw [E.correlatedOutcome_projectDistribution (Δ'.deviate μ' who d')] at h
  rw [hd] at h
  exact h

/-- Deviation-family equilibria are equivalent across an inert extension when
the enriched and base deviation families project to each other. -/
theorem isDeviationEqFamilyFor_iff
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    {μ' : PMF E.form.Profile}
    {Δ' : ProfileDeviationFamily E.form} {Δ : ProfileDeviationFamily F}
    (hproj : E.ProjectsDeviationFamily Δ' Δ)
    (hlift : E.LiftsDeviationFamily Δ' Δ) :
    E.form.IsDeviationEqFamilyFor pref μ' Δ' ↔
      F.IsDeviationEqFamilyFor pref (E.projectDistribution μ') Δ :=
  ⟨E.projected_isDeviationEqFamilyFor_of_isDeviationEqFamilyFor pref hlift,
    E.isDeviationEqFamilyFor_of_projected_isDeviationEqFamilyFor pref hproj⟩

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
  E.isDeviationEqFamilyFor_of_projected_isDeviationEqFamilyFor pref
    E.projects_constantDeviationProfileFamily hEq

/-- Coarse-correlated equilibria project along inert extensions. -/
theorem projected_coarseCorrelatedEqFor_of_coarseCorrelatedEqFor
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    {μ' : PMF E.form.Profile}
    (hEq : E.form.IsCoarseCorrelatedEqFor pref μ') :
    F.IsCoarseCorrelatedEqFor pref (E.projectDistribution μ') :=
  E.projected_isDeviationEqFamilyFor_of_isDeviationEqFamilyFor pref
    E.lifts_constantDeviationProfileFamily hEq

/-- Coarse-correlated equilibrium is invariant under inert extensions. -/
theorem coarseCorrelatedEqFor_iff
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    {μ' : PMF E.form.Profile} :
    E.form.IsCoarseCorrelatedEqFor pref μ' ↔
      F.IsCoarseCorrelatedEqFor pref (E.projectDistribution μ') :=
  E.isDeviationEqFamilyFor_iff pref E.projects_constantDeviationProfileFamily
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
  E.projected_isDeviationEqFamilyFor_of_isDeviationEqFamilyFor pref
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
theorem weaklyDominatesFor_of_projected_weaklyDominatesFor
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    {who : ι} {s t : E.form.Strategy who}
    (hdom : F.WeaklyDominatesFor pref who (E.proj who s) (E.proj who t)) :
    E.form.WeaklyDominatesFor pref who s t := by
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

/-- A kernel-game inert extension is an inert extension of the underlying game
form. Utility is reattached after the protocol-level construction. -/
abbrev InertExtension (G : KernelGame ι) := G.toGameForm.InertExtension

namespace InertExtension

variable {G : KernelGame ι} (E : G.InertExtension)

/-- The kernel game induced by an inert extension. -/
def game : KernelGame ι :=
  E.form.withUtility G.utility

/-- The projection from the inert extension to the base game preserves utility
distributions. -/
def toMorphism : Morphism E.game G where
  stratMap := E.proj
  udist_preserved := by
    intro σ'
    change (G.outcomeKernel (fun i => E.proj i (σ' i))).bind
        (fun ω => PMF.pure (G.utility ω)) =
      (E.outcomeKernel' σ').bind (fun ω => PMF.pure (G.utility ω))
    rw [E.outcome_inert σ']
    rfl

/-- The projection from the inert extension to the base game preserves expected
utilities. -/
def toEUMorphism : EUMorphism E.game G where
  toMorphism := E.toMorphism
  eu_preserved := by
    intro σ' who
    change expect (G.outcomeKernel (fun i => E.proj i (σ' i)))
        (fun ω => G.utility ω who) =
      expect (E.outcomeKernel' σ') (fun ω => G.utility ω who)
    rw [E.outcome_inert σ']
    rfl

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
  simpa [KernelGame.IsNashFor, KernelGame.euPref, game] using h

/-- Nash equilibria in the inert extension project to Nash equilibria in the
base game. -/
theorem projected_nash_of_nash
    {σ' : Profile E.game}
    (hN : E.game.IsNash σ') :
    G.IsNash (E.projectProfile σ') := by
  rw [KernelGame.IsNash_iff_IsNashFor_eu] at hN ⊢
  have h := E.projected_isNashFor_of_isNashFor G.euPref
    (by simpa [KernelGame.IsNashFor, KernelGame.euPref, game] using hN)
  simpa [KernelGame.IsNashFor, KernelGame.euPref] using h

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
