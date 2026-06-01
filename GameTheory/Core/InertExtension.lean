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
Solution-concept consequences live in `GameTheory.Concepts.Foundations.InertExtension`.
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
@[simp] theorem outcomeKernel_form (σ' : E.form.Profile) :
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

end InertExtension

end KernelGame

end GameTheory
