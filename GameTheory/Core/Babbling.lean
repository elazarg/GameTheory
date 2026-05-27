/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Core.GameForm

/-!
# Babbling Protocol Extensions

Protocol-level support for babbling embeddings and observable cheap-talk
extensions.

The central condition is deliberately local: it only talks about preference
comparisons at embedded base profiles and their unilateral enriched deviations.
Nash/EU corollaries live in `GameTheory.Concepts.Babbling`.
-/

namespace GameTheory

open Math.Probability

namespace GameForm

variable {ι : Type} [DecidableEq ι]

/-- Local preference preservation around embedded babbling profiles.

If `σ` is a base profile and player `who` deviates in the enriched form to
`s'`, then the base Nash comparison against the projected deviation implies the
corresponding enriched comparison at the embedded profile. -/
def BabblingDeviationPreservingFor (F H : GameForm ι)
    (prefF : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    (prefH : ι → PMF H.Outcome → PMF H.Outcome → Prop)
    (proj : ∀ i, H.Strategy i → F.Strategy i)
    (embed : ∀ i, F.Strategy i → H.Strategy i) : Prop :=
  ∀ (σ : F.Profile) (who : ι) (s' : H.Strategy who),
    prefF who
      (F.outcomeKernel σ)
      (F.outcomeKernel (Function.update σ who (proj who s'))) →
    prefH who
      (H.outcomeKernel (fun i => embed i (σ i)))
      (H.outcomeKernel (Function.update (fun i => embed i (σ i)) who s'))

end GameForm

namespace GameForm

variable {ι : Type} (F : GameForm ι)

/-- Observable pre-play cheap-talk extension of a game form.

Each player chooses a message and a contingent action plan from the realized
message profile to a base-game strategy. Messages are observed by all players
before action plans are evaluated. -/
structure CheapTalkExtension (F : GameForm ι) where
  Msg : ι → Type
  default : ∀ i, Msg i

namespace CheapTalkExtension

variable {F}

/-- Enriched cheap-talk strategy: a message plus a contingent base action. -/
def Strategy' (C : CheapTalkExtension F) (i : ι) : Type :=
  C.Msg i × ((∀ j : ι, C.Msg j) → F.Strategy i)

/-- The realized message profile of an enriched profile. -/
def messageProfile (C : CheapTalkExtension F)
    (σ' : ∀ i, C.Strategy' i) : ∀ i, C.Msg i :=
  fun i => (σ' i).1

/-- The induced base strategy profile after realized messages are observed. -/
def actionProfile (C : CheapTalkExtension F)
    (σ' : ∀ i, C.Strategy' i) : F.Profile :=
  fun i => (σ' i).2 (C.messageProfile σ')

/-- The game form induced by an observable cheap-talk extension. -/
def form (C : CheapTalkExtension F) : GameForm ι where
  Strategy := C.Strategy'
  Outcome := F.Outcome
  outcomeKernel := fun σ' => F.outcomeKernel (C.actionProfile σ')

/-- Canonical babbling strategy: send the default message and ignore all
messages when choosing the base strategy. -/
def embed (C : CheapTalkExtension F) (i : ι) (s : F.Strategy i) :
    C.form.Strategy i :=
  (C.default i, fun _ => s)

/-- Embed a base profile as a babbling cheap-talk profile. -/
def embedProfile (C : CheapTalkExtension F) (σ : F.Profile) : C.form.Profile :=
  fun i => C.embed i (σ i)

section DecidableEq

variable [DecidableEq ι]

/-- Project an enriched unilateral deviation to the base action it induces when
all other players babble at their default messages. -/
def proj (C : CheapTalkExtension F) (i : ι) (s' : C.form.Strategy i) :
    F.Strategy i :=
  s'.2 (Function.update C.default i s'.1)

@[simp] theorem proj_embed (C : CheapTalkExtension F)
    (i : ι) (s : F.Strategy i) :
    C.proj i (C.embed i s) = s := by
  simp [proj, embed]

omit [DecidableEq ι] in
@[simp] theorem outcomeKernel_embedProfile (C : CheapTalkExtension F)
    (σ : F.Profile) :
    C.form.outcomeKernel (C.embedProfile σ) = F.outcomeKernel σ := by
  rfl

theorem messageProfile_update_embedProfile (C : CheapTalkExtension F)
    (σ : F.Profile) (who : ι) (s' : C.form.Strategy who) :
    C.messageProfile (Function.update (C.embedProfile σ) who s') =
      Function.update C.default who s'.1 := by
  funext i
  by_cases h : i = who
  · subst h
    simp [messageProfile]
  · simp [messageProfile, embedProfile, embed, Function.update, h]

theorem actionProfile_update_embedProfile (C : CheapTalkExtension F)
    (σ : F.Profile) (who : ι) (s' : C.form.Strategy who) :
    C.actionProfile (Function.update (C.embedProfile σ) who s') =
      Function.update σ who (C.proj who s') := by
  funext i
  by_cases h : i = who
  · subst h
    simp [actionProfile, proj, C.messageProfile_update_embedProfile σ i s']
  · simp [actionProfile, embedProfile, embed, Function.update, h]

@[simp] theorem outcomeKernel_update_embedProfile (C : CheapTalkExtension F)
    (σ : F.Profile) (who : ι) (s' : C.form.Strategy who) :
    C.form.outcomeKernel (Function.update (C.embedProfile σ) who s') =
      F.outcomeKernel (Function.update σ who (C.proj who s')) := by
  simp [form, C.actionProfile_update_embedProfile σ who s']

/-- Observable cheap talk satisfies the local babbling-preservation condition:
when all other players babble, a unilateral enriched deviation only matters
through the base action it induces against default messages. -/
theorem babblingDeviationPreservingFor (C : CheapTalkExtension F)
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop) :
    F.BabblingDeviationPreservingFor C.form pref pref C.proj C.embed := by
  intro σ who s' h
  change pref who
    (C.form.outcomeKernel (C.embedProfile σ))
    (C.form.outcomeKernel (Function.update (C.embedProfile σ) who s'))
  simpa using h

end DecidableEq

end CheapTalkExtension

end GameForm

end GameTheory
