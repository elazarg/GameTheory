/-
# EXP-046: observable cheap talk as a static strategy enrichment

This competitor gives each player a public message and an action plan
contingent on the complete message profile. The hostile deviation changes both
objects at once. The experiment asks whether the ordinary static `GameForm`
and `IsNash` APIs can still prove the babbling theorem without Protocol timing.
-/

import GameTheory.Examples.Classic

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.CheapTalk

open GameTheory GameTheory.Examples GameTheory.Finite GameTheory.Probability

universe uι us uo um

variable {ι : Type uι}

/-- An observable public-message enrichment of a static game form. -/
structure Extension (F : GameForm.{uι, us, uo} ι) where
  /-- Each player's public-message carrier. -/
  Message : ι → Type um
  /-- The message used by the babbling embedding. -/
  default : ∀ i, Message i

namespace Extension

variable {F : GameForm.{uι, us, uo} ι} (C : Extension.{uι, us, uo, um} F)

/-- Message profiles use the canonical profile operation surface. -/
abbrev messageSignature : GameSignature.{uι, um, 0} ι where
  Strategy := C.Message
  Outcome := Unit

/-- A cheap-talk strategy sends a message and supplies a base strategy after
every public message profile. -/
def Strategy (i : ι) : Type (max uι um us) :=
  C.Message i × (Profile C.messageSignature → F.sig.Strategy i)

/-- The enriched static signature. -/
abbrev signature : GameSignature.{uι, max uι um us, uo} ι where
  Strategy := C.Strategy
  Outcome := F.sig.Outcome

/-- Read the public message sent by every player. -/
def messageProfile (profile : Profile C.signature) :
    Profile C.messageSignature :=
  fun i => (profile i).1

/-- Evaluate every contingent plan at the realized public messages. -/
def actionProfile (profile : Profile C.signature) : Profile F.sig :=
  fun i => (profile i).2 (C.messageProfile profile)

/-- The enriched play law is exactly the base play law at the induced action
profile. There is no second evaluator. -/
def form : GameForm ι where
  sig := C.signature
  play profile := F.play (C.actionProfile profile)

/-- A babbling strategy sends the default message and ignores all messages. -/
def embed (i : ι) (strategy : F.sig.Strategy i) : C.Strategy i :=
  (C.default i, fun _ => strategy)

/-- Embed a base profile coordinatewise as babbling strategies. -/
def embedProfile (profile : Profile F.sig) : Profile C.signature :=
  fun i => C.embed i (profile i)

@[simp]
theorem messageProfile_embedProfile (profile : Profile F.sig) :
    C.messageProfile (C.embedProfile profile) = C.default := rfl

@[simp]
theorem actionProfile_embedProfile (profile : Profile F.sig) :
    C.actionProfile (C.embedProfile profile) = profile := rfl

@[simp]
theorem form_play_embedProfile (profile : Profile F.sig) :
    C.form.play (C.embedProfile profile) = F.play profile := rfl

section DecidableEq

variable [DecidableEq ι]

/-- The base strategy induced by an enriched unilateral deviation while every
other player babbles. The deviator's new message is visible to its own
contingent plan. -/
def project (who : ι) (deviation : C.Strategy who) :
    F.sig.Strategy who :=
  deviation.2
    (Profile.update (sig := C.messageSignature) C.default who deviation.1)

/-- After an arbitrary enriched deviation from a babbling profile, the public
message profile is the default profile updated by the deviator's message. -/
theorem messageProfile_update_embedProfile (profile : Profile F.sig)
    (who : ι) (deviation : C.Strategy who) :
    C.messageProfile
        (Profile.update (C.embedProfile profile) who deviation) =
      Profile.update (sig := C.messageSignature) C.default who deviation.1 := by
  funext i
  by_cases hi : i = who
  · subst hi
    simp [messageProfile]
  · simp [messageProfile, embedProfile, embed, hi]

/-- The whole hostile cheap-talk deviation projects to one ordinary base
deviation. This is the key ownership test. -/
theorem actionProfile_update_embedProfile (profile : Profile F.sig)
    (who : ι) (deviation : C.Strategy who) :
    C.actionProfile
        (Profile.update (C.embedProfile profile) who deviation) =
      Profile.update profile who (C.project who deviation) := by
  funext i
  by_cases hi : i = who
  · subst hi
    simp only [actionProfile, Profile.update_same, project]
    rw [messageProfile_update_embedProfile]
  · simp [actionProfile, embedProfile, embed, hi]

/-- Consequently the enriched play law after the hostile deviation is the
base play law after its projected deviation. -/
theorem form_play_update_embedProfile (profile : Profile F.sig)
    (who : ι) (deviation : C.Strategy who) :
    C.form.play (Profile.update (C.embedProfile profile) who deviation) =
      F.play (Profile.update profile who (C.project who deviation)) := by
  show F.play
      (C.actionProfile
        (Profile.update (C.embedProfile profile) who deviation)) =
    F.play (Profile.update profile who (C.project who deviation))
  rw [actionProfile_update_embedProfile]

/-- Every base Nash equilibrium embeds as a babbling equilibrium. The
preference is arbitrary; only the strategy enrichment is communication
specific. -/
theorem babbling_isNash (preference : WeakPreference ι F.sig.Outcome)
    {profile : Profile F.sig}
    (hnash : IsNash F preference profile) :
    IsNash C.form preference (C.embedProfile profile) := by
  rw [isNash_iff] at hnash ⊢
  intro who deviation
  rw [form_play_embedProfile, form_play_update_embedProfile]
  exact hnash who (C.project who deviation)

end DecidableEq

end Extension

/-! ## Hostile Battle-of-the-Sexes consumer -/

/-- Two public messages, with `false` as the babbling default. -/
def battleMessages : Extension battleOfTheSexes.toForm where
  Message _ := Bool
  default _ := false

/-- Opera coordination survives when a deviator may replace both its public
message and its full message-contingent venue plan. -/
theorem battleOfTheSexes_opera_babbling_isNash :
    IsNash battleMessages.form
      (euPreference battleOfTheSexes.utility)
      (battleMessages.embedProfile bothOpera) :=
  battleMessages.babbling_isNash
    (preference := euPreference battleOfTheSexes.utility)
    battleOfTheSexes_bothOpera_isNash

/-- The same generic theorem embeds the football equilibrium. -/
theorem battleOfTheSexes_football_babbling_isNash :
    IsNash battleMessages.form
      (euPreference battleOfTheSexes.utility)
      (battleMessages.embedProfile bothFootball) :=
  battleMessages.babbling_isNash
    (preference := euPreference battleOfTheSexes.utility)
    battleOfTheSexes_bothFootball_isNash

end GameTheory.Experimental.PostArchitecture.CheapTalk
