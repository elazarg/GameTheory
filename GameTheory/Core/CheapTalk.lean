/-
# Observable one-stage cheap talk

An observable pre-play message followed by a message-contingent action is a
static strategy enrichment. Protocol remains reserved for communication whose
intermediate history or timing is itself semantically observable.

Primary reference: V. P. Crawford and J. Sobel, “Strategic Information
Transmission,” *Econometrica* 50 (1982).
-/

import GameTheory.Core.Equilibrium

noncomputable section

namespace GameTheory
namespace GameForm

universe uι us uo um

variable {ι : Type uι}

/-- An observable public-message enrichment of a static game form. -/
structure CheapTalkExtension (F : GameForm.{uι, us, uo} ι) where
  /-- Each player's public-message carrier. -/
  Message : ι → Type um
  /-- The message used by the babbling embedding. -/
  default : ∀ i, Message i

namespace CheapTalkExtension

variable {F : GameForm.{uι, us, uo} ι}
  (C : CheapTalkExtension.{uι, us, uo, um} F)

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
@[reducible]
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

@[simp]
theorem project_embed (who : ι) (strategy : F.sig.Strategy who) :
    C.project who (C.embed who strategy) = strategy := rfl

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

/-- Replacing a plan while retaining its message does not change the public
message profile. -/
@[simp]
theorem messageProfile_update_sameMessage (profile : Profile C.signature)
    (who : ι)
    (plan : Profile C.messageSignature → F.sig.Strategy who) :
    C.messageProfile
        (Profile.update profile who ((profile who).1, plan)) =
      C.messageProfile profile := by
  funext i
  by_cases hi : i = who
  · subst hi
    simp [messageProfile]
  · simp [messageProfile, hi]

/-- A player can retain its message and replace its realized action with any
base strategy by choosing a constant contingent plan. -/
@[simp]
theorem actionProfile_update_sameMessage_constPlan
    (profile : Profile C.signature) (who : ι)
    (strategy : F.sig.Strategy who) :
    C.actionProfile
        (Profile.update profile who ((profile who).1, fun _ => strategy)) =
      Profile.update (C.actionProfile profile) who strategy := by
  funext i
  by_cases hi : i = who
  · subst hi
    simp [actionProfile]
  · simp only [actionProfile, Profile.update_of_ne _ _ hi]
    rw [messageProfile_update_sameMessage]

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

/-- Every pure Nash profile of the cheap-talk extension induces a pure Nash
profile of the base form through its realized actions. -/
theorem actionProfile_isNash_of_isNash
    (preference : WeakPreference ι F.sig.Outcome)
    {profile : Profile C.signature}
    (hnash : IsNash C.form preference profile) :
    IsNash F preference (C.actionProfile profile) := by
  rw [isNash_iff] at hnash ⊢
  intro who strategy
  have hdeviation :=
    hnash who ((profile who).1, fun _ => strategy)
  simpa only [form, actionProfile_update_sameMessage_constPlan] using hdeviation

/-- A cheap-talk Nash profile has exactly the play law of its induced base
Nash profile. -/
theorem exists_base_isNash_play_eq_of_isNash
    (preference : WeakPreference ι F.sig.Outcome)
    {profile : Profile C.signature}
    (hnash : IsNash C.form preference profile) :
    ∃ baseProfile : Profile F.sig,
      IsNash F preference baseProfile ∧
        C.form.play profile = F.play baseProfile :=
  ⟨C.actionProfile profile,
    C.actionProfile_isNash_of_isNash preference hnash, rfl⟩

/-- Observable one-stage cheap talk preserves exactly the set of outcome laws
generated by pure Nash profiles. -/
theorem exists_isNash_play_iff (preference : WeakPreference ι F.sig.Outcome)
    (law : Probability.FinDist F.sig.Outcome) :
    (∃ profile : Profile C.signature,
        IsNash C.form preference profile ∧ C.form.play profile = law) ↔
      ∃ profile : Profile F.sig,
        IsNash F preference profile ∧ F.play profile = law := by
  constructor
  · rintro ⟨profile, hnash, hplay⟩
    exact ⟨C.actionProfile profile,
      C.actionProfile_isNash_of_isNash preference hnash, hplay⟩
  · rintro ⟨profile, hnash, hplay⟩
    exact ⟨C.embedProfile profile, C.babbling_isNash preference hnash,
      by simpa using hplay⟩

end DecidableEq

end CheapTalkExtension
end GameForm
end GameTheory
