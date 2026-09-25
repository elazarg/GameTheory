/-
# Game forms

A `GameForm` is utility-free static semantics: a signature plus a play law
sending profiles to outcome laws. It stores its signature; strategies and
outcomes stay owned by that signature and are never duplicated as form fields.

Preferences, utilities, deviations, and every solution concept are defined
elsewhere against this one object.
-/

import GameTheory.Core.Signature
import GameTheory.Math.Probability.Product
import GameTheory.Math.Probability.Mixture
import GameTheory.Math.Probability.Support

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι us uo uo'

variable {ι : Type uι}

/-- The utility-free semantics of a game. Storing the signature makes `us` and
`uo` non-inferable from `GameForm ι`, which is the measured cost of storing the
signature rather than indexing by it. -/
structure GameForm (ι : Type uι) where
  /-- The strategy and outcome carriers. -/
  sig : GameSignature.{uι, us, uo} ι
  /-- The stochastic outcome law of each profile. -/
  play : Profile sig → PMF sig.Outcome

-- Storing the signature must preserve its independent strategy and outcome
-- universes, although the linter sees both only through `GameForm`'s result.

namespace GameForm

/-- Build a game form whose profile determines one outcome. This is the
canonical embedding of deterministic semantics into the law-valued core. -/
abbrev deterministic (sig : GameSignature ι)
    (outcome : Profile sig → sig.Outcome) : GameForm ι where
  sig := sig
  play profile := PMF.pure (outcome profile)

@[simp]
theorem deterministic_play (sig : GameSignature ι)
    (outcome : Profile sig → sig.Outcome) (profile : Profile sig) :
    (deterministic sig outcome).play profile = PMF.pure (outcome profile) :=
  rfl

/-- The outcome law induced by a law over profiles. Every solution concept
compares values of this function, so law-linearity of deviations is built in:
a deviation acts on profiles and is lifted by `bind`. -/
def outcomeLaw (F : GameForm ι) (μ : PMF (Profile F.sig)) : PMF F.sig.Outcome :=
  μ.bind F.play

@[simp]
theorem outcomeLaw_pure (F : GameForm ι) (σ : Profile F.sig) :
    F.outcomeLaw (PMF.pure σ) = F.play σ :=
  PMF.pure_bind ..

theorem outcomeLaw_bind (F : GameForm ι) {α : Type*} (μ : PMF α)
    (f : α → PMF (Profile F.sig)) :
    F.outcomeLaw (μ.bind f) = μ.bind fun a => F.outcomeLaw (f a) :=
  PMF.bind_bind ..

@[simp]
theorem outcomeLaw_map (F : GameForm ι) {α : Type*} (μ : PMF α)
    (f : α → Profile F.sig) :
    F.outcomeLaw (μ.map f) = μ.bind fun a => F.play (f a) :=
  PMF.bind_map ..

/-! ## Outcome relabeling -/

/-- Relabel the outcome carrier of a signature. -/
abbrev _root_.GameTheory.GameSignature.mapOutcome (sig : GameSignature ι) (O : Type uo') :
    GameSignature ι where
  Strategy := sig.Strategy
  Outcome := O

/-- Push outcomes through a relabeling. Strategies, and hence profiles, are
unchanged. -/
abbrev mapOutcome (F : GameForm ι) {O : Type uo'} (f : F.sig.Outcome → O) : GameForm ι where
  sig := F.sig.mapOutcome O
  play σ := (F.play σ).map f

@[simp]
theorem mapOutcome_sig (F : GameForm ι) {O : Type uo'} (f : F.sig.Outcome → O) :
    (F.mapOutcome f).sig = F.sig.mapOutcome O := rfl

@[simp]
theorem mapOutcome_play (F : GameForm ι) {O : Type uo'} (f : F.sig.Outcome → O)
    (σ : Profile F.sig) : (F.mapOutcome f).play σ = (F.play σ).map f := rfl

@[simp]
theorem outcomeLaw_mapOutcome (F : GameForm ι) {O : Type uo'} (f : F.sig.Outcome → O)
    (μ : PMF (Profile F.sig)) :
    (F.mapOutcome f).outcomeLaw μ = (F.outcomeLaw μ).map f := by
  simp only [outcomeLaw, mapOutcome, PMF.map_bind]

/-! ## Recording the chosen profile -/

/-- Record the chosen strategy profile alongside every realized outcome.

The strategy carriers are definitionally unchanged. This is useful when a
downstream evaluator depends on both the selected profile and stochastic
outcome, for example a profile-observed transfer scheme. The construction does
not assert that any player observes the profile. -/
abbrev recordProfile (F : GameForm ι) : GameForm ι where
  sig :=
    { Strategy := F.sig.Strategy
      Outcome := Profile F.sig × F.sig.Outcome }
  play profile := F.play profile |>.map fun outcome => (profile, outcome)

@[simp]
theorem recordProfile_play (F : GameForm ι) (profile : Profile F.sig) :
    F.recordProfile.play profile =
      (F.play profile).map fun outcome => (profile, outcome) :=
  rfl

/-- The outcome law is affine in the law over profiles. -/
theorem outcomeLaw_mix (F : GameForm ι) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (first second : PMF (Profile F.sig)) :
    F.outcomeLaw (mix t h0 h1 first second) =
      mix t h0 h1 (F.outcomeLaw first) (F.outcomeLaw second) :=
  by simpa [outcomeLaw] using mix_bind t h0 h1 first second F.play

/-! ## Mixed extension

Independent randomization needs finitely many players and nothing else. -/

/-- Replace each strategy carrier by PMFs over strategies. -/
abbrev _root_.GameTheory.GameSignature.mixed (sig : GameSignature ι) : GameSignature ι where
  Strategy i := PMF (sig.Strategy i)
  Outcome := sig.Outcome

/-- The utility-free mixed extension: players randomize independently and the
original play law evaluates the realized pure profile. -/
abbrev mixed [Fintype ι] (F : GameForm ι) : GameForm ι where
  sig := F.sig.mixed
  play μ := (independentProduct μ).bind F.play

@[simp]
theorem mixed_sig [Fintype ι] (F : GameForm ι) : F.mixed.sig = F.sig.mixed := rfl

@[simp]
theorem mixed_play [Fintype ι] (F : GameForm ι) (μ : Profile F.sig.mixed) :
    F.mixed.play μ = (independentProduct μ).bind F.play := rfl

/-- The canonical embedding of a pure profile into the mixed extension. -/
def purify (F : GameForm ι) (σ : Profile F.sig) : Profile F.sig.mixed :=
  fun i => PMF.pure (σ i)

/-- The mixed extension restricts to the original play law on pure profiles. -/
@[simp]
theorem mixed_play_purify [Fintype ι] (F : GameForm ι)
    (σ : Profile F.sig) : F.mixed.play (F.purify σ) = F.play σ := by
  show (independentProduct fun i => PMF.pure (σ i)).bind F.play = F.play σ
  rw [independentProduct_pure, PMF.pure_bind]

/-- Replacing one coordinate of an independent product by a law is the same as
mixing the point-mass replacements. This is the linearity of the mixed
extension in a single player's randomization. -/
theorem pi_update_mixed [Fintype ι] [DecidableEq ι] (sig : GameSignature ι)
    (mixedProfile : Profile sig.mixed) (who : ι) (replacement : PMF (sig.Strategy who)) :
    independentProduct (Profile.update mixedProfile who replacement) =
      replacement.bind fun s =>
        independentProduct (Profile.update mixedProfile who (PMF.pure s)) := by
  let updated := Profile.update mixedProfile who replacement
  let kernel : ∀ i, sig.Strategy i → PMF (sig.Strategy i) := fun i a =>
    if h : i = who then PMF.pure a else mixedProfile i
  have hmarg : (fun i => (updated i).bind (kernel i)) = updated := by
    funext i
    by_cases hi : i = who
    · subst i
      simp [updated, kernel, Profile.update_same]
    · simp [updated, kernel, hi, Profile.update_of_ne]
  have hfactor := independentProduct_bind updated kernel
  rw [hmarg] at hfactor
  have hkernel (profile : Profile sig) :
      independentProduct (fun i => kernel i (profile i)) =
        independentProduct (Profile.update mixedProfile who (PMF.pure (profile who))) := by
    congr 1
    funext i
    by_cases hi : i = who
    · subst i
      simp [kernel, Profile.update_same]
    · simp [kernel, hi, Profile.update_of_ne]
  let redraw (s : sig.Strategy who) :=
    independentProduct (Profile.update mixedProfile who (PMF.pure s))
  have heval : (independentProduct updated).map (fun profile => profile who) =
      replacement := by
    rw [independentProduct_map_eval]
    simp [updated, Profile.update_same]
  have hbind : (independentProduct updated).bind (fun profile => redraw (profile who)) =
      independentProduct updated := by
    calc
      (independentProduct updated).bind (fun profile => redraw (profile who)) =
          (independentProduct updated).bind
            (fun profile => independentProduct (fun i => kernel i (profile i))) := by
        apply bind_congr_on_support
        intro profile _
        exact (hkernel profile).symm
      _ = independentProduct updated := hfactor
  calc
    independentProduct updated = replacement.bind redraw := by
      rw [← hbind, ← heval]
      exact (PMF.bind_map (independentProduct updated)
        (fun profile => profile who) redraw).symm

/-- Mapping one coordinate of an independent profile law is the independent
product with that marginal mapped. -/
theorem pi_map_recommendation [Fintype ι] [DecidableEq ι]
    (sig : GameSignature ι) (mixedProfile : Profile sig.mixed)
    (who : ι) (respond : sig.Strategy who → sig.Strategy who) :
    (independentProduct mixedProfile).map
        (fun profile =>
          Profile.update profile who (respond (profile who))) =
      independentProduct
        (Profile.update mixedProfile who
          ((mixedProfile who).map respond)) := by
  let mapSig : GameSignature ι :=
    { Strategy := fun i => sig.Strategy i → sig.Strategy i
      Outcome := sig.Outcome }
  let coordinateMap : Profile mapSig :=
    Profile.update (fun _ => id) who respond
  have hprofile (profile : Profile sig) :
      (fun i => coordinateMap i (profile i)) =
        Profile.update profile who (respond (profile who)) := by
    funext i
    by_cases hi : i = who
    · subst i
      simp [coordinateMap, mapSig, Profile.update_same]
    · simp [coordinateMap, mapSig, hi, Profile.update_of_ne]
  have hmarg : (fun i => (mixedProfile i).map (coordinateMap i)) =
      Profile.update mixedProfile who ((mixedProfile who).map respond) := by
    funext i
    by_cases hi : i = who
    · subst i
      simp [coordinateMap, mapSig, Profile.update_same]
    · simp [coordinateMap, mapSig, hi, Profile.update_of_ne, PMF.map_id]
  have hmap (profile : Profile sig) :
      (fun i => coordinateMap i (profile i)) =
        Profile.update profile who (respond (profile who)) := hprofile profile
  calc
    (independentProduct mixedProfile).map
        (fun profile => Profile.update profile who (respond (profile who))) =
      (independentProduct mixedProfile).map
        (fun profile i => coordinateMap i (profile i)) := by
          congr 1
          funext profile
          exact (hmap profile).symm
    _ = independentProduct (fun i => (mixedProfile i).map (coordinateMap i)) :=
      independentProduct_map mixedProfile coordinateMap
    _ = independentProduct
        (Profile.update mixedProfile who ((mixedProfile who).map respond)) := by
      rw [hmarg]

/-- The mixed extension's play law is affine in one player's randomization. -/
theorem mixed_play_update [Fintype ι] [DecidableEq ι] (F : GameForm ι)
    (mixedProfile : Profile F.sig.mixed) (who : ι)
    (replacement : PMF (F.sig.Strategy who)) :
    F.mixed.play (Profile.update mixedProfile who replacement) =
      replacement.bind fun s =>
        F.mixed.play (Profile.update mixedProfile who (PMF.pure s)) := by
  rw [mixed_play, pi_update_mixed F.sig mixedProfile who replacement, PMF.bind_bind]

end GameForm

end GameTheory
