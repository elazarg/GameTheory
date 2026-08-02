/-
# Game forms

A `GameForm` is utility-free static semantics: a signature plus a play law
sending profiles to outcome laws. It stores its signature; strategies and
outcomes stay owned by that signature and are never duplicated as form fields.

Preferences, utilities, deviations, and every solution concept are defined
elsewhere against this one object.
-/

import GameTheory.Core.Signature
import GameTheory.Probability.FinDist

noncomputable section

namespace GameTheory

open Probability

universe uι us uo uo'

variable {ι : Type uι}

set_option linter.checkUnivs false in
/-- The utility-free semantics of a game. Storing the signature makes `us` and
`uo` non-inferable from `GameForm ι`, which is the measured cost of storing the
signature rather than indexing by it. -/
structure GameForm (ι : Type uι) where
  /-- The strategy and outcome carriers. -/
  sig : GameSignature.{uι, us, uo} ι
  /-- The stochastic outcome law of each profile. -/
  play : Profile sig → FinDist sig.Outcome

namespace GameForm

/-- The outcome law induced by a law over profiles. Every solution concept
compares values of this function, so law-linearity of deviations is built in:
a deviation acts on profiles and is lifted by `bind`. -/
def outcomeLaw (F : GameForm ι) (μ : FinDist (Profile F.sig)) : FinDist F.sig.Outcome :=
  μ.bind F.play

@[simp]
theorem outcomeLaw_pure (F : GameForm ι) (σ : Profile F.sig) :
    F.outcomeLaw (FinDist.pure σ) = F.play σ :=
  FinDist.pure_bind ..

theorem outcomeLaw_bind (F : GameForm ι) {α : Type*} (μ : FinDist α)
    (f : α → FinDist (Profile F.sig)) :
    F.outcomeLaw (μ.bind f) = μ.bind fun a => F.outcomeLaw (f a) :=
  FinDist.bind_bind ..

@[simp]
theorem outcomeLaw_map (F : GameForm ι) {α : Type*} (μ : FinDist α)
    (f : α → Profile F.sig) :
    F.outcomeLaw (μ.map f) = μ.bind fun a => F.play (f a) :=
  FinDist.bind_map ..

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
    (μ : FinDist (Profile F.sig)) :
    (F.mapOutcome f).outcomeLaw μ = (F.outcomeLaw μ).map f := by
  simp only [outcomeLaw, mapOutcome, FinDist.map_eq_bind, FinDist.bind_bind]

/-- The outcome law is affine in the law over profiles. -/
theorem outcomeLaw_mix (F : GameForm ι) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (first second : FinDist (Profile F.sig)) :
    F.outcomeLaw (FinDist.mix t h0 h1 first second) =
      FinDist.mix t h0 h1 (F.outcomeLaw first) (F.outcomeLaw second) :=
  FinDist.mix_bind ..

/-! ## Mixed extension

Independent randomization needs finitely many players and nothing else. -/

/-- Replace each strategy carrier by its finite-support laws. -/
abbrev _root_.GameTheory.GameSignature.mixed (sig : GameSignature ι) : GameSignature ι where
  Strategy i := FinDist (sig.Strategy i)
  Outcome := sig.Outcome

/-- The utility-free mixed extension: players randomize independently and the
original play law evaluates the realized pure profile. -/
abbrev mixed [Fintype ι] (F : GameForm ι) : GameForm ι where
  sig := F.sig.mixed
  play μ := (FinDist.pi μ).bind F.play

@[simp]
theorem mixed_sig [Fintype ι] (F : GameForm ι) : F.mixed.sig = F.sig.mixed := rfl

@[simp]
theorem mixed_play [Fintype ι] (F : GameForm ι) (μ : Profile F.sig.mixed) :
    F.mixed.play μ = (FinDist.pi μ).bind F.play := rfl

/-- The canonical embedding of a pure profile into the mixed extension. -/
def purify [Fintype ι] (F : GameForm ι) (σ : Profile F.sig) : Profile F.sig.mixed :=
  fun i => FinDist.pure (σ i)

/-- The mixed extension restricts to the original play law on pure profiles. -/
@[simp]
theorem mixed_play_purify [Fintype ι] [DecidableEq ι] (F : GameForm ι)
    (σ : Profile F.sig) : F.mixed.play (F.purify σ) = F.play σ := by
  show (FinDist.pi fun i => FinDist.pure (σ i)).bind F.play = F.play σ
  rw [FinDist.pi_pure, FinDist.pure_bind]

/-- Replacing one coordinate of an independent product by a law is the same as
mixing the point-mass replacements. This is the linearity of the mixed
extension in a single player's randomization. -/
theorem pi_update_mixed [Fintype ι] [DecidableEq ι] (sig : GameSignature ι)
    (mixedProfile : Profile sig.mixed) (who : ι) (replacement : FinDist (sig.Strategy who)) :
    FinDist.pi (Profile.update mixedProfile who replacement) =
      replacement.bind fun s =>
        FinDist.pi (Profile.update mixedProfile who (FinDist.pure s)) := by
  refine FinDist.ext_of_prob fun profile => ?_
  have split : ∀ law : FinDist (sig.Strategy who),
      (∏ i, ((Profile.update mixedProfile who law) i).prob (profile i)) =
        law.prob (profile who) *
          ∏ i ∈ Finset.univ.erase who, (mixedProfile i).prob (profile i) := by
    intro law
    rw [← Finset.mul_prod_erase Finset.univ
      (fun i => ((Profile.update mixedProfile who law) i).prob (profile i))
      (Finset.mem_univ who)]
    congr 1
    · rw [Profile.update_same]
    · exact Finset.prod_congr rfl fun i hi => by
        rw [Profile.update_of_ne _ _ (Finset.ne_of_mem_erase hi)]
  rw [FinDist.prob_bind]
  simp only [FinDist.prob_pi, split]
  rw [FinDist.expect_mul_const, FinDist.expect_prob_pure]

/-- Mapping one coordinate of an independent profile law is the independent
product with that marginal mapped. -/
theorem pi_map_recommendation [Fintype ι] [DecidableEq ι]
    (sig : GameSignature ι) (mixedProfile : Profile sig.mixed)
    (who : ι) (respond : sig.Strategy who → sig.Strategy who) :
    (FinDist.pi mixedProfile).map
        (fun profile =>
          Profile.update profile who (respond (profile who))) =
      FinDist.pi
        (Profile.update mixedProfile who
          ((mixedProfile who).map respond)) := by
  rw [FinDist.pi_eq_map_product who mixedProfile, FinDist.map_comp]
  rw [FinDist.pi_eq_map_product who
    (Profile.update mixedProfile who ((mixedProfile who).map respond))]
  rw [Profile.update_same]
  have hrest :
      (fun j : {j // j ≠ who} =>
        (Profile.update mixedProfile who
          ((mixedProfile who).map respond)) j.1) =
        fun j : {j // j ≠ who} => mixedProfile j.1 := by
    funext j
    rw [Profile.update_of_ne _ _ j.2]
  rw [hrest]
  have hproduct :
      FinDist.product ((mixedProfile who).map respond)
          (FinDist.pi fun j : {j // j ≠ who} => mixedProfile j.1) =
        (FinDist.product (mixedProfile who)
          (FinDist.pi fun j : {j // j ≠ who} => mixedProfile j.1)).map
            (Prod.map respond id) := by
    rw [FinDist.map_product]
    simp
  rw [hproduct, FinDist.map_comp]
  congr 1
  funext pair
  apply (Equiv.piSplitAt who sig.Strategy).injective
  apply Prod.ext
  · simp
  · funext j
    simp [Profile.update_of_ne _ _ j.2]
    split
    · rename_i h
      exact False.elim (j.2 h)
    · rfl

/-- The mixed extension's play law is affine in one player's randomization. -/
theorem mixed_play_update [Fintype ι] [DecidableEq ι] (F : GameForm ι)
    (mixedProfile : Profile F.sig.mixed) (who : ι)
    (replacement : FinDist (F.sig.Strategy who)) :
    F.mixed.play (Profile.update mixedProfile who replacement) =
      replacement.bind fun s =>
        F.mixed.play (Profile.update mixedProfile who (FinDist.pure s)) := by
  rw [mixed_play, pi_update_mixed F.sig mixedProfile who replacement, FinDist.bind_bind]

end GameForm

end GameTheory
