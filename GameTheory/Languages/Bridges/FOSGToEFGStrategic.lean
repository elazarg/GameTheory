/-
# Strategic transfer for explicit-order FOSG serialization

The structural serializer exposes an equivalence between source behavioral
policies and serialized EFG behavioral policies, together with an exact law
after administrative microsteps are erased.  This leaf attaches an external
history utility to that law and transfers exact and approximate
expected-utility Nash.

The serialization order remains explicit.  No utility or solution concept is
stored in FOSG syntax, and no bridge-specific equilibrium predicate is added.
-/

import GameTheory.Languages.Bridges.FOSGToEFG
import GameTheory.Core.Approximate
import GameTheory.Core.Utility

noncomputable section

namespace GameTheory.Languages.Bridges.FOSGToEFG

open GameTheory.Languages
open GameTheory.Math.Probability
open GameTheory.Protocol

universe uι us ua up uq uk

variable {ι : Type uι}
variable (G : FOSG.Game.{uι, us, ua, up, uq, uk} ι)
variable (order : ExplicitOrder ι)
variable [DecidableEq ι]

/-- Source and serialized behavioral profiles are the same strategic data. -/
private def behavioralProfileEquiv :
    Profile G.information.behavioralSignature ≃
      Profile (information G order).behavioralSignature where
  toFun := translateBehavioral G order
  invFun := projectBehavioral G order
  left_inv := project_translate_profile G order
  right_inv := translate_project_profile G order

/-- Evaluate a serialized history by erasing its administrative microsteps
and applying the caller's source-history utility. -/
def serializedUtility (utility : G.History → ι → ℝ) :
    (execution G order).History → ι → ℝ :=
  fun history who => utility (eraseHistory G order history) who

/-- Projecting a unilateral serialized deviation changes only the same source
player's complete behavioral policy. -/
theorem projectBehavioral_update
    (target : (player : ι) →
      (information G order).BehavioralPolicy player)
    (who : ι) (replacement : (information G order).BehavioralPolicy who) :
    projectBehavioral G order
        (Profile.update
          (sig := (information G order).behavioralSignature)
          target who replacement) =
      Profile.update (sig := G.information.behavioralSignature)
        (projectBehavioral G order target) who
        (projectBehavioral G order
          (Profile.update
            (sig := (information G order).behavioralSignature)
            target who replacement) who) := by
  funext player
  by_cases hplayer : player = who
  · subst player
    simp
  · rw [Profile.update_of_ne
      (sig := G.information.behavioralSignature)
      (projectBehavioral G order target) _ hplayer]
    funext source
    unfold projectBehavioral
    rw [Profile.update_of_ne
      (sig := (information G order).behavioralSignature)
      target replacement hplayer]

/-- Translating a unilateral source deviation changes only the same player in
the serialized profile. -/
theorem translateBehavioral_update
    (source : (player : ι) → G.information.BehavioralPolicy player)
    (who : ι) (replacement : G.information.BehavioralPolicy who) :
    translateBehavioral G order
        (Profile.update (sig := G.information.behavioralSignature)
          source who replacement) =
      Profile.update (sig := (information G order).behavioralSignature)
        (translateBehavioral G order source) who
        (translateBehavioral G order
          (Profile.update (sig := G.information.behavioralSignature)
            source who replacement) who) := by
  funext player
  by_cases hplayer : player = who
  · subst player
    simp
  · rw [Profile.update_of_ne
      (sig := (information G order).behavioralSignature)
      (translateBehavioral G order source) _ hplayer]
    funext view
    unfold translateBehavioral
    rw [Profile.update_of_ne
      (sig := G.information.behavioralSignature)
      source replacement hplayer]

/-- A unilateral source deviation translated from the projection of an
arbitrary target profile is a unilateral deviation of that target profile. -/
theorem translateBehavioral_project_update
    (target : (player : ι) →
      (information G order).BehavioralPolicy player)
    (who : ι) (replacement : G.information.BehavioralPolicy who) :
    translateBehavioral G order
        (Profile.update (sig := G.information.behavioralSignature)
          (projectBehavioral G order target) who replacement) =
      Profile.update (sig := (information G order).behavioralSignature)
        target who
        (translateBehavioral G order
          (Profile.update (sig := G.information.behavioralSignature)
            (projectBehavioral G order target) who replacement)
          who) := by
  calc
    _ = Profile.update (sig := (information G order).behavioralSignature)
        (translateBehavioral G order (projectBehavioral G order target)) who
        (translateBehavioral G order
          (Profile.update (sig := G.information.behavioralSignature)
            (projectBehavioral G order target) who replacement) who) :=
      translateBehavioral_update G order
        (projectBehavioral G order target) who replacement
    _ = _ := by rw [translate_project_profile]

variable [Fintype ι]

/-- Erasing serialized microsteps preserves each player's expected utility for
an arbitrary target behavioral profile. -/
theorem expectedUtility_serialized_eq_source
    (utility : G.History → ι → ℝ) (who : ι)
    (target : (player : ι) →
      (information G order).BehavioralPolicy player)
    (rounds : ℕ) :
    expectedUtility (serializedUtility G order utility) who
        ((information G order).runBehavioral target
          (rounds * roundWidth order)) =
      expectedUtility utility who
        (G.information.runBehavioral
          (projectBehavioral G order target) rounds) := by
  calc
    _ = expectedUtility utility who
        (FinDist.map (eraseHistory G order)
          ((information G order).runBehavioral target
            (rounds * roundWidth order))) :=
      (expectedUtility_map utility who (eraseHistory G order) _).symm
    _ = _ := congrArg (expectedUtility utility who)
      (map_erase_runBehavioral_eq_source G order target rounds)

/-- Behavioral approximate Nash is invariant under explicit-order FOSG
serialization at the same real slack. -/
theorem isεNash_serialized_iff_source
    (utility : G.History → ι → ℝ)
    (target : Profile (information G order).behavioralSignature)
    (rounds : ℕ) (ε : ℝ) :
    IsεNash
        ((information G order).toBehavioralGameForm
          (rounds * roundWidth order))
        (serializedUtility G order utility) ε target ↔
      IsεNash (G.information.toBehavioralGameForm rounds) utility ε
        (projectBehavioral G order target) := by
  let equivalence := behavioralProfileEquiv G order
  have hforward :
      ∀ sourceProfile who replacement,
        ∃ targetReplacement,
          equivalence (Profile.update sourceProfile who replacement) =
            Profile.update (equivalence sourceProfile) who
              targetReplacement := by
    intro sourceProfile who replacement
    refine ⟨translateBehavioral G order
      (Profile.update sourceProfile who replacement) who, ?_⟩
    exact translateBehavioral_update G order sourceProfile who replacement
  have hbackward :
      ∀ sourceProfile who targetReplacement,
        ∃ replacement,
          equivalence (Profile.update sourceProfile who replacement) =
            Profile.update (equivalence sourceProfile) who
              targetReplacement := by
    intro sourceProfile who targetReplacement
    let updatedTarget :=
      Profile.update (translateBehavioral G order sourceProfile) who
        targetReplacement
    let replacement := projectBehavioral G order updatedTarget who
    refine ⟨replacement, ?_⟩
    have hproject :
        projectBehavioral G order updatedTarget =
          Profile.update (sig := G.information.behavioralSignature)
            sourceProfile who replacement := by
      calc
        projectBehavioral G order updatedTarget =
            Profile.update (sig := G.information.behavioralSignature)
              (projectBehavioral G order
                (translateBehavioral G order sourceProfile)) who
              replacement := by
          simpa only [updatedTarget, replacement] using
            projectBehavioral_update G order
              (translateBehavioral G order sourceProfile) who
              targetReplacement
        _ = Profile.update (sig := G.information.behavioralSignature)
            sourceProfile who replacement := by
          rw [project_translate_profile]
    calc
      equivalence (Profile.update sourceProfile who replacement) =
          equivalence (projectBehavioral G order updatedTarget) :=
        congrArg equivalence hproject.symm
      _ = updatedTarget := equivalence.apply_symm_apply updatedTarget
      _ = Profile.update (equivalence sourceProfile) who
          targetReplacement := rfl
  have hexpected :
      ∀ targetProfile who,
        expectedUtility (serializedUtility G order utility) who
            (((information G order).toBehavioralGameForm
              (rounds * roundWidth order)).play targetProfile) =
          expectedUtility utility who
            ((G.information.toBehavioralGameForm rounds).play
              (equivalence.symm targetProfile)) := by
    intro targetProfile who
    exact expectedUtility_serialized_eq_source G order utility who
      targetProfile rounds
  have htransport :=
    isεNash_iff_of_profileEquiv_of_expectedUtility_eq
      (G.information.toBehavioralGameForm rounds)
      ((information G order).toBehavioralGameForm
        (rounds * roundWidth order))
      utility (serializedUtility G order utility) equivalence
      hforward hbackward hexpected ε
      (projectBehavioral G order target)
  have htarget :
      equivalence (projectBehavioral G order target) = target :=
    equivalence.apply_symm_apply target
  rw [htarget] at htransport
  exact htransport

/-- Behavioral expected-utility Nash is invariant under explicit-order
serialization.  Every serialized deviation projects to a deviation by the
same source player, and every source deviation translates back to that player;
administrative phases never become strategic coordinates. -/
theorem isNash_serialized_iff_source
    (utility : G.History → ι → ℝ)
    (target : (player : ι) →
      (information G order).BehavioralPolicy player)
    (rounds : ℕ) :
    IsNash
        ((information G order).toBehavioralGameForm
          (rounds * roundWidth order))
        (euPreference (serializedUtility G order utility)) target ↔
      IsNash (G.information.toBehavioralGameForm rounds)
        (euPreference utility) (projectBehavioral G order target) := by
  rw [isNash_iff_isεNash_zero, isNash_iff_isεNash_zero]
  exact isεNash_serialized_iff_source G order utility target rounds 0

/-- The source-facing approximate-equilibrium transfer theorem. -/
theorem isεNash_translateBehavioral_iff
    (utility : G.History → ι → ℝ)
    (source : Profile G.information.behavioralSignature)
    (rounds : ℕ) (ε : ℝ) :
    IsεNash
        ((information G order).toBehavioralGameForm
          (rounds * roundWidth order))
        (serializedUtility G order utility) ε
        (translateBehavioral G order source) ↔
      IsεNash (G.information.toBehavioralGameForm rounds) utility ε
        source := by
  rw [isεNash_serialized_iff_source, project_translate_profile]

/-- The source-facing form of the transfer theorem. -/
theorem isNash_translateBehavioral_iff
    (utility : G.History → ι → ℝ)
    (source : (player : ι) → G.information.BehavioralPolicy player)
    (rounds : ℕ) :
    IsNash
        ((information G order).toBehavioralGameForm
          (rounds * roundWidth order))
        (euPreference (serializedUtility G order utility))
        (translateBehavioral G order source) ↔
      IsNash (G.information.toBehavioralGameForm rounds)
        (euPreference utility) source := by
  rw [isNash_serialized_iff_source, project_translate_profile]

end GameTheory.Languages.Bridges.FOSGToEFG
