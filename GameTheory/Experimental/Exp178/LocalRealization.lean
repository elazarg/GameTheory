module

/-
EXP-178: consent labels and affected coordinates remain separate.
The existing scheme realizes the validated matching displacement with two
consenters, three affected coordinates and a fourth untouched spectator.
Both deterministic spectator endpoints and their genuine mixture are exact.
This is a fixed displacement family, not a general matching compilation.
-/

public import GameTheory.Experimental.Exp177.MatchingConsent
public import GameTheory.Math.Probability.FiniteUniform

@[expose] public section

noncomputable section

namespace GameTheory.Experimental.LocalRealization

open GameTheory.Math.Probability
open GameTheory.Experimental.MatchingConsent

/-- Original assignment actors together with one unrelated spectator. -/
abbrev Actor := (Bool ⊕ Unit) ⊕ Unit

@[reducible]
def signature : GameSignature Actor where
  Strategy
    | .inl active => assignmentSignature.Strategy active
    | .inr _ => Bool
  Outcome := Unit

def extendProfile (profile : Profile assignmentSignature) (spectator : Bool) : Profile signature
  | .inl active => profile active
  | .inr _ => spectator

def sourceWithSpectator (bit : Bool) : Profile signature := extendProfile sourceProfile bit

def targetWithSpectator (bit : Bool) : Profile signature := extendProfile targetProfile bit

def affected : Finset Actor :=
  {.inl (.inl false), .inl (.inl true), .inl (.inr ())}

def consenting : Finset Actor := {.inl (.inl true), .inl (.inr ())}

theorem consenting_card : consenting.card = 2 := by decide

theorem affected_card : affected.card = 3 := by decide

theorem actor_card : Fintype.card Actor = 4 := by decide

theorem consenting_subset_affected : consenting ⊆ affected := by decide

theorem spectator_not_affected : (Sum.inr () : Actor) ∉ affected := by
  simp [affected]

theorem incumbent_not_consenting : (Sum.inl (.inl false) : Actor) ∉ consenting := by
  simp [consenting]

theorem affected_not_all : affected ≠ Finset.univ := by
  intro heq
  apply spectator_not_affected
  rw [heq]
  exact Finset.mem_univ _

/-- The local input loses the spectator bit before any kernel sees it. -/
theorem local_inputs_ignore_spectator (left right : Bool) :
    Profile.restrict affected (sourceWithSpectator left) =
      Profile.restrict affected (sourceWithSpectator right) := by
  funext coordinate
  rcases coordinate with ⟨actor, member⟩
  rcases actor with active | spectator
  · rfl
  · cases spectator
    exact (spectator_not_affected member).elim

/-- This exclusion holds for every kernel on the permitted local-input type,
not just the particular constant replacement used below. -/
theorem local_kernel_ignores_spectator
    (kernel : Subprofile signature affected → PMF (Subprofile signature affected))
    (left right : Bool) :
    kernel (Profile.restrict affected (sourceWithSpectator left)) =
      kernel (Profile.restrict affected (sourceWithSpectator right)) :=
  congrArg kernel (local_inputs_ignore_spectator left right)

/-- The judge label is independent of the three assignment coordinates this
fixed displacement rewrites. The spectator is absent from the local input. -/
def scheme : DeviationScheme signature Unit where
  members _ := affected
  Dev _ := Unit
  actLocal _ _ _ := PMF.pure (Profile.restrict affected (targetWithSpectator false))

/-- Restricting the replacement to affected coordinates discards its reference
spectator value. Overriding preserves the actual source spectator instead. -/
theorem override_realizes_target (bit : Bool) :
    Profile.override affected (Profile.restrict affected (targetWithSpectator false))
        (sourceWithSpectator bit) = targetWithSpectator bit := by
  funext actor
  rcases actor with active | spectator
  · rcases active with doctor | hospital
    · cases doctor <;>
        simp [Profile.override, Profile.restrict, affected, extendProfile,
          targetWithSpectator]
    · cases hospital
      simp [Profile.override, Profile.restrict, affected, extendProfile,
        targetWithSpectator]
  · cases spectator
    simp [Profile.override, affected, extendProfile,
      sourceWithSpectator, targetWithSpectator]

set_option backward.isDefEq.respectTransparency false in
/-- Exact profile-law realization retains every heterogeneous assignment and
both possible spectator values. -/
theorem scheme_applies (bit : Bool) :
    scheme.apply (PMF.pure (sourceWithSpectator bit)) () () =
      PMF.pure (targetWithSpectator bit) := by
  rw [DeviationScheme.apply_pure]
  simp only [scheme, PMF.pure_map]
  rw [override_realizes_target]

/-- The canonical frame theorem is nonvacuous: every produced spectator
coordinate comes from some supported source profile. -/
theorem spectator_frame (law : PMF (Profile signature))
    {result : Profile signature} (hresult : result ∈ (scheme.apply law () ()).support) :
    ∃ original ∈ law.support, result (.inr ()) = original (.inr ()) := by
  obtain ⟨original, supported, hagree⟩ := scheme.exists_agree_off_members law () () hresult
  exact ⟨original, supported, hagree (.inr ()) spectator_not_affected⟩

/-- Consent-only rewrites still fail in this enlarged encoding: the displaced
incumbent is outside their footprint and its assignment must change. -/
theorem no_consent_local_rewrite {Deviator : Type*}
    (D : DeviationScheme signature Deviator) (who : Deviator) (deviation : D.Dev who)
    (footprint : (D.members who : Set Actor) ⊆ (consenting : Set Actor)) (bit : Bool) :
    targetWithSpectator bit ∉
      (D.apply (PMF.pure (sourceWithSpectator bit)) who deviation).support := by
  intro htarget
  obtain ⟨original, supported, hagree⟩ :=
    D.exists_agree_off_members (PMF.pure (sourceWithSpectator bit)) who deviation htarget
  have horiginal : original = sourceWithSpectator bit :=
    (PMF.mem_support_pure_iff _ _).1 supported
  subst original
  have houtside : (Sum.inl (.inl false) : Actor) ∉ D.members who :=
    fun member => incumbent_not_consenting (footprint member)
  have hsame := hagree (.inl (.inl false)) houtside
  exact displaced_incumbent_outside_consent.2 hsame

def fairCoin : PMF Bool := uniformLaw Bool

def randomSource : PMF (Profile signature) :=
  fairCoin.bind fun bit => PMF.pure (sourceWithSpectator bit)

def randomTarget : PMF (Profile signature) :=
  fairCoin.bind fun bit => PMF.pure (targetWithSpectator bit)

set_option backward.isDefEq.respectTransparency false in
/-- Structural law-linearity transports the random spectator without
inspecting the status-quo law in the local kernel. -/
theorem scheme_applies_random : scheme.apply randomSource () () = randomTarget := by
  simp only [randomSource, randomTarget, DeviationScheme.apply_bind, scheme_applies]

theorem target_endpoints_distinct : targetWithSpectator false ≠ targetWithSpectator true := by
  intro heq
  have hbit := congrFun heq (.inr ())
  exact Bool.false_ne_true hbit

theorem randomTarget_support (bit : Bool) : targetWithSpectator bit ∈ randomTarget.support := by
  apply (PMF.mem_support_bind_iff fairCoin
    (fun bit => PMF.pure (targetWithSpectator bit)) (targetWithSpectator bit)).2
  exact ⟨bit, mem_support_uniformLaw bit, by simp⟩

theorem randomTarget_positive (bit : Bool) : 0 < randomTarget (targetWithSpectator bit) :=
  (randomTarget.apply_pos_iff _).2 (randomTarget_support bit)

/-- The complete spectator distribution, not only its support, is retained. -/
theorem randomTarget_spectator :
    randomTarget.map (fun profile => profile (.inr ())) = fairCoin := by
  simp only [randomTarget, PMF.map_bind, PMF.pure_map]
  exact PMF.bind_pure fairCoin

/-- Neither spectator endpoint is collapsed: the output is not a point mass. -/
theorem randomTarget_not_pure (profile : Profile signature) : randomTarget ≠ PMF.pure profile := by
  intro heq
  have hfalse := randomTarget_support false
  have htrue := randomTarget_support true
  rw [heq] at hfalse htrue
  exact target_endpoints_distinct
    (((PMF.mem_support_pure_iff _ _).1 hfalse).trans
      ((PMF.mem_support_pure_iff _ _).1 htrue).symm)

/-- Projection onto active actors recovers exactly the previously validated
matching assignments; no new matching evaluator is introduced. -/
theorem source_projection (bit : Bool) (active : Bool ⊕ Unit) :
    sourceWithSpectator bit (.inl active) = sourceProfile active := rfl

theorem target_projection (bit : Bool) (active : Bool ⊕ Unit) :
    targetWithSpectator bit (.inl active) = targetProfile active := rfl

theorem newcomer_gain (bit : Bool) :
    Preference.strict rankings.prefersLeft true
      (targetWithSpectator bit (.inl (.inl true)))
      (sourceWithSpectator bit (.inl (.inl true))) :=
  newcomer_strictly_improves

theorem hospital_gain (bit : Bool) :
    Preference.strict rankings.prefersRight ()
      (targetWithSpectator bit (.inl (.inr ())))
      (sourceWithSpectator bit (.inl (.inr ()))) :=
  hospital_strictly_improves

theorem incumbent_loss (bit : Bool) :
    Preference.strict rankings.prefersLeft false
      (sourceWithSpectator bit (.inl (.inl false)))
      (targetWithSpectator bit (.inl (.inl false))) :=
  displaced_incumbent_strictly_worse

end GameTheory.Experimental.LocalRealization
