/-
# EXP-093: executable client transformation adequacy

This hostile slice starts from the executable rational table frontend and ends
in a client-facing game whose heterogeneous actions, player names, and realized
outcomes have all changed.  The sole strategic meaning remains canonical
`IsNash`; the experiment asks whether the existing exact refinement and
transformation theorems compose cleanly enough for an unrelated client.
-/

import GameTheory.Core.Transform
import GameTheory.Finite.Correctness

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.RuntimeTransformAdequacy

open GameTheory.Math.Probability

/-! ## An executable domain game with heterogeneous actions -/

/-- Player `false` chooses a Boolean switch; player `true` chooses one of three
modes.  This unequal action topology is intentional. -/
abbrev RuntimeAction : Bool → Type
  | false => Bool
  | true => Fin 3

/-- The structured trace emitted by the domain runtime. -/
structure RuntimeTrace where
  left : Bool
  right : Fin 3
  coordinated : Bool
deriving DecidableEq, Repr

/-- Compile a realized heterogeneous action profile to the runtime trace. -/
def traceOf (profile : ∀ who, RuntimeAction who) : RuntimeTrace where
  left := profile false
  right := profile true
  coordinated := profile false == decide (profile true = (2 : Fin 3))

/-- Exact rational payoffs are read from the realized runtime trace. -/
def tracePayoff (trace : RuntimeTrace) (who : Bool) : ℚ :=
  if who then
    if trace.right = (2 : Fin 3) then 3 else 0
  else
    if trace.coordinated = true then 2 else 0

/-- The executable source game.  Player `false` wants its switch to predict
whether mode two is selected; player `true` strictly prefers mode two. -/
def runtimeGame : Finite.TableGame Bool where
  Action := RuntimeAction
  actionFintype := fun who => by cases who <;> infer_instance
  actionDecEq := fun who => by cases who <;> infer_instance
  payoff profile := tracePayoff (traceOf profile)

/-- The semantic utility on client-facing traces. -/
def traceUtility : Utility
    ((runtimeGame.toForm.mapOutcome traceOf).sig) :=
  fun trace who => (tracePayoff trace who : ℝ)

/-- In the source table, `true` paired with mode two is an equilibrium. -/
def equilibriumProfile : ∀ who, RuntimeAction who
  | false => true
  | true => 2

/-- The all-low profile is not an equilibrium because player `true` can choose
mode two. -/
def refutedProfile : ∀ who, RuntimeAction who
  | false => false
  | true => 0

theorem equilibrium_isNash_true :
    runtimeGame.isNash equilibriumProfile = true := by
  rfl

theorem refuted_isNash_false :
    runtimeGame.isNash refutedProfile = false := by
  rfl

/-! ## Independent domain command carriers -/

/-- A domain command is not definitionally a Boolean action. -/
structure ToggleCommand where
  code : Bool
deriving DecidableEq, Fintype, Repr

/-- A domain mode command is not definitionally a `Fin 3` action. -/
structure ModeCommand where
  code : Fin 3
deriving DecidableEq, Fintype, Repr

abbrev Command : Bool → Type
  | false => ToggleCommand
  | true => ModeCommand

def toggleWrap : Bool ≃ ToggleCommand where
  toFun := ToggleCommand.mk
  invFun := ToggleCommand.code
  left_inv _ := rfl
  right_inv := by rintro ⟨code⟩; rfl

def modeWrap : Fin 3 ≃ ModeCommand where
  toFun := ModeCommand.mk
  invFun := ModeCommand.code
  left_inv _ := rfl
  right_inv := by rintro ⟨code⟩; rfl

/-- Both domain encodings are deliberately nonidentity: the switch is flipped
and modes zero and two are exchanged before wrapping. -/
def commandEquiv : ∀ who, RuntimeAction who ≃ Command who
  | false => (Equiv.swap false true).trans toggleWrap
  | true => (Equiv.swap (0 : Fin 3) 2).trans modeWrap

/-- The target application names the old players in the opposite order. -/
def playerSwap : Bool ≃ Bool := Equiv.swap false true

/-! ## The complete exact bridge -/

/-- The client form emits runtime traces, accepts domain commands, and uses the
client's player indexing. -/
abbrev transformedForm : GameForm Bool :=
  ((runtimeGame.toForm.mapOutcome traceOf).relabelStrategies commandEquiv)
    |>.reindexPlayers playerSwap

/-- Utilities stay attached to the corresponding source player after the
client's player reindexing. -/
abbrev transformedPreference : WeakPreference Bool RuntimeTrace :=
  Preference.reindexPlayers playerSwap (euPreference traceUtility)

/-- Compile an executable source profile into the client's command and player
coordinates. -/
def transformedProfile (profile : Profile runtimeGame.sig) :
    Profile transformedForm.sig :=
  Profile.reindexPlayers playerSwap
    (Profile.relabelStrategies commandEquiv profile)

/-- The complete transformed runtime still realizes exactly the source trace.
This is an execution law, not a new runner. -/
theorem transformed_play (profile : Profile runtimeGame.sig) :
    transformedForm.play (transformedProfile profile) =
      FinDist.pure (traceOf profile) := by
  simp [transformedForm, transformedProfile]

/-- Executable Nash recognition is exactly canonical Nash after the client has
changed outcomes, both heterogeneous action carriers, and player indexing. -/
theorem transformed_isNash_iff (profile : Profile runtimeGame.sig) :
    IsNash transformedForm transformedPreference
        (transformedProfile profile) ↔
      runtimeGame.isNash profile = true := by
  calc
    IsNash transformedForm transformedPreference
        (transformedProfile profile) ↔
      IsNash
        ((runtimeGame.toForm.mapOutcome traceOf).relabelStrategies commandEquiv)
        (euPreference traceUtility)
        (Profile.relabelStrategies commandEquiv profile) :=
      isNash_reindexPlayers
        ((runtimeGame.toForm.mapOutcome traceOf).relabelStrategies commandEquiv)
        (euPreference traceUtility) playerSwap
        (Profile.relabelStrategies commandEquiv profile)
    _ ↔ IsNash (runtimeGame.toForm.mapOutcome traceOf)
        (euPreference traceUtility) profile :=
      isNash_relabelStrategies (runtimeGame.toForm.mapOutcome traceOf)
        (euPreference traceUtility) commandEquiv profile
    _ ↔ IsNash runtimeGame.toForm
        (euPreference fun outcome => traceUtility (traceOf outcome)) profile :=
      isNash_mapOutcome runtimeGame.toForm traceOf traceUtility profile
    _ ↔ IsNash runtimeGame.toForm (euPreference runtimeGame.utility) profile := by
      rfl
    _ ↔ runtimeGame.isNash profile = true :=
      (runtimeGame.isNash_eq_true_iff profile).symm

theorem transformed_equilibrium :
    IsNash transformedForm transformedPreference
      (transformedProfile equilibriumProfile) :=
  (transformed_isNash_iff equilibriumProfile).2 equilibrium_isNash_true

theorem transformed_refuted :
    ¬ IsNash transformedForm transformedPreference
      (transformedProfile refutedProfile) := by
  intro h
  have htrue := (transformed_isNash_iff refutedProfile).1 h
  rw [refuted_isNash_false] at htrue
  simp at htrue

/-! ## Negative control: lossy outcome summaries -/

/-- A tempting one-bit outcome presentation forgets payoff-relevant data. -/
def lossySummary (trace : RuntimeTrace) : Bool := trace.coordinated

/-- These two profiles receive the same lossy label. -/
theorem same_lossy_summary :
    lossySummary (traceOf refutedProfile) =
      lossySummary (traceOf equilibriumProfile) := by
  rfl

/-- Nevertheless player `true`'s exact payoff differs, so the lossy label
cannot support this game's utility semantics. -/
theorem lossy_summary_forgets_payoff :
    tracePayoff (traceOf refutedProfile) true ≠
      tracePayoff (traceOf equilibriumProfile) true := by
  decide

end GameTheory.Experimental.PostArchitecture.RuntimeTransformAdequacy
