/-
# Experiment 111: realizable stochastic public histories

This file is deliberately experiment-only.  Public histories are related to
play by the image of the canonical Protocol history projection; no second
history carrier or runner is introduced.
-/

import GameTheory.Tests.StochasticContinuation
import Mathlib.Tactic.NormNum

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.StochasticPublicHistoryCoherence

open GameTheory.Math.Probability GameTheory.Stochastic
open GameTheory.Stochastic.Game GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol

universe uι us ua

variable {ι : Type uι} (G : Stochastic.Game.{uι, us, ua} ι)

section Core

variable {initial : G.State} [∀ i, Nonempty (G.Action i)]

/-- A proof-free history is realizable exactly when it is the image of a
canonical Protocol history from the selected initial state. -/
def PublicHistoryRealizable (initial : G.State) (history : G.PublicHistory) : Prop :=
  ∃ complete : (G.toExecution initial).History,
    G.publicHistoryOfTrace initial complete.trace = history

theorem publicHistoryRealizable_of_history
    (complete : (G.toExecution initial).History) :
    PublicHistoryRealizable G initial
      (G.publicHistoryOfTrace initial complete.trace) :=
  ⟨complete, rfl⟩

theorem publicHistoryRealizable_refl (history : G.PublicHistory)
    (h : PublicHistoryRealizable G initial history) :
    PublicHistoryRealizable G initial history := h

/-- Two canonical profiles agree on every public history in the canonical
image. -/
def PublicHistoryAgreement
    (initial : G.State)
    (first second : G.BehaviorProfile initial) : Prop :=
  ∀ history, PublicHistoryRealizable G initial history →
    ∀ i, first i history = second i history

theorem PublicHistoryAgreement.refl
    (first : G.BehaviorProfile initial) :
    PublicHistoryAgreement G initial first first := by
  intro history _ i
  rfl

theorem PublicHistoryAgreement.symm
    {first second : G.BehaviorProfile initial}
    (h : PublicHistoryAgreement G initial first second) :
    PublicHistoryAgreement G initial second first := by
  intro history hreal i
  exact (h history hreal i).symm

theorem PublicHistoryAgreement.trans
    {first second third : G.BehaviorProfile initial}
    (hfirst : PublicHistoryAgreement G initial first second)
    (hsecond : PublicHistoryAgreement G initial second third) :
    PublicHistoryAgreement G initial first third := by
  intro history hreal i
  exact (hfirst history hreal i).trans (hsecond history hreal i)

theorem PublicHistoryAgreement.update_same [DecidableEq ι]
    {first second : G.BehaviorProfile initial}
    (h : PublicHistoryAgreement G initial first second) (who : ι)
    (replacement : (G.perfectMonitoring initial).BehavioralPolicy who) :
    PublicHistoryAgreement G initial (Profile.update first who replacement)
      (Profile.update second who replacement) := by
  intro history hreal i
  by_cases hi : i = who
  · subst i
    rw [Profile.update_same, Profile.update_same]
  · rw [Profile.update_of_ne first replacement hi,
      Profile.update_of_ne second replacement hi]
    exact h history hreal i

end Core

section Runner

variable [Fintype ι]
variable {initial : G.State} [∀ i, Nonempty (G.Action i)]

theorem runBehavioralFrom_eq_of_publicHistoryAgreement
    {first second : G.BehaviorProfile initial}
    (h : PublicHistoryAgreement G initial first second) (fuel : ℕ)
    (start : (G.toExecution initial).History) :
    (G.perfectMonitoring initial).runBehavioralFrom first fuel start =
      (G.perfectMonitoring initial).runBehavioralFrom second fuel start := by
  apply (G.perfectMonitoring initial).runBehavioralFrom_congr fuel start
  intro later hreach hterm i
  rw [G.perfectMonitoring_infoOf_eq_publicHistoryOfTrace initial i later.trace]
  exact h _ (publicHistoryRealizable_of_history G later) i

theorem publicHistoryLaw_eq_of_publicHistoryAgreement
    {first second : G.BehaviorProfile initial}
    (h : PublicHistoryAgreement G initial first second) (horizon : ℕ) :
    G.publicHistoryLaw initial first horizon =
      G.publicHistoryLaw initial second horizon := by
  unfold Game.publicHistoryLaw InformationModel.runBehavioral
  rw [runBehavioralFrom_eq_of_publicHistoryAgreement G h horizon
    (G.toExecution initial).initHistory]

theorem publicFiniteAveragePayoff_eq_of_publicHistoryAgreement
    {first second : G.BehaviorProfile initial}
    (h : PublicHistoryAgreement G initial first second) (horizon : ℕ) (who : ι) :
    G.finiteAveragePayoff initial horizon first who =
      G.finiteAveragePayoff initial horizon second who := by
  calc
    G.finiteAveragePayoff initial horizon first who =
        G.publicFiniteAveragePayoff initial horizon first who :=
      (G.publicFiniteAveragePayoff_eq_finiteAveragePayoff initial horizon
        first who).symm
    _ = G.publicFiniteAveragePayoff initial horizon second who := by
      unfold publicFiniteAveragePayoff
      rw [publicHistoryLaw_eq_of_publicHistoryAgreement G h horizon]
    _ = G.finiteAveragePayoff initial horizon second who :=
      G.publicFiniteAveragePayoff_eq_finiteAveragePayoff initial horizon
        second who

end Runner

section HostileFixture

open GameTheory.Tests.StochasticContinuation

local instance actionNonempty : ∀ i, Nonempty (actionGame.Action i) :=
  fun _ => ⟨false⟩

def forgedRecord : actionGame.StageRecord where
  source := false
  joint := firstActions
  target := false

abbrev isForgedRecord (record : actionGame.StageRecord) : Prop :=
  record.source = false ∧ record.target = false ∧
    record.joint false = true ∧ record.joint true = false

theorem isForgedRecord_iff (record : actionGame.StageRecord) :
    isForgedRecord record ↔ record = forgedRecord := by
  constructor
  · rintro ⟨hsource, htarget, hfalse, htrue⟩
    cases record with
    | mk source joint target =>
        simp only at hsource htarget hfalse htrue ⊢
        subst source
        subst target
        have hjoint : joint = firstActions := by
          funext who
          cases who
          · simpa [firstActions] using hfalse
          · simpa [firstActions] using htrue
        subst joint
        rfl
  · intro hrecord
    subst hrecord
    simp [isForgedRecord, forgedRecord, firstActions]

theorem forgedRecord_not_realizable :
    ¬ PublicHistoryRealizable actionGame false [forgedRecord] := by
  rintro ⟨complete, hcomplete⟩
  rcases complete with ⟨state, trace⟩
  cases trace with
  | start => simp [Game.publicHistoryOfTrace] at hcomplete
  | @extend source target prior joint isLegal realized =>
      have hprior : actionGame.publicHistoryOfTrace false prior = [] := by
        have htail := congrArg List.tail hcomplete
        simpa [Game.publicHistoryOfTrace] using htail
      cases prior with
      | start =>
          have hrecord :
              actionGame.stageRecordOfEvent false
                  ⟨_, joint, isLegal, _, realized⟩ = forgedRecord := by
            simpa [Game.publicHistoryOfTrace] using hcomplete
          have htarget := congrArg StageRecord.target hrecord
          have hsource := congrArg StageRecord.source hrecord
          have hjoint := congrArg (fun record => record.joint false) hrecord
          simp [Game.stageRecordOfEvent, forgedRecord] at htarget hsource hjoint
          have htransition := FinDist.mem_support_pure.mp realized
          rw [hjoint] at htransition
          exact Bool.noConfusion (htransition.symm.trans htarget)
      | extend priorTrace priorJoint priorLegal priorRealized =>
          simp [Game.publicHistoryOfTrace] at hprior

def forgedPublicProfile : PublicProfile actionGame false :=
  fun who history =>
    match who, history with
    | false, [record] =>
        if isForgedRecord record then FinDist.pure true
        else publicProfile false [record]
    | _, _ => publicProfile who history

def forgedProfile : actionGame.BehaviorProfile false :=
  toBehaviorProfile actionGame false forgedPublicProfile

theorem forgedPublicProfile_eq_of_realizable
    (history : actionGame.PublicHistory)
    (hreal : PublicHistoryRealizable actionGame false history) (who : Bool) :
    forgedPublicProfile who history = publicProfile who history := by
  cases who with
  | true => rfl
  | false =>
      cases history with
      | nil => rfl
      | cons record rest =>
          cases rest with
          | nil =>
              by_cases hforged : isForgedRecord record
              · have hrecord : record = forgedRecord :=
                  (isForgedRecord_iff record).mp hforged
                subst record
                exact False.elim (forgedRecord_not_realizable hreal)
              · simp [forgedPublicProfile, hforged]
          | cons record' rest' => rfl

theorem forgedProfile_agreement :
    PublicHistoryAgreement actionGame false canonicalProfile forgedProfile := by
  intro history hreal who
  unfold canonicalProfile forgedProfile toBehaviorProfile
  unfold toBehavioralPolicy
  rw [forgedPublicProfile_eq_of_realizable history hreal who]

theorem forged_history_law_eq (horizon : ℕ) :
    actionGame.publicHistoryLaw false canonicalProfile horizon =
      actionGame.publicHistoryLaw false forgedProfile horizon :=
  publicHistoryLaw_eq_of_publicHistoryAgreement actionGame forgedProfile_agreement horizon

theorem forged_finite_average_payoff_eq (horizon : ℕ) (who : Bool) :
    actionGame.finiteAveragePayoff false horizon canonicalProfile who =
      actionGame.finiteAveragePayoff false horizon forgedProfile who :=
  publicFiniteAveragePayoff_eq_of_publicHistoryAgreement actionGame
    forgedProfile_agreement horizon who

def livePublicProfile : PublicProfile actionGame false :=
  fun who history =>
    if who = false ∧ history = [] then FinDist.pure false
    else publicProfile who history

def liveProfile : actionGame.BehaviorProfile false :=
  toBehaviorProfile actionGame false livePublicProfile

theorem live_first_action_differs :
    livePublicProfile false [] ≠ publicProfile false [] := by
  intro h
  have hprob := congrArg (fun law => law.prob true) h
  norm_num [livePublicProfile, publicProfile, firstActions,
    FinDist.prob_pure_eq_ite] at hprob
  exact Bool.noConfusion hprob

end HostileFixture

end GameTheory.Experimental.PostArchitecture.StochasticPublicHistoryCoherence
