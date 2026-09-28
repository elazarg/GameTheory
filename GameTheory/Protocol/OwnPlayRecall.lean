/-
# Own-play recall

Any information model can be refined to one with perfect recall: each player
carries, beside its current information state, the record of its own moves —
the information state at each and the action taken. Nothing else is added.
Passing through an information state without acting leaves no trace, so the
refinement reveals neither the number of transitions nor other players'
activity beyond what the original information already revealed.

It is the coarsest such refinement. The refined model identifies two histories
exactly when the original does and the player's own play along them agrees,
and every refinement with perfect recall must separate at least those
histories.
-/

import GameTheory.Protocol.Information

namespace GameTheory.Protocol

namespace InfoSignals

variable {ι : Type*} {E : ExecutionProtocol ι} (S : InfoSignals E)

/-- Refine each player's information state by its own-play record. -/
@[reducible]
def withOwnPlayRecall : InfoSignals E where
  PublicSignal := S.PublicSignal
  PrivateSignal := S.PrivateSignal
  initialPublic := S.initialPublic
  initialPrivate := S.initialPrivate
  publicSignal := S.publicSignal
  privateSignal := S.privateSignal
  InfoState i := S.InfoState i × List (S.InfoState i × E.Action i)
  initInfo i view publicView := (S.initInfo i view publicView, [])
  pushInfo i prior choice view publicView :=
    (S.pushInfo i prior.1 choice view publicView,
      match choice with
      | some action => (prior.1, action) :: prior.2
      | none => prior.2)

/-- The refined information state is the original one together with the
original own-play record. -/
theorem withOwnPlayRecall_infoOf (i : ι) :
    ∀ {state : E.State} (trace : E.Trace state),
      S.withOwnPlayRecall.infoOf i trace = (S.infoOf i trace, S.ownPlay i trace)
  | _, .start => rfl
  | _, .extend prior joint isLegal realized => by
      rw [infoOf_extend, ownPlay_extend, infoOf_extend,
        withOwnPlayRecall_infoOf i prior]
      rfl

/-- Annotate each own move with the moves preceding it. This reconstructs the
refined own-play record from the original one. -/
def recallRecord {Info Action : Type*} :
    List (Info × Action) → List ((Info × List (Info × Action)) × Action)
  | [] => []
  | (info, action) :: earlier => ((info, earlier), action) :: recallRecord earlier

theorem withOwnPlayRecall_ownPlay (i : ι) :
    ∀ {state : E.State} (trace : E.Trace state),
      S.withOwnPlayRecall.ownPlay i trace = recallRecord (S.ownPlay i trace)
  | _, .start => rfl
  | _, .extend prior joint isLegal realized => by
      rw [ownPlay_extend, ownPlay_extend, S.withOwnPlayRecall_infoOf i prior]
      cases joint i with
      | none => exact withOwnPlayRecall_ownPlay i prior
      | some action =>
          simp only [recallRecord, withOwnPlayRecall_ownPlay i prior]

/-- The refinement identifies exactly the histories with equal original
information and equal own play. -/
theorem withOwnPlayRecall_infoOf_eq_iff (i : ι) {first second : E.State}
    (traceFirst : E.Trace first) (traceSecond : E.Trace second) :
    S.withOwnPlayRecall.infoOf i traceFirst = S.withOwnPlayRecall.infoOf i traceSecond ↔
      S.infoOf i traceFirst = S.infoOf i traceSecond ∧
        S.ownPlay i traceFirst = S.ownPlay i traceSecond := by
  rw [S.withOwnPlayRecall_infoOf, S.withOwnPlayRecall_infoOf]
  exact Prod.ext_iff

theorem withOwnPlayRecall_perfectRecall : S.withOwnPlayRecall.PerfectRecall := by
  intro i first second traceFirst traceSecond hinfo
  rw [S.withOwnPlayRecall_ownPlay, S.withOwnPlayRecall_ownPlay,
    ((S.withOwnPlayRecall_infoOf_eq_iff i traceFirst traceSecond).1 hinfo).2]

/-- A model refining the original information state carries the original
own-play record inside its own. -/
theorem ownPlay_map_of_refines (R : InfoSignals E)
    (project : ∀ i, R.InfoState i → S.InfoState i)
    (hproject : ∀ i {state : E.State} (trace : E.Trace state),
      project i (R.infoOf i trace) = S.infoOf i trace) (i : ι) :
    ∀ {state : E.State} (trace : E.Trace state),
      (R.ownPlay i trace).map (Prod.map (project i) id) = S.ownPlay i trace
  | _, .start => rfl
  | _, .extend prior joint isLegal realized => by
      rw [ownPlay_extend, ownPlay_extend]
      cases joint i with
      | none => exact ownPlay_map_of_refines R project hproject i prior
      | some action =>
          simp only [List.map_cons, Prod.map_apply, id_eq, hproject,
            ownPlay_map_of_refines R project hproject i prior]

/-- **Own-play recall is the coarsest perfect-recall refinement.** Every
refinement of the original information that has perfect recall distinguishes
at least the histories that own-play recall distinguishes. -/
theorem withOwnPlayRecall_infoOf_eq_of_refines (R : InfoSignals E)
    (project : ∀ i, R.InfoState i → S.InfoState i)
    (hproject : ∀ i {state : E.State} (trace : E.Trace state),
      project i (R.infoOf i trace) = S.infoOf i trace)
    (hrecall : R.PerfectRecall) (i : ι) {first second : E.State}
    (traceFirst : E.Trace first) (traceSecond : E.Trace second)
    (hinfo : R.infoOf i traceFirst = R.infoOf i traceSecond) :
    S.withOwnPlayRecall.infoOf i traceFirst = S.withOwnPlayRecall.infoOf i traceSecond := by
  rw [S.withOwnPlayRecall_infoOf_eq_iff, ← hproject i traceFirst, ← hproject i traceSecond,
    ← S.ownPlay_map_of_refines R project hproject i traceFirst,
    ← S.ownPlay_map_of_refines R project hproject i traceSecond,
    hinfo, hrecall i traceFirst traceSecond hinfo]
  exact ⟨rfl, rfl⟩

end InfoSignals

end GameTheory.Protocol
