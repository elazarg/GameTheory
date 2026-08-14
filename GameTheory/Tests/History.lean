/-
# The state forgets what the history remembers

A chance move splits play into two branches that the player observes, and the
branches then merge back into one state. At that state the player knows which
branch it came through; the state does not record it.

This is the hostile test for running a game along its history. A chooser indexed
by the state must answer identically at the merged state, whichever branch led
there, so the law it induces is a point mass. A profile of information-local
policies answers differently, because its argument is the history, and its law
puts half its mass on each ending. No state-indexed chooser produces that law,
which is what makes the history runner an extension rather than a restatement.

The same example bounds the claim: nothing here is hidden from the player. What
the state loses is not secrecy but *order* — which of two equally visible pasts
actually happened.
-/

import GameTheory.Protocol.Information

noncomputable section

namespace GameTheory.Tests

open GameTheory GameTheory.Protocol GameTheory.Probability
open GameTheory.Protocol.ExecutionProtocol (Trace History)

/-- Where play can be. `lft` and `rgt` are the two branches; both lead to
`mid`, where the single player moves. -/
inductive Stage | start | lft | rgt | mid | endL | endR
  deriving DecidableEq, Repr

/-- The player's two moves at the merged state. -/
inductive Move | l | r
  deriving DecidableEq, Repr

/-- The fair chance move that opens play. -/
def coin : FinDist Stage :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num) (FinDist.pure .lft) (FinDist.pure .rgt)

theorem prob_coin_lft : coin.prob .lft = 1 / 2 := by
  simp [coin, FinDist.prob_pure_eq_ite]

theorem prob_coin_rgt : coin.prob .rgt = 1 / 2 := by
  simp [coin, FinDist.prob_pure_eq_ite]; norm_num

theorem mem_support_coin_lft : Stage.lft ∈ coin.support :=
  FinDist.prob_pos_iff.mp (by rw [prob_coin_lft]; norm_num)

theorem mem_support_coin_rgt : Stage.rgt ∈ coin.support :=
  FinDist.prob_pos_iff.mp (by rw [prob_coin_rgt]; norm_num)

/-- Chance splits, the branches merge, and then the player moves. -/
@[reducible]
def merge : ExecutionProtocol Unit where
  State := Stage
  Action _ := Move
  init := .start
  active state _ := state = .mid
  available _ _ := Set.univ
  terminal state := state = .endL ∨ state = .endR
  step state joint :=
    match state with
    | .start => coin
    | .lft => FinDist.pure .mid
    | .rgt => FinDist.pure .mid
    | .mid =>
        match joint.1 () with
        | some .l => FinDist.pure .endL
        | some .r => FinDist.pure .endR
        | none => FinDist.pure .endL
    | .endL => FinDist.pure .endL
    | .endR => FinDist.pure .endR
  progress := by
    rintro state hterm
    by_cases hactive : state = Stage.mid
    · exact ⟨fun _ => some .l, fun _ => ⟨hactive, Set.mem_univ _⟩⟩
    · exact ⟨fun _ => none, fun _ => hactive⟩

/-! ## What each history reveals

Every transition is publicly announced, so the information state is the list of
states visited, most recent first. Nothing is hidden; the branches are told
apart by order alone. -/

/-- Everything is announced to everybody. -/
@[reducible]
def signals : InfoSignals merge where
  PublicSignal := Stage
  PrivateSignal _ := Unit
  initialPublic := .start
  initialPrivate _ := ()
  publicSignal event := event.target
  privateSignal _ _ := ()
  InfoState _ := List Stage
  initInfo _ _ announced := [announced]
  pushInfo _ info _ _ announced := announced :: info

/-- The information state always begins with the state just reached, so it
determines where play is — and, unlike the state, also how play got there. -/
theorem infoOf_eq_cons :
    ∀ {state : merge.State} (trace : Trace merge state),
      ∃ rest, signals.infoOf () trace = state :: rest
  | _, .start => ⟨[], rfl⟩
  | _, .extend prior joint isLegal realized => by
    obtain ⟨rest, hrest⟩ := infoOf_eq_cons prior
    exact ⟨signals.infoOf () prior, by rw [InfoSignals.infoOf_extend]⟩

/-- The menu at an information state, read off the state just reached. -/
def menuAt : List Stage → Set (Option Move)
  | .mid :: _ => {some .l, some .r}
  | _ => {none}

/-- The information model. Adequacy holds because the information state names
the state play reached, and the player is active exactly at `mid`. -/
@[reducible]
def model : InformationModel merge where
  toInfoSignals := signals
  menu _ info := menuAt info
  menu_adequate := by
    rintro ⟨⟩ state trace choice
    obtain ⟨rest, hrest⟩ := infoOf_eq_cons trace
    rw [hrest]
    match state with
    | .mid =>
      cases choice with
      | none => simp [menuAt, LegalOption]
      | some move => cases move <;> simp [menuAt, LegalOption]
    | .start | .lft | .rgt | .endL | .endR =>
      cases choice with
      | none => simp [menuAt, LegalOption]
      | some move => simp [menuAt, LegalOption]

/-! ## The policy that reads its history

Its answer at the merged state depends on the branch, which is information the
state does not carry. The policy that ignores the branch appears further down,
as the control. -/

/-- Play `l` after the left branch and `r` after the right one. -/
def follow : model.Policy () := fun info =>
  match info with
  | .mid :: .rgt :: _ => ⟨some .r, by simp [menuAt]⟩
  | .mid :: _ => ⟨some .l, by simp [menuAt]⟩
  | [] => ⟨none, by simp [menuAt]⟩
  | .start :: _ | .lft :: _ | .rgt :: _ | .endL :: _ | .endR :: _ =>
      ⟨none, by simp [menuAt]⟩

/-! ## The chooser a state cannot supply -/

theorem legal_start : merge.Legal .start merge.noop :=
  merge.noop_isLegal (by simp) (fun _ h => by simp at h)

theorem legal_lft : merge.Legal .lft merge.noop :=
  merge.noop_isLegal (by simp) (fun _ h => by simp at h)

theorem legal_rgt : merge.Legal .rgt merge.noop :=
  merge.noop_isLegal (by simp) (fun _ h => by simp at h)

theorem realized_lft : Stage.lft ∈ (merge.step .start ⟨_, legal_start⟩).support :=
  mem_support_coin_lft

theorem realized_rgt : Stage.rgt ∈ (merge.step .start ⟨_, legal_start⟩).support :=
  mem_support_coin_rgt

theorem realized_mid_of_lft : Stage.mid ∈ (merge.step .lft ⟨_, legal_lft⟩).support :=
  FinDist.mem_support_pure.2 rfl

theorem realized_mid_of_rgt : Stage.mid ∈ (merge.step .rgt ⟨_, legal_rgt⟩).support :=
  FinDist.mem_support_pure.2 rfl

/-- Reaching `mid` through the left branch. -/
def viaLeft : History merge :=
  ⟨.mid, .extend (.extend .start _ legal_start realized_lft) _ legal_lft realized_mid_of_lft⟩

/-- Reaching `mid` through the right branch. -/
def viaRight : History merge :=
  ⟨.mid, .extend (.extend .start _ legal_start realized_rgt) _ legal_rgt realized_mid_of_rgt⟩

theorem viaLeft_state : viaLeft.state = Stage.mid := rfl

theorem viaRight_state : viaRight.state = Stage.mid := rfl

theorem not_terminal_mid : ¬ merge.terminal Stage.mid := by simp

/-- The two histories leave the player in different information states: it saw
which branch it came through. -/
theorem infoOf_viaLeft :
    signals.infoOf () viaLeft.trace = [Stage.mid, Stage.lft, Stage.start] := rfl

theorem infoOf_viaRight :
    signals.infoOf () viaRight.trace = [Stage.mid, Stage.rgt, Stage.start] := rfl

/-- So it answers them differently. -/
theorem follow_after_left :
    (model.historyChooser (fun _ => follow) viaLeft not_terminal_mid).1 () = some Move.l := rfl

theorem follow_after_right :
    (model.historyChooser (fun _ => follow) viaRight not_terminal_mid).1 () = some Move.r := rfl

/-- **The hostile test.** No state-indexed chooser behaves like this profile.
The two histories reach one state, so any `Chooser` must answer them alike;
`follow` answers them differently, having read the branch out of its own
information state. -/
theorem historyChooser_follow_ne_toHistoryChooser (chooser : merge.Chooser) :
    model.historyChooser (fun _ => follow) ≠ chooser.toHistoryChooser := by
  intro hequal
  have hleft := congrFun (congrFun hequal viaLeft) not_terminal_mid
  have hright := congrFun (congrFun hequal viaRight) not_terminal_mid
  have hmoves := congrFun (Subtype.ext_iff.mp (hleft.trans hright.symm)) ()
  rw [follow_after_left, follow_after_right] at hmoves
  exact Move.noConfusion (Option.some.inj hmoves)

/-! ## The law a state-indexed chooser cannot induce

Behaving differently is one thing; producing a different law is what matters.
The lemmas below are stated for an arbitrary policy, so that the same machinery
proves both halves of the comparison: the profile that reads its history is
outside every state chooser's reach, and the profile that ignores it is not. -/

/-- Where a move takes play from the merged state. -/
def endingOf : Move → Stage
  | .l => .endL
  | .r => .endR

/-- Coin flips land on a branch. -/
theorem eq_of_mem_support_coin {s : Stage} (hs : s ∈ coin.support) : s = .lft ∨ s = .rgt := by
  by_contra hne
  push Not at hne
  refine FinDist.prob_eq_zero_iff.mp ?_ hs
  simp [coin, FinDist.prob_pure_eq_ite, hne.1, hne.2]

/-- From the merged state, play ends where the policy's move sends it. -/
theorem map_state_runFrom_mid (policy : model.Policy ()) (move : Move) (info : List Stage)
    (hplay : (policy info).1 = some move) (trace : Trace merge Stage.mid)
    (hinfo : signals.infoOf () trace = info) :
    FinDist.map History.state (model.runFrom (fun _ => policy) 1 ⟨Stage.mid, trace⟩) =
      FinDist.pure (endingOf move) := by
  have hterm : ¬ merge.terminal (History.state ⟨Stage.mid, trace⟩) := by simp
  have hstep :
      merge.step (History.state ⟨Stage.mid, trace⟩)
          (model.historyChooser (fun _ => policy) ⟨Stage.mid, trace⟩ hterm) =
        FinDist.pure (endingOf move) := by
    show (match (model.jointAt (fun _ => policy) trace) () with
      | some .l => FinDist.pure Stage.endL
      | some .r => FinDist.pure Stage.endR
      | none => FinDist.pure Stage.endL) = _
    rw [show (model.jointAt (fun _ => policy) trace) () = some move by
      simp only [InformationModel.jointAt, InformationModel.Policy.act]
      rw [show model.infoOf () trace = info from hinfo, hplay]]
    cases move <;> rfl
  rw [InformationModel.runFrom, ExecutionProtocol.runHistoryFor_succ_of_not_terminal _ 0 hterm]
  refine FinDist.map_bindOnSupport_const _ fun target hrealized => ?_
  rw [hstep, FinDist.mem_support_pure] at hrealized
  subst hrealized
  rw [ExecutionProtocol.runHistoryFor_zero, FinDist.map_pure]
  rfl

/-- A branch state is administrative: play passes through it to the merged
state, carrying the branch into the information state. -/
theorem map_state_runFrom_branch (policy : model.Policy ()) (move : Move) (branch : Stage)
    (hbranch : branch = .lft ∨ branch = .rgt)
    (hplay : (policy [Stage.mid, branch, Stage.start]).1 = some move)
    (trace : Trace merge branch) (hinfo : signals.infoOf () trace = [branch, Stage.start]) :
    FinDist.map History.state (model.runFrom (fun _ => policy) 2 ⟨branch, trace⟩) =
      FinDist.pure (endingOf move) := by
  have hterm : ¬ merge.terminal (History.state ⟨branch, trace⟩) := by
    rcases hbranch with rfl | rfl <;> simp
  have hstep :
      merge.step (History.state ⟨branch, trace⟩)
          (model.historyChooser (fun _ => policy) ⟨branch, trace⟩ hterm) =
        FinDist.pure Stage.mid := by
    rcases hbranch with rfl | rfl <;> rfl
  rw [InformationModel.runFrom, ExecutionProtocol.runHistoryFor_succ_of_not_terminal _ 1 hterm]
  refine FinDist.map_bindOnSupport_const _ fun target hrealized => ?_
  have hmid : target = Stage.mid := by
    rw [hstep, FinDist.mem_support_pure] at hrealized; exact hrealized
  subst hmid
  exact map_state_runFrom_mid policy move _ hplay _ (by rw [InfoSignals.infoOf_extend, hinfo])

theorem init_isChance : merge.IsChance merge.init := ⟨by simp, fun _ h => by simp at h⟩

/-- The law any profile induces on endings: the coin picks a branch, and the
policy's answer at that branch decides the ending. -/
theorem map_state_run (policy : model.Policy ()) (moveAt : Stage → Move)
    (hplay : ∀ branch, branch = .lft ∨ branch = .rgt →
      (policy [Stage.mid, branch, Stage.start]).1 = some (moveAt branch)) :
    FinDist.map History.state (model.run (fun _ => policy) 3) =
      coin.bind fun branch => FinDist.pure (endingOf (moveAt branch)) := by
  rw [InformationModel.run, InformationModel.runFrom,
    ExecutionProtocol.runHistoryFor_succ_of_not_terminal _ 2 init_isChance.1,
    FinDist.map_bindOnSupport]
  refine FinDist.bindOnSupport_eq_bind_of_eq_on_support fun branch hbranch => ?_
  have hb := eq_of_mem_support_coin hbranch
  exact map_state_runFrom_branch policy _ branch hb (hplay branch hb) _
    (by rw [InfoSignals.infoOf_extend]; rfl)

/-! ## The comparison

`follow` reads the branch; `stubborn` does not. Only the first produces a law
that no state-indexed chooser reaches. -/

theorem map_state_run_follow :
    FinDist.map History.state (model.run (fun _ => follow) 3) =
      coin.bind fun branch =>
        FinDist.pure (endingOf (if branch = Stage.rgt then Move.r else Move.l)) :=
  map_state_run follow _ (by rintro branch (rfl | rfl) <;> rfl)

/-- Half the mass on each ending. -/
theorem prob_endL_run_follow :
    (FinDist.map History.state (model.run (fun _ => follow) 3)).prob Stage.endL = 1 / 2 := by
  rw [map_state_run_follow, FinDist.prob_bind, coin, FinDist.expect_mix]
  simp [FinDist.prob_pure_eq_ite, endingOf]

theorem prob_endR_run_follow :
    (FinDist.map History.state (model.run (fun _ => follow) 3)).prob Stage.endR = 1 / 2 := by
  rw [map_state_run_follow, FinDist.prob_bind, coin, FinDist.expect_mix]
  simp [FinDist.prob_pure_eq_ite, endingOf]
  norm_num

/-- Under any state-indexed chooser, play from the merged state ends at one
fixed ending: the chooser has nothing left to condition on. -/
theorem exists_runFor_mid_eq_pure (chooser : merge.Chooser) :
    ∃ ending, merge.runFor chooser 1 Stage.mid = FinDist.pure ending := by
  have hterm : ¬ merge.terminal Stage.mid := by simp
  obtain ⟨move, hmove⟩ :=
    LegalOption.exists_eq_some_of_active ((chooser Stage.mid hterm).1 ())
      (ExecutionProtocol.legalOption_of_legal (chooser Stage.mid hterm).2 ()) rfl
  refine ⟨endingOf move, ?_⟩
  rw [ExecutionProtocol.runFor_succ_of_not_terminal chooser 0 hterm]
  show (match (chooser Stage.mid hterm).1 () with
    | some .l => FinDist.pure Stage.endL
    | some .r => FinDist.pure Stage.endR
    | none => FinDist.pure Stage.endL).bind (merge.runFor chooser 0) = _
  rw [hmove]
  cases move <;> simp [endingOf]

/-- Everything before the merged state is chance and administration, so a state
chooser's whole law is decided at that one state. -/
theorem runFor_init_eq_pure (chooser : merge.Chooser) {ending : Stage}
    (hmid : merge.runFor chooser 1 Stage.mid = FinDist.pure ending) :
    merge.runFor chooser 3 merge.init = FinDist.pure ending := by
  rw [ExecutionProtocol.runFor_succ_of_chance chooser 2 init_isChance]
  refine Eq.trans (FinDist.bind_congr fun s hs => ?_) (FinDist.bind_const _ _)
  rcases eq_of_mem_support_coin hs with rfl | rfl <;>
    · rw [ExecutionProtocol.runFor_succ_of_not_terminal chooser 1 (by simp)]
      exact (FinDist.pure_bind _ _).trans hmid

/-- **The law-level test.** The profile's law splits its mass between the two
endings. No state-indexed chooser can produce it, because at the merged state
such a chooser answers the same whichever branch led there, so its law is a
point mass. -/
theorem run_follow_ne_runFor (chooser : merge.Chooser) :
    FinDist.map History.state (model.run (fun _ => follow) 3) ≠
      merge.runFor chooser 3 merge.init := by
  obtain ⟨ending, hending⟩ := exists_runFor_mid_eq_pure chooser
  intro hequal
  rw [map_state_run_follow, runFor_init_eq_pure chooser hending] at hequal
  have hmem : ∀ branch ∈ coin.support,
      endingOf (if branch = Stage.rgt then Move.r else Move.l) = ending := by
    intro branch hbranch
    refine FinDist.mem_support_pure.mp ?_
    rw [← hequal, FinDist.support_bind]
    exact Set.mem_biUnion hbranch (FinDist.mem_support_pure.mpr rfl)
  have hL := hmem _ mem_support_coin_lft
  have hR := hmem _ mem_support_coin_rgt
  rw [if_neg (by simp), ← hR] at hL
  exact Stage.noConfusion hL

/-! ## The positive control

The theorem above would be worthless if it held for every profile. It does not:
a policy that ignores the branch induces a law a state chooser reproduces
exactly. What the test detects is therefore the use of history, not the mere
fact of running along one. -/

/-- Play `l` whatever the branch was. -/
def stubborn : model.Policy () := fun info =>
  match info with
  | .mid :: _ => ⟨some .l, by simp [menuAt]⟩
  | [] => ⟨none, by simp [menuAt]⟩
  | .start :: _ | .lft :: _ | .rgt :: _ | .endL :: _ | .endR :: _ =>
      ⟨none, by simp [menuAt]⟩

/-- The state chooser that plays `l` at the merged state. -/
def alwaysLeft : merge.Chooser := fun state hterm =>
  ⟨fun _ => if state = Stage.mid then some Move.l else none, by
    refine ExecutionProtocol.legal_of_legalOption hterm fun _ => ?_
    by_cases hmid : state = Stage.mid
    · rw [if_pos hmid]; exact ⟨hmid, Set.mem_univ _⟩
    · rw [if_neg hmid]; exact hmid⟩

theorem runFor_alwaysLeft_mid : merge.runFor alwaysLeft 1 Stage.mid = FinDist.pure Stage.endL := by
  have hterm : ¬ merge.terminal Stage.mid := by simp
  rw [ExecutionProtocol.runFor_succ_of_not_terminal alwaysLeft 0 hterm]
  show (match (alwaysLeft Stage.mid hterm).1 () with
    | some .l => FinDist.pure Stage.endL
    | some .r => FinDist.pure Stage.endR
    | none => FinDist.pure Stage.endL).bind (merge.runFor alwaysLeft 0) = _
  rw [show (alwaysLeft Stage.mid hterm).1 () = some Move.l by simp [alwaysLeft]]
  simp

/-- **The control.** The history-blind profile induces exactly the law of a
state-indexed chooser. So the history runner costs nothing where history is not
used, and the previous theorem holds because `follow` reads the branch, not
because it runs along a history. -/
theorem run_stubborn_eq_runFor :
    FinDist.map History.state (model.run (fun _ => stubborn) 3) =
      merge.runFor alwaysLeft 3 merge.init := by
  rw [map_state_run stubborn (fun _ => Move.l) (by rintro branch (rfl | rfl) <;> rfl),
    runFor_init_eq_pure alwaysLeft runFor_alwaysLeft_mid]
  exact FinDist.bind_const _ _

end GameTheory.Tests
