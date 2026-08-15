/-
# Explicit-order FOSG serialization

A simultaneous FOSG round is serialized into one hidden selection slot per
source player and one resolver step.  The target state retains the canonical
source history and certified source-local choices; it introduces no second
runner or history type.

The construction preserves source histories and source-local choices at every
serialization round. Exact public claims compare the target law after erasing
serialization-only microsteps; the un-erased EFG history contains strictly
more scheduling data. Whole-round support lands back at a clean boundary, and
the exact law and terminal-support results also hold for continuations from
any supplied reached boundary.
-/

import GameTheory.Languages.EFG
import GameTheory.Languages.FOSG

noncomputable section

namespace GameTheory.Languages.Bridges.FOSGToEFG

open GameTheory.Languages
open GameTheory.Math.Probability
open GameTheory.Protocol

universe uι us ua up uq uk

/-- An operational player schedule, given without installing global finite
typeclass data. -/
structure ExplicitOrder (ι : Type uι) where
  slots : ℕ
  player : Fin slots ≃ ι

variable {ι : Type uι}
variable (G : FOSG.Game.{uι, us, ua, up, uq, uk} ι)
variable (order : ExplicitOrder ι)

/-- The serializer carries canonical source histories literally. -/
abbrev History := G.execution.History

/-- A source-local contribution certified legal at the carried history. -/
abbrev ChoiceAt (history : History G) (player : ι) :=
  { choice : Option (G.execution.Action player) //
    LegalOption G.execution history.state player choice }

/-- Choices already collected in the first `count` schedule slots.  The outer
`Option` records whether a slot has been visited; the inner option is the
source player's actual contribution and can legitimately be `none`. -/
structure Prefix (history : History G) (count : ℕ) where
  count_le : count ≤ order.slots
  choices : (player : ι) → Option (ChoiceAt G history player)
  selected_iff : ∀ player,
    (choices player).isSome ↔ (order.player.symm player).1 < count

namespace Prefix

variable {G order}

/-- No source coordinate has been selected at the start of a round. -/
def initial (history : History G) : Prefix G order history 0 where
  count_le := Nat.zero_le _
  choices _ := none
  selected_iff _ := by simp

/-- Add the certified contribution at the next schedule slot. -/
def advance [DecidableEq ι] {history : History G} {count : ℕ}
    (collected : Prefix G order history count)
    (hcount : count < order.slots)
    (choice : ChoiceAt G history (order.player ⟨count, hcount⟩)) :
    Prefix G order history (count + 1) where
  count_le := hcount
  choices player :=
    if hplayer : player = order.player ⟨count, hcount⟩ then by
      subst player
      exact some choice
    else collected.choices player
  selected_iff player := by
    by_cases hplayer : player = order.player ⟨count, hcount⟩
    · subst player
      simp
    · have hvalue : (order.player.symm player).1 ≠ count := by
        intro heq
        apply hplayer
        calc
          player = order.player (order.player.symm player) :=
            (order.player.apply_symm_apply player).symm
          _ = order.player ⟨count, hcount⟩ := by
            congr 1
            exact Fin.ext heq
      simp only [hplayer, dite_false, collected.selected_iff]
      omega

/-- Every slot in a completed prefix contains a certified choice. -/
def completedChoice {history : History G}
    (collected : Prefix G order history order.slots)
    (player : ι) : ChoiceAt G history player :=
  (collected.choices player).get <|
    (collected.selected_iff player).2 (order.player.symm player).isLt

/-- Read a completed prefix as the simultaneous source joint action. -/
def joint {history : History G}
    (collected : Prefix G order history order.slots) :
    (player : ι) → Option (G.execution.Action player) :=
  fun player => (collected.completedChoice player).1

/-- Every coordinate of the completed joint retains its source legality
certificate. -/
theorem joint_legalOption {history : History G}
    (collected : Prefix G order history order.slots) (player : ι) :
    LegalOption G.execution history.state player (collected.joint player) := by
  exact (collected.completedChoice player).2

/-- A completed prefix is a legal source joint whenever the source has not
stopped. -/
theorem joint_legal {history : History G}
    (collected : Prefix G order history order.slots)
    (hterm : ¬ G.execution.terminal history.state) :
    G.execution.Legal history.state collected.joint :=
  ExecutionProtocol.legal_of_legalOption hterm collected.joint_legalOption

/-- A completed prefix reconstructed from a certified source joint. -/
def ofJoint {history : History G}
    (joint : (player : ι) → Option (G.execution.Action player))
    (hlegal : G.execution.Legal history.state joint) :
    Prefix G order history order.slots where
  count_le := Nat.le_refl _
  choices player := some ⟨joint player,
    G.execution.legalOption_of_legal hlegal player⟩
  selected_iff player := by
    simp

/-- Remove the last visited schedule slot. -/
def retreat {history : History G} {count : ℕ}
    (collected : Prefix G order history (count + 1)) :
    Prefix G order history count where
  count_le := Nat.le_trans (Nat.le_succ _) collected.count_le
  choices player :=
    if (order.player.symm player).1 < count then collected.choices player else none
  selected_iff player := by
    by_cases hselected : (order.player.symm player).1 < count
    · simp [hselected, collected.selected_iff, Nat.lt_succ_iff.mpr (Nat.le_of_lt hselected)]
    · simp [hselected]

/-- A prefix is determined by its selected coordinates. -/
theorem ext {history : History G} {count : ℕ}
    {first second : Prefix G order history count}
    (hchoices : first.choices = second.choices) : first = second := by
  cases first
  cases second
  simp_all

/-- Retreat cancels one advance, including the absence certificate at the
previously unselected slot. -/
theorem retreat_advance [DecidableEq ι] {history : History G} {count : ℕ}
    (collected : Prefix G order history count)
    (hcount : count < order.slots)
    (choice : ChoiceAt G history (order.player ⟨count, hcount⟩)) :
    (collected.advance hcount choice).retreat = collected := by
  apply ext
  funext player
  by_cases hselected : (order.player.symm player).1 < count
  · have hplayer : player ≠ order.player ⟨count, hcount⟩ := by
      intro heq
      subst player
      simp at hselected
    simp only [retreat, if_pos hselected, advance, hplayer, dite_false]
  · have hnone : collected.choices player = none := by
      apply Option.not_isSome_iff_eq_none.mp
      simpa [collected.selected_iff] using hselected
    simp [retreat, hselected, hnone]

/-- Reconstructing a completed prefix from its joint changes no coordinate. -/
theorem ofJoint_joint {history : History G}
    (collected : Prefix G order history order.slots)
    (hterm : ¬ G.execution.terminal history.state) :
    ofJoint (G := G) (order := order) collected.joint
      (collected.joint_legal hterm) = collected := by
  apply ext
  funext player
  simp only [ofJoint, joint, completedChoice]
  exact Option.some_get _

end Prefix

/-- A serialized state is a canonical source history plus its current
within-round prefix. -/
inductive State
  | stage (history : History G) (count : ℕ)
      (collected : Prefix G order history count)

namespace State

variable {G order}

def history : State G order → History G
  | .stage history _ _ => history

def count : State G order → ℕ
  | .stage _ count _ => count

/-- The proof-free source contribution stored for one player, when that
player's slot has already been visited. -/
def choiceValue (player : ι) : State G order →
    Option (Option (G.execution.Action player))
  | .stage _ _ collected => (collected.choices player).map Subtype.val

theorem count_le (state : State G order) : state.count ≤ order.slots := by
  cases state with
  | stage _ _ collected => exact collected.count_le

end State

/-- The player scheduled at a nonfinal prefix. -/
def scheduledPlayer {history : History G} {count : ℕ}
    (_collected : Prefix G order history count)
    (hcount : count < order.slots) : ι :=
  order.player ⟨count, hcount⟩

/-- Only the scheduled source player can act, and only when that player is
active in the source state. -/
def active : State G order → ι → Prop
  | .stage history count collected, player =>
      ∃ hcount : count < order.slots,
        player = scheduledPlayer G order collected hcount ∧
          G.execution.active history.state player

/-- Target play stops exactly when the carried source history has stopped. -/
def terminal (state : State G order) : Prop :=
  G.execution.terminal state.history.state

/-- A single scheduled target coordinate, containing the corresponding source
contribution. -/
def selectedJoint [DecidableEq ι] (owner : ι)
    (choice : Option (G.execution.Action owner)) :
    (player : ι) → Option (G.execution.Action player) :=
  G.execution.singletonJoint owner choice

/-- Target legality at a selection slot is exactly source-local legality for
the scheduled contribution. -/
theorem selectedJoint_legal [DecidableEq ι]
    {history : History G} {count : ℕ}
    (collected : Prefix G order history count)
    (hcount : count < order.slots)
    (hterm : ¬ G.execution.terminal history.state)
    (choice : ChoiceAt G history (scheduledPlayer G order collected hcount)) :
    ¬ terminal G order (.stage history count collected) ∧
      IsLegalJoint (active G order (.stage history count collected))
        (fun player => G.execution.available history.state player)
        (selectedJoint G (scheduledPlayer G order collected hcount) choice.1) := by
  refine ⟨hterm, fun player => ?_⟩
  by_cases howner : player = scheduledPlayer G order collected hcount
  · subst player
    cases hchoice : choice.1 with
    | none =>
        simp only [selectedJoint, ExecutionProtocol.singletonJoint, dite_true]
        intro hactive
        obtain ⟨_, _, hsource⟩ := hactive
        exact (show ¬ G.execution.active history.state
          (scheduledPlayer G order collected hcount) by
            simpa [LegalOption, hchoice] using choice.2) hsource
    | some action =>
        simp only [selectedJoint, ExecutionProtocol.singletonJoint, dite_true]
        have hsource :
            G.execution.active history.state
                (scheduledPlayer G order collected hcount) ∧
              action ∈ G.execution.available history.state
                (scheduledPlayer G order collected hcount) := by
          simpa [LegalOption, hchoice] using choice.2
        exact ⟨⟨hcount, rfl, hsource.1⟩, hsource.2⟩
  · simp only [selectedJoint, ExecutionProtocol.singletonJoint, howner, dite_false]
    intro hactive
    obtain ⟨_, heq, _⟩ := hactive
    exact howner heq

/-- Extract the scheduled source-local choice from a legal target joint. -/
def choiceOfJoint {history : History G} {count : ℕ}
    (collected : Prefix G order history count)
    (hcount : count < order.slots)
    (joint : (player : ι) → Option (G.execution.Action player))
    (hlegal : IsLegalJoint (active G order (.stage history count collected))
      (fun player => G.execution.available history.state player) joint) :
    ChoiceAt G history (scheduledPlayer G order collected hcount) := by
  let owner := scheduledPlayer G order collected hcount
  refine ⟨joint owner, ?_⟩
  have howner := hlegal owner
  cases hchoice : joint owner with
  | none =>
      rw [hchoice] at howner
      show ¬ G.execution.active history.state owner
      intro hsource
      exact howner ⟨hcount, rfl, hsource⟩
  | some action =>
      rw [hchoice] at howner
      exact ⟨howner.1.2.2, howner.2⟩

/-- Resolve one complete serialized prefix through the source transition law. -/
def resolve {history : History G}
    (collected : Prefix G order history order.slots)
    (hterm : ¬ G.execution.terminal history.state) :
    FinDist (State G order) :=
  let sourceLegal := collected.joint_legal hterm
  (G.execution.step history.state ⟨collected.joint, sourceLegal⟩).bindOnSupport
    fun _ realized =>
      FinDist.pure <| .stage (history.extend sourceLegal realized) 0
        (Prefix.initial (order := order) _)

/-- The generic serialized execution.  `DecidableEq` is an operational
capability of this construction, not data stored by either game. -/
@[reducible]
def execution [DecidableEq ι] : ExecutionProtocol ι where
  State := State G order
  Action := G.execution.Action
  init := .stage G.execution.initHistory 0
    (Prefix.initial (order := order) _)
  active := active G order
  available state player :=
    G.execution.available state.history.state player
  terminal := terminal G order
  step state joint := by
    cases state with
    | stage history count collected =>
        if hcount : count < order.slots then
          exact FinDist.pure <| .stage history (count + 1)
            (collected.advance hcount
              (choiceOfJoint G order collected hcount joint.1 joint.2.2))
        else
          have hcountEq : count = order.slots :=
            Nat.le_antisymm collected.count_le (Nat.le_of_not_gt hcount)
          subst count
          exact resolve G order collected joint.2.1
  progress := by
    intro state hterm
    cases state with
    | stage history count collected =>
        by_cases hcount : count < order.slots
        · obtain ⟨sourceJoint, sourceLegal⟩ :=
            G.execution.exists_legal hterm
          let owner := scheduledPlayer G order collected hcount
          let choice : ChoiceAt G history owner :=
            ⟨sourceJoint owner,
              G.execution.legalOption_of_legal sourceLegal owner⟩
          exact ⟨selectedJoint G owner choice.1,
            (selectedJoint_legal G order collected hcount hterm choice).2⟩
        · refine ⟨fun _ => none, ?_⟩
          intro player hactive
          exact hcount hactive.1

/-- A serialized state has at most one active player. -/
theorem singleMover [DecidableEq ι] (state : (execution G order).State)
    {first second : ι}
    (hfirst : (execution G order).active state first)
    (hsecond : (execution G order).active state second) :
    first = second := by
  obtain ⟨_, hfirstOwner, _⟩ := hfirst
  obtain ⟨_, hsecondOwner, _⟩ := hsecond
  exact hfirstOwner.trans hsecondOwner.symm

/-- The unique syntactic predecessor of a serialized state.  At a resolver
boundary the exact stored source trace supplies both the prior source history
and the completed source joint; within a round, `Prefix.retreat` removes the
last scheduled coordinate. -/
def predecessor : State G order → Option (State G order)
  | .stage ⟨_, .start⟩ 0 _ => none
  | .stage ⟨_, .extend (source := source) prior joint hlegal _⟩ 0 _ =>
      some <| .stage ⟨source, prior⟩ order.slots
        (Prefix.ofJoint (G := G) (order := order) joint hlegal)
  | .stage history (count + 1) collected =>
      some <| .stage history count collected.retreat

/-- A realized resolver transition reconstructs its completed predecessor from
the literal source trace stored in the target. -/
theorem predecessor_of_mem_resolve {history : History G}
    (collected : Prefix G order history order.slots)
    (hterm : ¬ G.execution.terminal history.state)
    {target : State G order}
    (realized : target ∈ (resolve G order collected hterm).support) :
    predecessor G order target = some (.stage history order.slots collected) := by
  simp only [resolve, FinDist.support_bindOnSupport, Set.mem_iUnion] at realized
  obtain ⟨reached, hreached, htarget⟩ := realized
  rw [FinDist.mem_support_pure] at htarget
  subst target
  unfold ExecutionProtocol.History.extend
  simp only [predecessor]
  rw [Prefix.ofJoint_joint collected hterm]

/-- A selection transition retreats to the preceding prefix. -/
theorem predecessor_of_mem_advance [DecidableEq ι]
    {history : History G} {count : ℕ}
    (collected : Prefix G order history count)
    (hcount : count < order.slots)
    (joint : (player : ι) → Option (G.execution.Action player))
    (hlegal : (execution G order).Legal (.stage history count collected) joint)
    {target : State G order}
    (realized : target ∈
      ((execution G order).step (.stage history count collected) ⟨joint, hlegal⟩).support) :
    predecessor G order target = some (.stage history count collected) := by
  have hstep :
      (execution G order).step (.stage history count collected)
          ⟨joint, hlegal⟩ =
        FinDist.pure (.stage history (count + 1)
          (collected.advance hcount
            (choiceOfJoint G order collected hcount joint hlegal.2))) := by
    simp [execution, hcount]
  rw [hstep] at realized
  rw [FinDist.mem_support_pure] at realized
  subst target
  simp only [predecessor]
  rw [Prefix.retreat_advance]

/-- Every realized target step has the source state as its syntactic
predecessor. -/
theorem predecessor_of_mem_step [DecidableEq ι]
    {source target : State G order}
    (joint : (player : ι) → Option (G.execution.Action player))
    (hlegal : (execution G order).Legal source joint)
    (realized : target ∈
      ((execution G order).step source ⟨joint, hlegal⟩).support) :
    predecessor G order target = some source := by
  cases source with
  | stage history count collected =>
      by_cases hcount : count < order.slots
      · exact predecessor_of_mem_advance G order collected hcount
          joint hlegal realized
      · have hcountEq : count = order.slots :=
          Nat.le_antisymm collected.count_le (Nat.le_of_not_gt hcount)
        subst count
        have hstep :
            (execution G order).step
                (.stage history order.slots collected) ⟨joint, hlegal⟩ =
              resolve G order collected hlegal.1 := by
          simp [execution]
        rw [hstep] at realized
        exact predecessor_of_mem_resolve G order collected hlegal.1 realized

/-- The serialized root is not produced by any target transition. -/
theorem init_not_mem_step [DecidableEq ι]
    (source : State G order)
    (joint : (player : ι) → Option (G.execution.Action player))
    (hlegal : (execution G order).Legal source joint) :
    (execution G order).init ∉
      ((execution G order).step source ⟨joint, hlegal⟩).support := by
  intro realized
  have hpred := predecessor_of_mem_step G order joint hlegal realized
  simp [predecessor, ExecutionProtocol.initHistory] at hpred

/-- A legal target joint has no contribution outside the scheduled slot. -/
theorem legal_joint_eq_selected [DecidableEq ι]
    {history : History G} {count : ℕ}
    (collected : Prefix G order history count)
    (hcount : count < order.slots)
    (joint : (player : ι) → Option (G.execution.Action player))
    (hlegal : (execution G order).Legal
      (.stage history count collected) joint) :
    joint = selectedJoint G (scheduledPlayer G order collected hcount)
      (joint (scheduledPlayer G order collected hcount)) := by
  funext player
  by_cases howner : player = scheduledPlayer G order collected hcount
  · subst player
    simp [selectedJoint]
  · have hinactive :
        ¬ active G order (.stage history count collected) player := by
      rintro ⟨_, heq, _⟩
      exact howner heq
    have hoption := hlegal.2 player
    cases hchoice : joint player with
    | none => simp [selectedJoint, howner]
    | some action =>
        rw [hchoice] at hoption
        exact False.elim (hinactive hoption.1)

/-- At one source state, two realized steps with the same target used the same
legal target joint. -/
theorem joint_eq_of_same_target [DecidableEq ι]
    {source target : State G order}
    (first second : (player : ι) → Option (G.execution.Action player))
    (firstLegal : (execution G order).Legal source first)
    (secondLegal : (execution G order).Legal source second)
    (firstRealized : target ∈
      ((execution G order).step source ⟨first, firstLegal⟩).support)
    (secondRealized : target ∈
      ((execution G order).step source ⟨second, secondLegal⟩).support) :
    first = second := by
  cases source with
  | stage history count collected =>
      by_cases hcount : count < order.slots
      · have firstStep :
            (execution G order).step (.stage history count collected)
                ⟨first, firstLegal⟩ =
              FinDist.pure (.stage history (count + 1)
                (collected.advance hcount
                  (choiceOfJoint G order collected hcount first
                    firstLegal.2))) := by
          simp [execution, hcount]
        have secondStep :
            (execution G order).step (.stage history count collected)
                ⟨second, secondLegal⟩ =
              FinDist.pure (.stage history (count + 1)
                (collected.advance hcount
                  (choiceOfJoint G order collected hcount second
                    secondLegal.2))) := by
          simp [execution, hcount]
        rw [firstStep, FinDist.mem_support_pure] at firstRealized
        rw [secondStep, FinDist.mem_support_pure] at secondRealized
        have htarget := firstRealized.symm.trans secondRealized
        let owner := scheduledPlayer G order collected hcount
        have hvalues := congrArg
          (State.choiceValue (G := G) (order := order) owner) htarget
        have hchoice : first owner = second owner := by
          have : some (first owner) = some (second owner) := by
            simpa [State.choiceValue, Prefix.advance, owner,
              scheduledPlayer, choiceOfJoint] using hvalues
          exact Option.some.inj this
        rw [legal_joint_eq_selected G order collected hcount first firstLegal,
          legal_joint_eq_selected G order collected hcount second secondLegal]
        rw [hchoice]
      · have hinactive (player : ι) :
            ¬ (execution G order).active
              (.stage history count collected) player := by
          intro hactive
          exact hcount hactive.1
        rw [(execution G order).eq_noop_of_legal_of_inactive
            firstLegal hinactive,
          (execution G order).eq_noop_of_legal_of_inactive
            secondLegal hinactive]

/-- A target state has at most one realized predecessor event. -/
theorem step_predecessor_unique [DecidableEq ι]
    {target firstSource secondSource : State G order}
    {firstJoint secondJoint :
      (player : ι) → Option (G.execution.Action player)}
    (firstLegal : (execution G order).Legal firstSource firstJoint)
    (secondLegal : (execution G order).Legal secondSource secondJoint)
    (firstRealized : target ∈
      ((execution G order).step firstSource
        ⟨firstJoint, firstLegal⟩).support)
    (secondRealized : target ∈
      ((execution G order).step secondSource
        ⟨secondJoint, secondLegal⟩).support) :
    firstSource = secondSource ∧ firstJoint = secondJoint := by
  have hfirst := predecessor_of_mem_step G order
    firstJoint firstLegal firstRealized
  have hsecond := predecessor_of_mem_step G order
    secondJoint secondLegal secondRealized
  have hsource : firstSource = secondSource :=
    Option.some.inj (hfirst.symm.trans hsecond)
  subst secondSource
  exact ⟨rfl, joint_eq_of_same_target G order firstJoint secondJoint
    firstLegal secondLegal firstRealized secondRealized⟩

/-- The generic serializer is tree-shaped even when the source FOSG merges
states reached by different histories. -/
theorem treeShaped [DecidableEq ι] :
    (execution G order).IsTreeShaped :=
  ExecutionProtocol.isTreeShaped_of_predecessor_unique
    (init_not_mem_step G order)
    (fun firstLegal secondLegal firstRealized secondRealized =>
      step_predecessor_unique G order firstLegal secondLegal
        firstRealized secondRealized)

/-- Serialized traces are unique because the stored source trace and prefix
determine every predecessor event. -/
theorem trace_unique [DecidableEq ι] {state : (execution G order).State}
    (first second : (execution G order).Trace state) : first = second :=
  ((treeShaped G order) state).elim first second

theorem step_select [DecidableEq ι]
    {history : History G} {count : ℕ}
    (collected : Prefix G order history count)
    (hcount : count < order.slots)
    (joint : (player : ι) → Option (G.execution.Action player))
    (hlegal : (execution G order).Legal
      (.stage history count collected) joint) :
    (execution G order).step (.stage history count collected)
        ⟨joint, hlegal⟩ =
      FinDist.pure (.stage history (count + 1)
        (collected.advance hcount
          (choiceOfJoint G order collected hcount joint hlegal.2))) := by
  simp [execution, hcount]

theorem step_resolve [DecidableEq ι]
    {history : History G}
    (collected : Prefix G order history order.slots)
    (joint : (player : ι) → Option (G.execution.Action player))
    (hlegal : (execution G order).Legal
      (.stage history order.slots collected) joint) :
    (execution G order).step (.stage history order.slots collected)
        ⟨joint, hlegal⟩ = resolve G order collected hlegal.1 := by
  simp [execution]

theorem mem_support_resolve_iff
    {history : History G}
    (collected : Prefix G order history order.slots)
    (hterm : ¬ G.execution.terminal history.state)
    (target : State G order) :
    target ∈ (resolve G order collected hterm).support ↔
      ∃ (reached : G.execution.State)
        (realized : reached ∈
          (G.execution.step history.state
            ⟨collected.joint, collected.joint_legal hterm⟩).support),
        target = .stage
          (history.extend (collected.joint_legal hterm) realized) 0
          (Prefix.initial (order := order) _) := by
  simp [resolve, FinDist.support_bindOnSupport]

/-- One source round always occupies every player slot and one resolver. -/
def roundWidth : ℕ := order.slots + 1

/-- The administrative phase exposed by target information.  It names the
scheduled player but contains no source action, activity bit, or prefix. -/
inductive Phase (ι : Type uι)
  | select (player : ι)
  | resolve
  deriving DecidableEq

/-- A target information state is exactly its administrative phase paired
with canonical source information. -/
structure View
    (G : FOSG.Game.{uι, us, ua, up, uq, uk} ι) (player : ι) where
  phase : Phase ι
  source : G.information.InfoState player

/-- Read the phase from the fixed-width target prefix. -/
def phaseOfState : State G order → Phase ι
  | .stage _ count collected =>
      if hcount : count < order.slots then
        .select (scheduledPlayer G order collected hcount)
      else .resolve

@[simp]
theorem phaseOfState_select {history : History G} {count : ℕ}
    (collected : Prefix G order history count)
    (hcount : count < order.slots) :
    phaseOfState G order (.stage history count collected) =
      .select (scheduledPlayer G order collected hcount) := by
  simp [phaseOfState, hcount, scheduledPlayer]

@[simp]
theorem phaseOfState_resolve {history : History G}
    (collected : Prefix G order history order.slots) :
    phaseOfState G order (.stage history order.slots collected) =
      .resolve := by
  simp [phaseOfState]

/-- The intended information value at a target state. -/
def viewOfState (player : ι) (state : State G order) : View G player :=
  ⟨phaseOfState G order state,
    G.information.infoOf player state.history.trace⟩

/-- Selection steps emit only the next phase.  Resolver steps additionally
replay the actual source public signal. -/
inductive PublicSignal
    (G : FOSG.Game.{uι, us, ua, up, uq, uk} ι)
  | admin (phase : Phase ι)
  | resolve (phase : Phase ι)
      (source : G.information.toInfoSignals.PublicSignal)

/-- A resolver private signal carries the actual source joint coordinate as
well as the actual source private signal.  The target resolver joint is the
all-`none` administrative joint and must not be substituted for it. -/
inductive PrivateSignal
    (G : FOSG.Game.{uι, us, ua, up, uq, uk} ι) (player : ι)
  | admin
  | resolve (own : Option (G.execution.Action player))
      (source : G.information.toInfoSignals.PrivateSignal player)

/-- Recover the literal source event stored in a resolver target history.
Selection targets have positive prefix count and return `none`. -/
def sourceEventOfTarget [DecidableEq ι]
    (event : (execution G order).StepEvent) :
    Option G.execution.StepEvent :=
  match event.target with
  | State.stage
      ⟨_, .extend (source := source) _ joint hlegal realized⟩ 0 _ =>
      some ⟨source, joint, hlegal, _, realized⟩
  | _ => none

def publicSignalOfEvent [DecidableEq ι]
    (event : (execution G order).StepEvent) : PublicSignal G :=
  match sourceEventOfTarget G order event with
  | none => .admin (phaseOfState G order event.target)
  | some sourceEvent =>
      .resolve (phaseOfState G order event.target)
        (G.information.publicSignal sourceEvent)

def privateSignalOfEvent [DecidableEq ι] (player : ι)
    (event : (execution G order).StepEvent) :
    PrivateSignal G player :=
  match sourceEventOfTarget G order event with
  | none => .admin
  | some sourceEvent =>
      .resolve (sourceEvent.joint player)
        (G.information.privateSignal player sourceEvent)

/-- Administrative signals alter only the phase.  Resolver signals apply
the source information update with the source player's real contribution. -/
def pushView (player : ι) (prior : View G player)
    (privateSignal : PrivateSignal G player)
    (publicSignal : PublicSignal G) : View G player :=
  match privateSignal, publicSignal with
  | .admin, .admin phase => ⟨phase, prior.source⟩
  | .resolve own sourcePrivate, .resolve phase sourcePublic =>
      ⟨phase, G.information.pushInfo player prior.source own
        sourcePrivate sourcePublic⟩
  | _, _ => prior

@[reducible]
def signals [DecidableEq ι] : InfoSignals (execution G order) where
  PublicSignal := PublicSignal G
  PrivateSignal := PrivateSignal G
  initialPublic := .admin (phaseOfState G order (execution G order).init)
  initialPrivate _ := .admin
  publicSignal := publicSignalOfEvent G order
  privateSignal := privateSignalOfEvent G order
  InfoState := View G
  initInfo player _ _ :=
    viewOfState G order player (execution G order).init
  pushInfo player prior _ privateSignal publicSignal :=
    pushView G player prior privateSignal publicSignal

/-- Every reached target information value is exactly its administrative
phase paired with the information of the carried canonical source history. -/
theorem infoOf_eq_viewOfState [DecidableEq ι] (player : ι) :
    ∀ {state : State G order} (trace : (execution G order).Trace state),
      (signals G order).infoOf player trace =
        viewOfState G order player state
  | _, .start => rfl
  | target, .extend (source := source) prior joint isLegal realized => by
      have hprior := infoOf_eq_viewOfState player prior
      cases source with
      | stage history count collected =>
          by_cases hcount : count < order.slots
          · rw [step_select G order collected hcount joint isLegal]
              at realized
            rw [FinDist.mem_support_pure] at realized
            subst target
            rw [InfoSignals.infoOf_extend, hprior]
            simp [signals, pushView, publicSignalOfEvent,
              privateSignalOfEvent, sourceEventOfTarget, viewOfState,
              phaseOfState, hcount]
            rfl
          · have hcountEq : count = order.slots :=
              Nat.le_antisymm collected.count_le
                (Nat.le_of_not_gt hcount)
            subst count
            rw [step_resolve G order collected joint isLegal] at realized
            rw [mem_support_resolve_iff] at realized
            obtain ⟨reached, sourceRealized, rfl⟩ := realized
            unfold ExecutionProtocol.History.extend
            rw [InfoSignals.infoOf_extend, hprior]
            simp [signals, pushView, publicSignalOfEvent,
              privateSignalOfEvent, sourceEventOfTarget, viewOfState,
              phaseOfState]
            simp only [State.history]
            rw [InfoSignals.infoOf_extend]

/-- At a player's own selection phase, expose exactly that player's source
menu.  Every other target menu is the forced administrative `none`. -/
def menu [DecidableEq ι] (player : ι) (view : View G player) :
    Set (Option (G.execution.Action player)) :=
  match view.phase with
  | .select owner =>
      if player = owner then G.information.menu player view.source else {none}
  | .resolve => {none}

theorem legalOption_scheduled [DecidableEq ι]
    {history : History G} {count : ℕ}
    (collected : Prefix G order history count)
    (hcount : count < order.slots)
    (choice : Option
      (G.execution.Action (scheduledPlayer G order collected hcount))) :
    LegalOption (execution G order) (.stage history count collected)
        (scheduledPlayer G order collected hcount) choice ↔
      LegalOption G.execution history.state
        (scheduledPlayer G order collected hcount) choice := by
  cases choice <;>
    simp [LegalOption, execution, active, hcount, State.history]

/-- The phase/source menu is adequate at every reached target history. -/
theorem menu_adequate [DecidableEq ι]
    (player : ι) {state : State G order}
    (trace : (execution G order).Trace state)
    (choice : Option (G.execution.Action player)) :
    choice ∈ menu G player ((signals G order).infoOf player trace) ↔
      LegalOption (execution G order) state player choice := by
  rw [infoOf_eq_viewOfState G order player trace]
  cases state with
  | stage history count collected =>
      by_cases hcount : count < order.slots
      · by_cases howner :
            player = scheduledPlayer G order collected hcount
        · subst player
          simp only [menu, viewOfState,
            phaseOfState_select G order collected hcount, if_pos,
            State.history]
          rw [G.information.menu_adequate]
          exact (legalOption_scheduled G order collected hcount choice).symm
        · simp only [menu, viewOfState,
            phaseOfState_select G order collected hcount, howner,
            if_false, Set.mem_singleton_iff]
          cases choice <;>
            simp [LegalOption, execution, active, hcount, howner,
              State.history]
      · cases choice <;>
          simp [menu, viewOfState, phaseOfState, hcount,
            LegalOption, active]

@[reducible]
def information [DecidableEq ι] : InformationModel (execution G order) where
  toInfoSignals := signals G order
  menu := menu G
  menu_adequate := menu_adequate G order

/-- A simultaneous FOSG serialized as a tree-shaped single-mover EFG. -/
@[reducible]
def toEFG [DecidableEq ι] : EFG.Game ι where
  execution := execution G order
  information := information G order
  treeShaped := treeShaped G order
  singleMover := singleMover G order

/-- The canonical target information state at which source player `player`
supplies one simultaneous-round contribution. -/
def scheduledView (player : ι) (source : G.information.InfoState player) :
    View G player :=
  ⟨.select player, source⟩

@[simp]
theorem menu_scheduledView [DecidableEq ι]
    (player : ι) (source : G.information.InfoState player) :
    menu G player (scheduledView G player source) =
      G.information.menu player source := by
  simp [menu, scheduledView]

/-- Target and source choices at the scheduled view have the same underlying
option and the same menu certificate. -/
def choiceEquiv [DecidableEq ι]
    (player : ι) (source : G.information.InfoState player) :
    (information G order).Choice player (scheduledView G player source) ≃
      G.information.Choice player source where
  toFun choice := ⟨choice.1, by
    have hmem : choice.1 ∈ menu G player (scheduledView G player source) :=
      choice.2
    rw [menu_scheduledView G player source] at hmem
    exact hmem⟩
  invFun choice := ⟨choice.1, by
    show choice.1 ∈ menu G player (scheduledView G player source)
    rw [menu_scheduledView G player source]
    exact choice.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Project an arbitrary target behavioral profile to the source by reading
only its canonical scheduled views. -/
def projectBehavioral [DecidableEq ι]
    (target : (player : ι) →
      (information G order).BehavioralPolicy player) :
    (player : ι) → G.information.BehavioralPolicy player :=
  fun player source =>
    FinDist.map (choiceEquiv G order player source)
      (target player (scheduledView G player source))

/-- Translate a source behavioral profile.  At all administrative target
views the only contribution is `none`; no arbitrary default is chosen. -/
def translateBehavioral [DecidableEq ι]
    (source : (player : ι) → G.information.BehavioralPolicy player) :
    (player : ι) → (information G order).BehavioralPolicy player :=
  fun player view =>
    match view with
    | ⟨.select owner, sourceInfo⟩ =>
        if howner : owner = player then by
          subst owner
          exact FinDist.map (choiceEquiv G order player sourceInfo).symm
            (source player sourceInfo)
        else
          FinDist.pure ⟨none, by simp [menu, Ne.symm howner]⟩
    | ⟨.resolve, _⟩ =>
        FinDist.pure ⟨none, by simp [menu]⟩

@[simp]
theorem translateBehavioral_scheduledView [DecidableEq ι]
    (source : (player : ι) → G.information.BehavioralPolicy player)
    (player : ι) (sourceInfo : G.information.InfoState player) :
    translateBehavioral G order source player
        (scheduledView G player sourceInfo) =
      FinDist.map (choiceEquiv G order player sourceInfo).symm
        (source player sourceInfo) := by
  simp [translateBehavioral, scheduledView]

/-- Translating and then projecting recovers every source local law. -/
theorem project_translate [DecidableEq ι]
    (source : (player : ι) → G.information.BehavioralPolicy player)
    (player : ι) (sourceInfo : G.information.InfoState player) :
    projectBehavioral G order (translateBehavioral G order source)
        player sourceInfo =
      source player sourceInfo := by
  rw [projectBehavioral, translateBehavioral_scheduledView, FinDist.map_comp]
  convert FinDist.map_id (source player sourceInfo) using 1
  apply congrArg (fun f => FinDist.map f (source player sourceInfo))
  funext choice
  apply Subtype.ext
  rfl

theorem project_translate_profile [DecidableEq ι]
    (source : (player : ι) → G.information.BehavioralPolicy player) :
    projectBehavioral G order (translateBehavioral G order source) = source := by
  funext player sourceInfo
  exact project_translate G order source player sourceInfo

/-- Projecting and then translating preserves an arbitrary target profile on
the scheduled views that represent genuine source choices. -/
theorem translate_project_scheduled [DecidableEq ι]
    (target : (player : ι) →
      (information G order).BehavioralPolicy player)
    (player : ι) (sourceInfo : G.information.InfoState player) :
    translateBehavioral G order (projectBehavioral G order target)
        player (scheduledView G player sourceInfo) =
      target player (scheduledView G player sourceInfo) := by
  rw [translateBehavioral_scheduledView, projectBehavioral, FinDist.map_comp]
  convert FinDist.map_id
    (target player (scheduledView G player sourceInfo)) using 1
  apply congrArg
    (fun f => FinDist.map f
      (target player (scheduledView G player sourceInfo)))
  funext choice
  apply Subtype.ext
  rfl

/-- Projecting and then translating recovers every target behavioral profile.
Outside a player's own selection phase the target menu is the singleton
administrative choice `none`, so no reachability restriction or default action
is needed. -/
theorem translate_project_profile [DecidableEq ι]
    (target : (player : ι) →
      (information G order).BehavioralPolicy player) :
    translateBehavioral G order (projectBehavioral G order target) = target := by
  funext player view
  rcases view with ⟨phase, sourceInfo⟩
  cases phase with
  | select owner =>
      by_cases howner : owner = player
      · subst owner
        exact translate_project_scheduled G order target player sourceInfo
      · have hsubsingleton : Subsingleton
            ((information G order).Choice player ⟨.select owner, sourceInfo⟩) := by
          constructor
          intro first second
          apply Subtype.ext
          have hfirst : first.1 = none := by
            simpa [information, menu, Ne.symm howner] using first.2
          have hsecond : second.1 = none := by
            simpa [information, menu, Ne.symm howner] using second.2
          exact hfirst.trans hsecond.symm
        letI := hsubsingleton
        have htranslation :
            translateBehavioral G order (projectBehavioral G order target)
              player ⟨.select owner, sourceInfo⟩ =
              FinDist.pure ⟨none, by simp [menu, Ne.symm howner]⟩ := by
          simp [translateBehavioral, howner]
        rw [htranslation]
        exact (FinDist.eq_pure_of_subsingleton
          (target player ⟨.select owner, sourceInfo⟩)
          ⟨none, by simp [menu, Ne.symm howner]⟩).symm
  | resolve =>
      have hsubsingleton : Subsingleton
          ((information G order).Choice player ⟨.resolve, sourceInfo⟩) := by
        constructor
        intro first second
        apply Subtype.ext
        have hfirst : first.1 = none := by
          have hmem : first.1 ∈ menu G player ⟨.resolve, sourceInfo⟩ :=
            first.2
          have hsingleton : first.1 ∈
              ({none} : Set (Option (G.execution.Action player))) := by
            exact hmem
          exact Set.mem_singleton_iff.mp hsingleton
        have hsecond : second.1 = none := by
          have hmem : second.1 ∈ menu G player ⟨.resolve, sourceInfo⟩ :=
            second.2
          have hsingleton : second.1 ∈
              ({none} : Set (Option (G.execution.Action player))) := by
            exact hmem
          exact Set.mem_singleton_iff.mp hsingleton
        exact hfirst.trans hsecond.symm
      letI := hsubsingleton
      have htranslation :
          translateBehavioral G order (projectBehavioral G order target)
            player ⟨.resolve, sourceInfo⟩ =
            FinDist.pure ⟨none, by simp [menu]⟩ := by
        simp [translateBehavioral]
      rw [htranslation]
      exact (FinDist.eq_pure_of_subsingleton
        (target player ⟨.resolve, sourceInfo⟩)
        ⟨none, by simp [menu]⟩).symm

/-! ## Exact behavioral-law preservation -/

/-- A source menu choice, recertified as a local contribution at the carried
source history. -/
private def sourceChoiceAt (history : History G) (player : ι)
    (choice : G.information.Choice player
      (G.information.infoOf player history.trace)) :
    ChoiceAt G history player :=
  ⟨choice.1,
    (G.information.menu_adequate player history.trace choice.1).mp
      choice.2⟩

/-- The law over certified source-local contributions read from the target's
canonical scheduled view. -/
private def targetChoiceAtLaw [DecidableEq ι]
    (target : (player : ι) →
      (information G order).BehavioralPolicy player)
    (history : History G) (player : ι) :
    FinDist (ChoiceAt G history player) :=
  FinDist.map
    (fun choice => sourceChoiceAt G history player
      (choiceEquiv G order player
        (G.information.infoOf player history.trace) choice))
    (target player (scheduledView G player
      (G.information.infoOf player history.trace)))

/-- The same certified local law, read directly from a source profile. -/
private def sourceChoiceAtLaw
    (source : (player : ι) → G.information.BehavioralPolicy player)
    (history : History G) (player : ι) :
    FinDist (ChoiceAt G history player) :=
  FinDist.map (sourceChoiceAt G history player)
    (source player (G.information.infoOf player history.trace))

private theorem targetChoiceAtLaw_eq_projected [DecidableEq ι]
    (target : (player : ι) →
      (information G order).BehavioralPolicy player)
    (history : History G) (player : ι) :
    targetChoiceAtLaw G order target history player =
      sourceChoiceAtLaw G (projectBehavioral G order target)
        history player := by
  unfold targetChoiceAtLaw sourceChoiceAtLaw projectBehavioral
  rw [FinDist.map_comp]
  rfl

/-- Extend a source history through one certified joint action. -/
private def extendCertifiedLaw (history : History G)
    (draw : { joint : (player : ι) → Option (G.execution.Action player) //
      G.execution.Legal history.state joint }) : FinDist (History G) :=
  (G.execution.step history.state draw).bindOnSupport
    fun _ realized => FinDist.pure (history.extend draw.2 realized)

/-- Resolve a completed prefix and retain the extended source history rather
than the administrative target boundary state. -/
private def extendCompletedLaw {history : History G}
    (collected : Prefix G order history order.slots)
    (hterm : ¬ G.execution.terminal history.state) :
    FinDist (History G) :=
  extendCertifiedLaw G history
    ⟨collected.joint, collected.joint_legal hterm⟩

/-- Forget target administrative microsteps while retaining the literal
source history carried by the serialized state. -/
def eraseHistory [DecidableEq ι]
    (history : (execution G order).History) : History G :=
  history.state.history

/-- Erasure preserves terminality exactly: administrative serialization
phases neither stop play early nor extend a stopped source history. -/
@[simp]
theorem terminal_eraseHistory_iff [DecidableEq ι]
    (history : (execution G order).History) :
    (execution G order).terminal history.state ↔
      G.execution.terminal (eraseHistory G order history).state := by
  rfl

/-- Sequentially draw the remaining scheduled target choices and finally
resolve the completed source joint.  This is an internal proof normal form,
not a second execution semantics. -/
private def completionLaw [DecidableEq ι]
    (target : (player : ι) →
      (information G order).BehavioralPolicy player)
    (history : History G)
    (hterm : ¬ G.execution.terminal history.state) :
    (remaining count : ℕ) → count + remaining = order.slots →
      Prefix G order history count → FinDist (History G)
  | 0, count, hcount, collected => by
      have heq : count = order.slots := by omega
      subst count
      exact extendCompletedLaw G order collected hterm
  | remaining + 1, count, hcount, collected => by
      have hslot : count < order.slots := by omega
      exact (targetChoiceAtLaw G order target history
        (scheduledPlayer G order collected hslot)).bind fun choice =>
          completionLaw target history hterm remaining (count + 1)
            (by omega) (collected.advance hslot choice)
termination_by remaining _ _ _ => remaining

/-- A target choice at a canonical scheduled view, read as the corresponding
certified source-local contribution. -/
private def scheduledChoiceAt [DecidableEq ι]
    (history : History G) (player : ι)
    (choice : (information G order).Choice player
      (scheduledView G player
        (G.information.infoOf player history.trace))) :
    ChoiceAt G history player :=
  sourceChoiceAt G history player
    (choiceEquiv G order player
      (G.information.infoOf player history.trace) choice)

/-- Embed the scheduled target choice into the unique possibly active joint
coordinate. -/
private def targetJointOfChoice [DecidableEq ι]
    {history : History G} {count : ℕ}
    (collected : Prefix G order history count)
    (hslot : count < order.slots)
    (hterm : ¬ G.execution.terminal history.state)
    (choice : (information G order).Choice
      (scheduledPlayer G order collected hslot)
      (scheduledView G (scheduledPlayer G order collected hslot)
        (G.information.infoOf
          (scheduledPlayer G order collected hslot) history.trace))) :
    { joint : (player : ι) → Option (G.execution.Action player) //
      (execution G order).Legal (.stage history count collected) joint } :=
  ⟨selectedJoint G (scheduledPlayer G order collected hslot) choice.1,
    by
      unfold ExecutionProtocol.Legal
      dsimp only [execution]
      simpa [scheduledChoiceAt, sourceChoiceAt, choiceEquiv,
        State.history] using
        selectedJoint_legal G order collected hslot hterm
          (scheduledChoiceAt G order history
            (scheduledPlayer G order collected hslot) choice)⟩

private theorem infoOf_stage_scheduled [DecidableEq ι]
    {history : History G} {count : ℕ}
    (collected : Prefix G order history count)
    (hslot : count < order.slots)
    (trace : (execution G order).Trace
      (.stage history count collected)) :
    (information G order).infoOf
        (scheduledPlayer G order collected hslot) trace =
      scheduledView G (scheduledPlayer G order collected hslot)
        (G.information.infoOf
          (scheduledPlayer G order collected hslot) history.trace) := by
  rw [infoOf_eq_viewOfState]
  simp [viewOfState, scheduledView, phaseOfState, hslot,
    scheduledPlayer, State.history]

/-- Read a choice at a view proved to be the canonical scheduled view.  The
equality is consumed here so dependent transport never leaks into the public
bridge statements. -/
private def choiceAtOfViewEq [DecidableEq ι]
    (history : History G) (player : ι)
    (view : (information G order).InfoState player)
    (hview : view = scheduledView G player
      (G.information.infoOf player history.trace))
    (choice : (information G order).Choice player view) :
    ChoiceAt G history player := by
  subst view
  exact scheduledChoiceAt G order history player choice

@[simp]
private theorem choiceAtOfViewEq_val [DecidableEq ι]
    (history : History G) (player : ι)
    (view : (information G order).InfoState player)
    (hview : view = scheduledView G player
      (G.information.infoOf player history.trace))
    (choice : (information G order).Choice player view) :
    (choiceAtOfViewEq G order history player view hview choice).1 =
      choice.1 := by
  subst view
  rfl

private theorem map_choiceAtOfViewEq [DecidableEq ι]
    (target : (player : ι) →
      (information G order).BehavioralPolicy player)
    (history : History G) (player : ι)
    (view : (information G order).InfoState player)
    (hview : view = scheduledView G player
      (G.information.infoOf player history.trace)) :
    FinDist.map (choiceAtOfViewEq G order history player view hview)
        (target player view) =
      targetChoiceAtLaw G order target history player := by
  subst view
  rfl

private def targetJointOfViewChoice [DecidableEq ι]
    {history : History G} {count : ℕ}
    (collected : Prefix G order history count)
    (hslot : count < order.slots)
    (hterm : ¬ G.execution.terminal history.state)
    (view : (information G order).InfoState
      (scheduledPlayer G order collected hslot))
    (hview : view = scheduledView G
      (scheduledPlayer G order collected hslot)
      (G.information.infoOf
        (scheduledPlayer G order collected hslot) history.trace))
    (choice : (information G order).Choice
      (scheduledPlayer G order collected hslot) view) :
    { joint : (player : ι) → Option (G.execution.Action player) //
      (execution G order).Legal (.stage history count collected) joint } :=
  ⟨selectedJoint G (scheduledPlayer G order collected hslot) choice.1,
    by
      unfold ExecutionProtocol.Legal
      dsimp only [execution]
      simpa [choiceAtOfViewEq_val, State.history] using
        selectedJoint_legal G order collected hslot hterm
          (choiceAtOfViewEq G order history
            (scheduledPlayer G order collected hslot) view hview choice)⟩

/-- At a selection stage, the generic behavioral joint is exactly the local
scheduled law embedded into its unique target coordinate. -/
private theorem behavioralJoint_stage [Fintype ι] [DecidableEq ι]
    (target : (player : ι) →
      (information G order).BehavioralPolicy player)
    {history : History G} {count : ℕ}
    (collected : Prefix G order history count)
    (hslot : count < order.slots)
    (hterm : ¬ G.execution.terminal history.state)
    (htargetTerm :
      ¬ (execution G order).terminal
        (.stage history count collected))
    (trace : (execution G order).Trace
      (.stage history count collected)) :
    (information G order).behavioralJoint target trace htargetTerm =
      FinDist.map
        (targetJointOfViewChoice G order collected hslot hterm
          ((information G order).infoOf
            (scheduledPlayer G order collected hslot) trace)
          (infoOf_stage_scheduled G order collected hslot trace))
        (target (scheduledPlayer G order collected hslot)
          ((information G order).infoOf
            (scheduledPlayer G order collected hslot) trace)) := by
  rw [InformationModel.behavioralJoint_eq_map_of_at_most_one_active
    (information G order) target trace htargetTerm
    (scheduledPlayer G order collected hslot) (by
      intro player hactive
      have hactive' : active G order (.stage history count collected) player := by
        with_reducible_and_instances exact hactive
      rw [active] at hactive'
      rcases hactive' with ⟨otherSlot, howner, _⟩
      simpa [scheduledPlayer] using howner)]
  apply congrArg
    (fun f => FinDist.map f
      (target (scheduledPlayer G order collected hslot)
        ((information G order).infoOf
          (scheduledPlayer G order collected hslot) trace)))
  funext choice
  apply Subtype.ext
  funext player
  by_cases howner :
      player = scheduledPlayer G order collected hslot
  · subst player
    rfl
  · simp [targetJointOfViewChoice, selectedJoint, howner]

@[simp]
private theorem choiceOfJoint_targetJointOfChoice [Fintype ι] [DecidableEq ι]
    {history : History G} {count : ℕ}
    (collected : Prefix G order history count)
    (hslot : count < order.slots)
    (hterm : ¬ G.execution.terminal history.state)
    (choice : (information G order).Choice
      (scheduledPlayer G order collected hslot)
      (scheduledView G (scheduledPlayer G order collected hslot)
        (G.information.infoOf
          (scheduledPlayer G order collected hslot) history.trace))) :
    choiceOfJoint G order collected hslot
        (targetJointOfChoice G order collected hslot hterm choice).1
        (targetJointOfChoice G order collected hslot hterm choice).2.2 =
      scheduledChoiceAt G order history
        (scheduledPlayer G order collected hslot) choice := by
  apply Subtype.ext
  simp [choiceOfJoint, targetJointOfChoice, selectedJoint,
    scheduledChoiceAt, sourceChoiceAt, choiceEquiv]

@[simp]
private theorem choiceOfJoint_targetJointOfViewChoice
    [Fintype ι] [DecidableEq ι]
    {history : History G} {count : ℕ}
    (collected : Prefix G order history count)
    (hslot : count < order.slots)
    (hterm : ¬ G.execution.terminal history.state)
    (view : (information G order).InfoState
      (scheduledPlayer G order collected hslot))
    (hview : view = scheduledView G
      (scheduledPlayer G order collected hslot)
      (G.information.infoOf
        (scheduledPlayer G order collected hslot) history.trace))
    (choice : (information G order).Choice
      (scheduledPlayer G order collected hslot) view) :
    choiceOfJoint G order collected hslot
        (targetJointOfViewChoice G order collected hslot hterm
          view hview choice).1
        (targetJointOfViewChoice G order collected hslot hterm
          view hview choice).2.2 =
      choiceAtOfViewEq G order history
        (scheduledPlayer G order collected hslot) view hview choice := by
  apply Subtype.ext
  simp [choiceOfJoint, targetJointOfViewChoice, selectedJoint,
    choiceAtOfViewEq_val]

/-- The resolver microstep erases exactly to the source transition selected by
the completed prefix. -/
private theorem map_erase_runBehavioralFrom_resolve [Fintype ι] [DecidableEq ι]
    (target : (player : ι) →
      (information G order).BehavioralPolicy player)
    (history : History G)
    (hterm : ¬ G.execution.terminal history.state)
    (collected : Prefix G order history order.slots)
    (trace : (execution G order).Trace
      (.stage history order.slots collected)) :
    FinDist.map (eraseHistory G order)
        ((information G order).runBehavioralFrom target 1
          ⟨.stage history order.slots collected, trace⟩) =
      extendCompletedLaw G order collected hterm := by
  have htargetTerm :
      ¬ (execution G order).terminal
        (.stage history order.slots collected) := hterm
  rw [InformationModel.runBehavioralFrom,
    show 1 = 0 + 1 by rfl,
    ExecutionProtocol.runRandomizedFor_succ_of_not_terminal
      (E := execution G order) _ 0
        (h := ⟨.stage history order.slots collected, trace⟩) htargetTerm,
    FinDist.map_bind]
  unfold InformationModel.randomizedChooser
  let idle (player : ι) :
      (information G order).Choice player
        ((information G order).infoOf player trace) :=
    ⟨none, by
      rw [infoOf_eq_viewOfState]
      simp [menu, viewOfState, phaseOfState]⟩
  have hpolicy (player : ι) :
      target player ((information G order).infoOf player trace) =
        FinDist.pure (idle player) := by
    haveI : Subsingleton
        ((information G order).Choice player
          ((information G order).infoOf player trace)) := ⟨by
      intro first second
      apply Subtype.ext
      have hfirst : first.1 = none := by
        simpa [information, menu, infoOf_eq_viewOfState,
          viewOfState, phaseOfState] using first.2
      have hsecond : second.1 = none := by
        simpa [information, menu, infoOf_eq_viewOfState,
          viewOfState, phaseOfState] using second.2
      rw [hfirst, hsecond]⟩
    exact FinDist.eq_pure_of_subsingleton _ (idle player)
  unfold InformationModel.behavioralJoint
  simp_rw [hpolicy]
  rw [FinDist.pi_pure, FinDist.map_pure,
    FinDist.pure_bind,
    FinDist.map_bindOnSupport]
  rw [FinDist.bindOnSupport_eq_bind_of_eq_on_support
    (g := fun state => FinDist.pure state.history) (by
      intro state realized
      rw [ExecutionProtocol.runRandomizedFor_zero, FinDist.map_pure]
      rfl)]
  rw [← FinDist.map_eq_bind]
  rw [dif_neg (Nat.lt_irrefl order.slots)]
  show FinDist.map (fun state : State G order => state.history)
      (resolve G order collected hterm) =
    extendCompletedLaw G order collected hterm
  unfold resolve extendCompletedLaw
  rw [FinDist.map_bindOnSupport]
  exact FinDist.bindOnSupport_congr fun reached realized => by
    rw [FinDist.map_pure]
    rfl

/-- From any within-round prefix, the remaining selection slots followed by
the resolver erase to the recursive source-history law above.  The theorem is
trace-parametric: target administrative traces affect neither future source
information nor the erased result. -/
private theorem map_erase_runBehavioralFrom_stage
    [Fintype ι] [DecidableEq ι]
    (target : (player : ι) →
      (information G order).BehavioralPolicy player)
    (history : History G)
    (hterm : ¬ G.execution.terminal history.state) :
    ∀ (remaining count : ℕ)
      (_hcount : count + remaining = order.slots)
      (collected : Prefix G order history count)
      (trace : (execution G order).Trace
        (.stage history count collected)),
      FinDist.map (eraseHistory G order)
          ((information G order).runBehavioralFrom target
            (remaining + 1)
            ⟨.stage history count collected, trace⟩) =
        completionLaw G order target history hterm
          remaining count _hcount collected := by
  intro remaining
  induction remaining with
  | zero =>
      intro count hcount collected trace
      have heq : count = order.slots := by omega
      subst count
      simpa [completionLaw] using
        map_erase_runBehavioralFrom_resolve G order target history
          hterm collected trace
  | succ remaining ih =>
      intro count hcount collected trace
      have hslot : count < order.slots := by omega
      let owner := scheduledPlayer G order collected hslot
      let actualView :=
        (information G order).infoOf owner trace
      have hview : actualView = scheduledView G owner
          (G.information.infoOf owner history.trace) :=
        infoOf_stage_scheduled G order collected hslot trace
      have htargetTerm :
          ¬ (execution G order).terminal
            (.stage history count collected) := by
        simpa [execution, terminal, State.history] using hterm
      rw [completionLaw]
      rw [← map_choiceAtOfViewEq G order target history owner
          actualView hview,
        FinDist.bind_map]
      rw [InformationModel.runBehavioralFrom,
        show remaining + 1 + 1 = (remaining + 1) + 1 by omega,
        ExecutionProtocol.runRandomizedFor_succ_of_not_terminal
          (E := execution G order) _ (remaining + 1)
            (h := ⟨.stage history count collected, trace⟩)
            htargetTerm,
        FinDist.map_bind]
      unfold InformationModel.randomizedChooser
      rw [behavioralJoint_stage G order target collected hslot
        hterm htargetTerm trace,
        FinDist.bind_map]
      apply FinDist.bind_congr
      intro choice hchoice
      refine FinDist.map_bindOnSupport_const _ fun state realized => ?_
      have realized' : state ∈
          ((execution G order).step
            (.stage history count collected)
            (targetJointOfViewChoice G order collected hslot hterm
              actualView hview choice)).support := by
        simpa only using realized
      simp only [execution] at realized'
      rw [dif_pos hslot, FinDist.mem_support_pure] at realized'
      subst state
      rw [← choiceOfJoint_targetJointOfViewChoice G order collected
        hslot hterm actualView hview choice]
      exact ih (count + 1) (by omega)
        (collected.advance hslot
          (choiceOfJoint G order collected hslot
            (targetJointOfViewChoice G order collected hslot hterm
              actualView hview choice).1
            (targetJointOfViewChoice G order collected hslot hterm
              actualView hview choice).2.2))
        ((⟨.stage history count collected, trace⟩ :
            (execution G order).History).extend
          (targetJointOfViewChoice G order collected hslot hterm
            actualView hview choice).2 realized).trace

/-- The explicit schedule as a duplicate-free exhaustive list. -/
private def playerOrder : List ι := List.ofFn order.player

@[simp]
private theorem playerOrder_length : (playerOrder order).length = order.slots := by
  simp [playerOrder]

private theorem playerOrder_nodup : (playerOrder order).Nodup := by
  exact List.nodup_ofFn_ofInjective order.player.injective

private theorem mem_playerOrder (player : ι) : player ∈ playerOrder order := by
  apply (List.mem_ofFn' order.player player).2
  exact ⟨order.player.symm player, order.player.apply_symm_apply player⟩

private theorem drop_playerOrder {history : History G} {count : ℕ}
    (collected : Prefix G order history count)
    (hslot : count < order.slots) :
    (playerOrder order).drop count =
      scheduledPlayer G order collected hslot ::
        (playerOrder order).drop (count + 1) := by
  rw [List.drop_eq_getElem_cons (by
    simpa [playerOrder] using hslot)]
  congr 1
  simp [playerOrder, scheduledPlayer]

namespace Prefix

/-- A total certified assignment agrees with a prefix exactly on the slots
already visited. -/
private def Matches {history : History G} {count : ℕ}
    (collected : Prefix G order history count)
    (assignment : (player : ι) → ChoiceAt G history player) : Prop :=
  ∀ player, collected.choices player =
    if (order.player.symm player).1 < count then
      some (assignment player)
    else none

private theorem initial_matches (history : History G)
    (assignment : (player : ι) → ChoiceAt G history player) :
    Matches (G := G) (order := order)
      (initial (G := G) (order := order) history) assignment := by
  intro player
  simp [initial]

private theorem advance_matches_setOne [DecidableEq ι]
    {history : History G} {count : ℕ}
    (collected : Prefix G order history count)
    (assignment : (player : ι) → ChoiceAt G history player)
    (hmatches : Matches (G := G) (order := order) collected assignment)
    (hslot : count < order.slots)
    (choice : ChoiceAt G history
      (scheduledPlayer G order collected hslot)) :
    Matches (G := G) (order := order)
      (collected.advance hslot choice)
      (FinDist.DependentAssignment.setOne assignment
        ⟨scheduledPlayer G order collected hslot, choice⟩) := by
  intro player
  by_cases howner :
      player = scheduledPlayer G order collected hslot
  · subst player
    have hnext :
        (order.player.symm
          (scheduledPlayer G order collected hslot)).1 < count + 1 := by
      simp [scheduledPlayer]
    have hset :
        FinDist.DependentAssignment.setOne assignment
            ⟨scheduledPlayer G order collected hslot, choice⟩
            (scheduledPlayer G order collected hslot) = choice := by
      simp [FinDist.DependentAssignment.setOne,
        FinDist.DependentAssignment.resolve]
    rw [show (collected.advance hslot choice).choices
          (scheduledPlayer G order collected hslot) = some choice by
        simp [advance, scheduledPlayer]]
    rw [if_pos hnext, hset]
  · have howner' :
        player ≠ order.player ⟨count, hslot⟩ := by
      simpa [scheduledPlayer] using howner
    have hadvance :
        (collected.advance hslot choice).choices player =
          collected.choices player := by
      simp [advance, howner']
    have hset :
        FinDist.DependentAssignment.setOne assignment
            ⟨scheduledPlayer G order collected hslot, choice⟩ player =
          assignment player := by
      simp [FinDist.DependentAssignment.setOne,
        FinDist.DependentAssignment.resolve, howner]
    rw [hadvance, hmatches player, hset]
    by_cases hselected : (order.player.symm player).1 < count
    · have hnext : (order.player.symm player).1 < count + 1 := by
        omega
      simp [hselected, hnext]
    · have hnext : ¬ (order.player.symm player).1 < count + 1 := by
        have hvalue : (order.player.symm player).1 ≠ count := by
          intro heq
          apply howner'
          calc
            player = order.player (order.player.symm player) :=
              (order.player.apply_symm_apply player).symm
            _ = order.player ⟨count, hslot⟩ := by
              congr 1
              exact Fin.ext heq
        omega
      simp [hselected, hnext]

end Prefix

/-- Turn a total certified assignment into its completed prefix. -/
private def prefixOfAssignment
    {history : History G}
    (assignment : (player : ι) → ChoiceAt G history player)
    (hterm : ¬ G.execution.terminal history.state) :
    Prefix G order history order.slots :=
  Prefix.ofJoint (G := G) (order := order)
    (fun player => (assignment player).1)
    (ExecutionProtocol.legal_of_legalOption hterm
      fun player => (assignment player).2)

@[simp]
private theorem prefixOfAssignment_joint
    {history : History G}
    (assignment : (player : ι) → ChoiceAt G history player)
    (hterm : ¬ G.execution.terminal history.state)
    (player : ι) :
    (prefixOfAssignment G order assignment hterm).joint player =
      (assignment player).1 := by
  simp [prefixOfAssignment, Prefix.joint,
    Prefix.completedChoice, Prefix.ofJoint]

private theorem Prefix.eq_prefixOfAssignment
    {history : History G}
    (collected : Prefix G order history order.slots)
    (assignment : (player : ι) → ChoiceAt G history player)
    (hmatches : Prefix.Matches (G := G) (order := order)
      collected assignment)
    (hterm : ¬ G.execution.terminal history.state) :
    collected = prefixOfAssignment G order assignment hterm := by
  apply Prefix.ext
  funext player
  rw [hmatches player]
  simp [prefixOfAssignment, Prefix.ofJoint]

/-- The bridge's recursive ordered law is the generic sequential dependent
draw over the remaining schedule. -/
private theorem completionLaw_eq_runDependent
    [DecidableEq ι]
    (target : (player : ι) →
      (information G order).BehavioralPolicy player)
    (history : History G)
    (hterm : ¬ G.execution.terminal history.state) :
    ∀ (remaining count : ℕ)
      (hcount : count + remaining = order.slots)
      (collected : Prefix G order history count)
      (assignment : (player : ι) → ChoiceAt G history player),
      Prefix.Matches (G := G) (order := order) collected assignment →
      completionLaw G order target history hterm
          remaining count hcount collected =
        (FinDist.runDependent
          (targetChoiceAtLaw G order target history)
          ((playerOrder order).drop count) assignment).bind
            (fun completed => extendCompletedLaw G order
              (prefixOfAssignment G order completed hterm) hterm) := by
  intro remaining
  induction remaining with
  | zero =>
      intro count hcount collected assignment hmatches
      have heq : count = order.slots := by omega
      subst count
      have hdrop :
          (playerOrder order).drop order.slots = [] := by
        apply List.drop_eq_nil_iff.mpr
        simp
      rw [completionLaw, hdrop, FinDist.runDependent,
        FinDist.pure_bind]
      rw [Prefix.eq_prefixOfAssignment G order collected assignment
        hmatches hterm]
  | succ remaining ih =>
      intro count hcount collected assignment hmatches
      have hslot : count < order.slots := by omega
      rw [completionLaw, drop_playerOrder G order collected hslot,
        FinDist.runDependent, FinDist.bind_bind]
      apply FinDist.bind_congr
      intro choice hchoice
      exact ih (count + 1) (by omega)
        (collected.advance hslot choice)
        (FinDist.DependentAssignment.setOne assignment
          ⟨scheduledPlayer G order collected hslot, choice⟩)
        (Prefix.advance_matches_setOne (G := G) (order := order)
          collected assignment hmatches hslot choice)

/-- A certified total assignment used only to initialize the generic
overwrite runner; exhaustiveness ensures none of its coordinates survive. -/
private noncomputable def defaultChoiceAssignment
    (history : History G)
    (hterm : ¬ G.execution.terminal history.state) :
    (player : ι) → ChoiceAt G history player :=
  let joint := Classical.choose (G.execution.exists_legal hterm)
  let hlegal := Classical.choose_spec (G.execution.exists_legal hterm)
  fun player => ⟨joint player,
    G.execution.legalOption_of_legal hlegal player⟩

/-- Starting at the empty prefix, the ordered recursive law is the canonical
independent product of the target's scheduled source-local laws. -/
private theorem completionLaw_initial_eq_pi
    [Fintype ι] [DecidableEq ι]
    (target : (player : ι) →
      (information G order).BehavioralPolicy player)
    (history : History G)
    (hterm : ¬ G.execution.terminal history.state) :
    completionLaw G order target history hterm order.slots 0
        (Nat.zero_add order.slots)
        (Prefix.initial (G := G) (order := order) history) =
      (FinDist.pi (targetChoiceAtLaw G order target history)).bind
        (fun completed => extendCompletedLaw G order
          (prefixOfAssignment G order completed hterm) hterm) := by
  rw [completionLaw_eq_runDependent G order target history hterm
    order.slots 0 (Nat.zero_add order.slots)
    (Prefix.initial (G := G) (order := order) history)
    (defaultChoiceAssignment G history hterm)
    (Prefix.initial_matches (G := G) (order := order) history
      (defaultChoiceAssignment G history hterm))]
  simp only [List.drop_zero]
  rw [FinDist.runDependent_eq_pi
    (targetChoiceAtLaw G order target history)
    (playerOrder order) (playerOrder_nodup order)
    (mem_playerOrder order) (defaultChoiceAssignment G history hterm)]

/-- One simultaneous source behavioral step is the independent product of its
certified local choice laws followed by the source transition kernel. -/
private theorem source_runBehavioralFrom_one_eq_choiceAtPi
    [Fintype ι]
    (source : (player : ι) → G.information.BehavioralPolicy player)
    (history : History G)
    (hterm : ¬ G.execution.terminal history.state) :
    G.information.runBehavioralFrom source 1 history =
      (FinDist.pi (sourceChoiceAtLaw G source history)).bind
        (fun assignment => extendCompletedLaw G order
          (prefixOfAssignment G order assignment hterm) hterm) := by
  rw [InformationModel.runBehavioralFrom,
    show 1 = 0 + 1 by rfl,
    ExecutionProtocol.runRandomizedFor_succ_of_not_terminal
      (E := G.execution) _ 0 (h := history) hterm]
  unfold InformationModel.randomizedChooser
  unfold InformationModel.behavioralJoint
  simp_rw [ExecutionProtocol.runRandomizedFor_zero]
  rw [FinDist.bind_map]
  unfold sourceChoiceAtLaw
  rw [FinDist.pi_map, FinDist.bind_map]
  apply FinDist.bind_congr
  intro choices hchoices
  let assignment : (player : ι) → ChoiceAt G history player :=
    fun player => sourceChoiceAt G history player (choices player)
  let behavioralDraw :
      { joint : (player : ι) → Option (G.execution.Action player) //
        G.execution.Legal history.state joint } :=
    ⟨fun player => (choices player).1,
      ExecutionProtocol.legal_of_legalOption hterm fun player =>
        (G.information.menu_adequate player history.trace
          (choices player).1).mp (choices player).2⟩
  let assignmentDraw :
      { joint : (player : ι) → Option (G.execution.Action player) //
        G.execution.Legal history.state joint } :=
    ⟨(prefixOfAssignment G order assignment hterm).joint,
      (prefixOfAssignment G order assignment hterm).joint_legal hterm⟩
  have hdraw : behavioralDraw = assignmentDraw := by
    apply Subtype.ext
    funext player
    simp [behavioralDraw, assignmentDraw, assignment, sourceChoiceAt]
  exact congrArg (extendCertifiedLaw G history) hdraw

/-- One complete serialized block erases to exactly one source behavioral
step for every target profile. -/
private theorem map_erase_runBehavioralFrom_boundary
    [Fintype ι] [DecidableEq ι]
    (target : (player : ι) →
      (information G order).BehavioralPolicy player)
    (history : History G)
    (hterm : ¬ G.execution.terminal history.state)
    (trace : (execution G order).Trace
      (.stage history 0
        (Prefix.initial (G := G) (order := order) history))) :
    FinDist.map (eraseHistory G order)
        ((information G order).runBehavioralFrom target
          (roundWidth order)
          ⟨.stage history 0
            (Prefix.initial (G := G) (order := order) history), trace⟩) =
      G.information.runBehavioralFrom
        (projectBehavioral G order target) 1 history := by
  rw [roundWidth]
  rw [map_erase_runBehavioralFrom_stage G order target history hterm
    order.slots 0 (Nat.zero_add order.slots)
    (Prefix.initial (G := G) (order := order) history) trace]
  rw [completionLaw_initial_eq_pi G order target history hterm]
  have hpi :
      FinDist.pi (targetChoiceAtLaw G order target history) =
        FinDist.pi (sourceChoiceAtLaw G
          (projectBehavioral G order target) history) := by
    apply congrArg FinDist.pi
    funext player
    exact targetChoiceAtLaw_eq_projected G order target history player
  rw [hpi]
  exact (source_runBehavioralFrom_one_eq_choiceAtPi G order
    (projectBehavioral G order target) history hterm).symm

private theorem map_erase_runBehavioralFrom_boundary_any
    [Fintype ι] [DecidableEq ι]
    (target : (player : ι) →
      (information G order).BehavioralPolicy player)
    (history : History G)
    (trace : (execution G order).Trace
      (.stage history 0
        (Prefix.initial (G := G) (order := order) history))) :
    FinDist.map (eraseHistory G order)
        ((information G order).runBehavioralFrom target
          (roundWidth order)
          ⟨.stage history 0
            (Prefix.initial (G := G) (order := order) history), trace⟩) =
      G.information.runBehavioralFrom
        (projectBehavioral G order target) 1 history := by
  by_cases hterm : G.execution.terminal history.state
  · have htarget : (execution G order).terminal
        (.stage history 0
          (Prefix.initial (G := G) (order := order) history)) := by
      simpa [execution, terminal, State.history] using hterm
    rw [InformationModel.runBehavioralFrom,
      ExecutionProtocol.runRandomizedFor_of_terminal
        (E := execution G order) _ _
        (h := ⟨.stage history 0
          (Prefix.initial (G := G) (order := order) history), trace⟩)
        htarget,
      FinDist.map_pure,
      InformationModel.runBehavioralFrom,
      ExecutionProtocol.runRandomizedFor_of_terminal
        (E := G.execution) _ _ (h := history) hterm]
    rfl
  · exact map_erase_runBehavioralFrom_boundary G order target
      history hterm trace

/-- A complete serialized suffix always returns to a round boundary. -/
private theorem state_of_mem_runBehavioralFrom_stage
    [Fintype ι] [DecidableEq ι]
    (target : (player : ι) →
      (information G order).BehavioralPolicy player)
    (history : History G)
    (hterm : ¬ G.execution.terminal history.state) :
    ∀ (remaining count : ℕ)
      (_hcount : count + remaining = order.slots)
      (collected : Prefix G order history count)
      (trace : (execution G order).Trace
        (.stage history count collected))
      {reached : (execution G order).History},
      reached ∈ ((information G order).runBehavioralFrom target
        (remaining + 1)
        ⟨.stage history count collected, trace⟩).support →
      ∃ sourceHistory : History G,
        reached.state = .stage sourceHistory 0
          (Prefix.initial (G := G) (order := order) sourceHistory) := by
  intro remaining
  induction remaining with
  | zero =>
      intro count hcount collected trace reached hreached
      have heq : count = order.slots := by omega
      subst count
      have htargetTerm :
          ¬ (execution G order).terminal
            (.stage history order.slots collected) := by
        simpa [execution, terminal, State.history] using hterm
      rw [InformationModel.runBehavioralFrom,
        show 0 + 1 = 0 + 1 by rfl,
        ExecutionProtocol.runRandomizedFor_succ_of_not_terminal
          (E := execution G order) _ 0
          (h := ⟨.stage history order.slots collected, trace⟩)
          htargetTerm] at hreached
      simp only [FinDist.support_bind, Set.mem_iUnion] at hreached
      obtain ⟨draw, hdraw, hreached⟩ := hreached
      simp only [FinDist.support_bindOnSupport, Set.mem_iUnion] at hreached
      obtain ⟨state, hstate, hreached⟩ := hreached
      rw [ExecutionProtocol.runRandomizedFor_zero,
        FinDist.mem_support_pure] at hreached
      subst reached
      have hstate' : state ∈
          ((execution G order).step
            (.stage history order.slots collected) draw).support := by
        simpa only using hstate
      simp only [execution] at hstate'
      rw [dif_neg (Nat.lt_irrefl order.slots)] at hstate'
      rw [mem_support_resolve_iff] at hstate'
      rcases hstate' with ⟨sourceState, realized, rfl⟩
      exact ⟨history.extend (collected.joint_legal draw.2.1) realized, rfl⟩
  | succ remaining ih =>
      intro count hcount collected trace reached hreached
      have hslot : count < order.slots := by omega
      have htargetTerm :
          ¬ (execution G order).terminal
            (.stage history count collected) := by
        simpa [execution, terminal, State.history] using hterm
      rw [InformationModel.runBehavioralFrom,
        show remaining + 1 + 1 = (remaining + 1) + 1 by omega,
        ExecutionProtocol.runRandomizedFor_succ_of_not_terminal
          (E := execution G order) _ (remaining + 1)
          (h := ⟨.stage history count collected, trace⟩)
          htargetTerm] at hreached
      simp only [FinDist.support_bind, Set.mem_iUnion] at hreached
      obtain ⟨draw, hdraw, hreached⟩ := hreached
      simp only [FinDist.support_bindOnSupport, Set.mem_iUnion] at hreached
      obtain ⟨state, hstate, hreached⟩ := hreached
      have hstate' : state ∈
          ((execution G order).step
            (.stage history count collected) draw).support := by
        simpa only using hstate
      simp only [execution] at hstate'
      rw [dif_pos hslot, FinDist.mem_support_pure] at hstate'
      subst state
      exact ih (count + 1) (by omega)
        (collected.advance hslot
          (choiceOfJoint G order collected hslot draw.1 draw.2.2))
        ((⟨.stage history count collected, trace⟩ :
          (execution G order).History).extend draw.2 hstate).trace
        hreached

private theorem state_of_mem_runBehavioralFrom_boundary_any
    [Fintype ι] [DecidableEq ι]
    (target : (player : ι) →
      (information G order).BehavioralPolicy player)
    (history : History G)
    (trace : (execution G order).Trace
      (.stage history 0
        (Prefix.initial (G := G) (order := order) history)))
    {reached : (execution G order).History}
    (hreached : reached ∈
      ((information G order).runBehavioralFrom target
        (roundWidth order)
        ⟨.stage history 0
          (Prefix.initial (G := G) (order := order) history), trace⟩).support) :
    ∃ sourceHistory : History G,
      reached.state = .stage sourceHistory 0
        (Prefix.initial (G := G) (order := order) sourceHistory) := by
  by_cases hterm : G.execution.terminal history.state
  · have htarget : (execution G order).terminal
        (.stage history 0
          (Prefix.initial (G := G) (order := order) history)) := by
      simpa [execution, terminal, State.history] using hterm
    rw [InformationModel.runBehavioralFrom,
      ExecutionProtocol.runRandomizedFor_of_terminal
        (E := execution G order) _ _
        (h := ⟨.stage history 0
          (Prefix.initial (G := G) (order := order) history), trace⟩)
        htarget,
      FinDist.mem_support_pure] at hreached
    subst reached
    exact ⟨history, rfl⟩
  · rw [roundWidth] at hreached
    exact state_of_mem_runBehavioralFrom_stage G order target history
      hterm order.slots 0 (Nat.zero_add order.slots)
      (Prefix.initial (G := G) (order := order) history) trace hreached

/-- Every integral number of serialized blocks ends at a round boundary. This
is the support invariant needed to continue serialized play from a reached
history without exposing a partially collected source joint. -/
theorem state_of_mem_runBehavioralFrom_rounds
    [Fintype ι] [DecidableEq ι]
    (target : (player : ι) →
      (information G order).BehavioralPolicy player) :
    ∀ (rounds : ℕ) (history : History G)
      (trace : (execution G order).Trace
        (.stage history 0
          (Prefix.initial (G := G) (order := order) history)))
      {reached : (execution G order).History},
      reached ∈ ((information G order).runBehavioralFrom target
        (rounds * roundWidth order)
        ⟨.stage history 0
          (Prefix.initial (G := G) (order := order) history), trace⟩).support →
      ∃ sourceHistory : History G,
        reached.state = .stage sourceHistory 0
          (Prefix.initial (G := G) (order := order) sourceHistory) := by
  intro rounds
  induction rounds with
  | zero =>
      intro history trace reached hreached
      rw [Nat.zero_mul, InformationModel.runBehavioralFrom,
        ExecutionProtocol.runRandomizedFor_zero,
        FinDist.mem_support_pure] at hreached
      subst reached
      exact ⟨history, rfl⟩
  | succ rounds ih =>
      intro history trace reached hreached
      rw [show (rounds + 1) * roundWidth order =
          roundWidth order + rounds * roundWidth order by
            simp [Nat.succ_mul, Nat.add_comm],
        InformationModel.runBehavioralFrom_add] at hreached
      simp only [FinDist.support_bind, Set.mem_iUnion] at hreached
      obtain ⟨middle, hmiddle, hreached⟩ := hreached
      obtain ⟨middleSource, hmiddleState⟩ :=
        state_of_mem_runBehavioralFrom_boundary_any G order target
          history trace hmiddle
      rcases middle with ⟨middleState, middleTrace⟩
      have hstate : middleState = .stage middleSource 0
          (Prefix.initial (G := G) (order := order) middleSource) :=
        hmiddleState
      subst middleState
      exact ih middleSource middleTrace hreached

/-- Whole serialized rounds started at the target root end at a round
boundary. -/
theorem state_of_mem_runBehavioral_rounds
    [Fintype ι] [DecidableEq ι]
    (target : (player : ι) →
      (information G order).BehavioralPolicy player)
    (rounds : ℕ) {reached : (execution G order).History}
    (hreached : reached ∈
      ((information G order).runBehavioral target
        (rounds * roundWidth order)).support) :
    ∃ sourceHistory : History G,
      reached.state = .stage sourceHistory 0
        (Prefix.initial (G := G) (order := order) sourceHistory) := by
  unfold InformationModel.runBehavioral at hreached
  have hinit : (execution G order).initHistory =
      ⟨.stage G.execution.initHistory 0
        (Prefix.initial (G := G) (order := order)
          G.execution.initHistory),
        (execution G order).initHistory.trace⟩ := by
    rfl
  rw [hinit] at hreached
  exact state_of_mem_runBehavioralFrom_rounds G order target rounds
    G.execution.initHistory (execution G order).initHistory.trace hreached

/-- From any reached round boundary, an integral number of serialized rounds
has exactly the projected source continuation law. This is stronger than the
initial-state law: downstream analyses may condition on the supplied boundary
history and continue from there. -/
theorem map_erase_runBehavioralFrom_eq_source
    [Fintype ι] [DecidableEq ι]
    (target : (player : ι) →
      (information G order).BehavioralPolicy player) :
    ∀ (rounds : ℕ) (history : History G)
      (trace : (execution G order).Trace
        (.stage history 0
          (Prefix.initial (G := G) (order := order) history))),
      FinDist.map (eraseHistory G order)
          ((information G order).runBehavioralFrom target
            (rounds * roundWidth order)
            ⟨.stage history 0
              (Prefix.initial (G := G) (order := order) history), trace⟩) =
        G.information.runBehavioralFrom
          (projectBehavioral G order target) rounds history := by
  intro rounds
  induction rounds with
  | zero =>
      intro history trace
      rw [Nat.zero_mul, InformationModel.runBehavioralFrom,
        ExecutionProtocol.runRandomizedFor_zero,
        FinDist.map_pure,
        InformationModel.runBehavioralFrom,
        ExecutionProtocol.runRandomizedFor_zero]
      rfl
  | succ rounds ih =>
      intro history trace
      rw [show (rounds + 1) * roundWidth order =
          roundWidth order + rounds * roundWidth order by
            simp [Nat.succ_mul, Nat.add_comm],
        InformationModel.runBehavioralFrom_add,
        FinDist.map_bind]
      calc
        _ = ((information G order).runBehavioralFrom target
              (roundWidth order)
              ⟨.stage history 0
                (Prefix.initial (G := G) (order := order) history), trace⟩).bind
            (fun middle =>
              G.information.runBehavioralFrom
                (projectBehavioral G order target) rounds
                (eraseHistory G order middle)) := by
          apply FinDist.bind_congr
          intro middle hmiddle
          obtain ⟨middleSource, hmiddleState⟩ :=
            state_of_mem_runBehavioralFrom_boundary_any G order target
              history trace hmiddle
          rcases middle with ⟨middleState, middleTrace⟩
          have hstate : middleState = .stage middleSource 0
              (Prefix.initial (G := G) (order := order) middleSource) :=
            hmiddleState
          subst middleState
          exact ih middleSource middleTrace
        _ = (FinDist.map (eraseHistory G order)
              ((information G order).runBehavioralFrom target
                (roundWidth order)
                ⟨.stage history 0
                  (Prefix.initial (G := G) (order := order) history), trace⟩)).bind
            (G.information.runBehavioralFrom
              (projectBehavioral G order target) rounds) := by
          rw [FinDist.bind_map]
        _ = (G.information.runBehavioralFrom
              (projectBehavioral G order target) 1 history).bind
            (G.information.runBehavioralFrom
              (projectBehavioral G order target) rounds) := by
          rw [map_erase_runBehavioralFrom_boundary_any G order target
            history trace]
        _ = G.information.runBehavioralFrom
              (projectBehavioral G order target) (rounds + 1) history := by
          rw [show rounds + 1 = 1 + rounds by omega,
            InformationModel.runBehavioralFrom_add]

/-- Exact scaled behavioral-history law from the initial state. -/
theorem map_erase_runBehavioral_eq_source
    [Fintype ι] [DecidableEq ι]
    (target : (player : ι) →
      (information G order).BehavioralPolicy player)
    (rounds : ℕ) :
    FinDist.map (eraseHistory G order)
        ((information G order).runBehavioral target
          (rounds * roundWidth order)) =
      G.information.runBehavioral
        (projectBehavioral G order target) rounds := by
  unfold InformationModel.runBehavioral
  have hinit : (execution G order).initHistory =
      ⟨.stage G.execution.initHistory 0
        (Prefix.initial (G := G) (order := order)
          G.execution.initHistory),
        (execution G order).initHistory.trace⟩ := by
    rfl
  rw [hinit]
  exact map_erase_runBehavioralFrom_eq_source G order target rounds
    G.execution.initHistory (execution G order).initHistory.trace

/-- A source continuation history has positive probability exactly when some
positively supported serialized continuation erases to it. -/
theorem mem_support_runBehavioralFrom_projected_iff
    [Fintype ι] [DecidableEq ι]
    (target : (player : ι) →
      (information G order).BehavioralPolicy player)
    (rounds : ℕ) (history : History G)
    (trace : (execution G order).Trace
      (.stage history 0
        (Prefix.initial (G := G) (order := order) history)))
    (sourceReached : History G) :
    sourceReached ∈
        (G.information.runBehavioralFrom
          (projectBehavioral G order target) rounds history).support ↔
      ∃ targetReached ∈
          ((information G order).runBehavioralFrom target
            (rounds * roundWidth order)
            ⟨.stage history 0
              (Prefix.initial (G := G) (order := order) history), trace⟩).support,
        eraseHistory G order targetReached = sourceReached := by
  rw [← map_erase_runBehavioralFrom_eq_source G order target rounds
    history trace, FinDist.support_map]
  rfl

/-- Initial-state support form of
`mem_support_runBehavioralFrom_projected_iff`. -/
theorem mem_support_runBehavioral_projected_iff
    [Fintype ι] [DecidableEq ι]
    (target : (player : ι) →
      (information G order).BehavioralPolicy player)
    (rounds : ℕ) (sourceReached : History G) :
    sourceReached ∈
        (G.information.runBehavioral
          (projectBehavioral G order target) rounds).support ↔
      ∃ targetReached ∈
          ((information G order).runBehavioral target
            (rounds * roundWidth order)).support,
        eraseHistory G order targetReached = sourceReached := by
  rw [← map_erase_runBehavioral_eq_source G order target rounds,
    FinDist.support_map]
  rfl

/-- Terminal continuations occur with positive probability before
serialization exactly when they occur after a whole number of serialized
rounds. -/
theorem exists_terminal_mem_support_runBehavioralFrom_iff
    [Fintype ι] [DecidableEq ι]
    (target : (player : ι) →
      (information G order).BehavioralPolicy player)
    (rounds : ℕ) (history : History G)
    (trace : (execution G order).Trace
      (.stage history 0
        (Prefix.initial (G := G) (order := order) history))) :
    (∃ targetReached ∈
        ((information G order).runBehavioralFrom target
          (rounds * roundWidth order)
          ⟨.stage history 0
            (Prefix.initial (G := G) (order := order) history), trace⟩).support,
      (execution G order).terminal targetReached.state) ↔
      ∃ sourceReached ∈
        (G.information.runBehavioralFrom
          (projectBehavioral G order target) rounds history).support,
        G.execution.terminal sourceReached.state := by
  constructor
  · rintro ⟨targetReached, htarget, hterm⟩
    refine ⟨eraseHistory G order targetReached, ?_, ?_⟩
    · exact (mem_support_runBehavioralFrom_projected_iff G order target
        rounds history trace _).2 ⟨targetReached, htarget, rfl⟩
    · exact (terminal_eraseHistory_iff G order targetReached).1 hterm
  · rintro ⟨sourceReached, hsource, hterm⟩
    obtain ⟨targetReached, htarget, herase⟩ :=
      (mem_support_runBehavioralFrom_projected_iff G order target rounds
        history trace sourceReached).1 hsource
    refine ⟨targetReached, htarget, ?_⟩
    apply (terminal_eraseHistory_iff G order targetReached).2
    rw [herase]
    exact hterm

/-- Initial-state terminal-support form of
`exists_terminal_mem_support_runBehavioralFrom_iff`. -/
theorem exists_terminal_mem_support_runBehavioral_iff
    [Fintype ι] [DecidableEq ι]
    (target : (player : ι) →
      (information G order).BehavioralPolicy player)
    (rounds : ℕ) :
    (∃ targetReached ∈
        ((information G order).runBehavioral target
          (rounds * roundWidth order)).support,
      (execution G order).terminal targetReached.state) ↔
      ∃ sourceReached ∈
        (G.information.runBehavioral
          (projectBehavioral G order target) rounds).support,
        G.execution.terminal sourceReached.state := by
  constructor
  · rintro ⟨targetReached, htarget, hterm⟩
    refine ⟨eraseHistory G order targetReached, ?_, ?_⟩
    · exact (mem_support_runBehavioral_projected_iff G order target
        rounds _).2 ⟨targetReached, htarget, rfl⟩
    · exact (terminal_eraseHistory_iff G order targetReached).1 hterm
  · rintro ⟨sourceReached, hsource, hterm⟩
    obtain ⟨targetReached, htarget, herase⟩ :=
      (mem_support_runBehavioral_projected_iff G order target rounds
        sourceReached).1 hsource
    refine ⟨targetReached, htarget, ?_⟩
    apply (terminal_eraseHistory_iff G order targetReached).2
    rw [herase]
    exact hterm

/-- Forward translation preserves every finite source history law. -/
theorem map_erase_runBehavioral_translate
    [Fintype ι] [DecidableEq ι]
    (source : (player : ι) → G.information.BehavioralPolicy player)
    (rounds : ℕ) :
    FinDist.map (eraseHistory G order)
        ((information G order).runBehavioral
          (translateBehavioral G order source)
          (rounds * roundWidth order)) =
      G.information.runBehavioral source rounds := by
  rw [map_erase_runBehavioral_eq_source,
    project_translate_profile]

/-- Arbitrary target play transports through its source projection to any
other explicit order without changing the erased history law. -/
theorem map_erase_runBehavioral_order_transport
    [Fintype ι] [DecidableEq ι]
    (first second : ExplicitOrder ι)
    (target : (player : ι) →
      (information G first).BehavioralPolicy player)
    (rounds : ℕ) :
    FinDist.map (eraseHistory G first)
        ((information G first).runBehavioral target
          (rounds * roundWidth first)) =
      FinDist.map (eraseHistory G second)
        ((information G second).runBehavioral
          (translateBehavioral G second
            (projectBehavioral G first target))
          (rounds * roundWidth second)) := by
  rw [map_erase_runBehavioral_eq_source,
    map_erase_runBehavioral_translate]

end GameTheory.Languages.Bridges.FOSGToEFG
