import GameTheory.Languages.FOSG.Information
import GameTheory.Languages.FOSG.Execution
import GameTheory.Languages.FOSG.Values
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Nodup
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# GameTheory.Languages.FOSG.Serial

Serialization of FOSGs into turn-based serial FOSGs.

This follows the paper's serial construction at the game-structure level. The
serialized game inserts deterministic player-choice states and chance-resolution
states. Deterministic inserted steps emit trivial observations, so serialized
observation spaces are `Option`-wrapped.
-/

namespace GameTheory

open Math.Probability

namespace FOSG

variable {ι W : Type} [DecidableEq ι]
variable {Act : ι → Type} {PrivObs : ι → Type} {PubObs : Type}

/-- A one-player serialized move: player `i` submits `ai`, every other player
submits `none`. -/
def singleMove (i : ι) (ai : Act i) : JointAction Act :=
  fun j =>
    if h : j = i then
      some (Eq.ndrec ai (by cases h; rfl))
    else
      none

@[simp] theorem singleMove_self (i : ι) (ai : Act i) :
    singleMove (Act := Act) i ai i = some ai := by
  simp [singleMove]

@[simp] theorem singleMove_other {i j : ι} (ai : Act i) (hij : j ≠ i) :
    singleMove (Act := Act) i ai j = none := by
  simp [singleMove, hij]

/-- A partial choice assignment is compatible with a legal joint action if every
recorded choice agrees with it. -/
def ExtendsPartial
    (G : FOSG ι W Act PrivObs PubObs)
    {w : W} (chosen : JointAction Act) (a : G.LegalAction w) : Prop :=
  ∀ j, chosen j = none ∨ chosen j = a.1 j

/-- Update a partial choice assignment with the current serialized move. -/
def recordChoice
    (chosen move : JointAction Act) (current : ι) : JointAction Act :=
  fun j => if j = current then move j else chosen j

@[simp] theorem recordChoice_self
    (chosen move : JointAction Act) (current : ι) :
    recordChoice chosen move current current = move current := by
  simp [recordChoice]

@[simp] theorem recordChoice_other
    (chosen move : JointAction Act) {current j : ι} (h : j ≠ current) :
    recordChoice chosen move current j = chosen j := by
  simp [recordChoice, h]

theorem extendsPartial_noop
    (G : FOSG ι W Act PrivObs PubObs)
    {w : W} (a : G.LegalAction w) :
    G.ExtendsPartial (noopAction Act) a := by
  intro j
  left
  rfl

theorem extendsPartial_recordChoice
    (G : FOSG ι W Act PrivObs PubObs)
    {w : W} {chosen move : JointAction Act} {current : ι} {a : G.LegalAction w}
    (hchosen : G.ExtendsPartial chosen a)
    (hcurrent : a.1 current = move current) :
    G.ExtendsPartial (recordChoice chosen move current) a := by
  intro j
  by_cases hji : j = current
  · right
    subst hji
    simp [recordChoice, hcurrent]
  · simpa [recordChoice, hji] using hchosen j

section Ordered

variable [LinearOrder ι]

/-- Active players sorted by the ambient linear order. -/
def orderedActive
    (G : FOSG ι W Act PrivObs PubObs) (w : W) : List ι :=
  (G.active w).sort (· ≤ ·)

theorem mem_orderedActive_iff
    (G : FOSG ι W Act PrivObs PubObs) (w : W) (i : ι) :
    i ∈ G.orderedActive w ↔ i ∈ G.active w := by
  simp [orderedActive, Finset.mem_sort]

theorem orderedActive_eq_nil_of_active_eq_empty
    (G : FOSG ι W Act PrivObs PubObs) {w : W}
    (hactive : G.active w = ∅) :
    G.orderedActive w = [] := by
  cases hlist : G.orderedActive w with
  | nil =>
      rfl
  | cons i rest =>
      exfalso
      have hi : i ∈ G.orderedActive w := by simp [hlist]
      have : i ∈ G.active w := (G.mem_orderedActive_iff w i).1 hi
      simp [hactive] at this

theorem active_eq_empty_of_orderedActive_eq_nil
    (G : FOSG ι W Act PrivObs PubObs) {w : W}
    (horder : G.orderedActive w = []) :
    G.active w = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.2
  intro i hi
  have : i ∈ G.orderedActive w := (G.mem_orderedActive_iff w i).2 hi
  simp [horder] at this

theorem current_mem_active_of_split
    (G : FOSG ι W Act PrivObs PubObs)
    {w : W} {current : ι} {rest : List ι}
    (hsplit : ∃ acted : List ι, G.orderedActive w = acted ++ current :: rest) :
    current ∈ G.active w := by
  rcases hsplit with ⟨acted, hsplit⟩
  have : current ∈ G.orderedActive w := by
    rw [hsplit]
    simp
  exact (G.mem_orderedActive_iff w current).1 this

theorem current_not_mem_rest_of_split
    (G : FOSG ι W Act PrivObs PubObs)
    {w : W} {current : ι} {rest : List ι}
    (hsplit : ∃ acted : List ι, G.orderedActive w = acted ++ current :: rest) :
    current ∉ rest := by
  rcases hsplit with ⟨acted, hsplit⟩
  have hnodup : (G.orderedActive w).Nodup :=
    Finset.sort_nodup (s := G.active w) (r := (· ≤ ·))
  have hnodup' : (acted ++ current :: rest).Nodup := by
    simpa [hsplit] using hnodup
  have hsuffix : (current :: rest).Nodup :=
    List.Nodup.of_append_right hnodup'
  exact (List.nodup_cons.mp hsuffix).1

/-- Valid intermediate serialized decision states: a partial assignment that can
still be extended to some legal joint action of the original world state, with
the current player and all remaining players still unset. -/
def ValidDecision
    (G : FOSG ι W Act PrivObs PubObs)
    (w : W) (chosen : JointAction Act) (current : ι) (rest : List ι) : Prop :=
  (∃ acted : List ι, G.orderedActive w = acted ++ current :: rest) ∧
  (∀ j, j ∈ current :: rest → chosen j = none) ∧
  (∃ a : G.LegalAction w, G.ExtendsPartial chosen a)

/-- Proof-layer invariant for canonical serialization of a fixed original legal
action: `chosen` records exactly the actions of the players in `acted`, and
records `none` for everyone else. This is stronger than `ExtendsPartial` and is
the right invariant for serialization-correctness proofs. -/
def MatchesActedPrefix
    (G : FOSG ι W Act PrivObs PubObs)
    {w : W} (ga : G.LegalAction w) (chosen : JointAction Act) (acted : List ι) : Prop :=
  ∀ j, chosen j = if j ∈ acted then ga.1 j else none

/-- The canonical partial choice assignment determined by a legal action `ga`
and the list of already-acted players. -/
def prefixChoice
    (G : FOSG ι W Act PrivObs PubObs)
    {w : W} (ga : G.LegalAction w) (acted : List ι) : JointAction Act :=
  fun j => if j ∈ acted then ga.1 j else none

/-- Serialized state space. `base w` is the original world state before any
serialized action is taken at `w`; `decide ...` stores the partial assignment
after some players have already acted; `chance w a` is the inserted stochastic
resolution step after all active players have selected their actions. -/
inductive SerialState
    (G : FOSG ι W Act PrivObs PubObs) where
  | base : W → SerialState G
  | decide :
      (w : W) →
      (chosen : JointAction Act) →
      (current : ι) →
      (rest : List ι) →
      ValidDecision G w chosen current rest →
      SerialState G
  | chance : (w : W) → G.LegalAction w → SerialState G

namespace SerialState

variable {G : FOSG ι W Act PrivObs PubObs}

/-- Active player function for the serialized game. -/
def active : SerialState G → Finset ι
  | .base w =>
      match G.orderedActive w with
      | [] => ∅
      | i :: _ => {i}
  | .decide _ _ i _ _ => {i}
  | .chance _ _ => ∅

/-- Terminal states of the serialized game. Only terminal base states are
terminal. -/
def terminal : SerialState G → Prop
  | .base w => G.terminal w
  | .decide _ _ _ _ _ => False
  | .chance _ _ => False

instance instDecidablePredTerminal [DecidablePred G.terminal] :
    DecidablePred (terminal (G := G)) := by
  intro s
  cases s with
  | base w =>
      exact ‹DecidablePred G.terminal› w
  | decide w chosen current rest hvalid =>
      exact isFalse (by simp [terminal])
  | chance w a =>
      exact isFalse (by simp [terminal])

/-- Underlying original-world state represented by a serialized state. -/
def world : SerialState G → W
  | .base w => w
  | .decide w _ _ _ _ => w
  | .chance w _ => w

@[simp] theorem world_base (w : W) :
    world (G := G) (.base w) = w := rfl

@[simp] theorem world_decide
    (w : W) (chosen : JointAction Act) (current : ι) (rest : List ι)
    (hvalid : G.ValidDecision w chosen current rest) :
    world (G := G) (.decide w chosen current rest hvalid) = w := rfl

@[simp] theorem world_chance
    (w : W) (a : G.LegalAction w) :
    world (G := G) (.chance w a) = w := rfl

/-- Serialized legal actions at a player-controlled serialized state. -/
def playerLegal
    (w : W) (chosen : JointAction Act) (current : ι) (a : JointAction Act) : Prop :=
  (∃ ai : Act current, a current = some ai) ∧
  (∀ j, j ≠ current → a j = none) ∧
  (∃ ga : G.LegalAction w, G.ExtendsPartial chosen ga ∧ ga.1 current = a current)

/-- Legal actions of the serialized game. -/
def legal : SerialState G → JointAction Act → Prop
  | .base w, a =>
      match G.orderedActive w with
      | [] => ¬ G.terminal w ∧ a = noopAction Act
      | current :: _ => playerLegal (G := G) w (noopAction Act) current a
  | .decide w chosen current _ _, a =>
      playerLegal (G := G) w chosen current a
  | .chance _ _, a =>
      a = noopAction Act

/-- Primitive local action sets for the serialized game. Joint legality for the
serialized FOSG is defined from these sets together with nonterminality. -/
def availableActions : SerialState G → (i : ι) → Set (Act i)
  | .base w, i =>
      match G.orderedActive w with
      | [] => ∅
      | current :: _ =>
          if i = current then
            { ai | playerLegal (G := G) w (noopAction Act) current
                (singleMove (Act := Act) i ai) }
          else ∅
  | .decide w chosen current _ _, i =>
      if i = current then
        { ai | playerLegal (G := G) w chosen current
            (singleMove (Act := Act) i ai) }
      else ∅
  | .chance _ _, _ => ∅

theorem legal_iff_jointActionLegal
    (s : SerialState G) (a : JointAction Act) :
    legal (G := G) s a ↔
      JointActionLegal Act (active (G := G)) (terminal (G := G))
        (availableActions (G := G)) s a := by
  sorry

abbrev LegalAction (s : SerialState G) : Type :=
  { a : JointAction Act // legal (G := G) s a }

abbrev FOSGLegalAction (s : SerialState G) : Type :=
  { a : JointAction Act //
      JointActionLegal Act (active (G := G)) (terminal (G := G))
        (availableActions (G := G)) s a }

def toFOSGLegalAction {s : SerialState G} (a : LegalAction (G := G) s) :
    FOSGLegalAction (G := G) s :=
  ⟨a.1, (legal_iff_jointActionLegal (G := G) s a.1).mp a.2⟩

def ofFOSGLegalAction {s : SerialState G} (a : FOSGLegalAction (G := G) s) :
    LegalAction (G := G) s :=
  ⟨a.1, (legal_iff_jointActionLegal (G := G) s a.1).mpr a.2⟩

@[simp] theorem toFOSGLegalAction_val {s : SerialState G} (a : LegalAction (G := G) s) :
    (toFOSGLegalAction (G := G) a).1 = a.1 := rfl

@[simp] theorem ofFOSGLegalAction_val {s : SerialState G} (a : FOSGLegalAction (G := G) s) :
    (ofFOSGLegalAction (G := G) a).1 = a.1 := rfl

omit [LinearOrder ι] in
theorem playerLegal_current_some
    {w : W} {chosen a : JointAction Act} {current : ι}
    (h : playerLegal (G := G) w chosen current a) :
    ∃ ai : Act current, a current = some ai := h.1

omit [LinearOrder ι] in
theorem playerLegal_other_none
    {w : W} {chosen a : JointAction Act} {current j : ι}
    (h : playerLegal (G := G) w chosen current a) (hji : j ≠ current) :
    a j = none := h.2.1 j hji

theorem active_eq_empty_of_base_terminal
    {w : W} (hterm : G.terminal w) :
    active (G := G) (.base w) = ∅ := by
  have hactive : G.active w = ∅ := G.active_eq_empty_of_terminal hterm
  have horder : G.orderedActive w = [] := G.orderedActive_eq_nil_of_active_eq_empty hactive
  simp [SerialState.active, horder]

/-- A legal original-world action at a base chance node of the original FOSG. -/
noncomputable def baseChanceLegalAction
    (w : W) (h : G.active w = ∅) (hNotTerm : ¬ G.terminal w) : G.LegalAction w := by
  exact ⟨noopAction Act, G.legal_noopAction_of_active_empty_of_not_terminal h hNotTerm⟩

omit [LinearOrder ι] in
@[simp] theorem baseChanceLegalAction_val
    (w : W) (h : G.active w = ∅) (hNotTerm : ¬ G.terminal w) :
    (baseChanceLegalAction (G := G) w h hNotTerm).1 = noopAction Act := rfl

/-- The original action chosen by an active player inside a legal joint action. -/
noncomputable def actionAtActive
    {w : W} (ga : G.LegalAction w) (i : ι) (hi : i ∈ G.active w) : Act i :=
  Classical.choose (G.active_has_some (a := ga) hi)

omit [LinearOrder ι] in
theorem actionAtActive_spec
    {w : W} (ga : G.LegalAction w) (i : ι) (hi : i ∈ G.active w) :
    ga.1 i = some (actionAtActive (G := G) ga i hi) :=
  Classical.choose_spec (G.active_has_some (a := ga) hi)

/-- The canonical serialized move for player `current`, replaying the action
that `ga` already chose for them. -/
noncomputable def moveOfLegalAction
    {w : W} (ga : G.LegalAction w) (current : ι) (hcurrent : current ∈ G.active w) :
    JointAction Act :=
  singleMove (Act := Act) current (actionAtActive (G := G) ga current hcurrent)

omit [LinearOrder ι] in
@[simp] theorem moveOfLegalAction_current
    {w : W} (ga : G.LegalAction w) (current : ι) (hcurrent : current ∈ G.active w) :
    moveOfLegalAction (G := G) ga current hcurrent current = ga.1 current := by
  simpa [moveOfLegalAction] using
    (actionAtActive_spec (G := G) ga current hcurrent).symm

omit [LinearOrder ι] in
@[simp] theorem moveOfLegalAction_other
    {w : W} (ga : G.LegalAction w) {current j : ι}
    (hcurrent : current ∈ G.active w) (hji : j ≠ current) :
    moveOfLegalAction (G := G) ga current hcurrent j = none := by
  simp [moveOfLegalAction, hji]

omit [LinearOrder ι] in
theorem matchesActedPrefix_noop
    {w : W} (ga : G.LegalAction w) :
    G.MatchesActedPrefix ga (noopAction Act) [] := by
  intro j
  simp [noopAction]

omit [LinearOrder ι] in
theorem matchesActedPrefix_prefixChoice
    {w : W} (ga : G.LegalAction w) (acted : List ι) :
    G.MatchesActedPrefix ga (G.prefixChoice ga acted) acted := by
  intro j
  rfl

omit [LinearOrder ι] in
@[simp] theorem prefixChoice_nil
    {w : W} (ga : G.LegalAction w) :
    G.prefixChoice ga [] = noopAction Act := by
  funext j
  simp [prefixChoice, noopAction]

omit [LinearOrder ι] in
@[simp] theorem prefixChoice_apply_of_mem
    {w : W} (ga : G.LegalAction w) {acted : List ι} {j : ι}
    (hj : j ∈ acted) :
    G.prefixChoice ga acted j = ga.1 j := by
  simp [prefixChoice, hj]

omit [LinearOrder ι] in
@[simp] theorem prefixChoice_apply_of_not_mem
    {w : W} (ga : G.LegalAction w) {acted : List ι} {j : ι}
    (hj : j ∉ acted) :
    G.prefixChoice ga acted j = none := by
  simp [prefixChoice, hj]

omit [LinearOrder ι] in
theorem matchesActedPrefix_recordChoice_move
    {w : W} (ga : G.LegalAction w) {chosen : JointAction Act} {acted : List ι}
    {current : ι} (hchosen : G.MatchesActedPrefix ga chosen acted)
    (hcurrent : current ∈ G.active w) :
    G.MatchesActedPrefix ga
      (recordChoice chosen (moveOfLegalAction (G := G) ga current hcurrent) current)
      (acted ++ [current]) := by
  intro j
  by_cases hji : j = current
  · subst hji
    simpa [recordChoice, moveOfLegalAction] using
      (actionAtActive_spec (G := G) ga j hcurrent).symm
  · simp [recordChoice, hji, hchosen j, List.mem_append]

omit [LinearOrder ι] in
theorem prefixChoice_recordChoice_move
    {w : W} (ga : G.LegalAction w) {acted : List ι} {current : ι}
    (hcurrent : current ∈ G.active w) :
    recordChoice (G.prefixChoice ga acted)
      (moveOfLegalAction (G := G) ga current hcurrent) current =
      G.prefixChoice ga (acted ++ [current]) := by
  funext j
  by_cases hji : j = current
  · subst hji
    simpa [recordChoice, prefixChoice, moveOfLegalAction] using
      (actionAtActive_spec (G := G) ga j hcurrent).symm
  · simp [recordChoice, prefixChoice, hji, List.mem_append]

theorem legalAction_eq_of_extends_matchesOrderedActive
    {w : W} {ga ga' : G.LegalAction w} {chosen : JointAction Act}
    (hchosen : G.MatchesActedPrefix ga chosen (G.orderedActive w))
    (hcomp : G.ExtendsPartial chosen ga') :
    ga' = ga := by
  apply Subtype.ext
  funext j
  by_cases hj : j ∈ G.active w
  · have hjOrder : j ∈ G.orderedActive w := (G.mem_orderedActive_iff w j).2 hj
    have hchosenj : chosen j = ga.1 j := by
      simpa [MatchesActedPrefix, hjOrder] using hchosen j
    rcases G.active_has_some (a := ga) hj with ⟨ai, hai⟩
    rcases hcomp j with hnone | hEq
    · rw [hchosenj, hai] at hnone
      cases hnone
    · exact hEq.symm.trans hchosenj
  · have hjOrder : j ∉ G.orderedActive w := by
      simpa [G.mem_orderedActive_iff w j] using hj
    have hnoneChosen : chosen j = none := by
      simpa [MatchesActedPrefix, hjOrder] using hchosen j
    have hnoneGa : ga.1 j = none := G.inactive_eq_none (a := ga) hj
    have hnoneGa' : ga'.1 j = none := G.inactive_eq_none (a := ga') hj
    rw [hnoneGa', hnoneGa]

theorem not_mem_acted_of_mem_remaining
    {w : W} {acted : List ι} {current : ι} {rest : List ι} {j : ι}
    (hsplit : G.orderedActive w = acted ++ current :: rest)
    (hj : j ∈ current :: rest) :
    j ∉ acted := by
  have hnodup : (G.orderedActive w).Nodup :=
    Finset.sort_nodup (s := G.active w) (r := (· ≤ ·))
  have hnodup' : (acted ++ current :: rest).Nodup := by
    simpa [hsplit] using hnodup
  have hdisj : List.Disjoint acted (current :: rest) :=
    List.disjoint_of_nodup_append hnodup'
  rw [List.disjoint_left] at hdisj
  exact fun hjActed => hdisj hjActed hj

theorem validDecision_of_prefix
    {w : W} (ga : G.LegalAction w) {acted : List ι} {current : ι} {rest : List ι}
    (hsplit : G.orderedActive w = acted ++ current :: rest) :
    G.ValidDecision w (G.prefixChoice ga acted) current rest := by
  refine ⟨⟨acted, hsplit⟩, ?_, ?_⟩
  · intro j hj
    exact prefixChoice_apply_of_not_mem (G := G) ga
      (not_mem_acted_of_mem_remaining (G := G) hsplit hj)
  · refine ⟨ga, ?_⟩
    intro j
    by_cases hjActed : j ∈ acted
    · right
      exact prefixChoice_apply_of_mem (G := G) ga hjActed
    · left
      exact prefixChoice_apply_of_not_mem (G := G) ga hjActed

theorem base_playerLegal_of_legalAction
    {w : W} (ga : G.LegalAction w) {current : ι} {rest : List ι}
    (horder : G.orderedActive w = current :: rest) :
    playerLegal (G := G) w (noopAction Act) current
      (moveOfLegalAction (G := G) ga current
        ((G.mem_orderedActive_iff w current).1 (by simp [horder]))) := by
  let hcurrent : current ∈ G.active w :=
    (G.mem_orderedActive_iff w current).1 (by simp [horder])
  refine ⟨⟨actionAtActive (G := G) ga current hcurrent, by simp [moveOfLegalAction]⟩, ?_, ?_⟩
  · intro j hj
    exact moveOfLegalAction_other (G := G) ga hcurrent hj
  · refine ⟨ga, G.extendsPartial_noop ga, ?_⟩
    exact (moveOfLegalAction_current (G := G) ga current hcurrent).symm

theorem decide_playerLegal_of_legalAction
    {w : W} (ga : G.LegalAction w) {chosen : JointAction Act}
    {current : ι} {rest : List ι} (hvalid : G.ValidDecision w chosen current rest)
    (hcomp : G.ExtendsPartial chosen ga) :
    playerLegal (G := G) w chosen current
      (moveOfLegalAction (G := G) ga current
        (G.current_mem_active_of_split
          (show ∃ acted, G.orderedActive w = acted ++ current :: rest from hvalid.1))) := by
  let hcurrent : current ∈ G.active w :=
    G.current_mem_active_of_split (show ∃ acted, G.orderedActive w = acted ++ current :: rest from
      hvalid.1)
  refine ⟨⟨actionAtActive (G := G) ga current hcurrent, by simp [moveOfLegalAction]⟩, ?_, ?_⟩
  · intro j hj
    exact moveOfLegalAction_other (G := G) ga hcurrent hj
  · refine ⟨ga, hcomp, ?_⟩
    exact (moveOfLegalAction_current (G := G) ga current hcurrent).symm

theorem validDecision_from_base
    {w : W} {current next : ι} {tail : List ι}
    (horder : G.orderedActive w = current :: next :: tail)
    {a : JointAction Act}
    (ha : playerLegal (G := G) w (noopAction Act) current a) :
    G.ValidDecision w (recordChoice (noopAction Act) a current) next tail := by
  rcases ha with ⟨_, hnone, ⟨ga, hcomp, hcurrent⟩⟩
  refine ⟨⟨[current], by simpa using horder⟩, ?_, ?_⟩
  · intro j hj
    have hneq : j ≠ current := by
      intro hji
      subst hji
      exact G.current_not_mem_rest_of_split ⟨[], horder⟩ hj
    simp [recordChoice, hneq]
  · refine ⟨ga, ?_⟩
    exact G.extendsPartial_recordChoice hcomp hcurrent

theorem validDecision_step
    {w : W} {chosen : JointAction Act} {current next : ι} {tail : List ι}
    (hvalid : G.ValidDecision w chosen current (next :: tail))
    {a : JointAction Act}
    (ha : playerLegal (G := G) w chosen current a) :
    G.ValidDecision w (recordChoice chosen a current) next tail := by
  rcases hvalid with ⟨hsplit, hnoneRem, hchosen⟩
  rcases hsplit with ⟨acted, hsplit⟩
  rcases ha with ⟨_, hnone, ⟨ga, hcomp, hcurrent⟩⟩
  refine ⟨⟨acted ++ [current], by simpa [List.append_assoc] using hsplit⟩, ?_, ?_⟩
  · intro j hj
    have hneq : j ≠ current := by
      intro hji
      subst hji
      exact G.current_not_mem_rest_of_split ⟨acted, hsplit⟩ (by simpa using hj)
    have hchosen : chosen j = none := hnoneRem j (by simp [hj])
    simp [recordChoice, hneq, hchosen]
  · refine ⟨ga, ?_⟩
    exact G.extendsPartial_recordChoice hcomp hcurrent

/-- The deterministic successor after a serialized player move from a base
state, parameterized by the ordered active-player list. -/
noncomputable def basePlayerSuccessorWithOrder
    (w : W) (oa : List ι) (horder : G.orderedActive w = oa)
    (a : { a : JointAction Act // legal (G := G) (.base w) a }) :
    SerialState G :=
  match oa with
  | [] => .base w
  | current :: rest =>
      let hlegal : playerLegal (G := G) w (noopAction Act) current a.1 := by
        simpa [SerialState.legal, horder] using a.2
      let ga : G.LegalAction w := Classical.choose hlegal.2.2
      match rest with
      | [] => .chance w ga
      | next :: tail =>
          .decide w (recordChoice (noopAction Act) a.1 current) next tail
            (validDecision_from_base (G := G) (a := a.1) (by simpa using horder) hlegal)

/-- The deterministic successor after a serialized player move from a base
state with nonempty active set. -/
noncomputable def basePlayerSuccessor
    (w : W) (a : { a : JointAction Act // legal (G := G) (.base w) a }) :
    SerialState G :=
  basePlayerSuccessorWithOrder (G := G) w (G.orderedActive w) rfl a

@[simp] theorem world_basePlayerSuccessorWithOrder
    {w : W} {oa : List ι} (horder : G.orderedActive w = oa)
    (a : { a : JointAction Act // legal (G := G) (.base w) a }) :
    SerialState.world (G := G)
      (SerialState.basePlayerSuccessorWithOrder (G := G) w oa horder a) = w := by
  cases oa with
  | nil =>
      simp [SerialState.basePlayerSuccessorWithOrder, SerialState.world]
  | cons current rest =>
      cases rest with
      | nil =>
          simp [SerialState.basePlayerSuccessorWithOrder, SerialState.world]
      | cons next tail =>
          simp [SerialState.basePlayerSuccessorWithOrder, SerialState.world]

@[simp] theorem world_basePlayerSuccessor
    {w : W} (a : { a : JointAction Act // legal (G := G) (.base w) a }) :
    SerialState.world (G := G) (SerialState.basePlayerSuccessor (G := G) w a) = w := by
  unfold SerialState.basePlayerSuccessor
  exact world_basePlayerSuccessorWithOrder (G := G) (w := w) rfl a

/-- The deterministic successor after a serialized player move from an
intermediate decision state. -/
noncomputable def decidePlayerSuccessor
    (w : W) (chosen : JointAction Act) (current : ι) (rest : List ι)
    (hvalid : G.ValidDecision w chosen current rest)
    (a : { a : JointAction Act // legal (G := G) (.decide w chosen current rest hvalid) a }) :
    SerialState G :=
  match rest with
  | [] =>
      let hlegal : playerLegal (G := G) w chosen current a.1 := by
        simpa [SerialState.legal] using a.2
      let ga : G.LegalAction w := Classical.choose hlegal.2.2
      .chance w ga
  | next :: tail =>
      let hlegal : playerLegal (G := G) w chosen current a.1 := by
        simpa [SerialState.legal] using a.2
      .decide w (recordChoice chosen a.1 current) next tail
        (validDecision_step (G := G) (a := a.1) hvalid hlegal)

@[simp] theorem world_decidePlayerSuccessor
    {w : W} {chosen : JointAction Act} {current : ι} {rest : List ι}
    {hvalid : G.ValidDecision w chosen current rest}
    (a : { a : JointAction Act //
      legal (G := G) (.decide w chosen current rest hvalid) a }) :
    SerialState.world (G := G)
      (SerialState.decidePlayerSuccessor (G := G) w chosen current rest hvalid a) = w := by
  unfold SerialState.decidePlayerSuccessor
  split <;> simp [SerialState.world]

/-- Canonical serialized action replaying the first active player's move from a
base state for a fixed original legal action. -/
noncomputable def baseReplayAction
    {w : W} (ga : G.LegalAction w) {current : ι} {rest : List ι}
    (horder : G.orderedActive w = current :: rest) :
    { a : JointAction Act // legal (G := G) (.base w) a } :=
  ⟨moveOfLegalAction (G := G) ga current
      ((G.mem_orderedActive_iff w current).1 (by simp [horder])),
    by
      simpa [SerialState.legal, horder] using
        base_playerLegal_of_legalAction (G := G) ga horder⟩

theorem basePlayerSuccessorWithOrder_replay_cons
    {w : W} (ga : G.LegalAction w) {current next : ι} {tail : List ι}
    (horder : G.orderedActive w = current :: next :: tail) :
    SerialState.basePlayerSuccessorWithOrder (G := G) w (current :: next :: tail) horder
      (baseReplayAction (G := G) ga horder) =
      .decide w (G.prefixChoice ga [current]) next tail
        (validDecision_of_prefix (G := G) ga
          (acted := [current]) (current := next) (rest := tail) (by simpa using horder)) := by
  have hcurrent : current ∈ G.active w :=
    (G.mem_orderedActive_iff w current).1 (by simp [horder])
  have hchoice :
      recordChoice (noopAction Act)
        (moveOfLegalAction (G := G) ga current hcurrent) current =
        G.prefixChoice ga [current] := by
    simpa [prefixChoice_nil (G := G) ga] using
      prefixChoice_recordChoice_move (G := G) ga (acted := []) hcurrent
  simp [SerialState.basePlayerSuccessorWithOrder, baseReplayAction, hchoice]

theorem basePlayerSuccessorWithOrder_replay_last
    {w : W} (ga : G.LegalAction w) {current : ι}
    (horder : G.orderedActive w = [current]) :
    SerialState.basePlayerSuccessorWithOrder (G := G) w [current] horder
      (baseReplayAction (G := G) ga horder) =
      .chance w ga := by
  have hcurrent : current ∈ G.active w :=
    (G.mem_orderedActive_iff w current).1 (by simp [horder])
  have hlegal :
      playerLegal (G := G) w (noopAction Act) current
        (moveOfLegalAction (G := G) ga current hcurrent) :=
    base_playerLegal_of_legalAction (G := G) ga horder
  let ga' : G.LegalAction w := Classical.choose hlegal.2.2
  have hga'comp : G.ExtendsPartial (noopAction Act) ga' :=
    (Classical.choose_spec hlegal.2.2).1
  have hga'current :
      ga'.1 current =
        moveOfLegalAction (G := G) ga current hcurrent current := by
    simpa [ga'] using (Classical.choose_spec hlegal.2.2).2
  have hmatchFull :
      G.MatchesActedPrefix ga (recordChoice (noopAction Act)
        (moveOfLegalAction (G := G) ga current hcurrent) current) (G.orderedActive w) := by
    simpa [horder, MatchesActedPrefix] using
      matchesActedPrefix_recordChoice_move (G := G) ga
        (chosen := noopAction Act) (acted := [])
        (hchosen := matchesActedPrefix_noop (G := G) ga) hcurrent
  have hga : ga' = ga := by
    apply legalAction_eq_of_extends_matchesOrderedActive (G := G) hmatchFull
    exact G.extendsPartial_recordChoice hga'comp hga'current
  have hgaChoose : (Classical.choose hlegal.2.2 : G.LegalAction w) = ga := by
    simpa [ga'] using hga
  unfold SerialState.basePlayerSuccessorWithOrder
  simpa [baseReplayAction, ga'] using hgaChoose

theorem basePlayerSuccessor_replay_cons
    {w : W} (ga : G.LegalAction w) {current next : ι} {tail : List ι}
    (horder : G.orderedActive w = current :: next :: tail) :
    SerialState.basePlayerSuccessor (G := G) w (baseReplayAction (G := G) ga horder) =
      .decide w (G.prefixChoice ga [current]) next tail
        (validDecision_of_prefix (G := G) ga
          (acted := [current]) (current := next) (rest := tail) (by simpa using horder)) := by
  have hbase :
      SerialState.basePlayerSuccessor (G := G) w (baseReplayAction (G := G) ga horder) =
      SerialState.basePlayerSuccessorWithOrder (G := G) w (current :: next :: tail) horder
        (baseReplayAction (G := G) ga horder) := by
    simp [SerialState.basePlayerSuccessor, horder]
  exact hbase.trans <|
    basePlayerSuccessorWithOrder_replay_cons (G := G) (ga := ga) (horder := horder)

theorem basePlayerSuccessor_replay_last
    {w : W} (ga : G.LegalAction w) {current : ι}
    (horder : G.orderedActive w = [current]) :
    SerialState.basePlayerSuccessor (G := G) w (baseReplayAction (G := G) ga horder) =
      .chance w ga := by
  have hbase :
      SerialState.basePlayerSuccessor (G := G) w (baseReplayAction (G := G) ga horder) =
      SerialState.basePlayerSuccessorWithOrder (G := G) w [current] horder
        (baseReplayAction (G := G) ga horder) := by
    simp [SerialState.basePlayerSuccessor, horder]
  exact hbase.trans <|
    basePlayerSuccessorWithOrder_replay_last (G := G) (ga := ga) (horder := horder)

/-- Canonical serialized action replaying the current player's move from a
decision state for a fixed original legal action. -/
noncomputable def decideReplayAction
    {w : W} (ga : G.LegalAction w) {acted : List ι} {current : ι} {rest : List ι}
    (hsplit : G.orderedActive w = acted ++ current :: rest) :
    { a : JointAction Act //
      legal (G := G) (.decide w (G.prefixChoice ga acted) current rest
        (validDecision_of_prefix (G := G) ga hsplit)) a } :=
  ⟨moveOfLegalAction (G := G) ga current
      (G.current_mem_active_of_split ⟨acted, hsplit⟩),
    by
      simpa [SerialState.legal] using
        decide_playerLegal_of_legalAction (G := G) ga
          (validDecision_of_prefix (G := G) ga hsplit)
          (by
            intro j
            by_cases hjActed : j ∈ acted
            · right
              exact prefixChoice_apply_of_mem (G := G) ga hjActed
            · left
              exact prefixChoice_apply_of_not_mem (G := G) ga hjActed)⟩

theorem decidePlayerSuccessor_replay_cons
    {w : W} (ga : G.LegalAction w) {acted : List ι} {current next : ι} {tail : List ι}
    (hsplit : G.orderedActive w = acted ++ current :: next :: tail) :
    SerialState.decidePlayerSuccessor (G := G) w (G.prefixChoice ga acted) current (next :: tail)
      (validDecision_of_prefix (G := G) ga hsplit)
      (decideReplayAction (G := G) ga hsplit) =
      .decide w (G.prefixChoice ga (acted ++ [current])) next tail
        (validDecision_of_prefix (G := G) ga
          (acted := acted ++ [current]) (current := next) (rest := tail)
          (by simpa [List.append_assoc] using hsplit)) := by
  have hcurrent : current ∈ G.active w :=
    G.current_mem_active_of_split ⟨acted, hsplit⟩
  have hchoice :
      recordChoice (G.prefixChoice ga acted)
        (moveOfLegalAction (G := G) ga current hcurrent) current =
        G.prefixChoice ga (acted ++ [current]) := by
    exact prefixChoice_recordChoice_move (G := G) ga (acted := acted) hcurrent
  simp [SerialState.decidePlayerSuccessor, decideReplayAction, hchoice]

theorem decidePlayerSuccessor_replay_last
    {w : W} (ga : G.LegalAction w) {acted : List ι} {current : ι}
    (hsplit : G.orderedActive w = acted ++ [current]) :
    SerialState.decidePlayerSuccessor (G := G) w (G.prefixChoice ga acted) current []
      (validDecision_of_prefix (G := G) ga hsplit)
      (decideReplayAction (G := G) ga hsplit) =
      .chance w ga := by
  have hcurrent : current ∈ G.active w :=
    G.current_mem_active_of_split ⟨acted, by simpa using hsplit⟩
  have hlegal :
      playerLegal (G := G) w (G.prefixChoice ga acted) current
        (moveOfLegalAction (G := G) ga current hcurrent) :=
    decide_playerLegal_of_legalAction (G := G) ga
      (validDecision_of_prefix (G := G) ga hsplit) (by
        intro j
        by_cases hjActed : j ∈ acted
        · right
          exact prefixChoice_apply_of_mem (G := G) ga hjActed
        · left
          exact prefixChoice_apply_of_not_mem (G := G) ga hjActed)
  let ga' : G.LegalAction w := Classical.choose hlegal.2.2
  have hga'comp : G.ExtendsPartial (G.prefixChoice ga acted) ga' :=
    (Classical.choose_spec hlegal.2.2).1
  have hga'current :
      ga'.1 current =
        moveOfLegalAction (G := G) ga current hcurrent current := by
    simpa [ga'] using (Classical.choose_spec hlegal.2.2).2
  have hmatchFull :
      G.MatchesActedPrefix ga
        (recordChoice (G.prefixChoice ga acted)
          (moveOfLegalAction (G := G) ga current hcurrent) current)
        (G.orderedActive w) := by
    simpa [hsplit, MatchesActedPrefix] using
      matchesActedPrefix_recordChoice_move (G := G) ga
        (chosen := G.prefixChoice ga acted) (acted := acted)
        (hchosen := matchesActedPrefix_prefixChoice (G := G) ga acted) hcurrent
  have hga : ga' = ga := by
    apply legalAction_eq_of_extends_matchesOrderedActive (G := G) hmatchFull
    exact G.extendsPartial_recordChoice hga'comp hga'current
  have hgaChoose : (Classical.choose hlegal.2.2 : G.LegalAction w) = ga := by
    simpa [ga'] using hga
  unfold SerialState.decidePlayerSuccessor
  simpa [decideReplayAction, ga'] using hgaChoose

/-- Canonical noop action at a serialized chance-resolution state. -/
noncomputable def chanceResolutionAction
    {w : W} (ga : G.LegalAction w) :
    { a : JointAction Act // legal (G := G) (.chance w ga) a } :=
  ⟨noopAction Act, by simp [SerialState.legal]⟩

/-- Transition kernel of the serialized game. -/
noncomputable def transition :
    (s : SerialState G) → {a : JointAction Act // legal (G := G) s a} → PMF (SerialState G)
  | .base w, a =>
      if hEmpty : G.orderedActive w = [] then
          let ha : ¬ G.terminal w ∧ a.1 = noopAction Act := by
            simpa [SerialState.legal, hEmpty] using a.2
          let ga := baseChanceLegalAction (G := G) w
            (G.active_eq_empty_of_orderedActive_eq_nil hEmpty) ha.1
          PMF.map (SerialState.base (G := G)) (G.transition w ga)
      else
        PMF.pure (basePlayerSuccessor (G := G) w a)
  | .decide w chosen current rest hvalid, a =>
      PMF.pure (decidePlayerSuccessor (G := G) w chosen current rest hvalid a)
  | .chance w ga, _ =>
      PMF.map (SerialState.base (G := G)) (G.transition w ga)

theorem transition_base_empty_eq
    {w : W} (hEmpty : G.orderedActive w = [])
    (a : { a : JointAction Act // legal (G := G) (.base w) a }) :
    SerialState.transition (G := G) (.base w) a =
      PMF.map (SerialState.base (G := G))
        (G.transition w (baseChanceLegalAction (G := G) w
          (G.active_eq_empty_of_orderedActive_eq_nil hEmpty) ((by
          have ha : ¬ G.terminal w ∧ a.1 = noopAction Act := by
            simpa [SerialState.legal, hEmpty] using a.2
          exact ha.1) : ¬ G.terminal w))) := by
  simp [SerialState.transition, hEmpty]

theorem transition_base_nonempty_eq
    {w : W} (hNonempty : G.orderedActive w ≠ [])
    (a : { a : JointAction Act // legal (G := G) (.base w) a }) :
    SerialState.transition (G := G) (.base w) a =
      PMF.pure (SerialState.basePlayerSuccessor (G := G) w a) := by
  simp [SerialState.transition, hNonempty]

theorem transition_decide_eq
    {w : W} {chosen : JointAction Act} {current : ι} {rest : List ι}
    {hvalid : G.ValidDecision w chosen current rest}
    (a : { a : JointAction Act //
      legal (G := G) (.decide w chosen current rest hvalid) a }) :
    SerialState.transition (G := G) (.decide w chosen current rest hvalid) a =
      PMF.pure (SerialState.decidePlayerSuccessor (G := G) w chosen current rest hvalid a) := by
  simp [SerialState.transition]

/-- Reward function of the serialized game. Deterministic action-selection steps
have zero reward; stochastic resolution steps inherit the original reward. -/
noncomputable def reward :
    (s : SerialState G) →
    {a : JointAction Act // legal (G := G) s a} →
    SerialState G → ι → ℝ
  | .base w, a, s', i =>
      if hEmpty : G.orderedActive w = [] then
          let ha : ¬ G.terminal w ∧ a.1 = noopAction Act := by
            simpa [SerialState.legal, hEmpty] using a.2
          let ga := baseChanceLegalAction (G := G) w
            (G.active_eq_empty_of_orderedActive_eq_nil hEmpty) ha.1
          match s' with
          | .base w' => G.reward w ga w' i
          | _ => 0
      else 0
  | .decide _ _ _ _ _, _, _, _ => 0
  | .chance w ga, _, s', i =>
      match s' with
      | .base w' => G.reward w ga w' i
      | _ => 0

theorem reward_decide_eq_zero
    {w : W} {chosen : JointAction Act} {current : ι} {rest : List ι}
    {hvalid : G.ValidDecision w chosen current rest}
    (a : { a : JointAction Act //
      legal (G := G) (.decide w chosen current rest hvalid) a })
    (s' : SerialState G) (i : ι) :
    SerialState.reward (G := G) (.decide w chosen current rest hvalid) a s' i = 0 := by
  simp [SerialState.reward]

theorem reward_chance_base_eq
    {w w' : W} (ga : G.LegalAction w)
    (a : { a : JointAction Act // legal (G := G) (.chance w ga) a })
    (i : ι) :
    SerialState.reward (G := G) (.chance w ga) a (.base w') i = G.reward w ga w' i := by
  simp [SerialState.reward]

theorem reward_decide_successor_eq_zero
    {w : W} {chosen : JointAction Act} {current : ι} {rest : List ι}
    {hvalid : G.ValidDecision w chosen current rest}
    (a : { a : JointAction Act //
      legal (G := G) (.decide w chosen current rest hvalid) a })
    (i : ι) :
    SerialState.reward (G := G) (.decide w chosen current rest hvalid) a
      (SerialState.decidePlayerSuccessor (G := G) w chosen current rest hvalid a) i = 0 := by
  exact reward_decide_eq_zero (G := G) a _ _

theorem reward_basePlayerSuccessor_eq_zero
    {w : W}
    (a : { a : JointAction Act // legal (G := G) (.base w) a })
    (hNonempty : G.orderedActive w ≠ []) (i : ι) :
    SerialState.reward (G := G) (.base w) a
      (SerialState.basePlayerSuccessor (G := G) w a) i = 0 := by
  simp [SerialState.reward, hNonempty]

theorem reward_base_empty_base_eq_of_active_empty
    {w w' : W}
    (hactive : G.active w = ∅)
    (a : { a : JointAction Act // legal (G := G) (.base w) a })
    (i : ι) :
    SerialState.reward (G := G) (.base w) a (.base w') i =
      G.reward w
        (baseChanceLegalAction (G := G) w hactive
          (by
            have horder : G.orderedActive w = [] :=
              G.orderedActive_eq_nil_of_active_eq_empty hactive
            have ha : ¬ G.terminal w ∧ a.1 = noopAction Act := by
              simpa [SerialState.legal, horder] using a.2
            exact ha.1))
        w' i := by
  have horder : G.orderedActive w = [] :=
    G.orderedActive_eq_nil_of_active_eq_empty hactive
  have hgaEq :
      baseChanceLegalAction (G := G) w
        (G.active_eq_empty_of_orderedActive_eq_nil horder)
        (by
          have ha : ¬ G.terminal w ∧ a.1 = noopAction Act := by
            simpa [SerialState.legal, horder] using a.2
          exact ha.1) =
      baseChanceLegalAction (G := G) w hactive
        (by
          have ha : ¬ G.terminal w ∧ a.1 = noopAction Act := by
            simpa [SerialState.legal, horder] using a.2
          exact ha.1) := by
    apply Subtype.ext
    funext j
    simp [baseChanceLegalAction_val]
  have hrew : G.reward w
      (baseChanceLegalAction (G := G) w
        (G.active_eq_empty_of_orderedActive_eq_nil horder)
        (by
          have ha : ¬ G.terminal w ∧ a.1 = noopAction Act := by
            simpa [SerialState.legal, horder] using a.2
          exact ha.1)) w' i =
      G.reward w
        (baseChanceLegalAction (G := G) w hactive
          (by
            have ha : ¬ G.terminal w ∧ a.1 = noopAction Act := by
              simpa [SerialState.legal, horder] using a.2
            exact ha.1)) w' i :=
    congrArg (fun ga => G.reward w ga w' i) hgaEq
  simp [SerialState.reward, horder, hrew]

/-- Private observations of the serialized game. Deterministic action-selection
steps emit `none`; stochastic resolution steps emit the original observation
wrapped in `some`. -/
noncomputable def privObs :
    (i : ι) →
    (s : SerialState G) →
    {a : JointAction Act // legal (G := G) s a} →
    SerialState G → Option (PrivObs i)
  | i, .base w, a, s' =>
      if hEmpty : G.orderedActive w = [] then
          let ha : ¬ G.terminal w ∧ a.1 = noopAction Act := by
            simpa [SerialState.legal, hEmpty] using a.2
          let ga := baseChanceLegalAction (G := G) w
            (G.active_eq_empty_of_orderedActive_eq_nil hEmpty) ha.1
          match s' with
          | .base w' => some (G.privObs i w ga w')
          | _ => none
      else none
  | _, .decide _ _ _ _ _, _, _ => none
  | i, .chance w ga, _, s' =>
      match s' with
      | .base w' => some (G.privObs i w ga w')
      | _ => none

theorem privObs_decide_eq_none
    {i : ι} {w : W} {chosen : JointAction Act} {current : ι} {rest : List ι}
    {hvalid : G.ValidDecision w chosen current rest}
    (a : { a : JointAction Act //
      legal (G := G) (.decide w chosen current rest hvalid) a })
    (s' : SerialState G) :
    SerialState.privObs (G := G) i (.decide w chosen current rest hvalid) a s' = none := by
  simp [SerialState.privObs]

theorem privObs_chance_base_eq
    {i : ι} {w w' : W} (ga : G.LegalAction w)
    (a : { a : JointAction Act // legal (G := G) (.chance w ga) a }) :
    SerialState.privObs (G := G) i (.chance w ga) a (.base w') =
      some (G.privObs i w ga w') := by
  simp [SerialState.privObs]

theorem privObs_decide_successor_eq_none
    {i : ι} {w : W} {chosen : JointAction Act} {current : ι} {rest : List ι}
    {hvalid : G.ValidDecision w chosen current rest}
    (a : { a : JointAction Act //
      legal (G := G) (.decide w chosen current rest hvalid) a }) :
    SerialState.privObs (G := G) i (.decide w chosen current rest hvalid) a
      (SerialState.decidePlayerSuccessor (G := G) w chosen current rest hvalid a) = none := by
  exact privObs_decide_eq_none (G := G) a _

/-- Public observations of the serialized game. Deterministic action-selection
steps emit `none`; stochastic resolution steps emit the original observation
wrapped in `some`. -/
noncomputable def pubObs :
    (s : SerialState G) →
    {a : JointAction Act // legal (G := G) s a} →
    SerialState G → Option PubObs
  | .base w, a, s' =>
      if hEmpty : G.orderedActive w = [] then
          let ha : ¬ G.terminal w ∧ a.1 = noopAction Act := by
            simpa [SerialState.legal, hEmpty] using a.2
          let ga := baseChanceLegalAction (G := G) w
            (G.active_eq_empty_of_orderedActive_eq_nil hEmpty) ha.1
          match s' with
          | .base w' => some (G.pubObs w ga w')
          | _ => none
      else none
  | .decide _ _ _ _ _, _, _ => none
  | .chance w ga, _, s' =>
      match s' with
      | .base w' => some (G.pubObs w ga w')
      | _ => none

theorem pubObs_decide_eq_none
    {w : W} {chosen : JointAction Act} {current : ι} {rest : List ι}
    {hvalid : G.ValidDecision w chosen current rest}
    (a : { a : JointAction Act //
      legal (G := G) (.decide w chosen current rest hvalid) a })
    (s' : SerialState G) :
    SerialState.pubObs (G := G) (.decide w chosen current rest hvalid) a s' = none := by
  simp [SerialState.pubObs]

theorem pubObs_chance_base_eq
    {w w' : W} (ga : G.LegalAction w)
    (a : { a : JointAction Act // legal (G := G) (.chance w ga) a }) :
    SerialState.pubObs (G := G) (.chance w ga) a (.base w') =
      some (G.pubObs w ga w') := by
  simp [SerialState.pubObs]

theorem pubObs_decide_successor_eq_none
    {w : W} {chosen : JointAction Act} {current : ι} {rest : List ι}
    {hvalid : G.ValidDecision w chosen current rest}
    (a : { a : JointAction Act //
      legal (G := G) (.decide w chosen current rest hvalid) a }) :
    SerialState.pubObs (G := G) (.decide w chosen current rest hvalid) a
      (SerialState.decidePlayerSuccessor (G := G) w chosen current rest hvalid a) = none := by
  exact pubObs_decide_eq_none (G := G) a _

theorem pubObs_basePlayerSuccessor_eq_none
    {w : W}
    (a : { a : JointAction Act // legal (G := G) (.base w) a })
    (hNonempty : G.orderedActive w ≠ []) :
    SerialState.pubObs (G := G) (.base w) a
      (SerialState.basePlayerSuccessor (G := G) w a) = none := by
  simp [SerialState.pubObs, hNonempty]

theorem pubObs_base_empty_base_eq_of_active_empty
    {w w' : W}
    (hactive : G.active w = ∅)
    (a : { a : JointAction Act // legal (G := G) (.base w) a }) :
    SerialState.pubObs (G := G) (.base w) a (.base w') =
      some (G.pubObs w
        (baseChanceLegalAction (G := G) w hactive
          (by
            have horder : G.orderedActive w = [] :=
              G.orderedActive_eq_nil_of_active_eq_empty hactive
            have ha : ¬ G.terminal w ∧ a.1 = noopAction Act := by
              simpa [SerialState.legal, horder] using a.2
            exact ha.1))
        w') := by
  have horder : G.orderedActive w = [] :=
    G.orderedActive_eq_nil_of_active_eq_empty hactive
  have hgaEq :
      baseChanceLegalAction (G := G) w
        (G.active_eq_empty_of_orderedActive_eq_nil horder)
        (by
          have ha : ¬ G.terminal w ∧ a.1 = noopAction Act := by
            simpa [SerialState.legal, horder] using a.2
          exact ha.1) =
      baseChanceLegalAction (G := G) w hactive
        (by
          have ha : ¬ G.terminal w ∧ a.1 = noopAction Act := by
            simpa [SerialState.legal, horder] using a.2
          exact ha.1) := by
    apply Subtype.ext
    funext j
    simp [baseChanceLegalAction_val]
  have hpub :
      some (G.pubObs w
        (baseChanceLegalAction (G := G) w
          (G.active_eq_empty_of_orderedActive_eq_nil horder)
          (by
            have ha : ¬ G.terminal w ∧ a.1 = noopAction Act := by
              simpa [SerialState.legal, horder] using a.2
            exact ha.1))
        w') =
      some (G.pubObs w
        (baseChanceLegalAction (G := G) w hactive
          (by
            have ha : ¬ G.terminal w ∧ a.1 = noopAction Act := by
              simpa [SerialState.legal, horder] using a.2
            exact ha.1))
        w') :=
    congrArg (fun ga => some (G.pubObs w ga w')) hgaEq
  simp [SerialState.pubObs, horder, hpub]

/-- Inserted serialized decision steps are pure bookkeeping: they keep the
underlying world state fixed and emit no observations or rewards. -/
theorem bookkeeping_decide_step
    {w : W} {chosen : JointAction Act} {current : ι} {rest : List ι}
    {hvalid : G.ValidDecision w chosen current rest}
    (a : { a : JointAction Act //
      legal (G := G) (.decide w chosen current rest hvalid) a })
    (i : ι) :
    SerialState.world (G := G)
      (SerialState.decidePlayerSuccessor (G := G) w chosen current rest hvalid a) = w ∧
    SerialState.reward (G := G) (.decide w chosen current rest hvalid) a
      (SerialState.decidePlayerSuccessor (G := G) w chosen current rest hvalid a) i = 0 ∧
    SerialState.privObs (G := G) i (.decide w chosen current rest hvalid) a
      (SerialState.decidePlayerSuccessor (G := G) w chosen current rest hvalid a) = none ∧
    SerialState.pubObs (G := G) (.decide w chosen current rest hvalid) a
      (SerialState.decidePlayerSuccessor (G := G) w chosen current rest hvalid a) = none := by
  refine ⟨world_decidePlayerSuccessor (G := G) a, ?_, ?_, ?_⟩
  · exact reward_decide_successor_eq_zero (G := G) a i
  · exact privObs_decide_successor_eq_none (G := G) a
  · exact pubObs_decide_successor_eq_none (G := G) a

/-- A serialized chance-resolution step reproduces the original transition's
reward and observations, wrapped into the serialized observation space. -/
theorem resolution_chance_step
    {i : ι} {w w' : W} (ga : G.LegalAction w)
    (a : { a : JointAction Act // legal (G := G) (.chance w ga) a }) :
    SerialState.world (G := G) (.base w') = w' ∧
    SerialState.reward (G := G) (.chance w ga) a (.base w') i = G.reward w ga w' i ∧
    SerialState.privObs (G := G) i (.chance w ga) a (.base w') =
      some (G.privObs i w ga w') ∧
    SerialState.pubObs (G := G) (.chance w ga) a (.base w') =
      some (G.pubObs w ga w') := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · exact reward_chance_base_eq (G := G) ga a i
  · exact privObs_chance_base_eq (G := G) ga a
  · exact pubObs_chance_base_eq (G := G) ga a

@[simp] theorem map_base_apply
    (p : PMF W) (w : W) :
    PMF.map (SerialState.base (G := G)) p (.base w) = p w := by
  rw [PMF.map_apply]
  rw [tsum_eq_single w]
  · simp
  · intro w' hw'
    by_cases hEq : (.base w : SerialState G) = .base w'
    · cases hEq
      contradiction
    · simp [hEq]

@[simp] theorem map_base_apply_decide
    (p : PMF W) (w : W) (chosen : JointAction Act) (current : ι) (rest : List ι)
    (hvalid : G.ValidDecision w chosen current rest) :
    PMF.map (SerialState.base (G := G)) p (.decide w chosen current rest hvalid) = 0 := by
  rw [PMF.map_apply]
  rw [ENNReal.tsum_eq_zero]
  intro w'
  simp

@[simp] theorem map_base_apply_chance
    (p : PMF W) (w : W) (a : G.LegalAction w) :
    PMF.map (SerialState.base (G := G)) p (.chance w a) = 0 := by
  rw [PMF.map_apply]
  rw [ENNReal.tsum_eq_zero]
  intro w'
  simp

theorem base_empty_support
    {w w' : W}
    (hEmpty : G.orderedActive w = [])
    (a : SerialState.FOSGLegalAction (G := G) (.base w))
    (hsupp : SerialState.transition (G := G) (.base w)
      (SerialState.ofFOSGLegalAction (G := G) a) (.base w') ≠ 0) :
    G.transition w
      (baseChanceLegalAction (G := G) w
        (G.active_eq_empty_of_orderedActive_eq_nil hEmpty)
        (by
          have ha : ¬ G.terminal w ∧ a.1 = noopAction Act := by
            have hold : SerialState.legal (G := G) (.base w) a.1 :=
              (legal_iff_jointActionLegal (G := G) (.base w) a.1).mpr a.2
            simpa [SerialState.legal, hEmpty] using hold
          exact ha.1)) w' ≠ 0 := by
  have hold : SerialState.legal (G := G) (.base w) a.1 :=
    (legal_iff_jointActionLegal (G := G) (.base w) a.1).mpr a.2
  have ha : ¬ G.terminal w ∧ a.1 = noopAction Act := by
    simpa [SerialState.legal, hEmpty] using hold
  simpa [SerialState.transition, hEmpty, ha.2, map_base_apply] using hsupp

theorem chance_support
    {w w' : W} (ga : G.LegalAction w)
    (a : SerialState.FOSGLegalAction (G := G) (.chance w ga))
    (hsupp : SerialState.transition (G := G) (.chance w ga)
      (SerialState.ofFOSGLegalAction (G := G) a) (.base w') ≠ 0) :
    G.transition w ga w' ≠ 0 := by
  simpa [SerialState.transition, map_base_apply] using hsupp

/-- The serialized FOSG. -/
noncomputable def serialize :
    FOSG ι (SerialState G) Act (fun i => Option (PrivObs i)) (Option PubObs) where
  init := .base G.init
  active := SerialState.active (G := G)
  availableActions := SerialState.availableActions (G := G)
  terminal := SerialState.terminal (G := G)
  transition := fun s a => SerialState.transition (G := G) s (SerialState.ofFOSGLegalAction a)
  reward := fun s a => SerialState.reward (G := G) s (SerialState.ofFOSGLegalAction a)
  privObs := fun i s a => SerialState.privObs (G := G) i s (SerialState.ofFOSGLegalAction a)
  pubObs := fun s a => SerialState.pubObs (G := G) s (SerialState.ofFOSGLegalAction a)
  terminal_active_eq_empty := by
    intro s hs
    cases s with
    | base w =>
        simpa [SerialState.terminal] using
          SerialState.active_eq_empty_of_base_terminal (G := G) hs
    | decide =>
        cases hs
    | chance =>
        cases hs
  terminal_no_legal := by
    intro s a hs
    exact fun hleg => hleg.1 hs
  nonterminal_exists_legal := by
    intro s hs
    cases s with
    | base w =>
        cases horder : G.orderedActive w with
        | nil =>
            refine ⟨noopAction Act, ?_⟩
            exact (legal_iff_jointActionLegal (G := G) (.base w) (noopAction Act)).mp <| by
              have hs' : ¬ G.terminal w := by simpa [SerialState.terminal] using hs
              have hlegal : ¬ G.terminal w ∧ noopAction Act = noopAction Act := ⟨hs', rfl⟩
              simpa [SerialState.legal, horder] using hlegal
        | cons current rest =>
            rcases G.nonterminal_exists_legal hs with ⟨a, ha⟩
            let ga : G.LegalAction w := ⟨a, ha⟩
            refine ⟨(baseReplayAction (G := G) ga horder).1, ?_⟩
            exact (legal_iff_jointActionLegal (G := G) (.base w) _).mp
              (baseReplayAction (G := G) ga horder).2
    | decide w chosen current rest hvalid =>
        rcases hvalid.2.2 with ⟨ga, hcomp⟩
        let move :=
          moveOfLegalAction (G := G) ga current
            (G.current_mem_active_of_split hvalid.1)
        refine ⟨move, ?_⟩
        have hold : SerialState.legal (G := G) (.decide w chosen current rest hvalid) move := by
          simpa [move, SerialState.legal] using
            decide_playerLegal_of_legalAction (G := G) ga hvalid hcomp
        exact (legal_iff_jointActionLegal (G := G)
          (.decide w chosen current rest hvalid) _).mp
          hold
    | chance w ga =>
        refine ⟨(chanceResolutionAction (G := G) ga).1, ?_⟩
        exact (legal_iff_jointActionLegal (G := G) (.chance w ga) _).mp
          (chanceResolutionAction (G := G) ga).2

instance instDecidablePredSerializeTerminal [DecidablePred G.terminal] :
    DecidablePred (serialize (G := G)).terminal := by
  intro s
  cases s with
  | base w =>
      simpa [serialize, SerialState.terminal] using (‹DecidablePred G.terminal› w)
  | decide w chosen current rest hvalid =>
      exact isFalse (by simp [serialize, SerialState.terminal])
  | chance w a =>
      exact isFalse (by simp [serialize, SerialState.terminal])

/-- Seriality predicate: every state has either no active players or exactly one
active player and deterministic transitions. -/
def IsSerial
    (G : FOSG ι W Act PrivObs PubObs) : Prop :=
  ∀ w, G.active w = ∅ ∨
    ∃ i, G.active w = {i} ∧ ∀ a : G.LegalAction w, ∃ w', G.transition w a = PMF.pure w'

theorem serialize_isSerial
    (G : FOSG ι W Act PrivObs PubObs) :
    IsSerial (SerialState.serialize (G := G)) := by
  intro s
  cases s with
  | base w =>
      cases horder : G.orderedActive w with
      | nil =>
          left
          simp [serialize, SerialState.active, horder]
      | cons current rest =>
          right
          refine ⟨current, ?_, ?_⟩
          · simp [serialize, SerialState.active, horder]
          · intro a
            refine ⟨SerialState.basePlayerSuccessor (G := G) w
              (SerialState.ofFOSGLegalAction (G := G) a), ?_⟩
            exact (transition_base_nonempty_eq (G := G) (w := w) (by simp [horder])
              (SerialState.ofFOSGLegalAction (G := G) a))
  | decide w chosen current rest hvalid =>
      right
      refine ⟨current, ?_, ?_⟩
      · simp [serialize, SerialState.active]
      · intro a
        refine ⟨SerialState.decidePlayerSuccessor (G := G) w chosen current rest hvalid
          (SerialState.ofFOSGLegalAction (G := G) a), ?_⟩
        simpa [serialize] using
          (transition_decide_eq (G := G)
            (w := w) (chosen := chosen) (current := current) (rest := rest)
            (hvalid := hvalid) (SerialState.ofFOSGLegalAction (G := G) a))
  | chance w ga =>
      left
      simp [serialize, SerialState.active]

end SerialState

end Ordered

end FOSG

end GameTheory

