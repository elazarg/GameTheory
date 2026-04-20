import GameTheory.Languages.FOSG.Basic
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

/-- The all-`none` joint action. -/
def noopAction (Act : ι → Type) : JointAction Act :=
  fun _ => none

omit [DecidableEq ι] in
@[simp] theorem noopAction_apply (i : ι) :
    noopAction Act i = none := rfl

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
  (∀ j, j ∉ G.active w → chosen j = none) ∧
  (∃ a : G.LegalAction w, G.ExtendsPartial chosen a)

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
noncomputable def baseChanceAction
    (w : W) (h : ¬ G.terminal w) : G.LegalAction w :=
  let a := Classical.choose (G.exists_legal_of_not_terminal h)
  ⟨a, Classical.choose_spec (G.exists_legal_of_not_terminal h)⟩

theorem validDecision_from_base
    {w : W} {current next : ι} {tail : List ι}
    (horder : G.orderedActive w = current :: next :: tail)
    {a : JointAction Act}
    (ha : playerLegal (G := G) w (noopAction Act) current a) :
    G.ValidDecision w (recordChoice (noopAction Act) a current) next tail := by
  rcases ha with ⟨_, hnone, ⟨ga, hcomp, hcurrent⟩⟩
  refine ⟨⟨[current], by simpa using horder⟩, ?_, ?_, ?_⟩
  · intro j hj
    have hneq : j ≠ current := by
      intro hji
      subst hji
      exact G.current_not_mem_rest_of_split ⟨[], horder⟩ hj
    simp [recordChoice, hneq]
  · intro j hj
    have hcur : current ∈ G.active w := G.current_mem_active_of_split ⟨[], horder⟩
    have hneq : j ≠ current := by
      intro hji
      subst hji
      exact hj hcur
    simp [recordChoice, hneq]
  · refine ⟨ga, ?_⟩
    exact G.extendsPartial_recordChoice hcomp hcurrent

theorem validDecision_step
    {w : W} {chosen : JointAction Act} {current next : ι} {tail : List ι}
    (hvalid : G.ValidDecision w chosen current (next :: tail))
    {a : JointAction Act}
    (ha : playerLegal (G := G) w chosen current a) :
    G.ValidDecision w (recordChoice chosen a current) next tail := by
  rcases hvalid with ⟨hsplit, hnoneRem, hnoneInactive, _⟩
  rcases hsplit with ⟨acted, hsplit⟩
  rcases ha with ⟨_, hnone, ⟨ga, hcomp, hcurrent⟩⟩
  refine ⟨⟨acted ++ [current], by simpa [List.append_assoc] using hsplit⟩, ?_, ?_, ?_⟩
  · intro j hj
    have hneq : j ≠ current := by
      intro hji
      subst hji
      exact G.current_not_mem_rest_of_split ⟨acted, hsplit⟩ (by simpa using hj)
    have hchosen : chosen j = none := hnoneRem j (by simp [hj])
    simp [recordChoice, hneq, hchosen]
  · intro j hj
    have hcur : current ∈ G.active w := G.current_mem_active_of_split ⟨acted, hsplit⟩
    have hneq : j ≠ current := by
      intro hji
      subst hji
      exact hj hcur
    simpa [recordChoice, hneq] using hnoneInactive j hj
  · refine ⟨ga, ?_⟩
    exact G.extendsPartial_recordChoice hcomp hcurrent

/-- The deterministic successor after a serialized player move from a base
state with nonempty active set. -/
noncomputable def basePlayerSuccessor
    (w : W) (a : { a : JointAction Act // legal (G := G) (.base w) a }) :
    SerialState G :=
  match horder : G.orderedActive w with
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

/-- Transition kernel of the serialized game. -/
noncomputable def transition :
    (s : SerialState G) → {a : JointAction Act // legal (G := G) s a} → PMF (SerialState G)
  | .base w, a =>
      if hEmpty : G.orderedActive w = [] then
          let ha : ¬ G.terminal w ∧ a.1 = noopAction Act := by
            simpa [SerialState.legal, hEmpty] using a.2
          let ga := baseChanceAction (G := G) w ha.1
          PMF.map (SerialState.base (G := G)) (G.transition w ga)
      else
        PMF.pure (basePlayerSuccessor (G := G) w a)
  | .decide w chosen current rest hvalid, a =>
      PMF.pure (decidePlayerSuccessor (G := G) w chosen current rest hvalid a)
  | .chance w ga, _ =>
      PMF.map (SerialState.base (G := G)) (G.transition w ga)

/-- Reward function of the serialized game. Deterministic action-selection steps
have zero reward; stochastic resolution steps inherit the original reward. -/
noncomputable def reward :
    (s : SerialState G) →
    {a : JointAction Act // legal (G := G) s a} →
    SerialState G → ι → ℝ
  | .base w, a, s', i =>
      match horder : G.orderedActive w with
      | [] =>
          let ha : ¬ G.terminal w ∧ a.1 = noopAction Act := by
            simpa [SerialState.legal, horder] using a.2
          let ga := baseChanceAction (G := G) w ha.1
          match s' with
          | .base w' => G.reward w ga w' i
          | _ => 0
      | _ :: _ => 0
  | .decide _ _ _ _ _, _, _, _ => 0
  | .chance w ga, _, s', i =>
      match s' with
      | .base w' => G.reward w ga w' i
      | _ => 0

/-- Private observations of the serialized game. Deterministic action-selection
steps emit `none`; stochastic resolution steps emit the original observation
wrapped in `some`. -/
noncomputable def privObs :
    (i : ι) →
    (s : SerialState G) →
    {a : JointAction Act // legal (G := G) s a} →
    SerialState G → Option (PrivObs i)
  | i, .base w, a, s' =>
      match horder : G.orderedActive w with
      | [] =>
          let ha : ¬ G.terminal w ∧ a.1 = noopAction Act := by
            simpa [SerialState.legal, horder] using a.2
          let ga := baseChanceAction (G := G) w ha.1
          match s' with
          | .base w' => some (G.privObs i w ga w')
          | _ => none
      | _ :: _ => none
  | _, .decide _ _ _ _ _, _, _ => none
  | i, .chance w ga, _, s' =>
      match s' with
      | .base w' => some (G.privObs i w ga w')
      | _ => none

/-- Public observations of the serialized game. Deterministic action-selection
steps emit `none`; stochastic resolution steps emit the original observation
wrapped in `some`. -/
noncomputable def pubObs :
    (s : SerialState G) →
    {a : JointAction Act // legal (G := G) s a} →
    SerialState G → Option PubObs
  | .base w, a, s' =>
      match horder : G.orderedActive w with
      | [] =>
          let ha : ¬ G.terminal w ∧ a.1 = noopAction Act := by
            simpa [SerialState.legal, horder] using a.2
          let ga := baseChanceAction (G := G) w ha.1
          match s' with
          | .base w' => some (G.pubObs w ga w')
          | _ => none
      | _ :: _ => none
  | .decide _ _ _ _ _, _, _ => none
  | .chance w ga, _, s' =>
      match s' with
      | .base w' => some (G.pubObs w ga w')
      | _ => none

/-- The serialized FOSG. -/
noncomputable def serialize :
    FOSG ι (SerialState G) Act (fun i => Option (PrivObs i)) (Option PubObs) where
  init := .base G.init
  active := SerialState.active (G := G)
  init_active_eq_empty := by
    simp [SerialState.active, G.active_init, G.orderedActive_eq_nil_of_active_eq_empty]
  terminal := SerialState.terminal (G := G)
  legal := SerialState.legal (G := G)
  transition := SerialState.transition (G := G)
  reward := SerialState.reward (G := G)
  privObs := SerialState.privObs (G := G)
  pubObs := SerialState.pubObs (G := G)
  legal_inactive_none := by
    intro s a i hlegal hi
    cases s with
    | base w =>
        cases horder : G.orderedActive w with
        | nil =>
            have ha : ¬ G.terminal w ∧ a = noopAction Act := by
              simpa [SerialState.legal, horder] using hlegal
            simp [ha.2]
        | cons current rest =>
            have ha : SerialState.playerLegal (G := G) w (noopAction Act) current a := by
              simpa [SerialState.legal, horder] using hlegal
            have hneq : i ≠ current := by
              intro hEq
              subst hEq
              exact hi (by simp [SerialState.active, horder])
            exact SerialState.playerLegal_other_none (G := G) ha hneq
    | decide w chosen current rest hvalid =>
        have ha : SerialState.playerLegal (G := G) w chosen current a := by
          simpa [SerialState.legal] using hlegal
        have hneq : i ≠ current := by
          intro hEq
          subst hEq
          exact hi (by simp [SerialState.active])
        exact SerialState.playerLegal_other_none (G := G) ha hneq
    | chance w ga =>
        have ha : a = noopAction Act := by
          simpa [SerialState.legal] using hlegal
        simp [ha]
  legal_active_some := by
    intro s a i hlegal hi
    cases s with
    | base w =>
        cases horder : G.orderedActive w with
        | nil =>
            simp [SerialState.active, horder] at hi
        | cons current rest =>
            have ha : SerialState.playerLegal (G := G) w (noopAction Act) current a := by
              simpa [SerialState.legal, horder] using hlegal
            have : i = current := by
              simpa [SerialState.active, horder] using hi
            subst this
            exact SerialState.playerLegal_current_some (G := G) ha
    | decide w chosen current rest hvalid =>
        have ha : SerialState.playerLegal (G := G) w chosen current a := by
          simpa [SerialState.legal] using hlegal
        have : i = current := by
          simpa [SerialState.active] using hi
        subst this
        exact SerialState.playerLegal_current_some (G := G) ha
    | chance w ga =>
        simp [SerialState.active] at hi
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
    cases s with
    | base w =>
        cases horder : G.orderedActive w with
        | nil =>
            intro hleg
            have htmp : ¬ G.terminal w ∧ a = noopAction Act := by
              simpa [SerialState.legal, horder] using hleg
            have : ¬ G.terminal w := htmp.1
            exact this hs
        | cons current rest =>
            intro hleg
            have hcur : current ∈ G.active w := by
              exact (G.mem_orderedActive_iff w current).1 (by simp [horder])
            have hempty : G.active w = ∅ := G.active_eq_empty_of_terminal hs
            simp [hempty] at hcur
    | decide =>
        cases hs
    | chance =>
        cases hs
  nonterminal_exists_legal := by
    intro s hs
    cases s with
    | base w =>
        cases horder : G.orderedActive w with
        | nil =>
            have hnot : ¬ G.terminal w := by
              simpa [SerialState.terminal] using hs
            refine ⟨noopAction Act, ?_⟩
            simpa [SerialState.legal, horder] using
              (show ¬ G.terminal w ∧ noopAction Act = noopAction Act from ⟨hnot, rfl⟩)
        | cons current rest =>
            have hcur : current ∈ G.active w := by
              exact (G.mem_orderedActive_iff w current).1 (by simp [horder])
            obtain ⟨ga, hga⟩ := G.exists_legal_of_not_terminal (w := w) (by
              intro hterm
              exact hs (by simpa [SerialState.terminal] using hterm))
            obtain ⟨ai, hai⟩ := G.legal_active_some (w := w) (a := ga) (i := current) hga hcur
            have hlegal : SerialState.playerLegal (G := G) w (noopAction Act) current
                (singleMove (Act := Act) current ai) := by
              refine ⟨⟨ai, by simp⟩, ?_, ?_⟩
              · intro j hj
                exact singleMove_other (Act := Act) (ai := ai) hj
              · refine ⟨⟨ga, hga⟩, G.extendsPartial_noop ⟨ga, hga⟩, ?_⟩
                simp [hai]
            exact ⟨singleMove (Act := Act) current ai, by
              simpa [SerialState.legal, horder] using hlegal⟩
    | decide w chosen current rest hvalid =>
        rcases hvalid with ⟨hsplit, _, _, ⟨ga, hcomp⟩⟩
        have hcur : current ∈ G.active w := G.current_mem_active_of_split hsplit
        obtain ⟨ai, hai⟩ := G.active_has_some (a := ga) hcur
        have hlegal : SerialState.playerLegal (G := G) w chosen current
            (singleMove (Act := Act) current ai) := by
          refine ⟨⟨ai, by simp⟩, ?_, ?_⟩
          · intro j hj
            exact singleMove_other (Act := Act) (ai := ai) hj
          · refine ⟨ga, hcomp, ?_⟩
            simp [hai]
        exact ⟨singleMove (Act := Act) current ai, by
          simpa [SerialState.legal] using hlegal⟩
    | chance w ga =>
        exact ⟨noopAction Act, by simp [SerialState.legal]⟩

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
          simp [SerialState.serialize, SerialState.active, horder]
      | cons current rest =>
          right
          refine ⟨current, by simp [SerialState.serialize, SerialState.active, horder], ?_⟩
          intro a
          refine ⟨SerialState.basePlayerSuccessor (G := G) w a, ?_⟩
          have hne : G.orderedActive w ≠ [] := by
            simp [horder]
          change SerialState.transition (G := G) (.base w) a =
            PMF.pure (SerialState.basePlayerSuccessor (G := G) w a)
          simp [SerialState.transition, hne]
  | decide w chosen current rest hvalid =>
      right
      refine ⟨current, by simp [SerialState.serialize, SerialState.active], ?_⟩
      intro a
      refine ⟨SerialState.decidePlayerSuccessor (G := G) w chosen current rest hvalid a, ?_⟩
      simp [SerialState.serialize, SerialState.transition]
  | chance w ga =>
      left
      simp [SerialState.serialize, SerialState.active]

end SerialState

end Ordered

end FOSG

end GameTheory
