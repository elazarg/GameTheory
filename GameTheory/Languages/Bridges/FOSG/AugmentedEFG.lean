import GameTheory.Languages.FOSG.Serial
import GameTheory.Languages.FOSG.History
import GameTheory.Languages.FOSG.Compile
import GameTheory.Languages.EFG.Augmented
import GameTheory.Languages.EFG.Refinements
import Mathlib.Data.Fintype.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# GameTheory.Languages.Bridges.FOSG.AugmentedEFG

Bridge support layer for the finite-horizon FOSG -> augmented-EFG pipeline.

This file provides the structural finite-horizon FOSG -> EFG bridge:

- PMF support enumeration
- finite bounded sequence codes
- finite coding of serialized FOSG states
- horizon-bounded positions
- the finite `InfoStructure` induced by serialized decision positions
- plain EFG unrolling over serialized positions
- a list-recursive replay layer for EFG histories
- a thin augmented-EFG wrapper whose forgetful base is definitionally the
  plain unrolling

Important status:
- `toPlainEFGAtHorizon` is a raw cutoff tree and may truncate nonterminal
  serialized states when `remaining = 0`
- `toAugmentedAtHorizon` is only a stage-4 scaffold: its public and player
  information states are currently just reachable EFG histories
- payoff transport and the actual serialized-view augmentation are deferred to
  the next layer
-/

namespace GameTheory

namespace FOSG

namespace AugmentedEFGBridge

open Math.Probability
open _root_.EFG

variable {ι W : Type} [DecidableEq ι] [LinearOrder ι]
variable {Act : ι → Type} {PrivObs : ι → Type} {PubObs : Type}

section Support

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Finite support of a PMF as a `Finset`. -/
noncomputable def supportFinset (p : PMF α) : Finset α :=
  Finset.univ.filter fun a => p a ≠ 0

omit [DecidableEq α] in
theorem mem_supportFinset_iff (p : PMF α) (a : α) :
    a ∈ supportFinset p ↔ p a ≠ 0 := by
  simp [supportFinset]

/-- Enumeration of PMF support by `Fin`. -/
noncomputable def supportEnum (p : PMF α) :
    Fin (supportFinset p).card → α :=
  fun i => (supportFinset p).toList.get ⟨i.1, by simpa using i.2⟩

omit [DecidableEq α] in
theorem supportEnum_mem (p : PMF α) (i : Fin (supportFinset p).card) :
    supportEnum p i ∈ supportFinset p := by
  unfold supportEnum
  exact Finset.mem_toList.mp (List.get_mem _ _)

theorem supportEnum_spec (p : PMF α) (i : Fin (supportFinset p).card) :
    p (supportEnum p i) ≠ 0 :=
  (mem_supportFinset_iff p _).1 (supportEnum_mem p i)

/-- The support of a PMF, packaged as a finite subtype. -/
def SupportSubtype (p : PMF α) : Type := {a : α // a ∈ supportFinset p}

noncomputable instance instFintypeSupportSubtype (p : PMF α) :
    Fintype (SupportSubtype p) := by
  classical
  unfold SupportSubtype
  infer_instance

noncomputable def supportSubtypePMF (p : PMF α) : PMF (SupportSubtype p) := by
  classical
  refine PMF.ofFintype (fun a => p a.1) ?_
  have hattach : (∑ a : SupportSubtype p, p a.1) = Finset.sum (supportFinset p) (fun a => p a) := by
    simpa [SupportSubtype] using (supportFinset p).sum_attach (f := fun a : α => p a)
  have hfilter :
      Finset.sum (Finset.univ.filter (fun a => p a ≠ 0)) (fun a => p a) = ∑ a : α, p a := by
    simpa using (Finset.sum_filter_ne_zero (s := Finset.univ) (f := fun a : α => p a))
  have huniv : ∑ a : α, p a = 1 := by
    simpa using p.tsum_coe
  exact hattach.trans <| by
    simpa [supportFinset] using hfilter.trans huniv

theorem supportSubtypePMF_apply (p : PMF α) (a : SupportSubtype p) :
    supportSubtypePMF p a = p a.1 := by
  simp [supportSubtypePMF]

/-- The support of a PMF reindexed to `Fin`. -/
noncomputable def supportPMF (p : PMF α) : PMF (Fin (Fintype.card (SupportSubtype p))) :=
  (supportSubtypePMF p).map (Fintype.equivFin (SupportSubtype p))

/-- The value of the `i`-th support branch. -/
noncomputable def supportValue (p : PMF α) (i : Fin (Fintype.card (SupportSubtype p))) : α :=
  ((Fintype.equivFin (SupportSubtype p)).symm i).1

theorem supportValue_mem (p : PMF α) (i : Fin (Fintype.card (SupportSubtype p))) :
    supportValue p i ∈ supportFinset p :=
  ((Fintype.equivFin (SupportSubtype p)).symm i).2

theorem supportValue_spec (p : PMF α) (i : Fin (Fintype.card (SupportSubtype p))) :
    p (supportValue p i) ≠ 0 :=
  (mem_supportFinset_iff p _).1 (supportValue_mem p i)

theorem supportSubtype_card_pos (p : PMF α) : 0 < Fintype.card (SupportSubtype p) := by
  classical
  rcases p.support_nonempty with ⟨a, ha⟩
  exact Fintype.card_pos_iff.mpr ⟨⟨a, (mem_supportFinset_iff p a).2 ha⟩⟩

theorem supportFinset_card_pos (p : PMF α) : 0 < (supportFinset p).card := by
  classical
  rcases p.support_nonempty with ⟨a, ha⟩
  have hmem : a ∈ supportFinset p := (mem_supportFinset_iff p a).2 ha
  exact Finset.card_pos.mpr ⟨a, hmem⟩

end Support

section BoundedSeq

variable {α : Type}

/-- Finite bounded sequence carrier: a length `n ≤ k` together with a function
on `Fin n`. This is the finite code used for bounded lists in the bridge. -/
abbrev BoundedSeq (α : Type) (k : Nat) :=
  Σ n : Fin (k + 1), Fin n.1 → α

noncomputable instance instFintypeBoundedSeq
    [Fintype α] (k : Nat) : Fintype (BoundedSeq α k) := by
  classical
  infer_instance

instance instDecidableEqBoundedSeq
    [DecidableEq α] (k : Nat) : DecidableEq (BoundedSeq α k) := by
  classical
  infer_instance

def BoundedSeq.toList {k : Nat} (s : BoundedSeq α k) : List α :=
  List.ofFn s.2

theorem BoundedSeq.length_toList {k : Nat} (s : BoundedSeq α k) :
    s.toList.length = s.1.1 := by
  simp [BoundedSeq.toList]

noncomputable def BoundedSeq.ofList {k : Nat} (xs : List α) (h : xs.length ≤ k) :
    BoundedSeq α k := by
  refine ⟨⟨xs.length, Nat.lt_succ_of_le h⟩, ?_⟩
  intro i
  exact xs.get ⟨i.1, by simpa using i.2⟩

theorem BoundedSeq.toList_ofList
    {k : Nat} [DecidableEq α] (xs : List α) (h : xs.length ≤ k) :
    (BoundedSeq.ofList xs h).toList = xs := by
  ext i
  simp [BoundedSeq.toList, BoundedSeq.ofList]

end BoundedSeq

section Labels

variable (G : FOSG ι W Act PrivObs PubObs)
variable [Fintype ι] [Fintype W] [DecidableEq W]
variable [∀ i, Fintype (Option (Act i))]
variable [DecidablePred G.terminal]

noncomputable abbrev SG := SerialState.serialize (G := G)
abbrev SState := SerialState G

noncomputable instance instFintypeJointAction : Fintype (JointAction Act) := by
  classical
  infer_instance

noncomputable instance instDecidableEqJointAction : DecidableEq (JointAction Act) := by
  classical
  infer_instance

noncomputable instance instFintypeSerialLegalAction (s : SState G) :
    Fintype ((SG G).LegalAction s) := by
  classical
  let _ : DecidablePred (fun a : JointAction Act => (SG G).legal s a) := Classical.decPred _
  unfold FOSG.LegalAction
  infer_instance

noncomputable instance instDecidableEqSerialLegalAction (s : SState G) :
    DecidableEq ((SG G).LegalAction s) := by
  classical
  infer_instance

abbrev RestCode := BoundedSeq ι (Fintype.card ι)

theorem rest_length_le_card
    {w : W} {chosen : JointAction Act} {current : ι} {rest : List ι}
    (hvalid : G.ValidDecision w chosen current rest) :
    rest.length ≤ Fintype.card ι := by
  rcases hvalid.1 with ⟨acted, hsplit⟩
  have hnodup : (G.orderedActive w).Nodup := by
    simpa [FOSG.orderedActive] using
      Finset.sort_nodup (s := G.active w) (r := (· ≤ ·))
  have hnodup' : (acted ++ current :: rest).Nodup := by
    simpa [hsplit] using hnodup
  have hsuffix : (current :: rest).Nodup := List.Nodup.of_append_right hnodup'
  exact (List.nodup_cons.mp hsuffix).2.length_le_card

/-- Finite stamp for serialized states. This is only used as an injective code,
not as a decodable semantic object. Decision states store their remaining
active-player suffix through a bounded sequence code. -/
noncomputable def stateStampOfState :
    SState G →
      W ⊕
        ((W × JointAction Act × ι × BoundedSeq ι (Fintype.card ι)) ⊕
          (W × JointAction Act))
  | .base w =>
      (Sum.inl w :
        W ⊕
          ((W × JointAction Act × ι × BoundedSeq ι (Fintype.card ι)) ⊕
            (W × JointAction Act)))
  | .decide w chosen current rest hvalid =>
      (Sum.inr <| Sum.inl (w, chosen, current,
        BoundedSeq.ofList rest (rest_length_le_card (G := G) hvalid)) :
        W ⊕
          ((W × JointAction Act × ι × BoundedSeq ι (Fintype.card ι)) ⊕
            (W × JointAction Act)))
  | .chance w a =>
      (Sum.inr <| Sum.inr (w, a.1) :
        W ⊕
          ((W × JointAction Act × ι × BoundedSeq ι (Fintype.card ι)) ⊕
            (W × JointAction Act)))

theorem stateStampOfState_injective :
    Function.Injective (stateStampOfState (G := G)) := by
  intro s t h
  cases s <;> cases t
  case base.base w w' =>
    have hw : w = w' := by
      simpa [stateStampOfState] using h
    subst hw
    rfl
  case base.decide =>
    cases (by simpa [stateStampOfState] using h : False)
  case base.chance =>
    cases (by simpa [stateStampOfState] using h : False)
  case decide.base =>
    cases (by simpa [stateStampOfState] using h : False)
  case decide.decide w chosen current rest hs w' chosen' current' rest' hs' =>
    have h' :
        (w, chosen, current, BoundedSeq.ofList rest (rest_length_le_card (G := G) hs)) =
          (w', chosen', current', BoundedSeq.ofList rest' (rest_length_le_card (G := G) hs')) := by
      simpa [stateStampOfState] using h
    have hw : w = w' := by
      simpa using congrArg (fun x => x.1) h'
    have hchosen : chosen = chosen' := by
      simpa using congrArg (fun x => x.2.1) h'
    have hcurrent : current = current' := by
      simpa using congrArg (fun x => x.2.2.1) h'
    have hrest : BoundedSeq.ofList rest (rest_length_le_card (G := G) hs) =
        BoundedSeq.ofList rest' (rest_length_le_card (G := G) hs') := by
      simpa using congrArg (fun x => x.2.2.2) h'
    subst hw hchosen hcurrent
    have hlist : rest = rest' := by
      have hlist' := congrArg (BoundedSeq.toList (α := ι) (k := Fintype.card ι)) hrest
      simpa [BoundedSeq.toList_ofList] using hlist'
    subst hlist
    have hproof : hs = hs' := Subsingleton.elim _ _
    subst hproof
    rfl
  case decide.chance =>
    cases (by simpa [stateStampOfState] using h : False)
  case chance.base =>
    cases (by simpa [stateStampOfState] using h : False)
  case chance.decide =>
    cases (by simpa [stateStampOfState] using h : False)
  case chance.chance w a w' a' =>
    have h' : (w, a.1) = (w', a'.1) := by
      simpa [stateStampOfState] using h
    have hw : w = w' := by
      simpa using congrArg Prod.fst h'
    have ha : a.1 = a'.1 := by
      simpa using congrArg Prod.snd h'
    subst hw
    apply congrArg (fun x => SerialState.chance w x)
    exact Subtype.ext ha

instance instFiniteSerialState : Finite (SState G) :=
  Finite.of_injective (stateStampOfState (G := G)) (stateStampOfState_injective (G := G))

noncomputable instance instFintypeSerialState : Fintype (SState G) :=
  Fintype.ofFinite (SState G)

noncomputable instance instDecidableEqSerialState : DecidableEq (SState G) := by
  classical
  infer_instance

noncomputable instance instFintypeSerialStep : Fintype ((SG G).Step) := by
  classical
  infer_instance

noncomputable instance instDecidableEqSerialStep : DecidableEq ((SG G).Step) := by
  classical
  infer_instance

/-- Horizon-bounded serialized positions. -/
structure Position (k : Nat) where
  state : SState G
  remaining : Nat
  hremaining : remaining ≤ k

namespace Position

def root (k : Nat) : Position G k :=
  ⟨.base G.init, k, le_rfl⟩

noncomputable def code {k : Nat} (pos : Position G k) :
    (W ⊕
      ((W × JointAction Act × ι × BoundedSeq ι (Fintype.card ι)) ⊕
        (W × JointAction Act))) × Fin (k + 1) :=
  (stateStampOfState (G := G) pos.state, ⟨pos.remaining, Nat.lt_succ_of_le pos.hremaining⟩)

theorem code_injective {k : Nat} :
    Function.Injective (code (G := G) (k := k)) := by
  intro p q h
  have hState :
      stateStampOfState (G := G) p.state = stateStampOfState (G := G) q.state := by
    exact Prod.mk.inj h |>.1
  have hRem :
      (⟨p.remaining, Nat.lt_succ_of_le p.hremaining⟩ : Fin (k + 1)) =
        ⟨q.remaining, Nat.lt_succ_of_le q.hremaining⟩ := by
    exact Prod.mk.inj h |>.2
  have hs : p.state = q.state := stateStampOfState_injective (G := G) hState
  have hr : p.remaining = q.remaining := Fin.mk.inj hRem
  cases p
  cases q
  cases hs
  cases hr
  rfl

instance instFinitePosition {k : Nat} : Finite (Position G k) :=
  Finite.of_injective (code (G := G) (k := k)) (code_injective (G := G) (k := k))

noncomputable instance instFintypePosition {k : Nat} :
    Fintype (Position G k) :=
  Fintype.ofFinite (Position G k)

noncomputable instance instDecidableEqPosition {k : Nat} :
    DecidableEq (Position G k) := by
  classical
  infer_instance

def isTruncated {k : Nat} (pos : Position G k) : Prop :=
  pos.remaining = 0

instance instDecidableIsTruncated {k : Nat} (pos : Position G k) :
    Decidable pos.isTruncated := inferInstanceAs (Decidable (pos.remaining = 0))

def player? {k : Nat} (pos : Position G k) : Option ι :=
  if pos.isTruncated then
    none
  else
    match pos.state with
    | .base w =>
        match G.orderedActive w with
        | [] => none
        | i :: _ => some i
    | .decide _ _ current _ _ => some current
    | .chance _ _ => none

theorem not_terminal_of_player
    {k : Nat} {pos : Position G k} {i : ι}
    (hplayer : pos.player? = some i) :
    ¬ (SG G).terminal pos.state := by
  have hnotTrunc : ¬ pos.isTruncated := by
    intro htrunc
    simp [Position.player?, htrunc] at hplayer
  cases hstate : pos.state with
  | base w =>
      cases horder : G.orderedActive w with
      | nil =>
          simp [Position.player?, hnotTrunc, hstate, horder] at hplayer
      | cons current rest =>
          intro hterm
          have hactive : SerialState.active (G := G) (.base w) = ∅ :=
            (SG G).terminal_active_eq_empty hterm
          have : ({current} : Finset ι) = ∅ := by
            simpa [SerialState.active, horder] using hactive
          simp at this
  | decide w chosen current rest hvalid =>
      simp [SG, SerialState.serialize, SerialState.terminal]
  | chance w a =>
      simp [SG, SerialState.serialize, SerialState.terminal]

noncomputable def actionArity {k : Nat} (pos : Position G k) : Nat :=
  Fintype.card ((SG G).LegalAction pos.state)

theorem actionArity_pos
    {k : Nat} {pos : Position G k} {i : ι}
    (hplayer : pos.player? = some i) :
    0 < actionArity (G := G) pos := by
  classical
  have hterm : ¬ (SG G).terminal pos.state := not_terminal_of_player (G := G) hplayer
  obtain ⟨a, ha⟩ := (SG G).nonterminal_exists_legal hterm
  show 0 < Fintype.card ((SG G).LegalAction pos.state)
  exact Fintype.card_pos_iff.mpr ⟨⟨a, ha⟩⟩

noncomputable def actionFromIndex
    {k : Nat} {pos : Position G k}
    (a : Fin (actionArity (G := G) pos)) :
    (SG G).LegalAction pos.state :=
  (Fintype.equivFin ((SG G).LegalAction pos.state)).symm a

noncomputable def rawActionFromIndex
    {k : Nat} {pos : Position G k}
    (a : Fin (actionArity (G := G) pos)) :
    { x : JointAction Act // SerialState.legal (G := G) pos.state x } :=
  SerialState.ofFOSGLegalAction (G := G) (s := pos.state) (actionFromIndex (G := G) a)

end Position

/-- History-bearing serialized positions for the next bridge refactor.

This is intentionally separate from the live `Position` used by the current
tree unrolling. It packages a bounded serialized step trail together with the
current serialized state and remaining horizon budget, so the later bridge pass
can recover serialized public/player views directly from the node state. -/
structure TracePosition (k : Nat) where
  state : SState G
  trail : { xs : List ((SG G).Step) // xs.length ≤ k }
  remaining : Nat
  hremaining : remaining ≤ k
  hlen : trail.1.length + remaining = k
  hchain : (SG G).StepChainFrom (.base G.init) trail.1
  hstate : (SG G).lastStateFrom (.base G.init) trail.1 = state

namespace TracePosition

noncomputable def trailCode {k : Nat} :
    { xs : List ((SG G).Step) // xs.length ≤ k } → BoundedSeq ((SG G).Step) k
  | ⟨xs, hxs⟩ => BoundedSeq.ofList xs hxs

theorem trailCode_injective {k : Nat} :
    Function.Injective (trailCode (G := G) (k := k)) := by
  intro xs ys h
  rcases xs with ⟨xs, hxs⟩
  rcases ys with ⟨ys, hys⟩
  change BoundedSeq.ofList xs hxs = BoundedSeq.ofList ys hys at h
  have hlist := congrArg BoundedSeq.toList h
  simpa [BoundedSeq.toList_ofList] using hlist

noncomputable def code {k : Nat} (pos : TracePosition G k) :
    SState G × BoundedSeq ((SG G).Step) k × Fin (k + 1) :=
  (pos.state, trailCode (G := G) (k := k) pos.trail,
    ⟨pos.remaining, Nat.lt_succ_of_le pos.hremaining⟩)

theorem code_injective {k : Nat} :
    Function.Injective (code (G := G) (k := k)) := by
  intro p q h
  have hState : p.state = q.state := by
    exact congrArg Prod.fst h
  have hTrail :
      trailCode (G := G) (k := k) p.trail = trailCode (G := G) (k := k) q.trail := by
    exact congrArg (fun x => x.2.1) h
  have hRem :
      (⟨p.remaining, Nat.lt_succ_of_le p.hremaining⟩ : Fin (k + 1)) =
        ⟨q.remaining, Nat.lt_succ_of_le q.hremaining⟩ := by
    exact congrArg (fun x => x.2.2) h
  have hTrail' : p.trail = q.trail :=
    trailCode_injective (G := G) (k := k) hTrail
  have hRem' : p.remaining = q.remaining := Fin.mk.inj hRem
  cases p
  cases q
  cases hState
  cases hTrail'
  cases hRem'
  simp at *

instance instFinite {k : Nat} : Finite (TracePosition G k) :=
  Finite.of_injective (code (G := G) (k := k)) (code_injective (G := G) (k := k))

noncomputable instance instFintype {k : Nat} : Fintype (TracePosition G k) :=
  Fintype.ofFinite (TracePosition G k)

noncomputable instance instDecidableEq {k : Nat} : DecidableEq (TracePosition G k) := by
  classical
  infer_instance

noncomputable def root (k : Nat) : TracePosition G k := by
  let trail : { xs : List ((SG G).Step) // xs.length ≤ k } := ⟨[], Nat.zero_le _⟩
  refine ⟨.base G.init, trail, k, le_rfl, ?_, trivial, ?_⟩
  · simp [trail]
  · simp [trail, FOSG.lastStateFrom]

@[simp] theorem trail_length {k : Nat} (pos : TracePosition G k) :
    pos.trail.1.length + pos.remaining = k := pos.hlen

noncomputable def history {k : Nat} (pos : TracePosition G k) : (SG G).History :=
  ⟨pos.trail.1, pos.hchain⟩

@[simp] theorem history_steps {k : Nat} (pos : TracePosition G k) :
    (history (G := G) pos).steps = pos.trail.1 := rfl

@[simp] theorem history_lastState {k : Nat} (pos : TracePosition G k) :
    (history (G := G) pos).lastState = pos.state := pos.hstate

noncomputable def publicView {k : Nat} (pos : TracePosition G k) : (SG G).PublicState :=
  (history (G := G) pos).publicView

noncomputable def playerView {k : Nat} (pos : TracePosition G k) (i : ι) :
    (SG G).InfoState i :=
  (history (G := G) pos).playerView i

theorem snoc_length_le {k : Nat} {pos : TracePosition G k} (e : (SG G).Step)
    (hrem : pos.remaining ≠ 0) :
    (pos.trail.1 ++ [e]).length ≤ k := by
  have h1 : 1 ≤ pos.remaining := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hrem)
  simpa [List.length_append] using
    (calc
      pos.trail.1.length + 1 ≤ pos.trail.1.length + pos.remaining := by
        exact Nat.add_le_add_left h1 _
      _ = k := pos.hlen)

noncomputable def appendStep {k : Nat} (pos : TracePosition G k) (e : (SG G).Step)
    (hrem : pos.remaining ≠ 0) (hsrc : e.src = pos.state) : TracePosition G k := by
  let hlen' : (pos.trail.1 ++ [e]).length ≤ k :=
    snoc_length_le (G := G) e hrem
  let trail' : { xs : List ((SG G).Step) // xs.length ≤ k } :=
    ⟨pos.trail.1 ++ [e], hlen'⟩
  refine ⟨e.dst, trail', pos.remaining - 1, le_trans (Nat.sub_le _ _) pos.hremaining, ?_, ?_, ?_⟩
  · have hpos : 0 < pos.remaining := Nat.pos_of_ne_zero hrem
    calc
      trail'.1.length + (pos.remaining - 1)
          = (pos.trail.1 ++ [e]).length + (pos.remaining - 1) := by rfl
      _ = pos.trail.1.length + 1 + (pos.remaining - 1) := by simp [List.length_append, Nat.add_assoc]
      _ = pos.trail.1.length + pos.remaining := by omega
      _ = k := pos.hlen
  · simpa [trail'] using
      FOSG.StepChainFrom.snoc (G := SG G) pos.hchain e (by simpa [pos.hstate] using hsrc)
  · simpa [trail'] using
      (SG G).lastStateFrom_append_singleton (.base G.init) pos.trail.1 e

@[simp] theorem appendStep_remaining {k : Nat} (pos : TracePosition G k) (e : (SG G).Step)
    (hrem : pos.remaining ≠ 0) (hsrc : e.src = pos.state) :
    (appendStep (G := G) pos e hrem hsrc).remaining = pos.remaining - 1 := rfl

@[simp] theorem appendStep_history_steps {k : Nat} (pos : TracePosition G k) (e : (SG G).Step)
    (hrem : pos.remaining ≠ 0) (hsrc : e.src = pos.state) :
    (appendStep (G := G) pos e hrem hsrc).history.steps = pos.history.steps ++ [e] := by
  simp [history, appendStep]

@[simp] theorem appendStep_history_lastState {k : Nat} (pos : TracePosition G k) (e : (SG G).Step)
    (hrem : pos.remaining ≠ 0) (hsrc : e.src = pos.state) :
    (appendStep (G := G) pos e hrem hsrc).history.lastState = e.dst := by
  simp [appendStep]

def toPosition {k : Nat} (pos : TracePosition G k) : Position G k :=
  ⟨pos.state, pos.remaining, pos.hremaining⟩

def player? {k : Nat} (pos : TracePosition G k) : Option ι :=
  Position.player? (G := G) pos.toPosition

theorem not_terminal_of_player
    {k : Nat} {pos : TracePosition G k} {i : ι}
    (hplayer : pos.player? = some i) :
    ¬ (SG G).terminal pos.state :=
  Position.not_terminal_of_player (G := G) hplayer

private theorem finiteAct (i : ι) : Finite (Act i) :=
  Finite.of_injective (fun ai => (some ai : Option (Act i))) (by
    intro a b h
    simpa using h)

noncomputable instance instFiniteAct (i : ι) : Finite (Act i) :=
  finiteAct i

noncomputable instance instFintypeAct (i : ι) : Fintype (Act i) := by
  classical
  exact Fintype.ofFinite (Act i)

noncomputable def originalPublicFrag (e : (SG G).Step) : G.PublicState := by
  classical
  cases hs : e.src with
  | base w =>
      by_cases hterm : G.terminal w
      · exact []
      · if hEmpty : G.orderedActive w = [] then
          match e.dst with
          | .base w' =>
              exact [G.pubObs w
                (SerialState.baseChanceLegalAction (G := G) w
                  (G.active_eq_empty_of_orderedActive_eq_nil hEmpty) hterm)
                w']
          | _ => exact []
        else
          exact []
  | decide w chosen current rest hvalid =>
      exact []
  | chance w ga =>
      match e.dst with
      | .base w' => exact [G.pubObs w ga w']
      | _ => exact []

noncomputable def originalPlayerFrag (who : ι) (e : (SG G).Step) : G.InfoState who := by
  classical
  cases hs : e.src with
  | base w =>
      by_cases hterm : G.terminal w
      · exact []
      · if hEmpty : G.orderedActive w = [] then
          match e.dst with
          | .base w' =>
              exact [.obs
                (G.privObs who w
                  (SerialState.baseChanceLegalAction (G := G) w
                    (G.active_eq_empty_of_orderedActive_eq_nil hEmpty) hterm) w')
                (G.pubObs w
                  (SerialState.baseChanceLegalAction (G := G) w
                    (G.active_eq_empty_of_orderedActive_eq_nil hEmpty) hterm) w')]
          | _ => exact []
        else
          match e.act.1 who with
          | some ai => exact [.act ai]
          | none => exact []
  | decide w chosen current rest hvalid =>
      match e.act.1 who with
      | some ai => exact [.act ai]
      | none => exact []
  | chance w ga =>
      match e.dst with
      | .base w' => exact [.obs (G.privObs who w ga w') (G.pubObs w ga w')]
      | _ => exact []

noncomputable def originalPublicViewFrom : List ((SG G).Step) → G.PublicState
  | [] => []
  | e :: es => originalPublicFrag (G := G) e ++ originalPublicViewFrom es

noncomputable def originalPlayerViewFrom (who : ι) : List ((SG G).Step) → G.InfoState who
  | [] => []
  | e :: es => originalPlayerFrag (G := G) who e ++ originalPlayerViewFrom who es

noncomputable def originalPublicView {k : Nat} (pos : TracePosition G k) : G.PublicState :=
  originalPublicViewFrom (G := G) pos.history.steps

noncomputable def originalPlayerView {k : Nat} (pos : TracePosition G k) (who : ι) :
  G.InfoState who :=
  originalPlayerViewFrom (G := G) who pos.history.steps

theorem originalPublicFrag_eq_filterMap_originalPlayerFrag
    (who : ι) (e : (SG G).Step) :
    originalPublicFrag (G := G) e =
      List.filterMap (FOSG.PlayerEvent.publicPart (G := G) (i := who))
        (originalPlayerFrag (G := G) who e) := by
  classical
  rcases e with ⟨src, act, dst, hsupp⟩
  cases src with
  | base w =>
      by_cases hterm : G.terminal w
      · simp [originalPublicFrag, originalPlayerFrag, hterm, FOSG.PlayerEvent.publicPart]
      · by_cases hEmpty : G.orderedActive w = []
        · cases dst <;>
            simp [originalPublicFrag, originalPlayerFrag, hterm, hEmpty,
              FOSG.PlayerEvent.publicPart]
        · cases hact : act.1 who <;>
            simp [originalPublicFrag, originalPlayerFrag, hterm, hEmpty,
              hact, FOSG.PlayerEvent.publicPart]
  | decide w chosen current rest hvalid =>
      cases hact : act.1 who <;>
        simp [originalPublicFrag, originalPlayerFrag, hact, FOSG.PlayerEvent.publicPart]
  | chance w ga =>
      cases dst <;>
        simp [originalPublicFrag, originalPlayerFrag, FOSG.PlayerEvent.publicPart]

theorem originalPublicViewFrom_eq_filterMap_originalPlayerViewFrom
    (who : ι) (es : List ((SG G).Step)) :
    originalPublicViewFrom (G := G) es =
      List.filterMap (FOSG.PlayerEvent.publicPart (G := G) (i := who))
        (originalPlayerViewFrom (G := G) who es) := by
  induction es with
  | nil =>
      rfl
  | cons e es ih =>
      rw [originalPublicViewFrom, originalPlayerViewFrom,
        originalPublicFrag_eq_filterMap_originalPlayerFrag (G := G) (who := who) (e := e)]
      simp [ih, List.filterMap_append]

/-- Collapse a serialized realized step to the corresponding original realized
step when the serialized step performs stochastic resolution. Deterministic
bookkeeping steps erase to `none`. -/
noncomputable def eraseStep? : (SG G).Step → Option G.Step
  | ⟨.base w, act, .base w', support⟩ =>
      if hEmpty : G.orderedActive w = [] then
        let a' : SerialState.FOSGLegalAction (G := G) (.base w) := act
        let aRaw : SerialState.LegalAction (G := G) (.base w) :=
          SerialState.ofFOSGLegalAction (G := G) a'
        some ⟨w,
          SerialState.baseChanceLegalAction (G := G) w
            (G.active_eq_empty_of_orderedActive_eq_nil hEmpty)
            (by
              have hleg : SerialState.legal (G := G) (.base w) aRaw.1 := aRaw.2
              have ha : ¬ G.terminal w ∧ act.1 = noopAction Act := by
                simpa [SerialState.legal, hEmpty] using hleg
              exact ha.1),
          w',
          SerialState.base_empty_support (G := G) hEmpty a' (by
            simpa [aRaw, SerialState.ofFOSGLegalAction_val] using support)⟩
      else
        none
  | ⟨.base w, act, .decide w' chosen current rest hvalid, support⟩ =>
      none
  | ⟨.base w, act, .chance w' ga, support⟩ =>
      none
  | ⟨.decide w chosen current rest hvalid, act, dst, support⟩ =>
      none
  | ⟨.chance w ga, act, .base w', support⟩ =>
      let a' : SerialState.FOSGLegalAction (G := G) (.chance w ga) := act
      some ⟨w, ga, w', SerialState.chance_support (G := G) ga a' (by
        simpa [SerialState.ofFOSGLegalAction_val] using support)⟩
  | ⟨.chance w ga, act, .decide w' chosen current rest hvalid, support⟩ =>
      none
  | ⟨.chance w ga, act, .chance w' ga', support⟩ =>
      none

theorem eraseStep?_some_src
    (e : (SG G).Step) (e' : G.Step)
    (h : eraseStep? (G := G) e = some e') :
    e'.src = SerialState.world (G := G) e.src := by
  classical
  cases e with
  | mk src act dst support =>
      cases src with
      | base w =>
          cases dst with
          | base w' =>
              by_cases hEmpty : G.orderedActive w = []
              · simp [eraseStep?, hEmpty] at h
                cases h
                rfl
              · simp [eraseStep?, hEmpty] at h
          | decide w' chosen current rest hvalid =>
              simp [eraseStep?] at h
          | chance w' ga =>
              simp [eraseStep?] at h
      | decide w chosen current rest hvalid =>
          simp [eraseStep?] at h
      | chance w ga =>
          cases dst with
          | base w' =>
              simp [eraseStep?] at h
              cases h
              rfl
          | decide w' chosen current rest hvalid =>
              simp [eraseStep?] at h
          | chance w' ga' =>
              simp [eraseStep?] at h

theorem eraseStep?_some_dst
    (e : (SG G).Step) (e' : G.Step)
    (h : eraseStep? (G := G) e = some e') :
    e'.dst = SerialState.world (G := G) e.dst := by
  classical
  cases e with
  | mk src act dst support =>
      cases src with
      | base w =>
          cases dst with
          | base w' =>
              by_cases hEmpty : G.orderedActive w = []
              · simp [eraseStep?, hEmpty] at h
                cases h
                rfl
              · simp [eraseStep?, hEmpty] at h
          | decide w' chosen current rest hvalid =>
              simp [eraseStep?] at h
          | chance w' ga =>
              simp [eraseStep?] at h
      | decide w chosen current rest hvalid =>
          simp [eraseStep?] at h
      | chance w ga =>
          cases dst with
          | base w' =>
              simp [eraseStep?] at h
              cases h
              rfl
          | decide w' chosen current rest hvalid =>
              simp [eraseStep?] at h
          | chance w' ga' =>
              simp [eraseStep?] at h

theorem eraseStep?_none_world_eq
    (e : (SG G).Step)
    (h : eraseStep? (G := G) e = none) :
    SerialState.world (G := G) e.dst = SerialState.world (G := G) e.src := by
  classical
  cases e with
  | mk src act dst support =>
      cases src with
      | base w =>
          let actRaw : SerialState.LegalAction (G := G) (.base w) :=
            SerialState.ofFOSGLegalAction (G := G) act
          by_cases hEmpty : G.orderedActive w = []
          · cases dst with
            | base w' =>
                simp [eraseStep?, hEmpty] at h
            | decide w' chosen current rest hvalid =>
                have : False := by
                  have hsupp :
                      SerialState.transition (G := G) (.base w) actRaw
                        (.decide w' chosen current rest hvalid) ≠ 0 := by
                    simpa [actRaw, SerialState.ofFOSGLegalAction_val] using support
                  have hzero :
                      SerialState.transition (G := G) (.base w) actRaw
                        (.decide w' chosen current rest hvalid) = 0 := by
                    rw [SerialState.transition_base_empty_eq (G := G) (w := w) hEmpty actRaw]
                    simp
                  exact hsupp hzero
                exact False.elim this
            | chance w' ga =>
                have : False := by
                  have hsupp :
                      SerialState.transition (G := G) (.base w) actRaw
                        (.chance w' ga) ≠ 0 := by
                    simpa [actRaw, SerialState.ofFOSGLegalAction_val] using support
                  have hzero :
                      SerialState.transition (G := G) (.base w) actRaw
                        (.chance w' ga) = 0 := by
                    rw [SerialState.transition_base_empty_eq (G := G) (w := w) hEmpty actRaw]
                    simp
                  exact hsupp hzero
                exact False.elim this
          · have hpure :
              PMF.pure (SerialState.basePlayerSuccessor (G := G) w actRaw) dst ≠ 0 := by
                have hsupp :
                    SerialState.transition (G := G) (.base w) actRaw dst ≠ 0 := by
                  simpa [actRaw, SerialState.ofFOSGLegalAction_val] using support
                simpa [SerialState.transition_base_nonempty_eq (G := G) (w := w) hEmpty actRaw]
                  using hsupp
            have hdst :
                dst = SerialState.basePlayerSuccessor (G := G) w actRaw := by
              simpa [PMF.pure_apply] using hpure
            simpa [hdst] using
              (SerialState.world_basePlayerSuccessor (G := G) (w := w) (a := actRaw)).symm
      | decide w chosen current rest hvalid =>
          let actRaw : SerialState.LegalAction (G := G) (.decide w chosen current rest hvalid) :=
            SerialState.ofFOSGLegalAction (G := G) act
          have hpure :
              PMF.pure (SerialState.decidePlayerSuccessor (G := G) w chosen current rest hvalid actRaw) dst ≠ 0 := by
            have hsupp :
                SerialState.transition (G := G) (.decide w chosen current rest hvalid) actRaw dst ≠ 0 := by
              simpa [actRaw, SerialState.ofFOSGLegalAction_val] using support
            simpa [SerialState.transition_decide_eq (G := G) (w := w) (chosen := chosen)
              (current := current) (rest := rest) (hvalid := hvalid) actRaw] using hsupp
          have hdst :
              dst = SerialState.decidePlayerSuccessor (G := G) w chosen current rest hvalid actRaw := by
            simpa [PMF.pure_apply] using hpure
          simpa [hdst] using
            (SerialState.world_decidePlayerSuccessor (G := G) (w := w) (chosen := chosen)
              (current := current) (rest := rest) (hvalid := hvalid) (a := actRaw)).symm
      | chance w ga =>
          let actRaw : SerialState.LegalAction (G := G) (.chance w ga) :=
            SerialState.ofFOSGLegalAction (G := G) act
          cases dst with
          | base w' =>
              simp [eraseStep?] at h
          | decide w' chosen current rest hvalid =>
              have : False := by
                have hsupp :
                    SerialState.transition (G := G) (.chance w ga) actRaw
                      (.decide w' chosen current rest hvalid) ≠ 0 := by
                  simpa [actRaw, SerialState.ofFOSGLegalAction_val] using support
                have hzero :
                    SerialState.transition (G := G) (.chance w ga) actRaw
                      (.decide w' chosen current rest hvalid) = 0 := by
                  simp [SerialState.transition]
                exact hsupp hzero
              exact False.elim this
          | chance w' ga' =>
              have : False := by
                have hsupp :
                    SerialState.transition (G := G) (.chance w ga) actRaw
                      (.chance w' ga') ≠ 0 := by
                  simpa [actRaw, SerialState.ofFOSGLegalAction_val] using support
                have hzero :
                    SerialState.transition (G := G) (.chance w ga) actRaw
                      (.chance w' ga') = 0 := by
                  simp [SerialState.transition]
                exact hsupp hzero
              exact False.elim this

private noncomputable def originalHistoryFromAux
    (s : SState G) (h : G.History)
    (hs : h.lastState = SerialState.world (G := G) s) :
    (es : List ((SG G).Step)) → (SG G).StepChainFrom s es →
      { h' : G.History // h'.lastState = SerialState.world (G := G) ((SG G).lastStateFrom s es) }
  | [], _ => ⟨h, by simpa [FOSG.lastStateFrom] using hs⟩
  | e :: es, hchain =>
      match hErase : eraseStep? (G := G) e with
      | some e' =>
          let hsrc' : e'.src = h.lastState := by
            calc
              e'.src = SerialState.world (G := G) e.src := eraseStep?_some_src (G := G) e e' hErase
              _ = SerialState.world (G := G) s := by simpa [hchain.1]
              _ = h.lastState := hs.symm
          let h' := h.appendStep e' hsrc'
          have hs' : h'.lastState = SerialState.world (G := G) e.dst := by
            simpa [h', History.lastState_appendStep] using eraseStep?_some_dst (G := G) e e' hErase
          originalHistoryFromAux e.dst h' hs' es (by simpa using hchain.2)
      | none =>
          let hs' : h.lastState = SerialState.world (G := G) e.dst := by
            calc
              h.lastState = SerialState.world (G := G) s := hs
              _ = SerialState.world (G := G) e.src := by simpa [hchain.1]
              _ = SerialState.world (G := G) e.dst :=
                (eraseStep?_none_world_eq (G := G) e hErase).symm
          originalHistoryFromAux e.dst h hs' es (by simpa using hchain.2)

private theorem originalHistoryFromAux_steps
    (s : SState G) (h : G.History)
    (hs : h.lastState = SerialState.world (G := G) s) :
    ∀ (es : List ((SG G).Step)) (hchain : (SG G).StepChainFrom s es),
      (originalHistoryFromAux (G := G) s h hs es hchain).1.steps =
        h.steps ++ es.filterMap (eraseStep? (G := G))
  | [], _ => by
      simp [originalHistoryFromAux]
  | e :: es, hchain => by
      rcases hchain with ⟨hsrc, htail⟩
      simp only [List.filterMap_cons]
      cases hErase : eraseStep? (G := G) e with
      | some e' =>
          let hsrc' : e'.src = h.lastState := by
            calc
              e'.src = SerialState.world (G := G) e.src := eraseStep?_some_src (G := G) e e' hErase
              _ = SerialState.world (G := G) s := by rw [hsrc]
              _ = h.lastState := hs.symm
          let h' := h.appendStep e' hsrc'
          have hs' : h'.lastState = SerialState.world (G := G) e.dst := by
            simpa [h', History.lastState_appendStep] using
              eraseStep?_some_dst (G := G) e e' hErase
          have hrec :
              (originalHistoryFromAux (G := G) e.dst h' hs' es htail).1.steps =
                h'.steps ++ es.filterMap (eraseStep? (G := G)) :=
            originalHistoryFromAux_steps e.dst h' hs' es htail
          unfold originalHistoryFromAux
          split
          · rename_i e'' hErase'
            have heq : e'' = e' := by
              apply Option.some.inj
              rw [← hErase', hErase]
            subst e''
            simpa [hrec, h', List.append_assoc]
          · rename_i hErase'
            exfalso
            rw [hErase] at hErase'
            contradiction
      | none =>
          let hs' : h.lastState = SerialState.world (G := G) e.dst := by
            calc
              h.lastState = SerialState.world (G := G) s := hs
              _ = SerialState.world (G := G) e.src := by rw [hsrc]
              _ = SerialState.world (G := G) e.dst :=
                (eraseStep?_none_world_eq (G := G) e hErase).symm
          have hrec :
              (originalHistoryFromAux (G := G) e.dst h hs' es htail).1.steps =
                h.steps ++ es.filterMap (eraseStep? (G := G)) :=
            originalHistoryFromAux_steps e.dst h hs' es htail
          unfold originalHistoryFromAux
          split
          · rename_i e' hErase'
            exfalso
            rw [hErase] at hErase'
            contradiction
          · rename_i hErase'
            simpa [hrec]

/-- The original FOSG history represented by a serialized trace position, obtained
by erasing bookkeeping serialized steps and collapsing resolution steps back to
their underlying original realized transitions. -/
noncomputable def originalHistory {k : Nat} (pos : TracePosition G k) : G.History :=
  (originalHistoryFromAux (G := G) (.base G.init) (History.nil G) (by simp)
    pos.trail.1 pos.hchain).1

@[simp] theorem originalHistory_steps {k : Nat} (pos : TracePosition G k) :
    (originalHistory (G := G) pos).steps =
      pos.history.steps.filterMap (eraseStep? (G := G)) := by
  simpa [originalHistory, TracePosition.history] using
    originalHistoryFromAux_steps (G := G) (.base G.init) (History.nil G) (by simp)
      pos.trail.1 pos.hchain

@[simp] theorem originalHistory_lastState {k : Nat} (pos : TracePosition G k) :
    (originalHistory (G := G) pos).lastState = SerialState.world (G := G) pos.state := by
  simpa [originalHistory, pos.hstate] using
    (originalHistoryFromAux (G := G) (.base G.init) (History.nil G) (by simp)
      pos.trail.1 pos.hchain).2

end TracePosition

abbrev PlayerIx := Fin (Fintype.card ι)

noncomputable def playerEquiv : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι

noncomputable def origPlayer (p : Fin (Fintype.card ι)) : ι := (playerEquiv (ι := ι)).symm p

/-- Finite infoset structure induced by history-bearing serialized positions. -/
noncomputable def traceInfoStructure (k : Nat) : InfoStructure where
  n := Fintype.card ι
  Infoset := fun p =>
    {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)}
  arity := fun _ I => Position.actionArity (G := G) I.1.toPosition
  arity_pos := by
    intro p I
    exact Position.actionArity_pos (G := G) I.2

namespace TracePosition

abbrev PayoffVec (k : Nat) := Payoff (traceInfoStructure (G := G) k).Player

noncomputable def zeroPayoff {k : Nat} : PayoffVec (G := G) k :=
  fun _ => 0

noncomputable def liftPayoff {k : Nat} (u : Payoff ι) : PayoffVec (G := G) k :=
  fun p => u (origPlayer (ι := ι) p)

noncomputable def addPayoff {k : Nat}
    (x y : PayoffVec (G := G) k) : PayoffVec (G := G) k :=
  fun p => x p + y p

noncomputable def actionFromIndex {k : Nat}
    (pos : TracePosition G k)
    (a : Fin (Position.actionArity (G := G) pos.toPosition)) :
    (SG G).LegalAction pos.state :=
  Position.actionFromIndex (G := G) (pos := pos.toPosition) a

noncomputable def rawActionFromIndex {k : Nat}
    (pos : TracePosition G k)
    (a : Fin (Position.actionArity (G := G) pos.toPosition)) :
    {x : JointAction Act // SerialState.legal (G := G) pos.state x} :=
  Position.rawActionFromIndex (G := G) (pos := pos.toPosition) a

end TracePosition

/-- Finite infoset structure induced by serialized horizon-bounded positions. -/
noncomputable def infoStructure (k : Nat) : InfoStructure where
  n := Fintype.card ι
  Infoset := fun p => {pos : Position G k // pos.player? = some (origPlayer (ι := ι) p)}
  arity := fun p I => Position.actionArity (G := G) I.1
  arity_pos := by
    intro p I
    exact Position.actionArity_pos (G := G) I.2

namespace Position

noncomputable def descend {k : Nat} (pos : Position G k) (s : SState G) : Position G k :=
  ⟨s, pos.remaining - 1, le_trans (Nat.sub_le _ _) pos.hremaining⟩

abbrev PayoffVec (k : Nat) := Payoff (infoStructure (G := G) k).Player

noncomputable def zeroPayoff {k : Nat} : PayoffVec (G := G) k :=
  fun _ => 0

noncomputable def liftPayoff {k : Nat} (u : Payoff ι) : PayoffVec (G := G) k :=
  fun p => u (origPlayer (ι := ι) p)

noncomputable def addPayoff {k : Nat}
    (x y : PayoffVec (G := G) k) : PayoffVec (G := G) k :=
  fun p => x p + y p

noncomputable def decisionSuccessor {k : Nat} (pos : Position G k)
    (la : { x : JointAction Act // SerialState.legal (G := G) pos.state x }) : SState G :=
  match hstate : pos.state with
  | .base w =>
      SerialState.basePlayerSuccessor (G := G) w <| by
        simpa [hstate] using la
  | .decide w chosen current rest hvalid =>
      SerialState.decidePlayerSuccessor (G := G) w chosen current rest hvalid <| by
        simpa [hstate] using la
  | .chance _ _ =>
      pos.state

noncomputable def decisionChild {k : Nat} {p : PlayerIx}
    (I : {pos : Position G k // pos.player? = some (origPlayer (ι := ι) p)})
    (a : Fin (Position.actionArity (G := G) I.1)) : Position G k :=
  descend (G := G) I.1 (decisionSuccessor (G := G) I.1 (Position.rawActionFromIndex (G := G) a))

theorem descend_remaining {k : Nat} (pos : Position G k) (s : SState G) :
    (descend (G := G) pos s).remaining = pos.remaining - 1 := rfl

theorem decisionChild_remaining {k : Nat} {p : PlayerIx}
    (I : {pos : Position G k // pos.player? = some (origPlayer (ι := ι) p)})
    (a : Fin (Position.actionArity (G := G) I.1)) :
    (decisionChild G I a).remaining = I.1.remaining - 1 := rfl

theorem state_eq_base_or_decide_of_player
    {k : Nat} {pos : Position G k} {i : ι}
    (hplayer : pos.player? = some i) :
    (∃ w, pos.state = .base w ∧ G.orderedActive w ≠ []) ∨
      (∃ w chosen current rest hvalid,
        pos.state = .decide w chosen current rest hvalid) := by
  classical
  by_cases htrunc : pos.isTruncated
  · simp [Position.player?, htrunc] at hplayer
  · cases hstate : pos.state with
    | base w =>
        cases horder : G.orderedActive w with
        | nil =>
            simp [Position.player?, Position.isTruncated, htrunc, hstate, horder] at hplayer
        | cons current rest =>
            exact Or.inl ⟨w, rfl, by simp [horder]⟩
    | decide w chosen current rest hvalid =>
        exact Or.inr ⟨w, chosen, current, rest, hvalid, rfl⟩
    | chance w ga =>
        simp [Position.player?, Position.isTruncated, htrunc, hstate] at hplayer

theorem decisionTransition_ne_zero {k : Nat} {p : PlayerIx}
    (I : {pos : Position G k // pos.player? = some (origPlayer (ι := ι) p)})
    (a : Fin (Position.actionArity (G := G) I.1)) :
    SerialState.transition (G := G) I.1.state
      (Position.rawActionFromIndex (G := G) (pos := I.1) a)
      (Position.decisionSuccessor (G := G) I.1
        (Position.rawActionFromIndex (G := G) (pos := I.1) a)) ≠ 0 := by
  classical
  rcases I with ⟨⟨state, remaining, hremaining⟩, hI⟩
  dsimp at a ⊢
  rcases state_eq_base_or_decide_of_player (G := G) hI with hbase | hdecide
  · rcases hbase with ⟨w, hstate, hNonempty⟩
    have hs : state = .base w := by simpa using hstate
    subst state
    let pos : Position G k := ⟨.base w, remaining, hremaining⟩
    let act := Position.rawActionFromIndex (G := G) (pos := pos) a
    let dst := Position.decisionSuccessor (G := G) pos act
    have hdst : dst = SerialState.basePlayerSuccessor (G := G) w act := by
      simp [dst, act, pos, Position.decisionSuccessor]
    have hval :
        SerialState.transition (G := G) (.base w) act dst = 1 := by
      simpa [hdst] using
        congrArg (fun μ => μ dst)
          (SerialState.transition_base_nonempty_eq (G := G) (w := w) hNonempty act)
    intro hz
    rw [hval] at hz
    simp at hz
  · rcases hdecide with ⟨w, chosen, current, rest, hvalid, hstate⟩
    have hs : state = .decide w chosen current rest hvalid := by
      simpa using hstate
    subst state
    let pos : Position G k := ⟨.decide w chosen current rest hvalid, remaining, hremaining⟩
    let act := Position.rawActionFromIndex (G := G) (pos := pos) a
    let dst := Position.decisionSuccessor (G := G) pos act
    have hdst :
        dst = SerialState.decidePlayerSuccessor (G := G) w chosen current rest hvalid act := by
      simp [dst, act, pos, Position.decisionSuccessor]
    have hval :
        SerialState.transition (G := G) (.decide w chosen current rest hvalid) act dst = 1 := by
      simpa [hdst] using
        congrArg (fun μ => μ dst)
          (SerialState.transition_decide_eq (G := G)
            (w := w) (chosen := chosen) (current := current) (rest := rest)
            (hvalid := hvalid) act)
    intro hz
    rw [hval] at hz
    simp at hz

/-- Realized serialized step for a trace-position player edge. -/
noncomputable def TracePosition.decisionStep {k : Nat} {p : PlayerIx}
    (I : {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)})
    (a : Fin (Position.actionArity (G := G) I.1.toPosition)) :
    (SG G).Step where
  src := I.1.state
  act := TracePosition.actionFromIndex (G := G) I.1 a
  dst := Position.decisionSuccessor (G := G) I.1.toPosition
    (TracePosition.rawActionFromIndex (G := G) I.1 a)
  support := by
    change SerialState.transition (G := G) I.1.state
      (TracePosition.rawActionFromIndex (G := G) I.1 a)
      (Position.decisionSuccessor (G := G) I.1.toPosition
        (TracePosition.rawActionFromIndex (G := G) I.1 a)) ≠ 0
    simpa [TracePosition.toPosition, TracePosition.rawActionFromIndex] using
      Position.decisionTransition_ne_zero (G := G)
        (I := ⟨I.1.toPosition, I.2⟩) a

theorem TracePosition.remaining_ne_zero_of_player {k : Nat} {pos : TracePosition G k} {i : ι}
    (hplayer : pos.player? = some i) :
    pos.remaining ≠ 0 := by
  intro hzero
  simp [TracePosition.player?, Position.player?, Position.isTruncated,
    TracePosition.toPosition, hzero] at hplayer

/-- Trace-position child reached by a realized player edge. -/
noncomputable def TracePosition.decisionChild {k : Nat} {p : PlayerIx}
    (I : {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)})
    (a : Fin (Position.actionArity (G := G) I.1.toPosition)) :
    TracePosition G k :=
  TracePosition.appendStep (G := G) I.1 (TracePosition.decisionStep (G := G) I a)
    (TracePosition.remaining_ne_zero_of_player (G := G) I.2) rfl

@[simp] theorem TracePosition.decisionChild_history_steps {k : Nat} {p : PlayerIx}
    (I : {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)})
    (a : Fin (Position.actionArity (G := G) I.1.toPosition)) :
    (TracePosition.decisionChild (G := G) I a).history.steps =
      I.1.history.steps ++ [TracePosition.decisionStep (G := G) I a] := by
  simpa [TracePosition.decisionChild] using
    TracePosition.appendStep_history_steps (G := G) I.1
      (TracePosition.decisionStep (G := G) I a)
      (TracePosition.remaining_ne_zero_of_player (G := G) I.2) rfl

@[simp] theorem TracePosition.decisionChild_lastState {k : Nat} {p : PlayerIx}
    (I : {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)})
    (a : Fin (Position.actionArity (G := G) I.1.toPosition)) :
    (TracePosition.decisionChild (G := G) I a).history.lastState =
      (TracePosition.decisionStep (G := G) I a).dst := by
  simpa [TracePosition.decisionChild] using
    TracePosition.appendStep_history_lastState (G := G) I.1
      (TracePosition.decisionStep (G := G) I a)
      (TracePosition.remaining_ne_zero_of_player (G := G) I.2) rfl

@[simp] theorem TracePosition.decisionChild_remaining {k : Nat} {p : PlayerIx}
    (I : {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)})
    (a : Fin (Position.actionArity (G := G) I.1.toPosition)) :
    (TracePosition.decisionChild (G := G) I a).remaining = I.1.remaining - 1 := by
  simp [TracePosition.decisionChild]

theorem TracePosition.current_mem_active_of_player
    {k : Nat} {pos : TracePosition G k} {i : ι}
    (hplayer : pos.player? = some i) :
    i ∈ G.active (TracePosition.originalHistory (G := G) pos).lastState := by
  rcases Position.state_eq_base_or_decide_of_player
      (G := G) (pos := pos.toPosition) hplayer with hbase | hdecide
  · rcases hbase with ⟨w, hstate, hnonempty⟩
    cases horder : G.orderedActive w with
    | nil =>
        exact False.elim (hnonempty horder)
    | cons current rest =>
        have hs : pos.state = .base w := by
          simpa [TracePosition.toPosition] using hstate
        have htmp := hplayer
        simp [TracePosition.player?, TracePosition.toPosition, Position.player?,
          Position.isTruncated, hs, horder] at htmp
        have hcurr : current = i := htmp.2
        have hmem : current ∈ G.orderedActive w := by
          simp [horder]
        have hactive : current ∈ G.active w := (G.mem_orderedActive_iff w current).1 hmem
        have hworld : SerialState.world (G := G) pos.state = w := by
          simpa [hs] using (SerialState.world_base (G := G) w)
        rw [TracePosition.originalHistory_lastState (G := G) pos]
        simpa [hworld, hcurr] using hactive
  · rcases hdecide with ⟨w, chosen, current, rest, hvalid, hstate⟩
    have hs : pos.state = .decide w chosen current rest hvalid := by
      simpa [TracePosition.toPosition] using hstate
    have htmp := hplayer
    simp [TracePosition.player?, TracePosition.toPosition, Position.player?,
      Position.isTruncated, hs] at htmp
    have hcurr : current = i := htmp.2
    have hactive : current ∈ G.active w := G.current_mem_active_of_split (w := w) hvalid.1
    have hworld : SerialState.world (G := G) pos.state = w := by
      simpa [hs] using (SerialState.world_decide (G := G) w chosen current rest hvalid)
    rw [TracePosition.originalHistory_lastState (G := G) pos]
    simpa [hworld, hcurr] using hactive

theorem TracePosition.not_terminal_originalHistory_of_player
    {k : Nat} {pos : TracePosition G k} {i : ι}
    (hplayer : pos.player? = some i) :
    ¬ G.terminal (TracePosition.originalHistory (G := G) pos).lastState := by
  intro hterm
  have hactive : i ∈ G.active (TracePosition.originalHistory (G := G) pos).lastState :=
    TracePosition.current_mem_active_of_player (G := G) hplayer
  have hempty : G.active (TracePosition.originalHistory (G := G) pos).lastState = ∅ :=
    G.terminal_active_eq_empty hterm
  have hiempty : i ∉ G.active (TracePosition.originalHistory (G := G) pos).lastState := by
    rw [hempty]
    simp
  exact hiempty hactive

theorem TracePosition.actionFromIndex_eq_singleMove
    {k : Nat} {p : PlayerIx}
    (I : {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)})
    (a : Fin (Position.actionArity (G := G) I.1.toPosition)) :
    ∃ ai : Act (origPlayer (ι := ι) p),
      (TracePosition.actionFromIndex (G := G) I.1 a).1 =
        singleMove (Act := Act) (origPlayer (ι := ι) p) ai := by
  classical
  rcases Position.state_eq_base_or_decide_of_player
      (G := G) (pos := I.1.toPosition) I.2 with hbase | hdecide
  · rcases hbase with ⟨w, hstate, hnonempty⟩
    cases horder : G.orderedActive w with
    | nil =>
        exact False.elim (hnonempty horder)
    | cons current rest =>
        have hs : I.1.state = .base w := by
          simpa [TracePosition.toPosition] using hstate
        have hI := I.2
        simp [TracePosition.player?, TracePosition.toPosition, Position.player?,
          Position.isTruncated, hs, horder] at hI
        have hcurr : current = origPlayer (ι := ι) p := hI.2
        cases hcurr
        have hleg :
            SerialState.playerLegal (G := G) w (noopAction Act) (origPlayer (ι := ι) p)
              (TracePosition.rawActionFromIndex (G := G) I.1 a).1 := by
          simpa [TracePosition.rawActionFromIndex, TracePosition.actionFromIndex,
            TracePosition.toPosition, Position.rawActionFromIndex, Position.actionFromIndex,
            SerialState.legal, hs, horder] using
            (TracePosition.rawActionFromIndex (G := G) I.1 a).2
        rcases (SerialState.playerLegal_iff_exists_singleMove (G := G)).1 hleg with
          ⟨ai, ha, _⟩
        exact ⟨ai, by
          simpa [TracePosition.rawActionFromIndex, TracePosition.actionFromIndex,
            Position.rawActionFromIndex, Position.actionFromIndex] using ha⟩
  · rcases hdecide with ⟨w, chosen, current, rest, hvalid, hstate⟩
    have hs : I.1.state = .decide w chosen current rest hvalid := by
      simpa [TracePosition.toPosition] using hstate
    have hI := I.2
    simp [TracePosition.player?, TracePosition.toPosition, Position.player?,
      Position.isTruncated, hs] at hI
    have hcurr : current = origPlayer (ι := ι) p := hI.2
    cases hcurr
    have hleg :
        SerialState.playerLegal (G := G) w chosen (origPlayer (ι := ι) p)
          (TracePosition.rawActionFromIndex (G := G) I.1 a).1 := by
      simpa [TracePosition.rawActionFromIndex, TracePosition.actionFromIndex,
        TracePosition.toPosition, Position.rawActionFromIndex, Position.actionFromIndex,
        SerialState.legal, hs] using
        (TracePosition.rawActionFromIndex (G := G) I.1 a).2
    rcases (SerialState.playerLegal_iff_exists_singleMove (G := G)).1 hleg with
      ⟨ai, ha, _⟩
    exact ⟨ai, by
      simpa [TracePosition.rawActionFromIndex, TracePosition.actionFromIndex,
        Position.rawActionFromIndex, Position.actionFromIndex] using ha⟩

/-- The original concrete action represented by a trace decision index. -/
noncomputable def TracePosition.actualActionFromIndex
    {k : Nat} {p : PlayerIx}
    (I : {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)})
    (a : Fin (Position.actionArity (G := G) I.1.toPosition)) :
    Act (origPlayer (ι := ι) p) :=
  Classical.choose (TracePosition.actionFromIndex_eq_singleMove (G := G) I a)

@[simp] theorem TracePosition.actionFromIndex_eq_singleMove_actual
    {k : Nat} {p : PlayerIx}
    (I : {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)})
    (a : Fin (Position.actionArity (G := G) I.1.toPosition)) :
    (TracePosition.actionFromIndex (G := G) I.1 a).1 =
      singleMove (Act := Act) (origPlayer (ι := ι) p)
        (TracePosition.actualActionFromIndex (G := G) I a) :=
  Classical.choose_spec (TracePosition.actionFromIndex_eq_singleMove (G := G) I a)

@[simp] theorem TracePosition.actionFromIndex_apply_current
    {k : Nat} {p : PlayerIx}
    (I : {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)})
    (a : Fin (Position.actionArity (G := G) I.1.toPosition)) :
    (TracePosition.actionFromIndex (G := G) I.1 a).1 (origPlayer (ι := ι) p) =
      some (TracePosition.actualActionFromIndex (G := G) I a) := by
  simpa [TracePosition.actionFromIndex_eq_singleMove_actual (G := G) I a]

@[simp] theorem TracePosition.actionFromIndex_apply_other
    {k : Nat} {p : PlayerIx}
    (I : {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)})
    (a : Fin (Position.actionArity (G := G) I.1.toPosition))
    {j : ι} (hj : j ≠ origPlayer (ι := ι) p) :
    (TracePosition.actionFromIndex (G := G) I.1 a).1 j = none := by
  simpa [TracePosition.actionFromIndex_eq_singleMove_actual (G := G) I a, hj]

theorem TracePosition.actualActionFromIndex_mem_available
    {k : Nat} {p : PlayerIx}
    (I : {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)})
    (a : Fin (Position.actionArity (G := G) I.1.toPosition)) :
    TracePosition.actualActionFromIndex (G := G) I a ∈
      G.availableActionsAtHistory (TracePosition.originalHistory (G := G) I.1)
        (origPlayer (ι := ι) p) := by
  classical
  rcases Position.state_eq_base_or_decide_of_player
      (G := G) (pos := I.1.toPosition) I.2 with hbase | hdecide
  · rcases hbase with ⟨w, hstate, hnonempty⟩
    cases horder : G.orderedActive w with
    | nil =>
        exact False.elim (hnonempty horder)
    | cons current rest =>
        have hs : I.1.state = .base w := by
          simpa [TracePosition.toPosition] using hstate
        have hI := I.2
        simp [TracePosition.player?, TracePosition.toPosition, Position.player?,
          Position.isTruncated, hs, horder] at hI
        have hcurr : current = origPlayer (ι := ι) p := hI.2
        cases hcurr
        have hworld : SerialState.world (G := G) I.1.state = w := by
          simpa [hs] using (SerialState.world_base (G := G) w)
        have hlast : (TracePosition.originalHistory (G := G) I.1).lastState = w := by
          rw [TracePosition.originalHistory_lastState (G := G) I.1]
          exact hworld
        have hleg :
            SerialState.playerLegal (G := G) w (noopAction Act) (origPlayer (ι := ι) p)
              (singleMove (Act := Act) (origPlayer (ι := ι) p)
                (TracePosition.actualActionFromIndex (G := G) I a)) := by
          rw [← TracePosition.actionFromIndex_eq_singleMove_actual (G := G) I a]
          simpa [TracePosition.rawActionFromIndex, TracePosition.actionFromIndex,
            TracePosition.toPosition, Position.rawActionFromIndex,
            Position.actionFromIndex, SerialState.legal, hs, horder] using
            (TracePosition.rawActionFromIndex (G := G) I.1 a).2
        rcases hleg with ⟨_, _, ⟨ga, _, hcurr⟩⟩
        have hga := (G.legal_iff_forall).1 ga.2
        have hlocal :
            origPlayer (ι := ι) p ∈ G.active w ∧
              TracePosition.actualActionFromIndex (G := G) I a ∈
                G.availableActions w (origPlayer (ι := ι) p) := by
          simpa [FOSG.locallyLegalAtState, hcurr] using hga.2 (origPlayer (ι := ι) p)
        rw [FOSG.mem_availableActionsAtHistory_iff]
        rw [hlast]
        exact ⟨by
          exact hlocal.1,
          by exact hlocal.2⟩
  · rcases hdecide with ⟨w, chosen, current, rest, hvalid, hstate⟩
    have hs : I.1.state = .decide w chosen current rest hvalid := by
      simpa [TracePosition.toPosition] using hstate
    have hI := I.2
    simp [TracePosition.player?, TracePosition.toPosition, Position.player?,
      Position.isTruncated, hs] at hI
    have hcurrEq : current = origPlayer (ι := ι) p := hI.2
    cases hcurrEq
    have hworld : SerialState.world (G := G) I.1.state = w := by
      simpa [hs] using
        (SerialState.world_decide (G := G) w chosen (origPlayer (ι := ι) p) rest hvalid)
    have hlast : (TracePosition.originalHistory (G := G) I.1).lastState = w := by
      rw [TracePosition.originalHistory_lastState (G := G) I.1]
      exact hworld
    have hleg :
        SerialState.playerLegal (G := G) w chosen (origPlayer (ι := ι) p)
          (singleMove (Act := Act) (origPlayer (ι := ι) p)
            (TracePosition.actualActionFromIndex (G := G) I a)) := by
      rw [← TracePosition.actionFromIndex_eq_singleMove_actual (G := G) I a]
      simpa [TracePosition.rawActionFromIndex, TracePosition.actionFromIndex,
        TracePosition.toPosition, Position.rawActionFromIndex,
        Position.actionFromIndex, SerialState.legal, hs] using
        (TracePosition.rawActionFromIndex (G := G) I.1 a).2
    rcases hleg with ⟨_, _, ⟨ga, _, hcurr⟩⟩
    have hga := (G.legal_iff_forall).1 ga.2
    have hlocal :
        origPlayer (ι := ι) p ∈ G.active w ∧
          TracePosition.actualActionFromIndex (G := G) I a ∈
            G.availableActions w (origPlayer (ι := ι) p) := by
      simpa [FOSG.locallyLegalAtState, hcurr] using hga.2 (origPlayer (ι := ι) p)
    rw [FOSG.mem_availableActionsAtHistory_iff]
    rw [hlast]
    exact ⟨by
      exact hlocal.1,
      by exact hlocal.2⟩

instance instFiniteAct (i : ι) : Finite (Act i) :=
  Finite.of_injective (Option.some : Act i → Option (Act i))
    (by intro a b h; exact Option.some.inj h)

noncomputable instance instFintypeAct (i : ι) : Fintype (Act i) :=
  Fintype.ofFinite (Act i)

/-- Original concrete actions available at a trace decision position. -/
abbrev TracePosition.AvailableActionSubtype
    {k : Nat} {p : PlayerIx}
    (I : {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)}) :=
  { ai : Act (origPlayer (ι := ι) p) //
      ai ∈ G.availableActionsAtHistory (TracePosition.originalHistory (G := G) I.1)
        (origPlayer (ι := ι) p) }

theorem TracePosition.legal_singleMove_of_mem_available
    {k : Nat} {p : PlayerIx}
    (I : {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)})
    {ai : Act (origPlayer (ι := ι) p)}
    (hai : ai ∈
      G.availableActionsAtHistory (TracePosition.originalHistory (G := G) I.1)
        (origPlayer (ι := ι) p)) :
    SerialState.legal (G := G) I.1.state
      (singleMove (Act := Act) (origPlayer (ι := ι) p) ai) := by
  classical
  rcases Position.state_eq_base_or_decide_of_player
      (G := G) (pos := I.1.toPosition) I.2 with hbase | hdecide
  · rcases hbase with ⟨w, hstate, hnonempty⟩
    cases horder : G.orderedActive w with
    | nil =>
        exact False.elim (hnonempty horder)
    | cons current rest =>
        have hs : I.1.state = .base w := by
          simpa [TracePosition.toPosition] using hstate
        have hI := I.2
        simp [TracePosition.player?, TracePosition.toPosition, Position.player?,
          Position.isTruncated, hs, horder] at hI
        have hcurr : current = origPlayer (ι := ι) p := hI.2
        cases hcurr
        have hnotTerm : ¬ G.terminal (TracePosition.originalHistory (G := G) I.1).lastState :=
          TracePosition.not_terminal_originalHistory_of_player (G := G) I.2
        have hlast : (TracePosition.originalHistory (G := G) I.1).lastState = w := by
          rw [TracePosition.originalHistory_lastState (G := G) I.1]
          simpa [hs] using (SerialState.world_base (G := G) w)
        have hnotTermW : ¬ G.terminal w := by
          simpa [hlast] using hnotTerm
        obtain ⟨a0, ha0⟩ := G.nonterminal_exists_legal hnotTermW
        let ga0 : G.LegalAction w := ⟨a0, ha0⟩
        let ga : G.LegalAction w := by
          refine ⟨recordChoice ga0.1 (singleMove (Act := Act) (origPlayer (ι := ι) p) ai)
            (origPlayer (ι := ι) p), ?_⟩
          refine (G.legal_iff_forall).2 ?_
          refine ⟨hnotTermW, ?_⟩
          intro j
          by_cases hj : j = origPlayer (ι := ι) p
          · subst hj
            rw [recordChoice_self]
            rw [FOSG.mem_availableActionsAtHistory_iff] at hai
            rw [hlast] at hai
            simpa [FOSG.locallyLegalAtState, singleMove] using hai
          · rw [recordChoice_other _ _ (h := hj)]
            simpa [FOSG.locallyLegalAtState] using (G.legal_iff_forall).1 ga0.2 |>.2 j
        have hcomp : G.ExtendsPartial (noopAction Act) ga := by
          exact G.extendsPartial_noop ga
        simpa [SerialState.legal, hs, horder, singleMove] using
          (show SerialState.playerLegal (G := G) w (noopAction Act) (origPlayer (ι := ι) p)
            (singleMove (Act := Act) (origPlayer (ι := ι) p) ai) from
            ⟨⟨ai, by simp [singleMove]⟩,
              by intro j hj; simp [singleMove, hj],
              ⟨ga, hcomp, by simp [ga, singleMove]⟩⟩)
  · rcases hdecide with ⟨w, chosen, current, rest, hvalid, hstate⟩
    have hs : I.1.state = .decide w chosen current rest hvalid := by
      simpa [TracePosition.toPosition] using hstate
    have hI := I.2
    simp [TracePosition.player?, TracePosition.toPosition, Position.player?,
      Position.isTruncated, hs] at hI
    have hcurrEq : current = origPlayer (ι := ι) p := hI.2
    cases hcurrEq
    have hlast : (TracePosition.originalHistory (G := G) I.1).lastState = w := by
      rw [TracePosition.originalHistory_lastState (G := G) I.1]
      simpa [hs] using
        (SerialState.world_decide (G := G) w chosen (origPlayer (ι := ι) p) rest hvalid)
    rcases hvalid.2.2 with ⟨ga0, hga0comp⟩
    let ga : G.LegalAction w := by
      refine ⟨recordChoice ga0.1 (singleMove (Act := Act) (origPlayer (ι := ι) p) ai)
        (origPlayer (ι := ι) p), ?_⟩
      refine (G.legal_iff_forall).2 ?_
      have hnotTermW : ¬ G.terminal w := by
        have hnotTerm :=
          TracePosition.not_terminal_originalHistory_of_player (G := G) I.2
        simpa [hlast] using hnotTerm
      refine ⟨hnotTermW, ?_⟩
      intro j
      by_cases hj : j = origPlayer (ι := ι) p
      · subst hj
        rw [recordChoice_self]
        rw [FOSG.mem_availableActionsAtHistory_iff] at hai
        rw [hlast] at hai
        simpa [FOSG.locallyLegalAtState, singleMove] using hai
      · rw [recordChoice_other _ _ (h := hj)]
        simpa [FOSG.locallyLegalAtState] using (G.legal_iff_forall).1 ga0.2 |>.2 j
    have hcomp : G.ExtendsPartial chosen ga := by
      intro j
      by_cases hj : j = origPlayer (ι := ι) p
      · subst hj
        left
        exact hvalid.2.1 (origPlayer (ι := ι) p) (by simp)
      · rcases hga0comp j with hnone | hsame
        · left
          exact hnone
        · right
          rw [show ga.1 j = ga0.1 j by simp [ga, recordChoice_other _ _ (h := hj)]]
          exact hsame
    simpa [SerialState.legal, hs, singleMove] using
      (show SerialState.playerLegal (G := G) w chosen (origPlayer (ι := ι) p)
        (singleMove (Act := Act) (origPlayer (ι := ι) p) ai) from
        ⟨⟨ai, by simp [singleMove]⟩,
          by intro j hj; simp [singleMove, hj],
          ⟨ga, hcomp, by simp [ga, singleMove]⟩⟩)

/-- The serialized legal action corresponding to an original available action at
the trace decision position. -/
noncomputable def TracePosition.legalActionOfAvailableAction
    {k : Nat} {p : PlayerIx}
    (I : {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)})
    (ai : TracePosition.AvailableActionSubtype (G := G) I) :
    (SG G).LegalAction I.1.state := by
  let a :
      SerialState.LegalAction (G := G) I.1.state := ⟨
        singleMove (Act := Act) (origPlayer (ι := ι) p) ai.1,
        TracePosition.legal_singleMove_of_mem_available (G := G) I ai.2
      ⟩
  exact SerialState.toFOSGLegalAction (G := G) a

@[simp] theorem TracePosition.legalActionOfAvailableAction_val
    {k : Nat} {p : PlayerIx}
    (I : {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)})
    (ai : TracePosition.AvailableActionSubtype (G := G) I) :
    (TracePosition.legalActionOfAvailableAction (G := G) I ai).1 =
      singleMove (Act := Act) (origPlayer (ι := ι) p) ai.1 := by
  simp [TracePosition.legalActionOfAvailableAction]

@[simp] theorem TracePosition.legalActionOfAvailableAction_apply_current
    {k : Nat} {p : PlayerIx}
    (I : {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)})
    (ai : TracePosition.AvailableActionSubtype (G := G) I) :
    (TracePosition.legalActionOfAvailableAction (G := G) I ai).1 (origPlayer (ι := ι) p) =
      some ai.1 := by
  simpa [TracePosition.legalActionOfAvailableAction_val (G := G) I ai]

@[simp] theorem TracePosition.legalActionOfAvailableAction_apply_other
    {k : Nat} {p : PlayerIx}
    (I : {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)})
    (ai : TracePosition.AvailableActionSubtype (G := G) I) {j : ι}
    (hj : j ≠ origPlayer (ι := ι) p) :
    (TracePosition.legalActionOfAvailableAction (G := G) I ai).1 j = none := by
  simpa [TracePosition.legalActionOfAvailableAction_val (G := G) I ai, hj]

/-- Decision indices at a trace player node are canonically equivalent to the
original available concrete actions at the corresponding original history. -/
noncomputable def TracePosition.actionIndexEquivAvailableAction
    {k : Nat} {p : PlayerIx}
    (I : {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)}) :
    Fin (Position.actionArity (G := G) I.1.toPosition) ≃
      TracePosition.AvailableActionSubtype (G := G) I := by
  classical
  refine Equiv.ofBijective
    (fun a => ⟨TracePosition.actualActionFromIndex (G := G) I a,
      TracePosition.actualActionFromIndex_mem_available (G := G) I a⟩) ?_
  constructor
  · intro a b hab
    have hacts :
        TracePosition.actionFromIndex (G := G) I.1 a =
          TracePosition.actionFromIndex (G := G) I.1 b := by
      ext j
      by_cases hj : j = origPlayer (ι := ι) p
      · subst hj
        have h1 :
            TracePosition.actualActionFromIndex (G := G) I a =
              TracePosition.actualActionFromIndex (G := G) I b :=
          congrArg Subtype.val hab
        simp [TracePosition.actionFromIndex_apply_current, h1]
      · simp [TracePosition.actionFromIndex_apply_other, hj]
    have ha :
        (Fintype.equivFin ((SG G).LegalAction I.1.state))
          (TracePosition.actionFromIndex (G := G) I.1 a) = a := by
      simpa [TracePosition.actionFromIndex, Position.actionFromIndex, TracePosition.toPosition] using
        Equiv.apply_symm_apply
          (Fintype.equivFin ((SG G).LegalAction (TracePosition.toPosition (G := G) I.1).state)) a
    have hb :
        (Fintype.equivFin ((SG G).LegalAction I.1.state))
          (TracePosition.actionFromIndex (G := G) I.1 b) = b := by
      simpa [TracePosition.actionFromIndex, Position.actionFromIndex, TracePosition.toPosition] using
        Equiv.apply_symm_apply
          (Fintype.equivFin ((SG G).LegalAction (TracePosition.toPosition (G := G) I.1).state)) b
    rw [← ha, ← hb]
    exact congrArg (Fintype.equivFin ((SG G).LegalAction I.1.state)) hacts
  · intro ai
    refine ⟨(Fintype.equivFin ((SG G).LegalAction I.1.state))
      (TracePosition.legalActionOfAvailableAction (G := G) I ai), ?_⟩
    apply Subtype.ext
    change
      TracePosition.actualActionFromIndex (G := G) I
          ((Fintype.equivFin ((SG G).LegalAction I.1.state))
            (TracePosition.legalActionOfAvailableAction (G := G) I ai)) = ai.1
    have hEq :
        TracePosition.actionFromIndex (G := G) I.1
          ((Fintype.equivFin ((SG G).LegalAction I.1.state))
            (TracePosition.legalActionOfAvailableAction (G := G) I ai)) =
        TracePosition.legalActionOfAvailableAction (G := G) I ai := by
      change
        (Fintype.equivFin ((SG G).LegalAction I.1.state)).symm
            ((Fintype.equivFin ((SG G).LegalAction I.1.state))
              (TracePosition.legalActionOfAvailableAction (G := G) I ai)) =
          TracePosition.legalActionOfAvailableAction (G := G) I ai
      exact (Fintype.equivFin ((SG G).LegalAction I.1.state)).symm_apply_apply _
    have hcur := congrArg (fun la => la.1 (origPlayer (ι := ι) p)) hEq
    apply Option.some.inj
    simpa [TracePosition.actionFromIndex_apply_current,
      TracePosition.legalActionOfAvailableAction_apply_current] using hcur

/-- Recover the original available concrete action underlying a support point
of the native behavioral strategy at a trace decision position. -/
noncomputable def TracePosition.supportActionSubtype
    {k : Nat} {p : PlayerIx}
    (σ : G.LegalBehavioralProfile)
    (I : {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)})
    (oi : Option (Act (origPlayer (ι := ι) p)))
    (hoi : oi ∈
      ((σ.toProfile (origPlayer (ι := ι) p))
        ((TracePosition.originalHistory (G := G) I.1).playerView (origPlayer (ι := ι) p))).support) :
    TracePosition.AvailableActionSubtype (G := G) I := by
  let h := TracePosition.originalHistory (G := G) I.1
  have hoi' : oi ∈
      ((σ (origPlayer (ι := ι) p)).1 (h.playerView (origPlayer (ι := ι) p))).support := by
    simpa [h] using hoi
  have hlegal : oi ∈ G.availableMoves h (origPlayer (ι := ι) p) := by
    exact (σ (origPlayer (ι := ι) p)).2 h hoi'
  cases hoiEq : oi with
  | none =>
      have hactive :
          origPlayer (ι := ι) p ∈ G.active h.lastState :=
        TracePosition.current_mem_active_of_player (G := G) I.2
      rw [G.mem_availableMoves_iff] at hlegal
      simp [FOSG.locallyLegalAtState, hactive, hoiEq] at hlegal
  | some ai =>
      refine ⟨ai, ?_⟩
      rw [show ai ∈ G.availableActionsAtHistory h (origPlayer (ι := ι) p) ↔
          some ai ∈ G.availableMoves h (origPlayer (ι := ι) p) by
          simp [FOSG.availableActionsAtHistory, FOSG.availableMoves,
            FOSG.availableMovesAtState, FOSG.locallyLegalAtState]]
      simpa [hoiEq] using hlegal

/-- The trace decision index corresponding to a support point of the native
behavioral strategy at the same original player view. -/
noncomputable def TracePosition.supportDecisionIndex
    {k : Nat} {p : PlayerIx}
    (σ : G.LegalBehavioralProfile)
    (I : {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)})
    (oi : Option (Act (origPlayer (ι := ι) p)))
    (hoi : oi ∈
      ((σ.toProfile (origPlayer (ι := ι) p))
        ((TracePosition.originalHistory (G := G) I.1).playerView (origPlayer (ι := ι) p))).support) :
    Fin (Position.actionArity (G := G) I.1.toPosition) :=
  (TracePosition.actionIndexEquivAvailableAction (G := G) I).symm
    (TracePosition.supportActionSubtype (G := G) σ I oi hoi)

theorem TracePosition.supportDecisionIndex_injective
    {k : Nat} {p : PlayerIx}
    (σ : G.LegalBehavioralProfile)
    (I : {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)})
    {oi₁ oi₂ : Option (Act (origPlayer (ι := ι) p))}
    {h₁ : oi₁ ∈
      ((σ.toProfile (origPlayer (ι := ι) p))
        ((TracePosition.originalHistory (G := G) I.1).playerView
          (origPlayer (ι := ι) p))).support}
    {h₂ : oi₂ ∈
      ((σ.toProfile (origPlayer (ι := ι) p))
        ((TracePosition.originalHistory (G := G) I.1).playerView
          (origPlayer (ι := ι) p))).support}
    (heq : TracePosition.supportDecisionIndex (G := G) σ I oi₁ h₁ =
      TracePosition.supportDecisionIndex (G := G) σ I oi₂ h₂) :
    oi₁ = oi₂ := by
  let h := TracePosition.originalHistory (G := G) I.1
  have hactive :
      origPlayer (ι := ι) p ∈ G.active h.lastState :=
    TracePosition.current_mem_active_of_player (G := G) I.2
  have hsub :
      TracePosition.supportActionSubtype (G := G) σ I oi₁ h₁ =
        TracePosition.supportActionSubtype (G := G) σ I oi₂ h₂ := by
    exact (TracePosition.actionIndexEquivAvailableAction (G := G) I).symm.injective heq
  cases hoi1Eq : oi₁ with
  | none =>
      have hlegal : none ∈ G.availableMoves h (origPlayer (ι := ι) p) := by
        have hoi1' : none ∈
            ((σ (origPlayer (ι := ι) p)).1
              (h.playerView (origPlayer (ι := ι) p))).support := by
          simpa [h, hoi1Eq] using h₁
        exact (σ (origPlayer (ι := ι) p)).2 h hoi1'
      rw [G.mem_availableMoves_iff] at hlegal
      simp [FOSG.locallyLegalAtState, hactive, hoi1Eq] at hlegal
  | some ai₁ =>
      cases hoi2Eq : oi₂ with
      | none =>
          have hlegal : none ∈ G.availableMoves h (origPlayer (ι := ι) p) := by
            have hoi2' : none ∈
                ((σ (origPlayer (ι := ι) p)).1
                  (h.playerView (origPlayer (ι := ι) p))).support := by
              simpa [h, hoi2Eq] using h₂
            exact (σ (origPlayer (ι := ι) p)).2 h hoi2'
          rw [G.mem_availableMoves_iff] at hlegal
          simp [FOSG.locallyLegalAtState, hactive, hoi2Eq] at hlegal
      | some ai₂ =>
          have hval : ai₁ = ai₂ := by
            simpa [hoi1Eq, hoi2Eq] using congrArg Subtype.val hsub
          simp [hoi1Eq, hoi2Eq, hval]

@[simp] theorem TracePosition.supportDecisionIndex_eq_actionFromIndex
    {k : Nat} {p : PlayerIx}
    (σ : G.LegalBehavioralProfile)
    (I : {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)})
    (a : Fin (Position.actionArity (G := G) I.1.toPosition))
    (hmem : some (TracePosition.actualActionFromIndex (G := G) I a) ∈
      ((σ.toProfile (origPlayer (ι := ι) p))
        ((TracePosition.originalHistory (G := G) I.1).playerView
          (origPlayer (ι := ι) p))).support) :
    TracePosition.supportDecisionIndex (G := G) σ I
      (some (TracePosition.actualActionFromIndex (G := G) I a)) hmem = a := by
  have hsub :
      TracePosition.supportActionSubtype (G := G) σ I
          (some (TracePosition.actualActionFromIndex (G := G) I a)) hmem =
        ⟨TracePosition.actualActionFromIndex (G := G) I a,
          TracePosition.actualActionFromIndex_mem_available (G := G) I a⟩ := by
    apply Subtype.ext
    rfl
  unfold TracePosition.supportDecisionIndex
  rw [hsub]
  exact (TracePosition.actionIndexEquivAvailableAction (G := G) I).symm_apply_apply _

/-- Translate a native legal behavioral strategy to the trace-backed bounded
plain EFG bridge. -/
noncomputable def translateBehavioralStrategy
    {k : Nat} (σ : G.LegalBehavioralProfile) (p : PlayerIx) :
    EFG.BehavioralStrategy (traceInfoStructure (G := G) k) p :=
  fun I =>
    let τ :=
      (σ.toProfile (origPlayer (ι := ι) p))
        ((TracePosition.originalHistory (G := G) I.1).playerView (origPlayer (ι := ι) p))
    τ.bindOnSupport (fun oi hoi =>
      PMF.pure (TracePosition.supportDecisionIndex (G := G) σ I oi hoi))

/-- Translate a native legal behavioral profile to the trace-backed bounded
plain EFG bridge. -/
noncomputable def translateBehavioralProfile
    {k : Nat} (σ : G.LegalBehavioralProfile) :
    EFG.BehavioralProfile (traceInfoStructure (G := G) k) :=
  fun p => translateBehavioralStrategy (G := G) σ p

theorem TracePosition.supportDecisionIndex_eq_some_actual
    {k : Nat} {p : PlayerIx}
    (σ : G.LegalBehavioralProfile)
    (I : {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)})
    {oi : Option (Act (origPlayer (ι := ι) p))}
    {hoi : oi ∈
      ((σ.toProfile (origPlayer (ι := ι) p))
        ((TracePosition.originalHistory (G := G) I.1).playerView
          (origPlayer (ι := ι) p))).support}
    {a : Fin (Position.actionArity (G := G) I.1.toPosition)}
    (heq : TracePosition.supportDecisionIndex (G := G) σ I oi hoi = a) :
    oi = some (TracePosition.actualActionFromIndex (G := G) I a) := by
  let h := TracePosition.originalHistory (G := G) I.1
  have hsub :
      TracePosition.supportActionSubtype (G := G) σ I oi hoi =
        ⟨TracePosition.actualActionFromIndex (G := G) I a,
          TracePosition.actualActionFromIndex_mem_available (G := G) I a⟩ := by
    have hsub' :=
      congrArg (TracePosition.actionIndexEquivAvailableAction (G := G) I) heq
    simpa [TracePosition.supportDecisionIndex] using hsub'
  cases hoiEq : oi with
  | none =>
      have hactive :
          origPlayer (ι := ι) p ∈ G.active h.lastState :=
        TracePosition.current_mem_active_of_player (G := G) I.2
      have hoi' : none ∈
          ((σ (origPlayer (ι := ι) p)).1 (h.playerView (origPlayer (ι := ι) p))).support := by
        simpa [h, hoiEq] using hoi
      have hlegal : none ∈ G.availableMoves h (origPlayer (ι := ι) p) := by
        exact (σ (origPlayer (ι := ι) p)).2 h hoi'
      rw [G.mem_availableMoves_iff] at hlegal
      simp [FOSG.locallyLegalAtState, hactive, hoiEq] at hlegal
  | some ai =>
      have hai :
          ai = TracePosition.actualActionFromIndex (G := G) I a := by
        simpa [hoiEq] using congrArg Subtype.val hsub
      simp [hoiEq, hai]

@[simp] theorem translateBehavioralStrategy_apply
    {k : Nat} (σ : G.LegalBehavioralProfile) {p : PlayerIx}
    (I : {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)})
    (a : Fin (Position.actionArity (G := G) I.1.toPosition)) :
    translateBehavioralStrategy (G := G) σ p I a =
      (σ.toProfile (origPlayer (ι := ι) p))
        ((TracePosition.originalHistory (G := G) I.1).playerView (origPlayer (ι := ι) p))
        (some (TracePosition.actualActionFromIndex (G := G) I a)) := by
  classical
  let τ :=
    (σ.toProfile (origPlayer (ι := ι) p))
      ((TracePosition.originalHistory (G := G) I.1).playerView (origPlayer (ι := ι) p))
  let oiTarget := some (TracePosition.actualActionFromIndex (G := G) I a)
  by_cases hmem : oiTarget ∈ τ.support
  · unfold translateBehavioralStrategy
    rw [PMF.bindOnSupport_apply]
    refine (tsum_eq_single oiTarget ?_).trans ?_
    · intro oi hne
      have hidx :
          ∀ h : τ oi ≠ 0, TracePosition.supportDecisionIndex (G := G) σ I oi h ≠ a := by
        intro h heq
        have hoitarget :
            oi = some (TracePosition.actualActionFromIndex (G := G) I a) :=
          TracePosition.supportDecisionIndex_eq_some_actual (G := G) σ I heq
        exact hne hoitarget
      have hif :
          (if h : τ oi = 0 then 0
            else (PMF.pure (TracePosition.supportDecisionIndex (G := G) σ I oi h)) a) = 0 := by
        split_ifs with hoi0
        · rfl
        · exact PMF.pure_apply_of_ne
            (a := TracePosition.supportDecisionIndex (G := G) σ I oi hoi0)
            (a' := a) (hidx hoi0).symm
      have hprod :
          τ oi *
              (if h : τ oi = 0 then 0
                else (PMF.pure (TracePosition.supportDecisionIndex (G := G) σ I oi h)) a) = 0 := by
        split_ifs with hoi0
        · simp [hoi0]
        · have hpure0 :
              (PMF.pure (TracePosition.supportDecisionIndex (G := G) σ I oi hoi0)) a = 0 :=
            PMF.pure_apply_of_ne
              (a := TracePosition.supportDecisionIndex (G := G) σ I oi hoi0)
              (a' := a) (hidx hoi0).symm
          simp [hpure0]
      exact hprod
    · rw [dif_neg ((PMF.mem_support_iff _ _).1 hmem)]
      rw [TracePosition.supportDecisionIndex_eq_actionFromIndex (G := G) σ I a hmem]
      simp [τ, oiTarget, PMF.pure_apply_self]
  · unfold translateBehavioralStrategy
    have hzero :
        (τ.bindOnSupport fun oi hoi =>
          PMF.pure (TracePosition.supportDecisionIndex (G := G) σ I oi hoi)) a = 0 := by
      rw [PMF.bindOnSupport_eq_zero_iff]
      intro oi hoi0
      apply PMF.pure_apply_of_ne
      intro heq
      have hoitarget :
          oi = some (TracePosition.actualActionFromIndex (G := G) I a) :=
        TracePosition.supportDecisionIndex_eq_some_actual (G := G) σ I heq.symm
      have : oiTarget ∈ τ.support := by
        simpa [oiTarget, hoitarget] using (PMF.mem_support_iff τ oi).2 hoi0
      exact hmem this
    have htarget0 : τ oiTarget = 0 := by
      by_contra hne
      exact hmem ((PMF.mem_support_iff _ _).2 hne)
    have hfinal :
        (τ.bindOnSupport fun oi hoi =>
          PMF.pure (TracePosition.supportDecisionIndex (G := G) σ I oi hoi)) a =
            τ oiTarget := by
      rw [hzero, htarget0]
    simpa [translateBehavioralStrategy, τ, oiTarget] using hfinal

@[simp] theorem translateBehavioralProfile_apply
    {k : Nat} (σ : G.LegalBehavioralProfile) (p : PlayerIx)
    (I : {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)})
    (a : Fin (Position.actionArity (G := G) I.1.toPosition)) :
    translateBehavioralProfile (G := G) σ p I a =
      (σ.toProfile (origPlayer (ι := ι) p))
        ((TracePosition.originalHistory (G := G) I.1).playerView (origPlayer (ι := ι) p))
        (some (TracePosition.actualActionFromIndex (G := G) I a)) := by
  simpa [translateBehavioralProfile] using
    (translateBehavioralStrategy_apply (G := G) σ I a)

/-- Chance successor law for a serialized position.

This is totalized on all positions, but only the `player? = none` branches are
live under `treeFrom`. The player-controlled branches return trivial self-loops
and are not used by the unrolling. -/
noncomputable def chanceStatePMF {k : Nat} (pos : Position G k) : PMF (SState G) := by
  classical
  exact
    match pos.state with
    | .base w =>
        if hterm : G.terminal w then
          PMF.pure (SerialState.base (G := G) w)
        else
          match horder : G.orderedActive w with
          | [] =>
              PMF.map (SerialState.base (G := G))
                (G.transition w (SerialState.baseChanceLegalAction (G := G) w
                  (G.active_eq_empty_of_orderedActive_eq_nil horder) hterm))
          | _ :: _ =>
              PMF.pure (SerialState.base (G := G) w)
    | .decide w chosen current rest hvalid =>
        PMF.pure (SerialState.decide w chosen current rest hvalid)
    | .chance w ga =>
        PMF.map (SerialState.base (G := G)) (G.transition w ga)

noncomputable def chanceEdgePayoff {k : Nat}
    (pos : Position G k) (dst : SState G) : PayoffVec (G := G) k := by
  classical
  exact
    match pos.state with
    | .base w =>
        if hterm : G.terminal w then
          zeroPayoff (G := G)
        else
          match horder : G.orderedActive w with
          | [] =>
              match dst with
              | .base w' =>
                  liftPayoff (G := G) <|
                    G.reward w
                      (SerialState.baseChanceLegalAction (G := G) w
                        (G.active_eq_empty_of_orderedActive_eq_nil horder) hterm)
                      w'
              | _ => zeroPayoff (G := G)
          | _ :: _ =>
              zeroPayoff (G := G)
    | .decide _ _ _ _ _ =>
        zeroPayoff (G := G)
    | .chance w ga =>
        match dst with
        | .base w' => liftPayoff (G := G) (G.reward w ga w')
        | _ => zeroPayoff (G := G)

end Position

/-- Live chance successor law for a trace-position.

This is the trace-level version of `Position.chanceStatePMF`, restricted to
states that are genuinely in a live chance configuration: no acting player, not
terminal, and not truncated. Impossible branches are discharged immediately. -/
noncomputable def TracePosition.liveChancePMF {k : Nat}
    (pos : TracePosition G k)
    (hplayer : pos.player? = none)
    (hnotTerm : ¬ (SG G).terminal pos.state)
    (hrem : pos.remaining ≠ 0) : PMF (SState G) := by
  classical
  cases hs : pos.state with
  | base w =>
      by_cases hEmpty : G.orderedActive w = []
      · exact
          PMF.map (SerialState.base (G := G))
            (G.transition w
              (SerialState.baseChanceLegalAction (G := G) w
                (G.active_eq_empty_of_orderedActive_eq_nil hEmpty) (by
                  simpa [hs] using hnotTerm)))
      · cases horder : G.orderedActive w with
        | nil =>
            exact False.elim (hEmpty horder)
        | cons current rest =>
            exfalso
            simp [TracePosition.player?, Position.player?, Position.isTruncated,
              TracePosition.toPosition, hs, horder, hrem] at hplayer
  | decide w chosen current rest hvalid =>
      exfalso
      simp [TracePosition.player?, Position.player?, Position.isTruncated,
        TracePosition.toPosition, hs, hrem] at hplayer
  | chance w ga =>
      exact PMF.map (SerialState.base (G := G)) (G.transition w ga)

theorem TracePosition.liveChancePMF_supportValue_eq_base {k : Nat}
    (pos : TracePosition G k)
    (hplayer : pos.player? = none)
    (hnotTerm : ¬ (SG G).terminal pos.state)
    (hrem : pos.remaining ≠ 0)
    (b : Fin (Fintype.card (SupportSubtype
      (TracePosition.liveChancePMF (G := G) pos hplayer hnotTerm hrem)))) :
    ∃ w' : W,
      supportValue (TracePosition.liveChancePMF (G := G) pos hplayer hnotTerm hrem) b =
        .base w' := by
  classical
  let dst := supportValue (TracePosition.liveChancePMF (G := G) pos hplayer hnotTerm hrem) b
  have hmem : dst ∈ (TracePosition.liveChancePMF (G := G) pos hplayer hnotTerm hrem).support :=
    (PMF.mem_support_iff _ _).2 (supportValue_spec _ b)
  cases hs : pos.state with
  | base w =>
      by_cases hEmpty : G.orderedActive w = []
      · have hmap :
            TracePosition.liveChancePMF (G := G) pos hplayer hnotTerm hrem =
              PMF.map (SerialState.base (G := G))
                (G.transition w
                  (SerialState.baseChanceLegalAction (G := G) w
                    (G.active_eq_empty_of_orderedActive_eq_nil hEmpty)
                    (by simpa [hs] using hnotTerm))) := by
          cases pos
          cases hs
          simp [TracePosition.liveChancePMF, hEmpty]
        rw [hmap, PMF.mem_support_map_iff] at hmem
        rcases hmem with ⟨w', -, hw'⟩
        exact ⟨w', hw'.symm⟩
      · cases horder : G.orderedActive w with
        | nil =>
            exact False.elim (hEmpty horder)
        | cons current rest =>
            exfalso
            simp [TracePosition.player?, Position.player?, Position.isTruncated,
              TracePosition.toPosition, hs, horder, hrem] at hplayer
  | decide w chosen current rest hvalid =>
      exfalso
      simp [TracePosition.player?, Position.player?, Position.isTruncated,
        TracePosition.toPosition, hs, hrem] at hplayer
  | chance w ga =>
      have hmap :
          TracePosition.liveChancePMF (G := G) pos hplayer hnotTerm hrem =
            PMF.map (SerialState.base (G := G)) (G.transition w ga) := by
        cases pos
        cases hs
        simp [TracePosition.liveChancePMF]
      rw [hmap, PMF.mem_support_map_iff] at hmem
      rcases hmem with ⟨w', -, hw'⟩
      exact ⟨w', hw'.symm⟩

theorem TracePosition.state_eq_base_empty_or_chance_of_no_player {k : Nat}
    {pos : TracePosition G k}
    (hplayer : pos.player? = none)
    (hnotTerm : ¬ (SG G).terminal pos.state)
    (hrem : pos.remaining ≠ 0) :
    (∃ w, pos.state = .base w ∧ G.orderedActive w = []) ∨
      (∃ w, ∃ ga : G.LegalAction w, pos.state = .chance w ga) := by
  classical
  cases hs : pos.state with
  | base w =>
      by_cases hEmpty : G.orderedActive w = []
      · exact Or.inl ⟨w, rfl, hEmpty⟩
      · cases horder : G.orderedActive w with
        | nil =>
            exact False.elim (hEmpty horder)
        | cons current rest =>
            exfalso
            simp [TracePosition.player?, Position.player?, Position.isTruncated,
              TracePosition.toPosition, hs, horder, hrem] at hplayer
  | decide w chosen current rest hvalid =>
      exfalso
      simp [TracePosition.player?, Position.player?, Position.isTruncated,
        TracePosition.toPosition, hs, hrem] at hplayer
  | chance w ga =>
      exact Or.inr ⟨w, ga, rfl⟩

/-- Realized serialized chance edge bundled with its source alignment. -/
noncomputable def TracePosition.chanceEdge {k : Nat}
    (pos : TracePosition G k)
    (hplayer : pos.player? = none)
    (hnotTerm : ¬ (SG G).terminal pos.state)
    (hrem : pos.remaining ≠ 0)
    (b : Fin (Fintype.card (SupportSubtype
      (TracePosition.liveChancePMF (G := G) pos hplayer hnotTerm hrem)))) :
    { e : (SG G).Step // e.src = pos.state } := by
  classical
  let w' := Classical.choose <|
    TracePosition.liveChancePMF_supportValue_eq_base (G := G) pos hplayer hnotTerm hrem b
  have hdst :
      supportValue (TracePosition.liveChancePMF (G := G) pos hplayer hnotTerm hrem) b = .base w' :=
    Classical.choose_spec <|
      TracePosition.liveChancePMF_supportValue_eq_base (G := G) pos hplayer hnotTerm hrem b
  have hsupp :
      TracePosition.liveChancePMF (G := G) pos hplayer hnotTerm hrem (.base w') ≠ 0 := by
    simpa [hdst] using supportValue_spec
      (TracePosition.liveChancePMF (G := G) pos hplayer hnotTerm hrem) b
  cases hs : pos.state with
  | base w =>
      by_cases hEmpty : G.orderedActive w = []
      · let a : (SG G).LegalAction (.base w) := by
            refine ⟨noopAction Act, ?_⟩
            exact (SerialState.legal_iff_jointActionLegal (G := G) (.base w) (noopAction Act)).mp <| by
              simpa [SerialState.legal, hEmpty, hs] using hnotTerm
        refine ⟨⟨.base w, a, .base w', ?_⟩, rfl⟩
        have hmap :
            TracePosition.liveChancePMF (G := G) pos hplayer hnotTerm hrem =
              PMF.map (SerialState.base (G := G))
                (G.transition w
                  (SerialState.baseChanceLegalAction (G := G) w
                    (G.active_eq_empty_of_orderedActive_eq_nil hEmpty)
                    (by simpa [hs] using hnotTerm))) := by
          cases pos
          cases hs
          simp [TracePosition.liveChancePMF, hEmpty]
        have hsupp' :
            PMF.map (SerialState.base (G := G))
              (G.transition w
                (SerialState.baseChanceLegalAction (G := G) w
                  (G.active_eq_empty_of_orderedActive_eq_nil hEmpty)
                  (by simpa [hs] using hnotTerm))) (.base w') ≠ 0 := by
          simpa [hmap] using hsupp
        change SerialState.transition (G := G) (.base w)
          (SerialState.ofFOSGLegalAction (G := G) a) (.base w') ≠ 0
        simpa [a, SerialState.transition, hEmpty] using hsupp'
      · cases horder : G.orderedActive w with
        | nil =>
            exact False.elim (hEmpty horder)
        | cons current rest =>
            exfalso
            simp [TracePosition.player?, Position.player?, Position.isTruncated,
              TracePosition.toPosition, hs, horder, hrem] at hplayer
  | decide w chosen current rest hvalid =>
      exfalso
      simp [TracePosition.player?, Position.player?, Position.isTruncated,
        TracePosition.toPosition, hs, hrem] at hplayer
  | chance w ga =>
      let a : (SG G).LegalAction (.chance w ga) := by
            refine ⟨noopAction Act, ?_⟩
            exact (SerialState.legal_iff_jointActionLegal (G := G) (.chance w ga) (noopAction Act)).mp <| by
              simp [SerialState.legal]
      refine ⟨⟨.chance w ga, a, .base w', ?_⟩, rfl⟩
      have hmap :
          TracePosition.liveChancePMF (G := G) pos hplayer hnotTerm hrem =
            PMF.map (SerialState.base (G := G)) (G.transition w ga) := by
        cases pos
        cases hs
        simp [TracePosition.liveChancePMF]
      have hsupp' :
          PMF.map (SerialState.base (G := G)) (G.transition w ga) (.base w') ≠ 0 := by
        simpa [hmap] using hsupp
      change SerialState.transition (G := G) (.chance w ga)
        (SerialState.ofFOSGLegalAction (G := G) a) (.base w') ≠ 0
      simpa [a, SerialState.transition] using hsupp'

/-- Realized serialized step for a live trace-position chance edge. -/
noncomputable def TracePosition.chanceStep {k : Nat}
    (pos : TracePosition G k)
    (hplayer : pos.player? = none)
    (hnotTerm : ¬ (SG G).terminal pos.state)
    (hrem : pos.remaining ≠ 0)
    (b : Fin (Fintype.card (SupportSubtype
      (TracePosition.liveChancePMF (G := G) pos hplayer hnotTerm hrem)))) :
    (SG G).Step :=
  (TracePosition.chanceEdge (G := G) pos hplayer hnotTerm hrem b).1

@[simp] theorem TracePosition.chanceStep_src {k : Nat}
    (pos : TracePosition G k)
    (hplayer : pos.player? = none)
    (hnotTerm : ¬ (SG G).terminal pos.state)
    (hrem : pos.remaining ≠ 0)
    (b : Fin (Fintype.card (SupportSubtype
      (TracePosition.liveChancePMF (G := G) pos hplayer hnotTerm hrem)))) :
    (TracePosition.chanceStep (G := G) pos hplayer hnotTerm hrem b).src = pos.state :=
  (TracePosition.chanceEdge (G := G) pos hplayer hnotTerm hrem b).2

/-- Trace-position child reached by a realized chance edge. -/
noncomputable def TracePosition.chanceChild {k : Nat}
    (pos : TracePosition G k)
    (hplayer : pos.player? = none)
    (hnotTerm : ¬ (SG G).terminal pos.state)
    (hrem : pos.remaining ≠ 0)
    (b : Fin (Fintype.card (SupportSubtype
      (TracePosition.liveChancePMF (G := G) pos hplayer hnotTerm hrem)))) :
    TracePosition G k :=
  TracePosition.appendStep (G := G) pos
    (TracePosition.chanceStep (G := G) pos hplayer hnotTerm hrem b)
    hrem (TracePosition.chanceStep_src (G := G) pos hplayer hnotTerm hrem b)

@[simp] theorem TracePosition.chanceChild_history_steps {k : Nat}
    (pos : TracePosition G k)
    (hplayer : pos.player? = none)
    (hnotTerm : ¬ (SG G).terminal pos.state)
    (hrem : pos.remaining ≠ 0)
    (b : Fin (Fintype.card (SupportSubtype
      (TracePosition.liveChancePMF (G := G) pos hplayer hnotTerm hrem)))) :
    (TracePosition.chanceChild (G := G) pos hplayer hnotTerm hrem b).history.steps =
      pos.history.steps ++ [TracePosition.chanceStep (G := G) pos hplayer hnotTerm hrem b] := by
  simpa [TracePosition.chanceChild] using
    TracePosition.appendStep_history_steps (G := G) pos
      (TracePosition.chanceStep (G := G) pos hplayer hnotTerm hrem b)
      hrem (TracePosition.chanceStep_src (G := G) pos hplayer hnotTerm hrem b)

@[simp] theorem TracePosition.chanceChild_lastState {k : Nat}
    (pos : TracePosition G k)
    (hplayer : pos.player? = none)
    (hnotTerm : ¬ (SG G).terminal pos.state)
    (hrem : pos.remaining ≠ 0)
    (b : Fin (Fintype.card (SupportSubtype
      (TracePosition.liveChancePMF (G := G) pos hplayer hnotTerm hrem)))) :
    (TracePosition.chanceChild (G := G) pos hplayer hnotTerm hrem b).history.lastState =
      (TracePosition.chanceStep (G := G) pos hplayer hnotTerm hrem b).dst := by
  simpa [TracePosition.chanceChild] using
    TracePosition.appendStep_history_lastState (G := G) pos
      (TracePosition.chanceStep (G := G) pos hplayer hnotTerm hrem b)
      hrem (TracePosition.chanceStep_src (G := G) pos hplayer hnotTerm hrem b)

@[simp] theorem TracePosition.chanceChild_remaining {k : Nat}
    (pos : TracePosition G k)
    (hplayer : pos.player? = none)
    (hnotTerm : ¬ (SG G).terminal pos.state)
    (hrem : pos.remaining ≠ 0)
    (b : Fin (Fintype.card (SupportSubtype
      (TracePosition.liveChancePMF (G := G) pos hplayer hnotTerm hrem)))) :
    (TracePosition.chanceChild (G := G) pos hplayer hnotTerm hrem b).remaining =
      pos.remaining - 1 := by
  simp [TracePosition.chanceChild]

abbrev Outcome (k : Nat) := Position G k × Position.PayoffVec (G := G) k

abbrev TraceOutcome (k : Nat) := TracePosition G k × TracePosition.PayoffVec (G := G) k

noncomputable def traceTreeFromAccum {k : Nat} (pos : TracePosition G k)
    (acc : TracePosition.PayoffVec (G := G) k) :
    GameTree (traceInfoStructure (G := G) k) (TraceOutcome (G := G) k) :=
  if hrem : pos.remaining = 0 then
    .terminal (pos, acc)
  else if hterm : (SG G).terminal pos.state then
    .terminal (pos, acc)
  else
    match hplayer : pos.player? with
    | some i =>
        let p : PlayerIx := playerEquiv (ι := ι) i
        have hp : origPlayer (ι := ι) p = i := by
          simp [p, origPlayer, playerEquiv]
        let hI : pos.player? = some (origPlayer (ι := ι) p) := by
          simpa [hp] using hplayer
        let I : {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)} :=
          ⟨pos, hI⟩
        .decision (p := p) I
          (fun a => traceTreeFromAccum (Position.TracePosition.decisionChild (G := G) I a) acc)
    | none =>
        let μ := TracePosition.liveChancePMF (G := G) pos hplayer hterm hrem
        .chance
          (Fintype.card (SupportSubtype μ))
          (supportPMF μ)
          (supportSubtype_card_pos μ)
          (fun b =>
            let child := TracePosition.chanceChild (G := G) pos hplayer hterm hrem b
            let acc' := TracePosition.addPayoff (G := G) acc
              (Position.chanceEdgePayoff (G := G) pos.toPosition child.state)
            traceTreeFromAccum child acc')
termination_by pos.remaining
decreasing_by
  all_goals
    simpa [Position.TracePosition.decisionChild_remaining, TracePosition.chanceChild_remaining,
      Nat.pred_eq_sub_one] using Nat.pred_lt hrem

noncomputable def traceTreeFrom {k : Nat} (pos : TracePosition G k) :
    GameTree (traceInfoStructure (G := G) k) (TraceOutcome (G := G) k) :=
  traceTreeFromAccum (G := G) pos (TracePosition.zeroPayoff (G := G))

/-- Bridge-side execution recursion for the trace-backed plain EFG tree under a
translated legal FOSG behavioral profile. -/
noncomputable def traceEvalDistAccum
    {k : Nat} (σ : G.LegalBehavioralProfile) (pos : TracePosition G k)
    (acc : TracePosition.PayoffVec (G := G) k) :
    PMF (TraceOutcome (G := G) k) :=
  (traceTreeFromAccum (G := G) pos acc).evalDist
    (Position.translateBehavioralProfile (G := G) σ)

theorem traceTreeFromAccum_evalDist
    {k : Nat} (σ : G.LegalBehavioralProfile) (pos : TracePosition G k)
    (acc : TracePosition.PayoffVec (G := G) k) :
    (traceTreeFromAccum (G := G) pos acc).evalDist
        (Position.translateBehavioralProfile (G := G) σ) =
      traceEvalDistAccum (G := G) σ pos acc := by
  rfl

theorem traceTreeFrom_evalDist
    {k : Nat} (σ : G.LegalBehavioralProfile) (pos : TracePosition G k) :
    (traceTreeFrom (G := G) pos).evalDist
        (Position.translateBehavioralProfile (G := G) σ) =
      traceEvalDistAccum (G := G) σ pos (TracePosition.zeroPayoff (G := G)) := by
  simpa [traceTreeFrom] using
    traceTreeFromAccum_evalDist (G := G) σ pos (TracePosition.zeroPayoff (G := G))

noncomputable def toPlainTraceEFGAtHorizon (k : Nat) : EFGGame where
  inf := traceInfoStructure (G := G) k
  Outcome := TraceOutcome (G := G) k
  tree := traceTreeFrom (G := G) (TracePosition.root (G := G) k)
  utility := fun z => z.2

@[simp] theorem toPlainTraceEFGAtHorizon_outcomeKernel
    (σ : G.LegalBehavioralProfile) (k : Nat) :
    (toPlainTraceEFGAtHorizon (G := G) k).toKernelGame.outcomeKernel
        (Position.translateBehavioralProfile (G := G) σ) =
      traceEvalDistAccum (G := G) σ (TracePosition.root (G := G) k)
        (TracePosition.zeroPayoff (G := G)) := by
  simpa [EFGGame.toKernelGame, toPlainTraceEFGAtHorizon] using
    traceTreeFrom_evalDist (G := G) (k := k) σ (TracePosition.root (G := G) k)

noncomputable def treeFromAccum {k : Nat} (pos : Position G k)
    (acc : Position.PayoffVec (G := G) k) :
    GameTree (infoStructure (G := G) k) (Outcome (G := G) k) :=
  if hrem : pos.remaining = 0 then
    .terminal (pos, acc)
  else if hterm : (SG G).terminal pos.state then
    .terminal (pos, acc)
  else
    match hplayer : pos.player? with
    | some i =>
        let p : PlayerIx := playerEquiv (ι := ι) i
        have hp : origPlayer (ι := ι) p = i := by
          simp [p, origPlayer, playerEquiv]
        let hI : pos.player? = some (origPlayer (ι := ι) p) := by
          simpa [hp] using hplayer
        let I : {pos : Position G k // pos.player? = some (origPlayer (ι := ι) p)} := ⟨pos, hI⟩
        .decision (p := p) I (fun a => treeFromAccum (Position.decisionChild G I a) acc)
    | none =>
        let μ := Position.chanceStatePMF G pos
        .chance
          (Fintype.card (SupportSubtype μ))
          (supportPMF μ)
          (supportSubtype_card_pos μ)
          (fun b =>
            let dst := supportValue μ b
            let acc' := Position.addPayoff (G := G) acc (Position.chanceEdgePayoff (G := G) pos dst)
            treeFromAccum (Position.descend G pos dst) acc')
termination_by pos.remaining
decreasing_by
  all_goals
    simpa [Position.decisionChild_remaining, Position.descend_remaining, Nat.pred_eq_sub_one] using
      Nat.pred_lt hrem

noncomputable def treeFrom {k : Nat} (pos : Position G k) :
    GameTree (infoStructure (G := G) k) (Outcome (G := G) k) :=
  treeFromAccum (G := G) pos (Position.zeroPayoff (G := G))

/-- Raw finite-horizon EFG obtained by unrolling serialized positions.

This is a structural cutoff tree. If `k` is too small, truncation at
`remaining = 0` produces EFG terminal nodes whose underlying serialized states
need not yet be terminal. The theorem-facing public API should therefore prefer
`toPlainEFGOfBoundedHorizon`. -/
noncomputable def toPlainEFGAtHorizon (k : Nat) : EFGGame where
  inf := infoStructure (G := G) k
  Outcome := Outcome (G := G) k
  tree := treeFrom (G := G) (Position.root (G := G) k)
  utility := fun z => z.2

/-- Safe serialized-step budget for a `k`-step original FOSG horizon.

Each original step expands to at most one serialized move per player, followed
by one serialized resolution step. -/
def serialHorizon (k : Nat) : Nat :=
  k * (Fintype.card ι + 1)

/-- Public plain EFG bridge under a genuine FOSG horizon bound. -/
noncomputable abbrev toPlainEFGOfBoundedHorizon
    {k : Nat} (hBound : G.BoundedHorizon k) : EFGGame :=
  toPlainTraceEFGAtHorizon (G := G) (serialHorizon (ι := ι) k)

namespace Replay

abbrev Step (k : Nat) := HistoryStep (infoStructure (G := G) k)

noncomputable def advance? {k : Nat} (pos : Position G k) :
    Step (G := G) k → Option (Position G k)
  | .action _ I a =>
      if pos = I.1 then
        some (Position.decisionChild (G := G) I a)
      else
        none
  | .chance k' b =>
      let μ := Position.chanceStatePMF (G := G) pos
      if hplayer : pos.player? = none then
        if hcard : k' = Fintype.card (SupportSubtype μ) then
          some (Position.descend (G := G) pos (supportValue μ (Fin.cast hcard b)))
        else
          none
      else
        none

noncomputable def replayFrom {k : Nat} (pos : Position G k) :
    List (Step (G := G) k) → Option (Position G k)
  | [] => some pos
  | ℓ :: hs => do
      let pos' <- advance? (G := G) pos ℓ
      replayFrom pos' hs

noncomputable def replayHist (k : Nat) :
    List (Step (G := G) k) → Option (Position G k) :=
  replayFrom (G := G) (Position.root (G := G) k)

@[simp] theorem replayFrom_nil {k : Nat} (pos : Position G k) :
    replayFrom (G := G) pos [] = some pos := rfl

@[simp] theorem replayHist_nil (k : Nat) :
    replayHist (G := G) k [] = some (Position.root (G := G) k) := rfl

@[simp] theorem replayFrom_cons {k : Nat} (pos : Position G k)
    (ℓ : Step (G := G) k) (hs : List (Step (G := G) k)) :
    replayFrom (G := G) pos (ℓ :: hs) =
      Option.bind (advance? (G := G) pos ℓ) (fun pos' => replayFrom (G := G) pos' hs) := rfl

@[simp] theorem advance?_action_eq_some {k : Nat}
    {p : PlayerIx} (I : {pos : Position G k // pos.player? = some (origPlayer (ι := ι) p)})
    (a : Fin (Position.actionArity (G := G) I.1)) :
    advance? (G := G) I.1 (.action p I a) = some (Position.decisionChild (G := G) I a) := by
  simp [advance?]

@[simp] theorem advance?_chance_eq_some {k : Nat} {pos : Position G k}
    (hplayer : pos.player? = none)
    (b : Fin (Fintype.card (SupportSubtype (Position.chanceStatePMF (G := G) pos)))) :
    advance? (G := G) pos (.chance _ b) =
      some (Position.descend (G := G) pos
        (supportValue (Position.chanceStatePMF (G := G) pos) b)) := by
  simp [advance?, hplayer]

theorem advance?_some_of_historyStepStepAccum
    {k : Nat} {pos : Position G k} {acc : Position.PayoffVec (G := G) k}
    {ℓ : Step (G := G) k} {u : GameTree (infoStructure (G := G) k) (Outcome (G := G) k)}
    (hstep : HistoryStepStep ℓ (treeFromAccum (G := G) pos acc) u) :
    ∃ pos' acc',
      advance? (G := G) pos ℓ = some pos' ∧
      u = treeFromAccum (G := G) pos' acc' := by
  classical
  cases ℓ with
  | chance k' b =>
      rcases hstep with ⟨μ, hk, next, hs, hu⟩
      unfold treeFromAccum at hs
      split at hs
      · contradiction
      · split at hs
        · contradiction
        · split at hs
          · contradiction
          · cases hs
            refine ⟨Position.descend (G := G) pos (supportValue (Position.chanceStatePMF (G := G) pos) b),
              Position.addPayoff (G := G) acc
                (Position.chanceEdgePayoff (G := G) pos
                  (supportValue (Position.chanceStatePMF (G := G) pos) b)), ?_, ?_⟩
            · simpa [advance?]
            · exact hu.trans rfl
  | action p I a =>
      rcases hstep with ⟨next, hs, hu⟩
      unfold treeFromAccum at hs
      split at hs
      · contradiction
      · split at hs
        · contradiction
        · split at hs
          · rename_i i hplayer
            cases hs
            refine ⟨Position.decisionChild (G := G)
              ⟨pos, by simpa [origPlayer, playerEquiv] using hplayer⟩ a, acc, ?_, ?_⟩
            · simpa [advance?]
            · simpa using hu
          · contradiction

theorem replayFrom_some_of_reachAccum
    {k : Nat} {pos : Position G k} {acc : Position.PayoffVec (G := G) k}
    {h : List (Step (G := G) k)}
    {node : GameTree (infoStructure (G := G) k) (Outcome (G := G) k)}
    (hr : ReachBy h (treeFromAccum (G := G) pos acc) node) :
    ∃ pos' acc',
      replayFrom (G := G) pos h = some pos' ∧
      node = treeFromAccum (G := G) pos' acc' := by
  induction h generalizing pos acc node with
  | nil =>
      cases hr
      exact ⟨pos, acc, rfl, rfl⟩
  | cons ℓ hs ih =>
      cases hr with
      | cons hstep hr' =>
          rcases advance?_some_of_historyStepStepAccum (G := G) (pos := pos) (acc := acc) hstep with
            ⟨pos₁, acc₁, hadv, hmid⟩
          cases hmid
          rcases ih (pos := pos₁) (acc := acc₁) (node := node) hr' with
            ⟨pos₂, acc₂, hrest, htarget⟩
          refine ⟨pos₂, acc₂, ?_, htarget⟩
          simp [replayFrom_cons, hadv, hrest]

theorem replayHist_some_of_reach
    {k : Nat} {h : List (Step (G := G) k)}
    {node : GameTree (infoStructure (G := G) k) (Outcome (G := G) k)}
    (hr : ReachBy h (toPlainEFGAtHorizon (G := G) k).tree node) :
    ∃ pos' acc',
      replayHist (G := G) k h = some pos' ∧
      node = treeFromAccum (G := G) pos' acc' := by
  simpa [toPlainEFGAtHorizon, replayHist] using
    (replayFrom_some_of_reachAccum (G := G)
      (pos := Position.root (G := G) k)
      (acc := Position.zeroPayoff (G := G)) hr)

noncomputable def publicStep? {k : Nat} (pos : Position G k) :
    Step (G := G) k → Option ((SG G).PublicState × Position G k)
  | .action _ I a =>
      if h : pos = I.1 then
        let pos' := Position.decisionChild (G := G) I a
        some ([none], pos')
      else
        none
  | .chance k' b =>
      let μ := Position.chanceStatePMF (G := G) pos
      if hplayer : pos.player? = none then
        if hcard : k' = Fintype.card (SupportSubtype μ) then
          let dst := supportValue μ (Fin.cast hcard b)
          let pos' := Position.descend (G := G) pos dst
          match pos.state, dst with
          | .base w, .base w' =>
              if hterm : G.terminal w then
                none
              else
                match horder : G.orderedActive w with
                | [] =>
                    let ga := SerialState.baseChanceLegalAction (G := G) w
                      (G.active_eq_empty_of_orderedActive_eq_nil horder) hterm
                    some ([some (G.pubObs w ga w')], pos')
                | _ :: _ => none
          | .chance w ga, .base w' =>
              some ([some (G.pubObs w ga w')], pos')
          | _, _ => none
        else
          none
      else
        none

noncomputable def playerStep? {k : Nat} (who : ι) (pos : Position G k) :
    Step (G := G) k → Option ((SG G).InfoState who × Position G k)
  | .action _ I a =>
      if h : pos = I.1 then
        let la := Position.actionFromIndex (G := G) (pos := I.1) a
        let pos' := Position.decisionChild (G := G) I a
        let frag :=
          match la.1 who with
          | some awho => [FOSG.PlayerEvent.act awho, FOSG.PlayerEvent.obs none none]
          | none => [FOSG.PlayerEvent.obs none none]
        some (frag, pos')
      else
        none
  | .chance k' b =>
      let μ := Position.chanceStatePMF (G := G) pos
      if hplayer : pos.player? = none then
        if hcard : k' = Fintype.card (SupportSubtype μ) then
          let dst := supportValue μ (Fin.cast hcard b)
          let pos' := Position.descend (G := G) pos dst
          match pos.state, dst with
          | .base w, .base w' =>
              if hterm : G.terminal w then
                none
              else
                match horder : G.orderedActive w with
                | [] =>
                    let ga := SerialState.baseChanceLegalAction (G := G) w
                      (G.active_eq_empty_of_orderedActive_eq_nil horder) hterm
                    some ([FOSG.PlayerEvent.obs (some (G.privObs who w ga w'))
                      (some (G.pubObs w ga w'))], pos')
                | _ :: _ => none
          | .chance w ga, .base w' =>
              some ([FOSG.PlayerEvent.obs (some (G.privObs who w ga w'))
                (some (G.pubObs w ga w'))], pos')
          | _, _ => none
        else
          none
      else
        none

noncomputable def publicViewFrom {k : Nat} (pos : Position G k) :
    List (Step (G := G) k) → Option ((SG G).PublicState × Position G k)
  | [] => some ([], pos)
  | ℓ :: hs => do
      let (frag, pos') <- publicStep? (G := G) pos ℓ
      let (rest, pos'') <- publicViewFrom pos' hs
      pure (frag ++ rest, pos'')

noncomputable def playerViewFrom {k : Nat} (who : ι) (pos : Position G k) :
    List (Step (G := G) k) → Option ((SG G).InfoState who × Position G k)
  | [] => some ([], pos)
  | ℓ :: hs => do
      let (frag, pos') <- playerStep? (G := G) who pos ℓ
      let (rest, pos'') <- playerViewFrom who pos' hs
      pure (frag ++ rest, pos'')

noncomputable def publicViewHist? (k : Nat) (h : List (Step (G := G) k)) :
    Option ((SG G).PublicState) :=
  Option.map Prod.fst (publicViewFrom (G := G) (Position.root (G := G) k) h)

noncomputable def playerViewHist? (k : Nat) (who : ι) (h : List (Step (G := G) k)) :
    Option ((SG G).InfoState who) :=
  Option.map Prod.fst (playerViewFrom (G := G) who (Position.root (G := G) k) h)

theorem publicStep?_eq_filterMap_playerStep?
    {k : Nat} (who : ι) (pos : Position G k) (ℓ : Step (G := G) k) :
    publicStep? (G := G) pos ℓ =
      Option.map (fun (out : (SG G).InfoState who × Position G k) =>
        ((out.1).filterMap (FOSG.PlayerEvent.publicPart (G := SG G) (i := who)), out.2))
        (playerStep? (G := G) who pos ℓ) := by
  classical
  cases ℓ with
  | action p I a =>
      by_cases h : pos = I.1
      · simp [publicStep?, playerStep?, h, FOSG.PlayerEvent.publicPart]
        cases hact : ((Position.actionFromIndex (G := G) (pos := I.1) a).1 who) <;>
          simp [hact]
      · simp [publicStep?, playerStep?, h]
  | chance k' b =>
      by_cases hplayer : pos.player? = none
      · by_cases hcard : k' = Fintype.card (SupportSubtype (Position.chanceStatePMF (G := G) pos))
        · simp [publicStep?, playerStep?, hplayer, hcard]
          cases pos.state <;>
            cases supportValue (Position.chanceStatePMF (G := G) pos) (Fin.cast hcard b) <;>
            repeat' (first | split | simp [FOSG.PlayerEvent.publicPart])
        · simp [publicStep?, playerStep?, hplayer, hcard]
      · simp [publicStep?, playerStep?, hplayer]

theorem publicViewFrom_eq_filterMap_playerViewFrom
    {k : Nat} (who : ι) (pos : Position G k) (h : List (Step (G := G) k)) :
    publicViewFrom (G := G) pos h =
      Option.map (fun (out : (SG G).InfoState who × Position G k) =>
        ((out.1).filterMap (FOSG.PlayerEvent.publicPart (G := SG G) (i := who)), out.2))
        (playerViewFrom (G := G) who pos h) := by
  induction h generalizing pos with
  | nil =>
      rfl
  | cons ℓ hs ih =>
      simp [publicViewFrom, playerViewFrom]
      rw [publicStep?_eq_filterMap_playerStep?]
      cases hstep : playerStep? (G := G) who pos ℓ with
      | none =>
          simp [hstep]
      | some out =>
          rcases out with ⟨frag, pos'⟩
          cases hrest : playerViewFrom (G := G) who pos' hs with
          | none =>
              simp [hstep, hrest, ih]
          | some out' =>
              rcases out' with ⟨rest, pos''⟩
              simp [hstep, hrest, ih, List.filterMap_append]

theorem publicViewHist?_eq_filterMap_playerViewHist?
    {k : Nat} (who : ι) (h : List (Step (G := G) k)) :
    publicViewHist? (G := G) k h =
      Option.map (fun xs =>
        List.filterMap (FOSG.PlayerEvent.publicPart (G := SG G) (i := who)) xs)
        (playerViewHist? (G := G) k who h) := by
  simpa [publicViewHist?, playerViewHist?, Function.comp] using
    congrArg (Option.map Prod.fst)
      (publicViewFrom_eq_filterMap_playerViewFrom
        (G := G) who (Position.root (G := G) k) h)

end Replay

namespace TraceReplay

abbrev Step (k : Nat) := HistoryStep (traceInfoStructure (G := G) k)

noncomputable def advance? {k : Nat} (pos : TracePosition G k) :
    Step (G := G) k → Option (TracePosition G k)
  | .action _ I a =>
      if pos = I.1 then
        some (Position.TracePosition.decisionChild (G := G) I a)
      else
        none
  | .chance k' b =>
      if hplayer : pos.player? = none then
        if hrem : pos.remaining = 0 then
          none
        else if hterm : (SG G).terminal pos.state then
          none
        else
          let μ := TracePosition.liveChancePMF (G := G) pos hplayer hterm hrem
          if hcard : k' = Fintype.card (SupportSubtype μ) then
            some (TracePosition.chanceChild (G := G) pos hplayer hterm hrem (Fin.cast hcard b))
          else
            none
      else
        none

noncomputable def replayFrom {k : Nat} (pos : TracePosition G k) :
    List (Step (G := G) k) → Option (TracePosition G k)
  | [] => some pos
  | ℓ :: hs => do
      let pos' <- advance? (G := G) pos ℓ
      replayFrom pos' hs

noncomputable def replayHist (k : Nat) :
    List (Step (G := G) k) → Option (TracePosition G k) :=
  replayFrom (G := G) (TracePosition.root (G := G) k)

@[simp] theorem replayFrom_nil {k : Nat} (pos : TracePosition G k) :
    replayFrom (G := G) pos [] = some pos := rfl

@[simp] theorem replayHist_nil (k : Nat) :
    replayHist (G := G) k [] = some (TracePosition.root (G := G) k) := rfl

@[simp] theorem replayFrom_cons {k : Nat} (pos : TracePosition G k)
    (ℓ : Step (G := G) k) (hs : List (Step (G := G) k)) :
    replayFrom (G := G) pos (ℓ :: hs) =
      Option.bind (advance? (G := G) pos ℓ) (fun pos' => replayFrom (G := G) pos' hs) := rfl

@[simp] theorem advance?_action_eq_some {k : Nat}
    {p : PlayerIx}
    (I : {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)})
    (a : Fin (Position.actionArity (G := G) I.1.toPosition)) :
    advance? (G := G) I.1 (.action p I a) =
      some (Position.TracePosition.decisionChild (G := G) I a) := by
  simp [advance?]

@[simp] theorem advance?_chance_eq_some {k : Nat} {pos : TracePosition G k}
    (hplayer : pos.player? = none)
    (hrem : pos.remaining ≠ 0)
    (hterm : ¬ (SG G).terminal pos.state)
    (b : Fin (Fintype.card (SupportSubtype
      (TracePosition.liveChancePMF (G := G) pos hplayer hterm hrem)))) :
    advance? (G := G) pos (.chance _ b) =
      some (TracePosition.chanceChild (G := G) pos hplayer hterm hrem b) := by
  simp [advance?, hplayer, hrem, hterm]

theorem advance?_some_of_historyStepStepAccum
    {k : Nat} {pos : TracePosition G k} {acc : TracePosition.PayoffVec (G := G) k}
    {ℓ : Step (G := G) k}
    {u : GameTree (traceInfoStructure (G := G) k) (TraceOutcome (G := G) k)}
    (hstep : HistoryStepStep ℓ (traceTreeFromAccum (G := G) pos acc) u) :
    ∃ pos' acc',
      advance? (G := G) pos ℓ = some pos' ∧
      u = traceTreeFromAccum (G := G) pos' acc' := by
  classical
  cases ℓ with
  | chance k' b =>
      rcases hstep with ⟨μ, hk, next, hs, hu⟩
      unfold traceTreeFromAccum at hs
      split at hs
      · contradiction
      · split at hs
        · contradiction
        · split at hs
          · contradiction
          · cases hs
            rename_i hrem hterm hplayer
            refine ⟨TracePosition.chanceChild (G := G) pos hplayer hterm hrem b,
              TracePosition.addPayoff (G := G) acc
                (Position.chanceEdgePayoff (G := G) pos.toPosition
                  (TracePosition.chanceChild (G := G) pos hplayer hterm hrem b).state),
              ?_, ?_⟩
            · simpa [advance?, hplayer, hrem, hterm]
            · exact hu.trans rfl
  | action p I a =>
      rcases hstep with ⟨next, hs, hu⟩
      unfold traceTreeFromAccum at hs
      split at hs
      · contradiction
      · split at hs
        · contradiction
        · split at hs
          · rename_i i hplayer
            cases hs
            refine ⟨Position.TracePosition.decisionChild (G := G)
              ⟨pos, by simpa [origPlayer, playerEquiv] using hplayer⟩ a, acc, ?_, ?_⟩
            · simpa [advance?]
            · simpa using hu
          · contradiction

theorem replayFrom_some_of_reachAccum
    {k : Nat} {pos : TracePosition G k} {acc : TracePosition.PayoffVec (G := G) k}
    {h : List (Step (G := G) k)}
    {node : GameTree (traceInfoStructure (G := G) k) (TraceOutcome (G := G) k)}
    (hr : ReachBy h (traceTreeFromAccum (G := G) pos acc) node) :
    ∃ pos' acc',
      replayFrom (G := G) pos h = some pos' ∧
      node = traceTreeFromAccum (G := G) pos' acc' := by
  induction h generalizing pos acc node with
  | nil =>
      cases hr
      exact ⟨pos, acc, rfl, rfl⟩
  | cons ℓ hs ih =>
      cases hr with
      | cons hstep hr' =>
          rcases advance?_some_of_historyStepStepAccum (G := G) (pos := pos) (acc := acc) hstep with
            ⟨pos₁, acc₁, hadv, hmid⟩
          cases hmid
          rcases ih (pos := pos₁) (acc := acc₁) (node := node) hr' with
            ⟨pos₂, acc₂, hrest, htarget⟩
          refine ⟨pos₂, acc₂, ?_, htarget⟩
          simp [replayFrom_cons, hadv, hrest]

theorem replayHist_some_of_reach
    {k : Nat} {h : List (Step (G := G) k)}
    {node : GameTree (traceInfoStructure (G := G) k) (TraceOutcome (G := G) k)}
    (hr : ReachBy h (toPlainTraceEFGAtHorizon (G := G) k).tree node) :
    ∃ pos' acc',
      replayHist (G := G) k h = some pos' ∧
      node = traceTreeFromAccum (G := G) pos' acc' := by
  simpa [toPlainTraceEFGAtHorizon, replayHist] using
    (replayFrom_some_of_reachAccum (G := G)
      (pos := TracePosition.root (G := G) k)
      (acc := TracePosition.zeroPayoff (G := G)) hr)

noncomputable def publicViewHist? (k : Nat) (h : List (Step (G := G) k)) :
    Option G.PublicState :=
  Option.map (fun pos => TracePosition.originalPublicView (G := G) pos)
    (replayHist (G := G) k h)

noncomputable def playerViewHist? (k : Nat) (who : ι) (h : List (Step (G := G) k)) :
    Option (G.InfoState who) :=
  Option.map (fun pos => TracePosition.originalPlayerView (G := G) pos who)
    (replayHist (G := G) k h)

theorem publicViewHist?_eq_filterMap_playerViewHist?
    {k : Nat} (who : ι) (h : List (Step (G := G) k)) :
    publicViewHist? (G := G) k h =
      Option.map (fun xs =>
        List.filterMap (FOSG.PlayerEvent.publicPart (G := G) (i := who)) xs)
        (playerViewHist? (G := G) k who h) := by
  unfold publicViewHist? playerViewHist?
  cases hreplay : replayHist (G := G) k h with
  | none =>
      simp [hreplay]
  | some pos =>
      simpa [TracePosition.originalPublicView, TracePosition.originalPlayerView] using
        congrArg some
          (TracePosition.originalPublicViewFrom_eq_filterMap_originalPlayerViewFrom
            (G := G) who pos.history.steps)

end TraceReplay

/-- Thin augmented wrapper over the raw finite-horizon plain bridge.

At this stage, the bridge exposes the serialized public/player views decoded
from the unrolled EFG history. Replay success and semantic preservation are
still separate theorem work, but the augmentation itself is no longer the raw
EFG history scaffold. -/
noncomputable def toAugmentedAtHorizon (k : Nat) : EFG.AugmentedGame where
  base := toPlainEFGAtHorizon (G := G) k
  PubState := List (HistoryStep (infoStructure (G := G) k)) × Option ((SG G).PublicState)
  InfoState := fun p =>
    List (HistoryStep (infoStructure (G := G) k)) × Option ((SG G).InfoState (origPlayer (ι := ι) p))
  publicState := fun h => (h.hist, Replay.publicViewHist? (G := G) k h.hist)
  playerState := fun p h => (h.hist, Replay.playerViewHist? (G := G) k (origPlayer (ι := ι) p) h.hist)
  publicOf := fun p s =>
    (s.1, Option.map
      (fun xs => List.filterMap
        (FOSG.PlayerEvent.publicPart (G := SG G) (i := origPlayer (ι := ι) p)) xs) s.2)
  publicOf_playerState := by
    intro p h
    change
      (h.hist,
        Option.map
          (fun xs =>
            List.filterMap
              (FOSG.PlayerEvent.publicPart (G := SG G) (i := origPlayer (ι := ι) p)) xs)
          (Replay.playerViewHist? (G := G) k (origPlayer (ι := ι) p) h.hist)) =
      (h.hist, Replay.publicViewHist? (G := G) k h.hist)
    symm
    simpa using congrArg (Prod.mk h.hist)
      (Replay.publicViewHist?_eq_filterMap_playerViewHist?
        (G := G) (who := origPlayer (ι := ι) p) (h := h.hist))
  actionIdentified := by
    intro p d₁ d₂ hEq
    cases d₁ with
    | mk hist₁ I₁ next₁ reach₁ =>
        cases d₂ with
        | mk hist₂ I₂ next₂ reach₂ =>
            have hhist : hist₁ = hist₂ := by
              exact congrArg Prod.fst hEq
            subst hhist
            have hnode :
                GameTree.decision I₁ next₁ = GameTree.decision I₂ next₂ := by
              exact EFG.reachBy_deterministic reach₁ reach₂
            cases hnode
            rfl

@[simp] theorem forget_toAugmentedAtHorizon (k : Nat) :
    (toAugmentedAtHorizon (G := G) k).forget = toPlainEFGAtHorizon (G := G) k := by
  rfl

/-- Public augmented-EFG bridge under a genuine FOSG horizon bound. -/
noncomputable def toAugmentedTraceAtHorizon (k : Nat) : EFG.AugmentedGame where
  base := toPlainTraceEFGAtHorizon (G := G) k
  PubState := List (HistoryStep (traceInfoStructure (G := G) k)) × Option G.PublicState
  InfoState := fun p =>
    List (HistoryStep (traceInfoStructure (G := G) k)) ×
      Option (G.InfoState (origPlayer (ι := ι) p))
  publicState := fun h => (h.hist, TraceReplay.publicViewHist? (G := G) k h.hist)
  playerState := fun p h =>
    (h.hist, TraceReplay.playerViewHist? (G := G) k (origPlayer (ι := ι) p) h.hist)
  publicOf := fun p s =>
    (s.1, Option.map
      (fun xs => List.filterMap
        (FOSG.PlayerEvent.publicPart (G := G) (i := origPlayer (ι := ι) p)) xs) s.2)
  publicOf_playerState := by
    intro p h
    change
      (h.hist,
        Option.map
          (fun xs =>
            List.filterMap
              (FOSG.PlayerEvent.publicPart (G := G) (i := origPlayer (ι := ι) p)) xs)
          (TraceReplay.playerViewHist? (G := G) k (origPlayer (ι := ι) p) h.hist)) =
      (h.hist, TraceReplay.publicViewHist? (G := G) k h.hist)
    symm
    simpa using congrArg (Prod.mk h.hist)
      (TraceReplay.publicViewHist?_eq_filterMap_playerViewHist?
        (G := G) (who := origPlayer (ι := ι) p) (h := h.hist))
  actionIdentified := by
    intro p d₁ d₂ hEq
    cases d₁ with
    | mk hist₁ I₁ next₁ reach₁ =>
        cases d₂ with
        | mk hist₂ I₂ next₂ reach₂ =>
            have hhist : hist₁ = hist₂ := by
              exact congrArg Prod.fst hEq
            subst hhist
            have hnode :
                GameTree.decision I₁ next₁ = GameTree.decision I₂ next₂ := by
              exact EFG.reachBy_deterministic reach₁ reach₂
            cases hnode
            rfl

@[simp] theorem forget_toAugmentedTraceAtHorizon (k : Nat) :
    (toAugmentedTraceAtHorizon (G := G) k).forget = toPlainTraceEFGAtHorizon (G := G) k := by
  rfl

noncomputable abbrev toAugmentedOfBoundedHorizon
    {k : Nat} (hBound : G.BoundedHorizon k) : EFG.AugmentedGame :=
  toAugmentedTraceAtHorizon (G := G) (serialHorizon (ι := ι) k)

@[simp] theorem forget_toAugmentedOfBoundedHorizon
    {k : Nat} (hBound : G.BoundedHorizon k) :
    (toAugmentedOfBoundedHorizon (G := G) hBound).forget =
      toPlainEFGOfBoundedHorizon (G := G) hBound := by
  simpa [toAugmentedOfBoundedHorizon, toPlainEFGOfBoundedHorizon] using
    (forget_toAugmentedTraceAtHorizon (G := G) (k := serialHorizon (ι := ι) k))

end Labels

end AugmentedEFGBridge

end FOSG

end GameTheory
