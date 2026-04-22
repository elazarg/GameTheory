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

abbrev PlayerIx := Fin (Fintype.card ι)

noncomputable def playerEquiv : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι

noncomputable def origPlayer (p : Fin (Fintype.card ι)) : ι := (playerEquiv (ι := ι)).symm p

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

abbrev Outcome (k : Nat) := Position G k × Position.PayoffVec (G := G) k

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

/-- Public plain EFG bridge under a genuine FOSG horizon bound. -/
noncomputable abbrev toPlainEFGOfBoundedHorizon
    {k : Nat} (hBound : G.BoundedHorizon k) : EFGGame :=
  toPlainEFGAtHorizon (G := G) k

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

/- TODO:
Add the one-step replay lemma
`HistoryStepStep ℓ (treeFrom pos) u -> ∃ pos', advance? pos ℓ = some pos' ∧ u = treeFrom pos'`
and then extend it to a full reachable-history theorem:
`ReachBy h (treeFrom pos) node -> ∃ pos', replayFrom pos h = some pos'`.
The remaining work is a list-induction theorem on `ReachBy` that composes the
one-step lemma with `replayFrom_cons`. -/

end Replay

/-- Thin augmented wrapper over the raw finite-horizon plain bridge.

At this stage, the augmentation is the reachable EFG history itself. This keeps
the forgetful classical game definitionally equal to `toPlainEFGAtHorizon`,
while the replay layer above provides the structural hook for later refinement
to serialized FOSG public/player views. This is a scaffold layer, not yet the
actual paper-level augmentation. -/
noncomputable def toAugmentedAtHorizon (k : Nat) : EFG.AugmentedGame where
  base := toPlainEFGAtHorizon (G := G) k
  PubState := List (HistoryStep (infoStructure (G := G) k))
  InfoState := fun _ => List (HistoryStep (infoStructure (G := G) k))
  publicState := fun h => h.hist
  playerState := fun _ h => h.hist
  publicOf := fun _ s => s
  publicOf_playerState := by
    intro p h
    rfl
  actionIdentified := by
    intro p d₁ d₂ hEq
    cases d₁ with
    | mk hist₁ I₁ next₁ reach₁ =>
        cases d₂ with
        | mk hist₂ I₂ next₂ reach₂ =>
            cases hEq
            have hnode :
                GameTree.decision I₁ next₁ = GameTree.decision I₂ next₂ := by
              exact EFG.reachBy_deterministic reach₁ reach₂
            cases hnode
            rfl

@[simp] theorem forget_toAugmentedAtHorizon (k : Nat) :
    (toAugmentedAtHorizon (G := G) k).forget = toPlainEFGAtHorizon (G := G) k := rfl

/-- Public augmented-EFG bridge under a genuine FOSG horizon bound. -/
noncomputable abbrev toAugmentedOfBoundedHorizon
    {k : Nat} (hBound : G.BoundedHorizon k) : EFG.AugmentedGame :=
  toAugmentedAtHorizon (G := G) k

@[simp] theorem forget_toAugmentedOfBoundedHorizon
    {k : Nat} (hBound : G.BoundedHorizon k) :
    (toAugmentedOfBoundedHorizon (G := G) hBound).forget =
      toPlainEFGOfBoundedHorizon (G := G) hBound := rfl

end Labels

end AugmentedEFGBridge

end FOSG

end GameTheory
