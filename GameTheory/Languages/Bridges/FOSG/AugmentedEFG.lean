import GameTheory.Languages.Bridges.FOSG.SerialExec
import GameTheory.Languages.EFG.Augmented
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# GameTheory.Languages.Bridges.FOSG.AugmentedEFG

Small FOSG -> augmented-EFG bridge.

The semantic spine is `SerialExec`: outcomes are native FOSG histories, and the
bridge tree is only a finite EFG presentation of the original-step process.  The
tree presents each simultaneous FOSG step as one decision opportunity per
player, followed by a chance node for the original transition.  Inactive players
have only `none` in the support of translated legal FOSG strategies.
-/

namespace GameTheory

namespace FOSG

namespace AugmentedEFGBridge

open EFG
open Math.Probability

variable {ι W : Type} [DecidableEq ι] [Fintype ι]
variable {Act : ι → Type} [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]
variable {PrivObs : ι → Type} {PubObs : Type}
variable (G : FOSG ι W Act PrivObs PubObs)
variable [Fintype W] [DecidablePred G.terminal]

/-- EFG player indices corresponding to original FOSG players. -/
abbrev PlayerIx := Fin (Fintype.card ι)

/-- Noncomputable equivalence between original players and finite EFG players. -/
noncomputable def playerEquiv : ι ≃ PlayerIx (ι := ι) :=
  Fintype.equivFin ι

/-- Recover the original FOSG player represented by an EFG player index. -/
noncomputable def origPlayer (p : PlayerIx (ι := ι)) : ι :=
  (playerEquiv (ι := ι)).symm p

omit [DecidableEq ι] in
@[simp] theorem origPlayer_playerEquiv (i : ι) :
    origPlayer (ι := ι) (playerEquiv (ι := ι) i) = i := by
  simp [origPlayer, playerEquiv]

/-- Conservative serialized budget for one original step per active player plus
one chance resolution.  The public API is original-step based, so this value is
kept only as a scheduling bound. -/
def serialHorizon (k : Nat) : Nat :=
  k * (Fintype.card ι + 1)

/-- Fixed-width finite word used to make bounded views finite. -/
abbrev Word (α : Type) (n : Nat) := Fin n → Option α

namespace Word

/-- Encode a finite list into a fixed-width word, truncating past the width. -/
def ofList {α : Type} (n : Nat) (xs : List α) : Word α n :=
  fun i => xs[i.1]?

/-- Decode a fixed-width word back to the list of populated entries. -/
def toList {α : Type} {n : Nat} (w : Word α n) : List α :=
  (List.finRange n).filterMap w

theorem toList_ofList_eq_self {α : Type} {n : Nat} (xs : List α)
    (hxs : xs.length ≤ n) :
    toList (ofList n xs) = xs := by
  revert xs
  induction n with
  | zero =>
      intro xs hxs
      have hnil : xs = [] := by
        cases xs with
        | nil => rfl
        | cons _ xs => simp at hxs
      subst hnil
      simp [toList, ofList]
  | succ n ih =>
      intro xs hxs
      cases xs with
      | nil =>
          simp [toList, ofList]
      | cons x xs =>
          have htail : xs.length ≤ n := by simpa using Nat.succ_le_succ_iff.mp hxs
          simp only [toList, ofList, List.finRange_succ, Fin.coe_ofNat_eq_mod,
            Nat.zero_mod, List.length_cons, lt_add_iff_pos_left, Order.lt_add_one_iff,
            zero_le, getElem?_pos, List.getElem_cons_zero, Option.some.injEq,
            List.filterMap_cons_some, List.filterMap_map, Function.comp_apply,
            Fin.val_succ, List.getElem?_cons_succ, List.cons.injEq, true_and]
          exact ih xs htail

end Word

noncomputable instance instDecidableEqPlayerEvent
    {i : ι} [DecidableEq (Act i)] [DecidableEq (PrivObs i)] [DecidableEq PubObs] :
    DecidableEq (PlayerEvent G i) :=
  Classical.decEq _

noncomputable instance instFintypePlayerEvent
    {i : ι} [Fintype (PrivObs i)] [DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs] :
    Fintype (PlayerEvent G i) := by
  classical
  exact Fintype.ofEquiv (Act i ⊕ PrivObs i × PubObs)
    { toFun := fun x =>
        match x with
        | Sum.inl a => .act a
        | Sum.inr obs => .obs obs.1 obs.2
      invFun := fun e =>
        match e with
        | .act a => Sum.inl a
        | .obs priv pub => Sum.inr (priv, pub)
      left_inv := by
        intro x
        cases x <;> rfl
      right_inv := by
        intro e
        cases e <;> rfl }

/-- Player-view infosets are bounded encodings of original FOSG player views. -/
abbrev EncPlayerView
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    (i : ι) (k : Nat) :=
  Word (PlayerEvent G i) (2 * k)

/-- Public states are bounded encodings of original FOSG public views. -/
abbrev EncPublicView
    [Fintype PubObs] [DecidableEq PubObs] (k : Nat) :=
  Word PubObs k

noncomputable def encodePlayerView
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    {k : Nat} (h : G.History) (i : ι) : EncPlayerView (G := G) i k :=
  Word.ofList (2 * k) (h.playerView i)

def encodePublicView
    [Fintype PubObs] [DecidableEq PubObs]
    {k : Nat} (h : G.History) : EncPublicView (PubObs := PubObs) k :=
  Word.ofList k h.publicView

omit [Fintype ι] [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)] [Fintype W]
  [DecidablePred G.terminal] in
theorem step_playerView_length_le_two
    (e : G.Step) (i : ι) : (e.playerView i).length ≤ 2 := by
  unfold Step.playerView
  split <;> simp

omit [Fintype ι] [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)] [Fintype W]
  [DecidablePred G.terminal] in
theorem playerViewFrom_length_le_two_mul
    (es : List G.Step) (i : ι) :
    (History.playerViewFrom (G := G) i es).length ≤ 2 * es.length := by
  induction es with
  | nil =>
      simp [History.playerViewFrom]
  | cons e es ih =>
      simp only [History.playerViewFrom, List.length_append, List.length_cons]
      have hstep := step_playerView_length_le_two (G := G) e i
      omega

omit [Fintype ι] [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)] [Fintype W]
  [DecidablePred G.terminal] in
theorem history_playerView_length_le_two_mul_steps
    (h : G.History) (i : ι) :
    (h.playerView i).length ≤ 2 * h.steps.length := by
  simpa [History.playerView] using
    playerViewFrom_length_le_two_mul (G := G) h.steps i

/-- Information structure for the bridge tree.  Decision infosets are encoded
original player views; actions are optional local moves.  Invalid optional moves
are totalized in the tree but get zero probability under translated legal FOSG
profiles. -/
noncomputable def infoStructure
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    (k : Nat) : InfoStructure where
  n := Fintype.card ι
  Infoset := fun p => EncPlayerView (G := G) (origPlayer (ι := ι) p) k
  arity := fun p _ => Fintype.card (Option (Act (origPlayer (ι := ι) p)))
  arity_pos := by
    intro p _
    exact Fintype.card_pos_iff.mpr ⟨none⟩

/-- Decode an EFG action index into the optional original move it represents. -/
noncomputable def actionOfIndex
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    {k : Nat} {p : PlayerIx (ι := ι)}
    (I : (infoStructure (G := G) k).Infoset p)
    (a : (infoStructure (G := G) k).Act I) : Option (Act (origPlayer (ι := ι) p)) :=
  (Fintype.equivFin (Option (Act (origPlayer (ι := ι) p)))).symm a

/-- Encode an optional original move as an EFG action index. -/
noncomputable def indexOfAction
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    {k : Nat} {p : PlayerIx (ι := ι)}
    (I : (infoStructure (G := G) k).Infoset p)
    (a : Option (Act (origPlayer (ι := ι) p))) :
    (infoStructure (G := G) k).Act I :=
  Fintype.equivFin (Option (Act (origPlayer (ι := ι) p))) a

omit [Fintype W] [DecidablePred G.terminal] in
@[simp] theorem actionOfIndex_indexOfAction
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    {k : Nat} {p : PlayerIx (ι := ι)}
    (I : (infoStructure (G := G) k).Infoset p)
    (a : Option (Act (origPlayer (ι := ι) p))) :
    actionOfIndex (G := G) I (indexOfAction (G := G) I a) = a := by
  simp [actionOfIndex, indexOfAction]

theorem fintype_card_pos_of_pmf {α : Type} [Fintype α] (p : PMF α) :
    0 < Fintype.card α := by
  classical
  rcases p.support_nonempty with ⟨a, _ha⟩
  exact Fintype.card_pos_iff.mpr ⟨a⟩

namespace Tree

variable [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
variable [Fintype PubObs] [DecidableEq PubObs]

abbrev PayoffVec (k : Nat) := Payoff (infoStructure (G := G) k).Player

/-- Replace one player's optional move in a partial joint action. -/
def recordOption (chosen : JointAction Act) (i : ι) (a : Option (Act i)) :
    JointAction Act :=
  fun j =>
    if h : j = i then
      h ▸ a
    else
      chosen j

/-- Default legal action used to totalize invalid EFG branches.  Translated
legal FOSG strategies put zero mass on those branches. -/
noncomputable def legalize
    (h : G.History) (hnot : ¬ G.terminal h.lastState) (chosen : JointAction Act) :
    G.LegalAction h.lastState := by
  classical
  by_cases hc : G.legal h.lastState chosen
  · exact ⟨chosen, hc⟩
  · let a0 := Classical.choose (G.nonterminal_exists_legal hnot)
    exact ⟨a0, Classical.choose_spec (G.nonterminal_exists_legal hnot)⟩

/-- Present the simultaneous move as sequential EFG decisions, then continue
with the assembled partial joint action. -/
noncomputable def choosePlayers
    (k : Nat) (h : G.History) : List (PlayerIx (ι := ι)) → JointAction Act →
      (JointAction Act → GameTree (infoStructure (G := G) k) (SerialExec.State G)) →
      GameTree (infoStructure (G := G) k) (SerialExec.State G)
  | [], chosen, cont => cont chosen
  | p :: rest, chosen, cont =>
      let i := origPlayer (ι := ι) p
      let I : (infoStructure (G := G) k).Infoset p :=
        encodePlayerView (G := G) h i
      .decision I (fun aIx =>
        let aOpt : Option (Act i) := actionOfIndex (G := G) I aIx
        choosePlayers k h rest
          (recordOption (Act := Act) chosen i aOpt) cont)

/-- Tree for original-step execution from a native history.  The outer
recursion consumes original FOSG steps; the inner recursion presents one
decision opportunity per player. -/
noncomputable def fromHistory
    (k : Nat) : Nat → G.History → GameTree (infoStructure (G := G) k) (SerialExec.State G)
  | 0, h => .terminal h
  | remaining + 1, h =>
      if hterm : G.terminal h.lastState then
        .terminal h
      else
        choosePlayers (G := G) k h (List.finRange (Fintype.card ι))
          (noopAction Act)
          (fun chosen =>
            let a := legalize (G := G) h hterm chosen
            let μ := G.transition h.lastState a
            .chance (Fintype.card W) (PMF.map (Fintype.equivFin W) μ)
              (fintype_card_pos_of_pmf μ)
              (fun b =>
                let dst := (Fintype.equivFin W).symm b
                let h' := h.extendByOutcome a dst
                fromHistory k remaining h'))

end Tree

@[simp] theorem tree_fromHistory_zero
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    (k : Nat) (h : G.History) :
    Tree.fromHistory (G := G) k 0 h =
      (GameTree.terminal h :
        GameTree (infoStructure (G := G) k) (SerialExec.State G)) := by
  simp [Tree.fromHistory]

@[simp] theorem tree_fromHistory_succ_terminal
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    (k n : Nat) (h : G.History) (hterm : G.terminal h.lastState) :
    Tree.fromHistory (G := G) k (n + 1) h =
      (GameTree.terminal h :
        GameTree (infoStructure (G := G) k) (SerialExec.State G)) := by
  simp [Tree.fromHistory, hterm]

theorem tree_fromHistory_succ_nonterminal
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    (k n : Nat) (h : G.History) (hnot : ¬ G.terminal h.lastState) :
    Tree.fromHistory (G := G) k (n + 1) h =
      Tree.choosePlayers (G := G) k h (List.finRange (Fintype.card ι))
        (noopAction Act)
        (fun chosen =>
          let a := Tree.legalize (G := G) h hnot chosen
          let μ := G.transition h.lastState a
          GameTree.chance (Fintype.card W) (PMF.map (Fintype.equivFin W) μ)
            (fintype_card_pos_of_pmf μ)
            (fun b =>
              let dst := (Fintype.equivFin W).symm b
              let h' := h.extendByOutcome a dst
              Tree.fromHistory (G := G) k n h')) := by
  simp [Tree.fromHistory, hnot]

@[simp] theorem tree_eval_zero
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    (k : Nat) (h : G.History) (σ : EFG.BehavioralProfile (infoStructure (G := G) k)) :
    (Tree.fromHistory (G := G) k 0 h).evalDist σ = PMF.pure h := by
  simp

/-- Plain EFG presentation of the finite-horizon FOSG execution process. -/
noncomputable def toPlainEFGAtHorizon
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    (k : Nat) : EFGGame where
  inf := infoStructure (G := G) k
  Outcome := SerialExec.State G
  tree := Tree.fromHistory (G := G) k k (SerialExec.root G)
  utility := fun h p => History.utility h (origPlayer (ι := ι) p)

@[simp] theorem toPlainEFGAtHorizon_zero_outcomeKernel
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    (σ : EFG.BehavioralProfile (toPlainEFGAtHorizon (G := G) 0).inf) :
    (toPlainEFGAtHorizon (G := G) 0).toKernelGame.outcomeKernel σ =
      PMF.pure (SerialExec.root G) := by
  change (Tree.fromHistory (G := G) 0 0 (SerialExec.root G)).evalDist σ =
    PMF.pure (SerialExec.root G)
  rw [tree_fromHistory_zero]
  rfl

/-- Bounded-horizon wrapper for the plain bridge.  The proposition is used by
terminal-support theorems; the tree itself is horizon-parametric. -/
noncomputable def toPlainEFGOfBoundedHorizon
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    {k : Nat} (_hBound : G.BoundedHorizon k) : EFGGame :=
  toPlainEFGAtHorizon (G := G) k

/-- Translate a legal FOSG behavioral profile to the EFG presentation. -/
noncomputable def translateBehavioralProfile
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    {k : Nat} (σ : G.LegalBehavioralProfile) :
    EFG.BehavioralProfile (infoStructure (G := G) k) :=
  fun p I =>
    let i := origPlayer (ι := ι) p
    let view : G.InfoState i := Word.toList I
    PMF.map (indexOfAction (G := G) I) (σ.toProfile i view)

@[simp] theorem tree_eval_zero_eq_runDistFrom_zero
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    (k : Nat) (σ : G.LegalBehavioralProfile) (h : G.History) :
    (Tree.fromHistory (G := G) k 0 h).evalDist
        (translateBehavioralProfile (G := G) σ) =
      History.runDistFrom G σ 0 h := by
  simp

@[simp] theorem tree_eval_succ_terminal_eq_runDistFrom
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    (k n : Nat) (σ : G.LegalBehavioralProfile) (h : G.History)
    (hterm : G.terminal h.lastState) :
    (Tree.fromHistory (G := G) k (n + 1) h).evalDist
        (translateBehavioralProfile (G := G) σ) =
      History.runDistFrom G σ (n + 1) h := by
  simp [hterm]

theorem tree_eval_succ_nonterminal_unfold
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    (k n : Nat) (σ : G.LegalBehavioralProfile) (h : G.History)
    (hnot : ¬ G.terminal h.lastState) :
    (Tree.fromHistory (G := G) k (n + 1) h).evalDist
        (translateBehavioralProfile (G := G) σ) =
      (Tree.choosePlayers (G := G) k h (List.finRange (Fintype.card ι))
        (noopAction Act)
        (fun chosen =>
          let a := Tree.legalize (G := G) h hnot chosen
          let μ := G.transition h.lastState a
          GameTree.chance (Fintype.card W) (PMF.map (Fintype.equivFin W) μ)
            (fintype_card_pos_of_pmf μ)
            (fun b =>
              let dst := (Fintype.equivFin W).symm b
              let h' := h.extendByOutcome a dst
              Tree.fromHistory (G := G) k n h'))).evalDist
        (translateBehavioralProfile (G := G) σ) := by
  rw [tree_fromHistory_succ_nonterminal (G := G) k n h hnot]

omit [Fintype W] [DecidablePred G.terminal] in
theorem choosePlayers_nil_evalDist
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    {k : Nat} (σ : G.LegalBehavioralProfile) (h : G.History)
    (chosen : JointAction Act)
    (cont : JointAction Act → GameTree (infoStructure (G := G) k) (SerialExec.State G)) :
    (Tree.choosePlayers (G := G) k h [] chosen cont).evalDist
        (translateBehavioralProfile (G := G) σ) =
      (cont chosen).evalDist (translateBehavioralProfile (G := G) σ) := rfl

omit [Fintype W] [DecidablePred G.terminal] in
theorem choosePlayers_cons_evalDist
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    {k : Nat} (σ : G.LegalBehavioralProfile) (h : G.History)
    (p : PlayerIx (ι := ι)) (rest : List (PlayerIx (ι := ι))) (chosen : JointAction Act)
    (cont : JointAction Act → GameTree (infoStructure (G := G) k) (SerialExec.State G))
    (hlen : (h.playerView (origPlayer (ι := ι) p)).length ≤ 2 * k) :
    (Tree.choosePlayers (G := G) k h (p :: rest) chosen cont).evalDist
        (translateBehavioralProfile (G := G) σ) =
      (σ.toProfile (origPlayer (ι := ι) p) (h.playerView (origPlayer (ι := ι) p))).bind fun aOpt =>
        (Tree.choosePlayers (G := G) k h rest
            (Tree.recordOption (Act := Act) chosen (origPlayer (ι := ι) p) aOpt) cont).evalDist
          (translateBehavioralProfile (G := G) σ) := by
  simp only [Tree.choosePlayers, encodePlayerView, evalDist_decision, translateBehavioralProfile,
    hlen, Word.toList_ofList_eq_self, legalBehavioralProfile_toProfile_apply, PMF.bind_map]
  congr 1
  funext aOpt
  simp

/-- The bounded augmented-EFG bridge.  Public/player augmented states are
length-stamped native views of the reached history. -/
noncomputable def toAugmentedOfBoundedHorizon
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    {k : Nat} (hBound : G.BoundedHorizon k) : EFG.AugmentedGame where
  base := toPlainEFGOfBoundedHorizon (G := G) hBound
  PubState := List (HistoryStep (toPlainEFGOfBoundedHorizon (G := G) hBound).inf)
  InfoState := fun p =>
    List (HistoryStep (toPlainEFGOfBoundedHorizon (G := G) hBound).inf) ×
      EncPlayerView (G := G) (origPlayer (ι := ι) p) k
  publicState := fun h => h.hist
  playerState := fun p h => (h.hist, Word.ofList (2 * k) [])
  publicOf := fun _ s => s.1
  publicOf_playerState := by
    intro p h
    rfl
  actionIdentified := by
    intro p d₁ d₂ _hEq
    simp [toPlainEFGOfBoundedHorizon, toPlainEFGAtHorizon, infoStructure]

@[simp] theorem forget_toAugmentedOfBoundedHorizon
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    {k : Nat} (hBound : G.BoundedHorizon k) :
    (toAugmentedOfBoundedHorizon (G := G) hBound).forget =
      toPlainEFGOfBoundedHorizon (G := G) hBound := rfl

/-- The temporary length-stamped augmentation has no thick public sets. -/
theorem noThickPublicSets_toAugmentedOfBoundedHorizon
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    {k : Nat} (hBound : G.BoundedHorizon k) :
    (toAugmentedOfBoundedHorizon (G := G) hBound).NoThickPublicSets := by
  intro g h hpublic _hprefix
  exact hpublic

end AugmentedEFGBridge

end FOSG

end GameTheory
