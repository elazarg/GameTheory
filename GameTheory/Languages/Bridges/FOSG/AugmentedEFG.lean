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

omit [DecidableEq ι] in
@[simp] theorem playerEquiv_origPlayer (p : PlayerIx (ι := ι)) :
    playerEquiv (ι := ι) (origPlayer (ι := ι) p) = p := by
  simp [origPlayer, playerEquiv]

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
with the assembled partial joint action.  The `pVal` index is the next EFG
player index to resolve. -/
noncomputable def choosePlayersFrom
    (k : Nat) (h : G.History) (pVal : Nat) (chosen : JointAction Act)
    (cont : JointAction Act → GameTree (infoStructure (G := G) k) (SerialExec.State G)) :
      GameTree (infoStructure (G := G) k) (SerialExec.State G) :=
  if hp : pVal < Fintype.card ι then
    let p : PlayerIx (ι := ι) := ⟨pVal, hp⟩
      let i := origPlayer (ι := ι) p
      let I : (infoStructure (G := G) k).Infoset p :=
        encodePlayerView (G := G) h i
      .decision I (fun aIx =>
        let aOpt : Option (Act i) := actionOfIndex (G := G) I aIx
        choosePlayersFrom k h (pVal + 1)
          (recordOption (Act := Act) chosen i aOpt) cont)
  else
    cont chosen
termination_by Fintype.card ι - pVal

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
        choosePlayersFrom (G := G) k h 0 (noopAction Act)
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
      Tree.choosePlayersFrom (G := G) k h 0 (noopAction Act)
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

/-- An EFG behavioral profile is compatible with the FOSG bridge if every
positive-probability EFG action decodes to a FOSG move available at every
native history with the same original player view.

This is the restriction needed before defining an inverse `EFG → FOSG`
strategy translation.  The forward translation from legal FOSG profiles
satisfies it automatically. -/
def EFGProfileRespectsFOSG
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    {k : Nat} (τ : EFG.BehavioralProfile (infoStructure (G := G) k)) : Prop :=
  ∀ (p : PlayerIx (ι := ι)) (I : (infoStructure (G := G) k).Infoset p)
    (h : G.History) {aIx : (infoStructure (G := G) k).Act I},
    aIx ∈ (τ p I).support →
    h.playerView (origPlayer (ι := ι) p) = Word.toList I →
    actionOfIndex (G := G) I aIx ∈
      G.availableMoves h (origPlayer (ι := ι) p)

omit [Fintype W] [DecidablePred G.terminal] in
theorem translateBehavioralProfile_respectsFOSG
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    {k : Nat} (σ : G.LegalBehavioralProfile) :
    EFGProfileRespectsFOSG (G := G) (k := k)
      (translateBehavioralProfile (G := G) σ) := by
  classical
  intro p I h aIx hsupp hview
  rw [translateBehavioralProfile] at hsupp
  rcases (PMF.mem_support_map_iff _ _ _).mp hsupp with ⟨aOpt, haOpt, hidx⟩
  have haEq : aOpt = actionOfIndex (G := G) I aIx := by
    rw [← hidx]
    simp
  rw [← haEq]
  exact (σ (origPlayer (ι := ι) p)).2 h (by simpa [hview] using haOpt)

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
      (Tree.choosePlayersFrom (G := G) k h 0 (noopAction Act)
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

/-- The optional-move law used by the EFG presentation at a native history. -/
noncomputable def efgChoiceProfile
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    (σ : G.LegalBehavioralProfile) (h : G.History) :
    (p : PlayerIx (ι := ι)) → PMF (Option (Act (origPlayer (ι := ι) p))) :=
  fun p => σ.toProfile (origPlayer (ι := ι) p) (h.playerView (origPlayer (ι := ι) p))

/-- Convert a product of EFG-indexed optional moves back to a native joint
action. -/
noncomputable def efgChoicesEquiv :
    ((p : PlayerIx (ι := ι)) → Option (Act (origPlayer (ι := ι) p))) ≃
      JointAction Act :=
  ((playerEquiv (ι := ι)).symm).piCongr fun _ => Equiv.refl _

/-- The joint-action law induced by the EFG optional decisions. -/
noncomputable def efgJointActionDist
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    (σ : G.LegalBehavioralProfile) (h : G.History) : PMF (JointAction Act) :=
  PMF.map (efgChoicesEquiv (Act := Act)) <|
    Math.PMFProduct.pmfPi (efgChoiceProfile (G := G) σ h)

omit [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)] [Fintype W]
  [DecidablePred G.terminal] in
@[simp] theorem efgChoicesEquiv_symm_recordOption
    (chosen : JointAction Act) (p : PlayerIx (ι := ι))
    (a : Option (Act (origPlayer (ι := ι) p))) :
    (efgChoicesEquiv (Act := Act)).symm
        (Tree.recordOption (Act := Act) chosen (origPlayer (ι := ι) p) a) =
      Function.update ((efgChoicesEquiv (Act := Act)).symm chosen) p a := by
  classical
  funext q
  by_cases hq : q = p
  · subst hq
    simp only [Function.update_self]
    change Tree.recordOption (Act := Act) chosen (origPlayer (ι := ι) q) a
        (origPlayer (ι := ι) q) = a
    simp [Tree.recordOption]
  · have horig : origPlayer (ι := ι) q ≠ origPlayer (ι := ι) p := by
      intro h
      apply hq
      have := congrArg (playerEquiv (ι := ι)) h
      simpa using this
    have hneq : (playerEquiv (ι := ι)).symm q ≠ origPlayer (ι := ι) p := by
      simpa [origPlayer] using horig
    simp only [Function.update_of_ne hq]
    change Tree.recordOption (Act := Act) chosen (origPlayer (ι := ι) p) a
        (origPlayer (ι := ι) q) = chosen (origPlayer (ι := ι) q)
    simp [Tree.recordOption, horig]

omit [∀ i, DecidableEq (Act i)] [Fintype W] [DecidablePred G.terminal] in
theorem efgJointActionDist_eq_jointActionDist
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    (σ : G.LegalBehavioralProfile) (h : G.History) :
    efgJointActionDist (G := G) σ h = G.jointActionDist σ h := by
  classical
  ext a
  rw [efgJointActionDist, PMF.map_apply]
  rw [tsum_eq_single ((efgChoicesEquiv (Act := Act)).symm a)]
  · have hif :
        a = efgChoicesEquiv (Act := Act) ((efgChoicesEquiv (Act := Act)).symm a) := by
        simp
    rw [if_pos hif]
    rw [Math.PMFProduct.pmfPi_apply, G.jointActionDist_apply]
    exact Fintype.prod_equiv (playerEquiv (ι := ι)).symm
      (fun p : PlayerIx (ι := ι) =>
        (σ.toProfile (origPlayer (ι := ι) p) (h.playerView (origPlayer (ι := ι) p)))
          (((efgChoicesEquiv (Act := Act)).symm a) p))
      (fun i : ι => (σ.toProfile i (h.playerView i)) (a i))
      (by
        intro p
        change
          (σ.toProfile ((playerEquiv (ι := ι)).symm p)
              (h.playerView ((playerEquiv (ι := ι)).symm p)))
            (((Equiv.refl (Option (Act ((playerEquiv (ι := ι)).symm p)))).symm)
              (a ((playerEquiv (ι := ι)).symm p))) =
          (σ.toProfile ((playerEquiv (ι := ι)).symm p)
              (h.playerView ((playerEquiv (ι := ι)).symm p)))
            (a ((playerEquiv (ι := ι)).symm p))
        rfl)
  · intro choices hchoices
    by_cases hEq : a = efgChoicesEquiv (Act := Act) choices
    · exfalso
      apply hchoices
      simp [hEq]
    · simp [hEq]

omit [∀ i, DecidableEq (Act i)] [Fintype W] [DecidablePred G.terminal] in
theorem efgJointActionDist_bind_eq_jointActionDist_bind
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    (σ : G.LegalBehavioralProfile) (h : G.History)
    {β : Type} (f : JointAction Act → PMF β) :
    (efgJointActionDist (G := G) σ h).bind f =
      (G.jointActionDist σ h).bind f := by
  rw [efgJointActionDist_eq_jointActionDist (G := G) σ h]

omit [Fintype W] [DecidablePred G.terminal] in
theorem choosePlayersFrom_evalDist_gen
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    {k : Nat} (σ : G.LegalBehavioralProfile) (h : G.History)
    (pVal : Nat) (chosen : JointAction Act)
    (cont : JointAction Act → GameTree (infoStructure (G := G) k) (SerialExec.State G))
    (hview : ∀ p : PlayerIx (ι := ι),
      (h.playerView (origPlayer (ι := ι) p)).length ≤ 2 * k) :
    (Tree.choosePlayersFrom (G := G) k h pVal chosen cont).evalDist
        (translateBehavioralProfile (G := G) σ) =
      (Math.PMFProduct.pmfPi (fun p : PlayerIx (ι := ι) =>
        if p.1 < pVal then
          PMF.pure (((efgChoicesEquiv (Act := Act)).symm chosen) p)
        else
          efgChoiceProfile (G := G) σ h p)).bind
        (fun choices =>
          (cont (efgChoicesEquiv (Act := Act) choices)).evalDist
            (translateBehavioralProfile (G := G) σ)) := by
  classical
  suffices hmain : ∀ m, m = Fintype.card ι - pVal →
      (Tree.choosePlayersFrom (G := G) k h pVal chosen cont).evalDist
          (translateBehavioralProfile (G := G) σ) =
        (Math.PMFProduct.pmfPi (fun p : PlayerIx (ι := ι) =>
          if p.1 < pVal then
            PMF.pure (((efgChoicesEquiv (Act := Act)).symm chosen) p)
          else
            efgChoiceProfile (G := G) σ h p)).bind
          (fun choices =>
            (cont (efgChoicesEquiv (Act := Act) choices)).evalDist
              (translateBehavioralProfile (G := G) σ)) from
    hmain _ rfl
  intro m hm
  induction m generalizing pVal chosen with
  | zero =>
      have hp : ¬ pVal < Fintype.card ι := by omega
      rw [Tree.choosePlayersFrom, dif_neg hp]
      have hall : ∀ p : PlayerIx (ι := ι), p.1 < pVal := fun p => by omega
      simp only [hall, ite_true]
      rw [Math.PMFProduct.pmfPi_pure]
      simp
  | succ m ih =>
      have hp : pVal < Fintype.card ι := by omega
      let p : PlayerIx (ι := ι) := ⟨pVal, hp⟩
      rw [Tree.choosePlayersFrom, dif_pos hp]
      simp only [evalDist_decision, translateBehavioralProfile, encodePlayerView]
      rw [Word.toList_ofList_eq_self (hxs := hview p)]
      rw [legalBehavioralProfile_toProfile_apply]
      rw [PMF.bind_map]
      conv_lhs =>
        arg 2
        ext a
        simp [Function.comp_apply]
      change
        (σ.toProfile (origPlayer (ι := ι) p) (h.playerView (origPlayer (ι := ι) p))).bind
            (fun a =>
              (Tree.choosePlayersFrom (G := G) k h (pVal + 1)
                  (Tree.recordOption (Act := Act) chosen (origPlayer (ι := ι) p) a)
                  cont).evalDist (translateBehavioralProfile (G := G) σ)) =
          (Math.PMFProduct.pmfPi (fun q : PlayerIx (ι := ι) =>
            if q.1 < pVal then
              PMF.pure (((efgChoicesEquiv (Act := Act)).symm chosen) q)
            else efgChoiceProfile (G := G) σ h q)).bind
            (fun choices =>
              (cont (efgChoicesEquiv (Act := Act) choices)).evalDist
                (translateBehavioralProfile (G := G) σ))
      have hrec : ∀ a,
          (Tree.choosePlayersFrom (G := G) k h (pVal + 1)
              (Tree.recordOption (Act := Act) chosen (origPlayer (ι := ι) p) a)
              cont).evalDist (translateBehavioralProfile (G := G) σ) =
            (Math.PMFProduct.pmfPi (fun q : PlayerIx (ι := ι) =>
              if q.1 < pVal + 1 then
                PMF.pure (((efgChoicesEquiv (Act := Act)).symm
                  (Tree.recordOption (Act := Act) chosen (origPlayer (ι := ι) p) a)) q)
              else efgChoiceProfile (G := G) σ h q)).bind
              (fun choices =>
                (cont (efgChoicesEquiv (Act := Act) choices)).evalDist
                  (translateBehavioralProfile (G := G) σ)) := by
        intro a
        exact ih (pVal + 1)
          (Tree.recordOption (Act := Act) chosen (origPlayer (ι := ι) p) a) (by omega)
      simp_rw [hrec]
      let σ' : (q : PlayerIx (ι := ι)) → PMF (Option (Act (origPlayer (ι := ι) q))) :=
        fun q =>
          if q.1 < pVal then
            PMF.pure (((efgChoicesEquiv (Act := Act)).symm chosen) q)
          else efgChoiceProfile (G := G) σ h q
      have hpσ : σ' p =
          σ.toProfile (origPlayer (ι := ι) p) (h.playerView (origPlayer (ι := ι) p)) := by
        simp [σ', efgChoiceProfile, p]
      have hfam : ∀ a,
          (fun q : PlayerIx (ι := ι) =>
            if q.1 < pVal + 1 then
              PMF.pure (((efgChoicesEquiv (Act := Act)).symm
                (Tree.recordOption (Act := Act) chosen (origPlayer (ι := ι) p) a)) q)
            else efgChoiceProfile (G := G) σ h q) =
          Function.update σ' p (PMF.pure a) := by
        intro a
        funext q
        by_cases hq : q = p
        · subst hq
          simp [σ', p]
        · have hneVal : q.1 ≠ pVal := by
            intro hval
            exact hq (Fin.ext hval)
          by_cases hlt : q.1 < pVal
          · have hltSucc : q.1 < pVal + 1 := by omega
            simp [σ', hq, hlt, hltSucc]
          · have hnotSucc : ¬ q.1 < pVal + 1 := by omega
            simp [σ', hq, hlt, hnotSucc]
      simp_rw [hfam]
      rw [show Math.PMFProduct.pmfPi σ' =
          Math.PMFProduct.pmfPi (Function.update σ' p
            (σ.toProfile (origPlayer (ι := ι) p)
              (h.playerView (origPlayer (ι := ι) p)))) from by
            rw [Function.update_eq_self_iff.mpr hpσ.symm]]
      rw [Math.PMFProduct.pmfPi_update_bind]
      rw [PMF.bind_bind]

omit [Fintype W] [DecidablePred G.terminal] in
theorem choosePlayersFrom_zero_evalDist_eq_efgJointActionDist_bind
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    {k : Nat} (σ : G.LegalBehavioralProfile) (h : G.History)
    (chosen : JointAction Act)
    (cont : JointAction Act → GameTree (infoStructure (G := G) k) (SerialExec.State G))
    (hview : ∀ p : PlayerIx (ι := ι),
      (h.playerView (origPlayer (ι := ι) p)).length ≤ 2 * k) :
    (Tree.choosePlayersFrom (G := G) k h 0 chosen cont).evalDist
        (translateBehavioralProfile (G := G) σ) =
      (efgJointActionDist (G := G) σ h).bind
        (fun chosen =>
          (cont chosen).evalDist (translateBehavioralProfile (G := G) σ)) := by
  rw [choosePlayersFrom_evalDist_gen (G := G) σ h 0 chosen cont hview]
  simp only [Nat.not_lt_zero, ite_false]
  simp [efgJointActionDist, PMF.bind_map]
  rfl

theorem sum_subtype_eq_sum_ite
    {α M : Type} [Fintype α] [AddCommMonoid M]
    {p : α → Prop} [DecidablePred p] (F : (a : α) → p a → M) :
    (∑ x : { a : α // p a }, F x.1 x.2) =
      ∑ a : α, if h : p a then F a h else 0 := by
  classical
  let f : α → M := fun a => if h : p a then F a h else 0
  have hsub :
      (Finset.subtype p (Finset.univ : Finset α)).sum (fun x => f x.1) =
        ∑ x : { a : α // p a }, F x.1 x.2 := by
    have huniv :
        Finset.subtype p (Finset.univ : Finset α) =
          (Finset.univ : Finset { a : α // p a }) := by
      ext x
      simp
    rw [huniv]
    refine Finset.sum_congr rfl ?_
    intro x _
    simp only [f]
    have hp : p x.1 := x.2
    simp [hp]
  calc
    ∑ x : { a : α // p a }, F x.1 x.2
      = (Finset.subtype p (Finset.univ : Finset α)).sum (fun x => f x.1) := hsub.symm
    _ = ∑ a : α, if p a then f a else 0 := by
      simpa [Finset.sum_filter] using
        (Finset.sum_subtype_eq_sum_filter
          (s := (Finset.univ : Finset α)) (p := p) (f := f))
    _ = ∑ a : α, f a := by
      refine Finset.sum_congr rfl ?_
      intro a _
      by_cases hp : p a <;> simp [f, hp]
    _ = ∑ a : α, if h : p a then F a h else 0 := rfl

omit [∀ i, DecidableEq (Act i)] [Fintype W] [DecidablePred G.terminal] in
theorem jointActionDist_bind_legalize_eq_legalActionLaw_bind
    (σ : G.LegalBehavioralProfile) (h : G.History)
    (hnot : ¬ G.terminal h.lastState)
    {β : Type} (f : G.LegalAction h.lastState → PMF β) :
    (G.jointActionDist σ h).bind (fun chosen =>
        f (Tree.legalize (G := G) h hnot chosen)) =
      (G.legalActionLaw σ h hnot).bind f := by
  classical
  ext b
  rw [PMF.bind_apply, PMF.bind_apply]
  rw [tsum_fintype, tsum_fintype]
  calc
    ∑ chosen : JointAction Act,
        G.jointActionDist σ h chosen * f (Tree.legalize (G := G) h hnot chosen) b
      = ∑ chosen : JointAction Act,
          (if hlegal : G.legal h.lastState chosen then
            G.jointActionDist σ h chosen * f ⟨chosen, hlegal⟩ b
          else (0 : ENNReal)) := by
            refine Finset.sum_congr rfl ?_
            intro chosen _
            by_cases hlegal : G.legal h.lastState chosen
            · simp [hlegal, Tree.legalize]
            · have hzero := G.legalBehavioralProfile_jointActionDist_eq_zero_of_not_legal
                σ h hnot hlegal
              simp [hlegal, hzero]
    _ = ∑ a : G.LegalAction h.lastState,
          G.jointActionDist σ h a.1 * f a b := by
            exact (sum_subtype_eq_sum_ite
              (p := fun chosen : JointAction Act => G.legal h.lastState chosen)
              (F := fun chosen hlegal =>
                G.jointActionDist σ h chosen * f ⟨chosen, hlegal⟩ b)).symm
    _ = ∑ a : G.LegalAction h.lastState,
          (G.legalActionLaw σ h hnot) a * f a b := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [G.legalActionLaw_apply σ h hnot a]

omit [∀ i, DecidableEq (Act i)] [Fintype W] [DecidablePred G.terminal] in
theorem jointActionDist_bind_legalize_eq_legalActionLaw_bind_coe
    (σ : G.LegalBehavioralProfile) (h : G.History)
    (hnot : ¬ G.terminal h.lastState)
    {β : Type} (g : JointAction Act → PMF β) :
    (G.jointActionDist σ h).bind (fun chosen =>
        g (Tree.legalize (G := G) h hnot chosen).1) =
      (G.legalActionLaw σ h hnot).bind (fun a => g a.1) := by
  classical
  ext b
  rw [PMF.bind_apply, PMF.bind_apply]
  rw [tsum_fintype, tsum_fintype]
  calc
    ∑ chosen : JointAction Act,
        G.jointActionDist σ h chosen * g (Tree.legalize (G := G) h hnot chosen).1 b
      = ∑ chosen : JointAction Act,
          (if G.legal h.lastState chosen then
            G.jointActionDist σ h chosen * g chosen b
          else (0 : ENNReal)) := by
            refine Finset.sum_congr rfl ?_
            intro chosen _
            by_cases hlegal : G.legal h.lastState chosen
            · simp [hlegal, Tree.legalize]
            · have hzero := G.legalBehavioralProfile_jointActionDist_eq_zero_of_not_legal
                σ h hnot hlegal
              simp [hlegal, hzero]
    _ = ∑ a : G.LegalAction h.lastState,
          G.jointActionDist σ h a.1 * g a.1 b := by
            calc
              ∑ chosen : JointAction Act,
                  (if G.legal h.lastState chosen then
                    G.jointActionDist σ h chosen * g chosen b
                  else (0 : ENNReal))
                = ∑ a ∈ Finset.subtype (fun chosen : JointAction Act =>
                    G.legal h.lastState chosen) (Finset.univ : Finset (JointAction Act)),
                  G.jointActionDist σ h a.1 * g a.1 b := by
                    have htype :
                        ∑ a : { chosen : JointAction Act // G.legal h.lastState chosen },
                          G.jointActionDist σ h a.1 * g a.1 b =
                        ∑ chosen : JointAction Act,
                          (if G.legal h.lastState chosen then
                            G.jointActionDist σ h chosen * g chosen b
                          else (0 : ENNReal)) := by
                      simpa [Finset.sum_filter] using
                        (Finset.sum_subtype_eq_sum_filter
                          (s := (Finset.univ : Finset (JointAction Act)))
                          (p := fun chosen : JointAction Act => G.legal h.lastState chosen)
                          (f := fun chosen : JointAction Act =>
                            G.jointActionDist σ h chosen * g chosen b))
                    simpa using htype.symm
              _ = ∑ a : G.LegalAction h.lastState,
                  G.jointActionDist σ h a.1 * g a.1 b := by
                    simp
    _ = ∑ a : G.LegalAction h.lastState,
          (G.legalActionLaw σ h hnot) a * g a.1 b := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [G.legalActionLaw_apply σ h hnot a]

theorem tree_eval_eq_runDistFrom_of_length_add_le
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    {k : Nat} (σ : G.LegalBehavioralProfile) :
    ∀ (n : Nat) (h : G.History), h.steps.length + n ≤ k →
      (Tree.fromHistory (G := G) k n h).evalDist
          (translateBehavioralProfile (G := G) σ) =
        History.runDistFrom G σ n h
  | 0, h, _hlen => by
      simp
  | n + 1, h, hlen => by
      by_cases hterm : G.terminal h.lastState
      · simp [hterm]
      · rw [tree_eval_succ_nonterminal_unfold (G := G) k n σ h hterm]
        rw [History.runDistFrom_succ_nonterminal (G := G) (σ := σ) (n := n) (h := h) hterm]
        have hsteps : h.steps.length ≤ k := by omega
        have hview : ∀ p : PlayerIx (ι := ι),
            (h.playerView (origPlayer (ι := ι) p)).length ≤ 2 * k := by
          intro p
          have hv := history_playerView_length_le_two_mul_steps
            (G := G) h (origPlayer (ι := ι) p)
          omega
        rw [choosePlayersFrom_zero_evalDist_eq_efgJointActionDist_bind
          (G := G) σ h (noopAction Act)
          (fun chosen =>
            let a := Tree.legalize (G := G) h hterm chosen
            let μ := G.transition h.lastState a
            GameTree.chance (Fintype.card W) (PMF.map (Fintype.equivFin W) μ)
              (fintype_card_pos_of_pmf μ)
              (fun b =>
                let dst := (Fintype.equivFin W).symm b
                let h' := h.extendByOutcome a dst
                Tree.fromHistory (G := G) k n h')) hview]
        rw [efgJointActionDist_bind_eq_jointActionDist_bind (G := G) σ h]
        change (G.jointActionDist σ h).bind
            (fun chosen =>
              (fun a : G.LegalAction h.lastState =>
                (GameTree.chance (Fintype.card W)
                  (PMF.map (Fintype.equivFin W) (G.transition h.lastState a))
                  (fintype_card_pos_of_pmf (G.transition h.lastState a))
                  (fun b =>
                    let dst := (Fintype.equivFin W).symm b
                    Tree.fromHistory (G := G) k n (h.extendByOutcome a dst))).evalDist
                  (translateBehavioralProfile (G := G) σ))
                (Tree.legalize (G := G) h hterm chosen)) =
          (G.legalActionLaw σ h hterm).bind fun a =>
            (G.transition h.lastState a).bind fun dst =>
              History.runDistFrom G σ n (h.extendByOutcome a dst)
        rw [show (G.jointActionDist σ h).bind
            (fun chosen =>
              (fun a : G.LegalAction h.lastState =>
                (GameTree.chance (Fintype.card W)
                  (PMF.map (Fintype.equivFin W) (G.transition h.lastState a))
                  (fintype_card_pos_of_pmf (G.transition h.lastState a))
                  (fun b =>
                    let dst := (Fintype.equivFin W).symm b
                    Tree.fromHistory (G := G) k n (h.extendByOutcome a dst))).evalDist
                  (translateBehavioralProfile (G := G) σ))
                (Tree.legalize (G := G) h hterm chosen)) =
              (G.legalActionLaw σ h hterm).bind
                (fun a : G.LegalAction h.lastState =>
                  (GameTree.chance (Fintype.card W)
                    (PMF.map (Fintype.equivFin W) (G.transition h.lastState a))
                    (fintype_card_pos_of_pmf (G.transition h.lastState a))
                    (fun b =>
                      let dst := (Fintype.equivFin W).symm b
                      Tree.fromHistory (G := G) k n (h.extendByOutcome a dst))).evalDist
                    (translateBehavioralProfile (G := G) σ)) from
            jointActionDist_bind_legalize_eq_legalActionLaw_bind
              (G := G) σ h hterm
              (f := fun a : G.LegalAction h.lastState =>
                (GameTree.chance (Fintype.card W)
                  (PMF.map (Fintype.equivFin W) (G.transition h.lastState a))
                  (fintype_card_pos_of_pmf (G.transition h.lastState a))
                  (fun b =>
                    let dst := (Fintype.equivFin W).symm b
                    Tree.fromHistory (G := G) k n (h.extendByOutcome a dst))).evalDist
                  (translateBehavioralProfile (G := G) σ))]
        congr 1
        funext a
        simp only [evalDist_chance]
        rw [PMF.bind_map]
        congr 1
        funext dst
        simp only [Function.comp_apply]
        have hrec := tree_eval_eq_runDistFrom_of_length_add_le (k := k)
          σ n (h.extendByOutcome a dst) (by
          by_cases hsupp : G.transition h.lastState a dst ≠ 0
          · rw [History.extendByOutcome_of_support (h := h) (a := a) (dst := dst) hsupp]
            simp
            omega
          · have hzero : G.transition h.lastState a dst = 0 := by
              exact of_not_not hsupp
            rw [History.extendByOutcome_of_no_support (h := h) (a := a) (dst := dst) hzero]
            omega)
        simpa using hrec

theorem toPlainEFGAtHorizon_outcomeKernel_eq_runDist
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    (k : Nat) (σ : G.LegalBehavioralProfile) :
    (toPlainEFGAtHorizon (G := G) k).toKernelGame.outcomeKernel
        (translateBehavioralProfile (G := G) σ) =
      G.runDist k σ := by
  change (Tree.fromHistory (G := G) k k (SerialExec.root G)).evalDist
      (translateBehavioralProfile (G := G) σ) =
    G.runDist k σ
  rw [tree_eval_eq_runDistFrom_of_length_add_le (G := G) (k := k) σ k (SerialExec.root G)]
  · rfl
  · simp [SerialExec.root]

theorem toPlainEFGOfBoundedHorizon_outcomeKernel_eq_runDist
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    {k : Nat} (hBound : G.BoundedHorizon k) (σ : G.LegalBehavioralProfile) :
    (toPlainEFGOfBoundedHorizon (G := G) hBound).toKernelGame.outcomeKernel
        (translateBehavioralProfile (G := G) σ) =
      G.runDist k σ := by
  exact toPlainEFGAtHorizon_outcomeKernel_eq_runDist (G := G) k σ

theorem toPlainEFGOfBoundedHorizon_outcomeKernel_eq_nativeBounded
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs] [Fintype G.History]
    {k : Nat} (hBound : G.BoundedHorizon k) (σ : G.LegalBehavioralProfile) :
    (toPlainEFGOfBoundedHorizon (G := G) hBound).toKernelGame.outcomeKernel
        (translateBehavioralProfile (G := G) σ) =
      (G.toKernelGameOfBoundedHorizon hBound).outcomeKernel σ := by
  rw [toPlainEFGOfBoundedHorizon_outcomeKernel_eq_runDist,
    G.toKernelGameOfBoundedHorizon_outcomeKernel]

theorem toPlainEFGOfBoundedHorizon_support_isTerminal
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    {k : Nat} (hBound : G.BoundedHorizon k)
    (σ : G.LegalBehavioralProfile) (h : G.History)
    (hsupp : h ∈ ((toPlainEFGOfBoundedHorizon (G := G) hBound).toKernelGame.outcomeKernel
        (translateBehavioralProfile (G := G) σ)).support) :
    h.IsTerminal := by
  have hsuppRun : h ∈ (G.runDist k σ).support := by
    rw [← toPlainEFGOfBoundedHorizon_outcomeKernel_eq_runDist (G := G) hBound σ]
    exact hsupp
  exact G.runDist_support_isTerminal_of_boundedHorizon hBound σ h hsuppRun

/-! ### Boundary cast helpers for inverse strategy translation

The EFG presentation is indexed by `PlayerIx = Fin (Fintype.card ι)` and uses
`origPlayer p` as the underlying FOSG player.  When constructing an inverse
EFG-to-FOSG profile we work with a FOSG player `i : ι` and need to talk about
the EFG infoset for the corresponding EFG index `playerEquiv i`.  The cast
`origPlayer (playerEquiv i) = i` is not definitional, so we isolate it here. -/

/-- Encode a native FOSG player view as the EFG bridge infoset for the EFG
player index corresponding to `i`. -/
noncomputable def encodedInfoOfView
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    {k : Nat} (i : ι) (view : G.InfoState i) :
    (infoStructure (G := G) k).Infoset (playerEquiv (ι := ι) i) :=
  cast (by simp [infoStructure, EncPlayerView]) (Word.ofList (2 * k) view)

/-- Decode an EFG action index at the encoded EFG player corresponding to a
FOSG player `i` back to an optional FOSG move for `i`. -/
noncomputable def actionOfIndexForPlayer
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    {k : Nat} (i : ι)
    (I : (infoStructure (G := G) k).Infoset (playerEquiv (ι := ι) i))
    (a : (infoStructure (G := G) k).Act I) : Option (Act i) :=
  cast (by rw [origPlayer_playerEquiv]) (actionOfIndex (G := G) I a)

/-! ### Inverse strategy translation

For a respectful EFG profile, project back to a legal FOSG behavioral
profile. -/

omit [Fintype ι] [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]
  [Fintype W] [DecidablePred G.terminal] in
private theorem availableMoves_cast_mem
    {i j : ι} (hij : i = j) (h : G.History)
    {oi : Option (Act i)} (hmem : oi ∈ G.availableMoves h i) :
    cast (by rw [hij]) oi ∈ G.availableMoves h j := by
  subst hij
  simpa using hmem

omit [Fintype W] [DecidablePred G.terminal] in
private theorem word_toList_cast_eq
    {α β : Type} (n : Nat) (xs : List α) (h : α = β) (hlen : xs.length ≤ n) :
    Word.toList (cast (by rw [h]) (Word.ofList n xs) : Word β n)
      = cast (by rw [h]) xs := by
  subst h
  simp [Word.toList_ofList_eq_self _ hlen]

omit [Fintype ι] [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]
  [Fintype W] [DecidablePred G.terminal] in
private theorem playerView_cast_eq_of_eq
    {i j : ι} (hij : i = j) (h : G.History) :
    h.playerView j = cast (by rw [hij]) (h.playerView i) := by
  subst hij
  rfl

/-- The inverse strategy translation.  Given an EFG profile that respects
the FOSG legality predicate, produce a legal FOSG behavioral profile by
reading the EFG action distribution at the encoded player view and
decoding back to FOSG moves. -/
noncomputable def efgToFOSGProfile
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    {k : Nat} (hBound : G.BoundedHorizon k)
    (τ : EFG.BehavioralProfile (infoStructure (G := G) k))
    (hτ : EFGProfileRespectsFOSG (G := G) (k := k) τ) :
    G.LegalBehavioralProfile := by
  classical
  intro i
  refine ⟨fun view =>
    PMF.map
      (actionOfIndexForPlayer (G := G) (k := k) i
        (encodedInfoOfView (G := G) (k := k) i view))
      (τ (playerEquiv (ι := ι) i)
        (encodedInfoOfView (G := G) (k := k) i view)), ?_⟩
  intro h oi hsupp
  let p : PlayerIx (ι := ι) := playerEquiv (ι := ι) i
  let I : (infoStructure (G := G) k).Infoset p :=
    encodedInfoOfView (G := G) (k := k) i (h.playerView i)
  -- Unfold support of PMF.map
  have hsuppMap :
      oi ∈ (PMF.map (actionOfIndexForPlayer (G := G) (k := k) i I) (τ p I)).support :=
    hsupp
  rcases (PMF.mem_support_map_iff _ _ _).mp hsuppMap with ⟨aIx, hsupp_aIx, hcast⟩
  -- Length bound on the player view
  have hlen : (h.playerView i).length ≤ 2 * k := by
    have hsteps : h.steps.length ≤ k :=
      G.history_length_le_of_boundedHorizon hBound h
    have hv := history_playerView_length_le_two_mul_steps (G := G) h i
    omega
  -- Compute Word.toList of the encoded info via the cast helpers
  have hii : origPlayer (ι := ι) p = i := origPlayer_playerEquiv (ι := ι) i
  have htypeEq : EncPlayerView (G := G) i k =
      (infoStructure (G := G) k).Infoset p := by
    change Word (PlayerEvent G i) (2 * k) =
      Word (PlayerEvent G (origPlayer (ι := ι) p)) (2 * k)
    rw [hii]
  have hI_eq : I = cast htypeEq (Word.ofList (2 * k) (h.playerView i)) := rfl
  -- View at origPlayer p equals casted view at i
  have hview_cast :
      h.playerView (origPlayer (ι := ι) p) =
        cast (by rw [hii]) (h.playerView i) :=
    playerView_cast_eq_of_eq G hii.symm h
  -- Word.toList I = casted view
  have hPE : PlayerEvent G i = PlayerEvent G (origPlayer (ι := ι) p) := by
    rw [hii]
  have hWordTo :
      Word.toList (I : (infoStructure (G := G) k).Infoset p) =
        cast (by rw [hii]) (h.playerView i) := by
    rw [hI_eq]
    have hw := word_toList_cast_eq (n := 2 * k) (xs := h.playerView i)
      (h := hPE) hlen
    convert hw using 2
  -- hview required by hτ
  have hview : h.playerView (origPlayer (ι := ι) p) = Word.toList I := by
    rw [hview_cast, hWordTo]
  -- Apply hτ
  have hAvail : actionOfIndex (G := G) I aIx ∈
      G.availableMoves h (origPlayer (ι := ι) p) :=
    hτ p I h hsupp_aIx hview
  -- Push the cast through availableMoves to get the result at i
  have hcast_av :
      cast (by rw [hii]) (actionOfIndex (G := G) I aIx) ∈
        G.availableMoves h i :=
    availableMoves_cast_mem G hii h hAvail
  -- Match with oi
  have hoiEq : oi = cast (by rw [hii]) (actionOfIndex (G := G) I aIx) := by
    rw [← hcast]; rfl
  rw [hoiEq]
  exact hcast_av

omit [Fintype W] [DecidablePred G.terminal] in
@[simp] theorem efgToFOSGProfile_apply
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    {k : Nat} (hBound : G.BoundedHorizon k)
    (τ : EFG.BehavioralProfile (infoStructure (G := G) k))
    (hτ : EFGProfileRespectsFOSG (G := G) (k := k) τ)
    (i : ι) (view : G.InfoState i) :
    ((efgToFOSGProfile (G := G) hBound τ hτ) i).1 view =
      PMF.map (actionOfIndexForPlayer (G := G) (k := k) i
          (encodedInfoOfView (G := G) (k := k) i view))
        (τ (playerEquiv (ι := ι) i)
          (encodedInfoOfView (G := G) (k := k) i view)) := rfl

omit [Fintype ι] [∀ i, DecidableEq (Act i)] [Fintype W] [DecidablePred G.terminal] in
private theorem efgToFOSGProfile_translateBehavioralProfile_apply_aux
    {k : Nat} (σ : G.LegalBehavioralProfile)
    {i j : ι} (hji : j = i) (view : G.InfoState i) (hlen : view.length ≤ 2 * k)
    (I : Word (PlayerEvent G j) (2 * k))
    (hI : I = cast (by rw [hji]) (Word.ofList (2 * k) view)) :
    PMF.map (fun aIx : Fin (Fintype.card (Option (Act j))) =>
        (cast (by rw [hji]) ((Fintype.equivFin (Option (Act j))).symm aIx)
          : Option (Act i)))
      (PMF.map (fun b : Option (Act j) => Fintype.equivFin (Option (Act j)) b)
        (σ.toProfile j (Word.toList I)))
      = σ.toProfile i view := by
  classical
  subst hji
  -- Now j = i, casts are identity, I = Word.ofList (2 * k) view
  have hI' : I = Word.ofList (2 * k) view := by
    simpa using hI
  subst hI'
  rw [Word.toList_ofList_eq_self _ hlen]
  rw [PMF.map_comp]
  have hcomp : (fun aIx : Fin (Fintype.card (Option (Act j))) =>
      cast (rfl : Option (Act j) = Option (Act j))
        ((Fintype.equivFin (Option (Act j))).symm aIx))
      ∘ (fun b : Option (Act j) => Fintype.equivFin (Option (Act j)) b)
      = id := by
    funext b; simp
  rw [hcomp, PMF.map_id]

omit [Fintype W] [DecidablePred G.terminal] in
/-- Round-trip: translating a legal FOSG profile to EFG and back recovers the
original profile pointwise on player views whose length fits the horizon
encoding. -/
theorem efgToFOSGProfile_translateBehavioralProfile_apply
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    {k : Nat} (hBound : G.BoundedHorizon k) (σ : G.LegalBehavioralProfile)
    (i : ι) (view : G.InfoState i) (hlen : view.length ≤ 2 * k) :
    ((efgToFOSGProfile (G := G) hBound (translateBehavioralProfile (G := G) σ)
        (translateBehavioralProfile_respectsFOSG (G := G) σ)) i).1 view
      = σ.toProfile i view := by
  classical
  rw [efgToFOSGProfile_apply]
  -- Unfold translateBehavioralProfile to expose the inner PMF.map
  show PMF.map (actionOfIndexForPlayer (G := G) (k := k) i
      (encodedInfoOfView (G := G) (k := k) i view))
      (translateBehavioralProfile (G := G) σ (playerEquiv (ι := ι) i)
        (encodedInfoOfView (G := G) (k := k) i view)) = _
  unfold translateBehavioralProfile actionOfIndexForPlayer indexOfAction
    actionOfIndex
  exact efgToFOSGProfile_translateBehavioralProfile_apply_aux
    (G := G) σ (origPlayer_playerEquiv (ι := ι) i) view hlen
    (encodedInfoOfView (G := G) (k := k) i view) rfl

/-! ### Distributional transport for restricted EFG profiles

Step 1: pointwise, at infosets reachable in the bridge tree, a respectful EFG
profile τ agrees with its `translate ∘ efgToFOSG` round-trip. -/

omit [Fintype W] [DecidablePred G.terminal] in
/-- Auxiliary that abstracts the cast on the EFG player index.  We take a
generic `q : PlayerIx` together with a proof that `q = p`, so a `subst` makes
all the casts trivial. -/
private theorem translate_efgToFOSG_apply_encoded_aux
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    {k : Nat}
    (τ : EFG.BehavioralProfile (infoStructure (G := G) k))
    {p q : PlayerIx (ι := ι)} (hqp : q = p)
    (heqAct : Option (Act (origPlayer (ι := ι) q)) =
      Option (Act (origPlayer (ι := ι) p)))
    (heqInfoset : (infoStructure (G := G) k).Infoset q =
      (infoStructure (G := G) k).Infoset p)
    (Ip : (infoStructure (G := G) k).Infoset p)
    (Iq : (infoStructure (G := G) k).Infoset q)
    (hIqIp : HEq Iq Ip) :
    PMF.map (fun b : Option (Act (origPlayer (ι := ι) p)) =>
        Fintype.equivFin (Option (Act (origPlayer (ι := ι) p))) b)
      (PMF.map (fun aIx : (infoStructure (G := G) k).Act Iq =>
          (cast heqAct
            ((Fintype.equivFin (Option (Act (origPlayer (ι := ι) q)))).symm aIx) :
            Option (Act (origPlayer (ι := ι) p))))
        (τ q Iq))
      = τ p Ip := by
  classical
  subst hqp
  have hIqIp' : Iq = Ip := eq_of_heq hIqIp
  subst hIqIp'
  rw [PMF.map_comp]
  have hcomp : (fun b : Option (Act (origPlayer (ι := ι) q)) =>
      Fintype.equivFin (Option (Act (origPlayer (ι := ι) q))) b)
      ∘ (fun aIx : (infoStructure (G := G) k).Act Iq =>
          (cast heqAct
            ((Fintype.equivFin (Option (Act (origPlayer (ι := ι) q)))).symm aIx) :
            Option (Act (origPlayer (ι := ι) q))))
      = id := by
    funext aIx
    simp
  rw [hcomp]
  exact PMF.map_id _

omit [Fintype W] [DecidablePred G.terminal] in
private theorem translate_efgToFOSG_apply_encoded
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    {k : Nat} (hBound : G.BoundedHorizon k)
    (τ : EFG.BehavioralProfile (infoStructure (G := G) k))
    (hτ : EFGProfileRespectsFOSG (G := G) (k := k) τ)
    (p : PlayerIx (ι := ι)) (h : G.History)
    (hlen : (h.playerView (origPlayer (ι := ι) p)).length ≤ 2 * k) :
    translateBehavioralProfile (G := G)
        (efgToFOSGProfile (G := G) hBound τ hτ) p
        (encodePlayerView (G := G) (k := k) h (origPlayer (ι := ι) p))
      = τ p (encodePlayerView (G := G) (k := k) h (origPlayer (ι := ι) p)) := by
  classical
  set j : ι := origPlayer (ι := ι) p with hj
  set I : (infoStructure (G := G) k).Infoset p :=
    encodePlayerView (G := G) (k := k) h j with hIdef
  change translateBehavioralProfile (G := G)
      (efgToFOSGProfile (G := G) hBound τ hτ) p I = τ p I
  unfold translateBehavioralProfile
  have htoList : (Word.toList (I : (infoStructure (G := G) k).Infoset p) :
      List (PlayerEvent G j)) = h.playerView j :=
    Word.toList_ofList_eq_self (h.playerView j) hlen
  change PMF.map (indexOfAction (G := G) I)
      ((efgToFOSGProfile (G := G) hBound τ hτ).toProfile j (Word.toList I)) = _
  rw [htoList]
  change PMF.map (indexOfAction (G := G) I)
      (((efgToFOSGProfile (G := G) hBound τ hτ) j).1 (h.playerView j)) = _
  rw [efgToFOSGProfile_apply]
  -- LHS: PMF.map (indexOfAction I) (PMF.map (actionOfIndexForPlayer j I_inner) (τ q I_inner))
  --   where q = playerEquiv j, I_inner = encodedInfoOfView j (h.playerView j)
  set q : PlayerIx (ι := ι) := playerEquiv (ι := ι) j with hqdef
  have hqp : q = p := by
    rw [hqdef, hj]
    exact playerEquiv_origPlayer (ι := ι) p
  set I_inner : (infoStructure (G := G) k).Infoset q :=
    encodedInfoOfView (G := G) (k := k) j (h.playerView j) with hIinner
  have heqInfoset : (infoStructure (G := G) k).Infoset q =
      (infoStructure (G := G) k).Infoset p := by rw [hqp]
  have heqAct : Option (Act (origPlayer (ι := ι) q)) =
      Option (Act (origPlayer (ι := ι) p)) := by rw [hqp]
  have hI_inner_heq : HEq I_inner I := by
    -- I_inner = cast _ (Word.ofList (2*k) (h.playerView j))
    -- I = Word.ofList (2*k) (h.playerView j) (as Word (PlayerEvent G j) (2*k))
    -- both are heterogeneously equal underlying Word values
    have h1 : HEq I_inner (Word.ofList (2 * k) (h.playerView j)) := by
      rw [hIinner]
      change HEq (encodedInfoOfView (G := G) (k := k) j (h.playerView j))
        (Word.ofList (2 * k) (h.playerView j))
      exact cast_heq _ _
    have h2 : HEq (Word.ofList (2 * k) (h.playerView j) :
        Word (PlayerEvent G j) (2 * k)) I := by
      rw [hIdef]
      rfl
    exact h1.trans h2
  have hkey : PMF.map (indexOfAction (G := G) I)
      (PMF.map (actionOfIndexForPlayer (G := G) (k := k) j I_inner) (τ q I_inner))
      = τ p I := by
    unfold indexOfAction actionOfIndexForPlayer actionOfIndex
    exact translate_efgToFOSG_apply_encoded_aux (G := G) τ hqp heqAct
      heqInfoset I I_inner hI_inner_heq
  exact hkey

/-! Step 2: tree-level coincidence on `Tree.choosePlayersFrom`. -/

omit [Fintype W] [DecidablePred G.terminal] in
private theorem choosePlayersFrom_evalDist_eq_translate_efgToFOSG_aux
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    {k : Nat} (hBound : G.BoundedHorizon k)
    (τ : EFG.BehavioralProfile (infoStructure (G := G) k))
    (hτ : EFGProfileRespectsFOSG (G := G) (k := k) τ)
    (h : G.History)
    (hview : ∀ p : PlayerIx (ι := ι),
      (h.playerView (origPlayer (ι := ι) p)).length ≤ 2 * k) :
    ∀ (m pVal : Nat),
      m = Fintype.card ι - pVal →
      ∀ (chosen : JointAction Act)
        (cont : JointAction Act →
          GameTree (infoStructure (G := G) k) (SerialExec.State G)),
        (∀ chosen',
          (cont chosen').evalDist τ = (cont chosen').evalDist
            (translateBehavioralProfile (G := G)
              (efgToFOSGProfile (G := G) hBound τ hτ))) →
        (Tree.choosePlayersFrom (G := G) k h pVal chosen cont).evalDist τ
          = (Tree.choosePlayersFrom (G := G) k h pVal chosen cont).evalDist
              (translateBehavioralProfile (G := G)
                (efgToFOSGProfile (G := G) hBound τ hτ)) := by
  classical
  intro m
  induction m with
  | zero =>
      intro pVal hm chosen cont hcont
      have hp : ¬ pVal < Fintype.card ι := by omega
      conv_lhs => rw [Tree.choosePlayersFrom, dif_neg hp]
      conv_rhs => rw [Tree.choosePlayersFrom, dif_neg hp]
      exact hcont chosen
  | succ m ih =>
      intro pVal hm chosen cont hcont
      have hp : pVal < Fintype.card ι := by omega
      let p : PlayerIx (ι := ι) := ⟨pVal, hp⟩
      conv_lhs => rw [Tree.choosePlayersFrom, dif_pos hp]
      conv_rhs => rw [Tree.choosePlayersFrom, dif_pos hp]
      simp only [evalDist_decision]
      have hpw : τ p (encodePlayerView (G := G) (k := k) h
            (origPlayer (ι := ι) p))
          = translateBehavioralProfile (G := G)
              (efgToFOSGProfile (G := G) hBound τ hτ) p
              (encodePlayerView (G := G) (k := k) h
                (origPlayer (ι := ι) p)) := by
        rw [translate_efgToFOSG_apply_encoded (G := G) hBound τ hτ p h (hview p)]
      change (τ p (encodePlayerView (G := G) (k := k) h
            (origPlayer (ι := ι) p))).bind _ = _
      rw [hpw]
      congr 1
      funext aIx
      exact ih (pVal + 1) (by omega) _ cont hcont

omit [Fintype W] [DecidablePred G.terminal] in
private theorem choosePlayersFrom_evalDist_eq_translate_efgToFOSG
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    {k : Nat} (hBound : G.BoundedHorizon k)
    (τ : EFG.BehavioralProfile (infoStructure (G := G) k))
    (hτ : EFGProfileRespectsFOSG (G := G) (k := k) τ)
    (h : G.History)
    (hview : ∀ p : PlayerIx (ι := ι),
      (h.playerView (origPlayer (ι := ι) p)).length ≤ 2 * k)
    (pVal : Nat) (chosen : JointAction Act)
    (cont : JointAction Act →
      GameTree (infoStructure (G := G) k) (SerialExec.State G))
    (hcont : ∀ chosen',
      (cont chosen').evalDist τ = (cont chosen').evalDist
        (translateBehavioralProfile (G := G)
          (efgToFOSGProfile (G := G) hBound τ hτ))) :
    (Tree.choosePlayersFrom (G := G) k h pVal chosen cont).evalDist τ
      = (Tree.choosePlayersFrom (G := G) k h pVal chosen cont).evalDist
          (translateBehavioralProfile (G := G)
            (efgToFOSGProfile (G := G) hBound τ hτ)) :=
  choosePlayersFrom_evalDist_eq_translate_efgToFOSG_aux (G := G) hBound τ hτ h hview
    _ pVal rfl chosen cont hcont

/-! Step 3: outer induction on the bridge tree depth. -/

private theorem fromHistory_evalDist_eq_translate_efgToFOSG
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    {k : Nat} (hBound : G.BoundedHorizon k)
    (τ : EFG.BehavioralProfile (infoStructure (G := G) k))
    (hτ : EFGProfileRespectsFOSG (G := G) (k := k) τ)
    (n : Nat) (h : G.History) (hbound : h.steps.length + n ≤ k) :
    (Tree.fromHistory (G := G) k n h).evalDist τ
      = (Tree.fromHistory (G := G) k n h).evalDist
          (translateBehavioralProfile (G := G)
            (efgToFOSGProfile (G := G) hBound τ hτ)) := by
  classical
  induction n generalizing h with
  | zero =>
      simp [Tree.fromHistory]
  | succ n ih =>
      by_cases hterm : G.terminal h.lastState
      · simp [Tree.fromHistory, hterm]
      · rw [tree_fromHistory_succ_nonterminal (G := G) k n h hterm]
        have hview : ∀ p : PlayerIx (ι := ι),
            (h.playerView (origPlayer (ι := ι) p)).length ≤ 2 * k := by
          intro p
          have hv := history_playerView_length_le_two_mul_steps
            (G := G) h (origPlayer (ι := ι) p)
          omega
        apply choosePlayersFrom_evalDist_eq_translate_efgToFOSG
          (G := G) hBound τ hτ h hview 0 (noopAction Act)
        intro chosen
        -- chance node + recurse
        simp only [evalDist_chance]
        congr 1
        funext b
        have : (h.extendByOutcome (Tree.legalize (G := G) h hterm chosen)
            ((Fintype.equivFin W).symm b)).steps.length + n ≤ k := by
          by_cases hsupp : G.transition h.lastState
              (Tree.legalize (G := G) h hterm chosen)
              ((Fintype.equivFin W).symm b) ≠ 0
          · rw [History.extendByOutcome_of_support
              (h := h) (a := Tree.legalize (G := G) h hterm chosen)
              (dst := (Fintype.equivFin W).symm b) hsupp]
            simp; omega
          · have hzero : G.transition h.lastState
                (Tree.legalize (G := G) h hterm chosen)
                ((Fintype.equivFin W).symm b) = 0 :=
              of_not_not hsupp
            rw [History.extendByOutcome_of_no_support
              (h := h) (a := Tree.legalize (G := G) h hterm chosen)
              (dst := (Fintype.equivFin W).symm b) hzero]
            omega
        exact ih _ this

/-- Distributional transport for restricted EFG profiles: a bridge-tree
outcome distribution under any respectful EFG profile equals the FOSG
outcome distribution under the inverse-translated FOSG profile. -/
theorem toPlainEFGOfBoundedHorizon_outcomeKernel_eq_efgToFOSG
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs] [Fintype G.History]
    {k : Nat} (hBound : G.BoundedHorizon k)
    (τ : EFG.BehavioralProfile (infoStructure (G := G) k))
    (hτ : EFGProfileRespectsFOSG (G := G) (k := k) τ) :
    (toPlainEFGOfBoundedHorizon (G := G) hBound).toKernelGame.outcomeKernel τ
      = (G.toKernelGameOfBoundedHorizon hBound).outcomeKernel
          (efgToFOSGProfile (G := G) hBound τ hτ) := by
  have htree := fromHistory_evalDist_eq_translate_efgToFOSG
    G hBound τ hτ k (SerialExec.root G)
    (by simp [SerialExec.root])
  change (Tree.fromHistory (G := G) k k (SerialExec.root G)).evalDist τ = _
  rw [htree]
  exact toPlainEFGOfBoundedHorizon_outcomeKernel_eq_nativeBounded
    (G := G) hBound (efgToFOSGProfile (G := G) hBound τ hτ)

/-! ### Solution-concept corollaries

Per-player utility distribution and expected utility transport directly from
outcome-kernel equality plus the bridge's `utility` definition reindexing
through `origPlayer`.  These are corollaries, not new bridge primitives. -/

theorem toPlainEFGOfBoundedHorizon_eu_eq_native
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs] [Fintype G.History]
    {k : Nat} (hBound : G.BoundedHorizon k)
    (σ : G.LegalBehavioralProfile) (p : PlayerIx (ι := ι)) :
    (toPlainEFGOfBoundedHorizon (G := G) hBound).toKernelGame.eu
        (translateBehavioralProfile (G := G) σ) p
      = (G.toKernelGameOfBoundedHorizon hBound).eu σ (origPlayer (ι := ι) p) := by
  unfold KernelGame.eu
  rw [toPlainEFGOfBoundedHorizon_outcomeKernel_eq_nativeBounded
    (G := G) hBound σ]
  rfl

theorem toPlainEFGOfBoundedHorizon_udistPlayer_eq_efgToFOSG
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs] [Fintype G.History]
    {k : Nat} (hBound : G.BoundedHorizon k)
    (τ : EFG.BehavioralProfile (infoStructure (G := G) k))
    (hτ : EFGProfileRespectsFOSG (G := G) (k := k) τ)
    (p : PlayerIx (ι := ι)) :
    (toPlainEFGOfBoundedHorizon (G := G) hBound).toKernelGame.udistPlayer τ p
      = (G.toKernelGameOfBoundedHorizon hBound).udistPlayer
          (efgToFOSGProfile (G := G) hBound τ hτ) (origPlayer (ι := ι) p) := by
  unfold KernelGame.udistPlayer
  rw [toPlainEFGOfBoundedHorizon_outcomeKernel_eq_efgToFOSG (G := G) hBound τ hτ]
  rfl

theorem toPlainEFGOfBoundedHorizon_eu_eq_efgToFOSG
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs] [Fintype G.History]
    {k : Nat} (hBound : G.BoundedHorizon k)
    (τ : EFG.BehavioralProfile (infoStructure (G := G) k))
    (hτ : EFGProfileRespectsFOSG (G := G) (k := k) τ)
    (p : PlayerIx (ι := ι)) :
    (toPlainEFGOfBoundedHorizon (G := G) hBound).toKernelGame.eu τ p
      = (G.toKernelGameOfBoundedHorizon hBound).eu
          (efgToFOSGProfile (G := G) hBound τ hτ) (origPlayer (ι := ι) p) := by
  unfold KernelGame.eu
  rw [toPlainEFGOfBoundedHorizon_outcomeKernel_eq_efgToFOSG (G := G) hBound τ hτ]
  rfl

/-- Extract the player-view component carried by a bridge EFG node.

This is intentionally informative only at decision nodes: there the EFG infoset
is exactly the encoded original FOSG player view.  Chance and terminal nodes
return the empty word because the current bridge has no replay layer and no
downstream theorem needs non-decision-node native views. -/
noncomputable def nodePlayerView
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    {k : Nat} (p : PlayerIx (ι := ι))
    (node : GameTree (infoStructure (G := G) k) (SerialExec.State G)) :
    EncPlayerView (G := G) (origPlayer (ι := ι) p) k :=
  match node with
  | .decision (p := q) I _ =>
      if hq : q = p then hq ▸ I else Word.ofList (2 * k) []
  | _ => Word.ofList (2 * k) []

/-- The bounded augmented-EFG bridge.  Public states are length-stamped EFG
histories, which is enough for no-thick public sets.  At decision nodes, the
player component carries the encoded original FOSG player view already used as
the EFG infoset. -/
noncomputable def toAugmentedOfBoundedHorizon
    [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
    [Fintype PubObs] [DecidableEq PubObs]
    {k : Nat} (hBound : G.BoundedHorizon k) : EFG.AugmentedGame where
  base := toPlainEFGOfBoundedHorizon (G := G) hBound
  PubState := Nat
  InfoState := fun p =>
    Nat ×
      EncPlayerView (G := G) (origPlayer (ι := ι) p) k
  publicState := fun h => h.hist.length
  playerState := fun p h => (h.hist.length, nodePlayerView (G := G) p h.node)
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
  rcases _hprefix with ⟨suffix, hsuffix⟩
  have hlen : g.hist.length = h.hist.length := hpublic
  have hsuffixLen : suffix.length = 0 := by
    have hsum : g.hist.length + suffix.length = h.hist.length := by
      calc
        g.hist.length + suffix.length = (g.hist ++ suffix).length := by
          rw [List.length_append]
        _ = h.hist.length := congrArg List.length hsuffix
    omega
  have hsuffixNil : suffix = [] := List.eq_nil_of_length_eq_zero hsuffixLen
  calc
    g.hist = g.hist ++ [] := (List.append_nil g.hist).symm
    _ = h.hist := by simpa [hsuffixNil] using hsuffix

end AugmentedEFGBridge

end FOSG

end GameTheory
