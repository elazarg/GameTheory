/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.Bridges.FOSG.AugmentedEFG.Base

/-!
# GameTheory.Languages.Bridges.FOSG.AugmentedEFG

Inverse strategy translation and augmented-game wrapper for the finite-horizon
FOSG-to-EFG bridge.  The forward bridge construction and distributional
correctness facts live in `GameTheory.Languages.Bridges.FOSG.AugmentedEFG.Base`.
-/

namespace GameTheory

namespace FOSG

namespace AugmentedEFGBridge

open EFG
open Math.Probability

variable {ι W : Type}
variable [DecidableEq ι]
variable {Act : ι → Type} {PrivObs : ι → Type} {PubObs : Type}
variable (G : FOSG ι W Act PrivObs PubObs)
variable [Fintype ι] [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]
variable [Fintype W] [DecidablePred G.terminal]

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
    exact hw
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
        unfold Tree.transitionChance
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
