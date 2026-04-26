import GameTheory.Languages.Bridges.FOSG.AugmentedEFG

namespace GameTheory
namespace FOSG

open Math.Probability

namespace AugmentedEFGBridge

open EFG

variable {ι W : Type} [DecidableEq ι] [Fintype ι] [LinearOrder ι] [DecidableEq W]
variable {Act : ι → Type} [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]
variable {PrivObs : ι → Type} {PubObs : Type}
variable (G : FOSG ι W Act PrivObs PubObs)
variable [Fintype W]
variable [DecidablePred G.terminal]
variable [Fact G.LegalObservable]
variable [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
variable [Fintype PubObs] [DecidableEq PubObs]

namespace Semantic

omit [∀ i, DecidableEq (Act i)] [∀ i, DecidableEq (PrivObs i)] [DecidableEq PubObs] in
/-- Local relabeling theorem for semantic-vs-trace decision nodes.

This is the stable seam between the two bridges: they differ only by the
decision-node action indexing, via `viewIndexEquivPositionIndex`. -/
theorem decision_bind_eq_of_children_eq
    {k : Nat} (σ : G.LegalBehavioralProfile) {p : PlayerIx}
    (Ipos : {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)})
    (acc : TracePosition.PayoffVec (G := G) k)
    (hchild :
      ∀ a : Fin (Fintype.card
          (AvailableActionSubtype (G := G) (p := p) (infosetOfPosition (G := G) Ipos).1)),
        (treeFromAccum (G := G)
            (Position.TracePosition.decisionChild (G := G) Ipos
              ((viewIndexEquivPositionIndex (G := G) Ipos) a))
            acc).evalDist
            (translateBehavioralProfile (G := G) σ) =
          (AugmentedEFGBridge.traceTreeFromAccum (G := G)
            (Position.TracePosition.decisionChild (G := G) Ipos
              ((viewIndexEquivPositionIndex (G := G) Ipos) a))
            acc).evalDist
            (Position.translateBehavioralProfile (G := G) σ)) :
    (translateBehavioralProfile (G := G) σ p (infosetOfPosition (G := G) Ipos)).bind
        (fun a =>
          (treeFromAccum (G := G)
            (Position.TracePosition.decisionChild (G := G) Ipos
              ((viewIndexEquivPositionIndex (G := G) Ipos) a))
            acc).evalDist
            (translateBehavioralProfile (G := G) σ)) =
      (Position.translateBehavioralProfile (G := G) σ p Ipos).bind
        (fun a =>
          (AugmentedEFGBridge.traceTreeFromAccum (G := G)
            (Position.TracePosition.decisionChild (G := G) Ipos a)
            acc).evalDist
            (Position.translateBehavioralProfile (G := G) σ)) := by
  exact
    (bind_eq_bind_of_equiv
      (e := viewIndexEquivPositionIndex (G := G) Ipos)
      (μ₁ := translateBehavioralProfile (G := G) σ p (infosetOfPosition (G := G) Ipos))
      (μ₂ := Position.translateBehavioralProfile (G := G) σ p Ipos)
      (f := fun a =>
        (treeFromAccum (G := G)
          (Position.TracePosition.decisionChild (G := G) Ipos
            ((viewIndexEquivPositionIndex (G := G) Ipos) a))
          acc).evalDist
          (translateBehavioralProfile (G := G) σ))
      (g := fun a =>
        (AugmentedEFGBridge.traceTreeFromAccum (G := G)
          (Position.TracePosition.decisionChild (G := G) Ipos a)
          acc).evalDist
          (Position.translateBehavioralProfile (G := G) σ))
      (hμ := fun a =>
        translateBehavioralStrategy_infosetOfPosition_apply (G := G) σ Ipos a)
      (hg := hchild))

omit [DecidableEq W] [∀ i, DecidableEq (Act i)] [DecidablePred G.terminal]
  [∀ i, DecidableEq (PrivObs i)] [DecidableEq PubObs] in
/-- Local equality theorem for semantic-vs-trace chance nodes once child
evaluation agrees pointwise. -/
theorem evalDist_chance_eq_of_children_eq
    {k : Nat} (σ : G.LegalBehavioralProfile) (μ : PMF (SState G))
    (semChild : Fin (Fintype.card (SupportSubtype μ)) →
      GameTree (infoStructure (G := G) k) (Outcome (G := G) k))
    (traceChild : Fin (Fintype.card (SupportSubtype μ)) →
      GameTree (traceInfoStructure (G := G) k) (TraceOutcome (G := G) k))
    (hchild :
      ∀ b,
        (semChild b).evalDist (translateBehavioralProfile (G := G) σ) =
          (traceChild b).evalDist (Position.translateBehavioralProfile (G := G) σ)) :
    (GameTree.chance
      (Fintype.card (SupportSubtype μ))
      (supportPMF μ)
      (supportSubtype_card_pos μ)
      semChild).evalDist
      (translateBehavioralProfile (G := G) σ) =
    (GameTree.chance
      (Fintype.card (SupportSubtype μ))
      (supportPMF μ)
      (supportSubtype_card_pos μ)
      traceChild).evalDist
      (Position.translateBehavioralProfile (G := G) σ) := by
  simpa [EFG.evalDist_chance] using
    (bind_eq_bind_of_equiv
      (e := Equiv.refl _)
      (μ₁ := supportPMF μ)
      (μ₂ := supportPMF μ)
      (f := fun b => (semChild b).evalDist (translateBehavioralProfile (G := G) σ))
      (g := fun b => (traceChild b).evalDist (Position.translateBehavioralProfile (G := G) σ))
      (hμ := fun b => rfl)
      (hg := hchild))

omit [Fintype ι] [DecidableEq W] [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]
  [Fintype W] [DecidablePred G.terminal] [Fact G.LegalObservable]
  [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
  [Fintype PubObs] [DecidableEq PubObs] in
theorem player_eq_none_of_base_empty
    {k : Nat} {pos : TracePosition G k} {w : W}
    (hstate : pos.state = .base w)
    (hrem : pos.remaining ≠ 0)
    (hEmpty : G.orderedActive w = []) :
    pos.player? = none := by
  simp [TracePosition.player?, TracePosition.toPosition, Position.player?,
    Position.isTruncated, hrem, hstate, hEmpty]

omit [Fintype ι] [DecidableEq W] [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]
  [Fintype W] [DecidablePred G.terminal] [Fact G.LegalObservable]
  [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
  [Fintype PubObs] [DecidableEq PubObs] in
theorem player_eq_some_of_base_cons
    {k : Nat} {pos : TracePosition G k} {w : W} {current : ι} {rest : List ι}
    (hstate : pos.state = .base w)
    (hrem : pos.remaining ≠ 0)
    (horder : G.orderedActive w = current :: rest) :
    pos.player? = some current := by
  simp [TracePosition.player?, TracePosition.toPosition, Position.player?,
    Position.isTruncated, hrem, hstate, horder]

omit [Fintype ι] [DecidableEq W] [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]
  [Fintype W] [DecidablePred G.terminal] [Fact G.LegalObservable]
  [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
  [Fintype PubObs] [DecidableEq PubObs] in
theorem player_eq_some_of_decide
    {k : Nat} {pos : TracePosition G k}
    {w : W} {chosen : JointAction Act} {current : ι} {rest : List ι}
    {hvalid : G.ValidDecision w chosen current rest}
    (hstate : pos.state = .decide w chosen current rest hvalid)
    (hrem : pos.remaining ≠ 0) :
    pos.player? = some current := by
  simp [TracePosition.player?, TracePosition.toPosition, Position.player?,
    Position.isTruncated, hrem, hstate]

omit [Fintype ι] [DecidableEq W] [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]
  [Fintype W] [DecidablePred G.terminal] [Fact G.LegalObservable]
  [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
  [Fintype PubObs] [DecidableEq PubObs] in
theorem player_eq_none_of_chance
    {k : Nat} {pos : TracePosition G k} {w : W} {ga : G.LegalAction w}
    (hstate : pos.state = .chance w ga)
    (hrem : pos.remaining ≠ 0) :
    pos.player? = none := by
  simp [TracePosition.player?, TracePosition.toPosition, Position.player?,
    Position.isTruncated, hrem, hstate]

/-- Semantic execution branch for serialized base states, with the active-player
list exposed as an explicit argument. Keeping this branch out of the main
recursive definition avoids forcing Lean to reduce a dependent match on
`G.orderedActive w` inside semantic preservation proofs. -/
noncomputable def runBaseBranch
    {k : Nat}
    (pos0 : TracePosition G k)
    (self : (child : TracePosition G k) → child.remaining < pos0.remaining →
      TracePosition.PayoffVec (G := G) k →
      PMF (Outcome (G := G) k))
    (σ : G.LegalBehavioralProfile)
    {w : W}
    (hstate : pos0.state = .base w)
    (hrem : pos0.remaining ≠ 0)
    (hterm : ¬ (SG G).terminal pos0.state)
    (acc : TracePosition.PayoffVec (G := G) k)
    (order : List ι) (horder : G.orderedActive w = order) :
    PMF (Outcome (G := G) k) :=
  match order with
  | [] =>
      let hplayer : pos0.player? = none := by
        simpa using
          player_eq_none_of_base_empty (G := G) (pos := pos0) hstate hrem horder
      let μ := TracePosition.liveChancePMF (G := G) pos0 hplayer hterm hrem
      (supportPMF μ).bind
        (fun b =>
          let child := TracePosition.chanceChild (G := G) pos0 hplayer hterm hrem b
          let acc' := TracePosition.addPayoff (G := G) acc
            (Position.chanceEdgePayoff (G := G) pos0.toPosition child.state)
          self child
            (by
              simpa [child, TracePosition.chanceChild_remaining, Nat.pred_eq_sub_one] using
                Nat.pred_lt hrem)
            acc')
  | current :: rest =>
      let p : PlayerIx := playerEquiv (ι := ι) current
      have hp : origPlayer (ι := ι) p = current := by
        simp [p, origPlayer, playerEquiv]
      let hI : pos0.player? = some (origPlayer (ι := ι) p) := by
        simpa [hp] using
          player_eq_some_of_base_cons (G := G) (pos := pos0) hstate hrem horder
      let Ipos :
          {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)} :=
        ⟨pos0, hI⟩
      (translateBehavioralProfile (G := G) σ p (infosetOfPosition (G := G) Ipos)).bind
        (fun a =>
          let a' := (viewIndexEquivPositionIndex (G := G) Ipos) a
          let child := Position.TracePosition.decisionChild (G := G) Ipos a'
          self child
            (by
              simpa [child, Ipos, Position.TracePosition.decisionChild_remaining,
                Nat.pred_eq_sub_one] using
                Nat.pred_lt hrem)
            acc)

/-- Trace execution branch for serialized base states, parallel to
`runBaseBranch`. -/
noncomputable def traceBaseBranch
    {k : Nat}
    (pos0 : TracePosition G k)
    (self : (child : TracePosition G k) → child.remaining < pos0.remaining →
      TracePosition.PayoffVec (G := G) k →
      PMF (TraceOutcome (G := G) k))
    (σ : G.LegalBehavioralProfile)
    {w : W}
    (hstate : pos0.state = .base w)
    (hrem : pos0.remaining ≠ 0)
    (hterm : ¬ (SG G).terminal pos0.state)
    (acc : TracePosition.PayoffVec (G := G) k)
    (order : List ι) (horder : G.orderedActive w = order) :
    PMF (TraceOutcome (G := G) k) :=
  match order with
  | [] =>
      let hplayer : pos0.player? = none := by
        simpa using
          player_eq_none_of_base_empty (G := G) (pos := pos0) hstate hrem horder
      let μ := TracePosition.liveChancePMF (G := G) pos0 hplayer hterm hrem
      (supportPMF μ).bind
        (fun b =>
          let child := TracePosition.chanceChild (G := G) pos0 hplayer hterm hrem b
          let acc' := TracePosition.addPayoff (G := G) acc
            (Position.chanceEdgePayoff (G := G) pos0.toPosition child.state)
          self child
            (by
              simpa [child, TracePosition.chanceChild_remaining, Nat.pred_eq_sub_one] using
                Nat.pred_lt hrem)
            acc')
  | current :: rest =>
      let p : PlayerIx := playerEquiv (ι := ι) current
      have hp : origPlayer (ι := ι) p = current := by
        simp [p, origPlayer, playerEquiv]
      let hI : pos0.player? = some (origPlayer (ι := ι) p) := by
        simpa [hp] using
          player_eq_some_of_base_cons (G := G) (pos := pos0) hstate hrem horder
      let Ipos :
          {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)} :=
        ⟨pos0, hI⟩
      (Position.translateBehavioralProfile (G := G) σ p Ipos).bind
        (fun a =>
          let child := Position.TracePosition.decisionChild (G := G) Ipos a
          self child
            (by
              simpa [child, Ipos, Position.TracePosition.decisionChild_remaining,
                Nat.pred_eq_sub_one] using
                Nat.pred_lt hrem)
            acc)

omit [∀ i, DecidableEq (Act i)] [∀ i, DecidableEq (PrivObs i)] [DecidableEq PubObs] in
theorem runBaseBranch_eq_traceBaseBranch
    {k : Nat}
    (pos0 : TracePosition G k)
    {selfSem : (child : TracePosition G k) → child.remaining < pos0.remaining →
      TracePosition.PayoffVec (G := G) k →
      PMF (Outcome (G := G) k)}
    {selfTrace : (child : TracePosition G k) → child.remaining < pos0.remaining →
      TracePosition.PayoffVec (G := G) k →
      PMF (TraceOutcome (G := G) k)}
    (σ : G.LegalBehavioralProfile)
    {w : W}
    (hstate : pos0.state = .base w)
    (hrem : pos0.remaining ≠ 0)
    (hterm : ¬ (SG G).terminal pos0.state)
    (acc : TracePosition.PayoffVec (G := G) k)
    (order : List ι) (horder : G.orderedActive w = order)
    (hself : ∀ child hsem htrace acc',
      selfSem child hsem acc' = selfTrace child htrace acc') :
    runBaseBranch (G := G) pos0 selfSem σ hstate hrem hterm acc order horder =
      traceBaseBranch (G := G) pos0 selfTrace σ hstate hrem hterm acc order horder := by
  cases order with
  | nil =>
      dsimp [runBaseBranch, traceBaseBranch]
      let hplayer : pos0.player? = none := by
        simpa using
          player_eq_none_of_base_empty (G := G) (pos := pos0) hstate hrem horder
      let μ := TracePosition.liveChancePMF (G := G) pos0 hplayer hterm hrem
      exact
        (bind_eq_bind_of_equiv
          (e := Equiv.refl _)
          (μ₁ := supportPMF μ)
          (μ₂ := supportPMF μ)
          (f := fun b =>
            let child := TracePosition.chanceChild (G := G) pos0 hplayer hterm hrem b
            let acc' := TracePosition.addPayoff (G := G) acc
              (Position.chanceEdgePayoff (G := G) pos0.toPosition child.state)
            selfSem child
              (by
                simpa [child, TracePosition.chanceChild_remaining, Nat.pred_eq_sub_one] using
                  Nat.pred_lt hrem)
              acc')
          (g := fun b =>
            let child := TracePosition.chanceChild (G := G) pos0 hplayer hterm hrem b
            let acc' := TracePosition.addPayoff (G := G) acc
              (Position.chanceEdgePayoff (G := G) pos0.toPosition child.state)
            selfTrace child
              (by
                simpa [child, TracePosition.chanceChild_remaining, Nat.pred_eq_sub_one] using
                  Nat.pred_lt hrem)
              acc')
          (hμ := fun b => rfl)
          (hg := fun b => hself _ _ _ _))
  | cons current rest =>
      dsimp [runBaseBranch, traceBaseBranch]
      let p : PlayerIx := playerEquiv (ι := ι) current
      have hp : origPlayer (ι := ι) p = current := by
        simp [p, origPlayer, playerEquiv]
      let hI : pos0.player? = some (origPlayer (ι := ι) p) := by
        simpa [hp] using
          player_eq_some_of_base_cons (G := G) (pos := pos0) hstate hrem horder
      let Ipos :
          {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)} :=
        ⟨pos0, hI⟩
      exact
        (bind_eq_bind_of_equiv
          (e := viewIndexEquivPositionIndex (G := G) Ipos)
          (μ₁ := translateBehavioralProfile (G := G) σ p
            (infosetOfPosition (G := G) Ipos))
          (μ₂ := Position.translateBehavioralProfile (G := G) σ p Ipos)
          (f := fun a =>
            let child := Position.TracePosition.decisionChild (G := G) Ipos
              ((viewIndexEquivPositionIndex (G := G) Ipos) a)
            selfSem child
              (by
                simpa [child, Ipos, Position.TracePosition.decisionChild_remaining,
                  Nat.pred_eq_sub_one] using Nat.pred_lt hrem)
              acc)
          (g := fun a =>
            let child := Position.TracePosition.decisionChild (G := G) Ipos a
            selfTrace child
              (by
                simpa [child, Ipos, Position.TracePosition.decisionChild_remaining,
                  Nat.pred_eq_sub_one] using Nat.pred_lt hrem)
              acc)
          (hμ := fun a =>
            translateBehavioralStrategy_infosetOfPosition_apply (G := G) σ Ipos a)
          (hg := fun a => hself _ _ _ _))

omit [∀ i, DecidableEq (Act i)] [∀ i, DecidableEq (PrivObs i)] [DecidableEq PubObs] in
theorem runBaseBranch_congr
    {k : Nat}
    (pos0 : TracePosition G k)
    {self₁ self₂ : (child : TracePosition G k) → child.remaining < pos0.remaining →
      TracePosition.PayoffVec (G := G) k → PMF (Outcome (G := G) k)}
    (σ : G.LegalBehavioralProfile)
    {w : W}
    (hstate : pos0.state = .base w)
    (hrem : pos0.remaining ≠ 0)
    (hterm : ¬ (SG G).terminal pos0.state)
    (acc : TracePosition.PayoffVec (G := G) k)
    (order : List ι) (horder : G.orderedActive w = order)
    (hself : ∀ child h₁ h₂ acc', self₁ child h₁ acc' = self₂ child h₂ acc') :
    runBaseBranch (G := G) pos0 self₁ σ hstate hrem hterm acc order horder =
      runBaseBranch (G := G) pos0 self₂ σ hstate hrem hterm acc order horder := by
  cases order with
  | nil =>
      dsimp [runBaseBranch]
      let hplayer : pos0.player? = none := by
        simpa using
          player_eq_none_of_base_empty (G := G) (pos := pos0) hstate hrem horder
      let μ := TracePosition.liveChancePMF (G := G) pos0 hplayer hterm hrem
      exact
        (bind_eq_bind_of_equiv
          (e := Equiv.refl _)
          (μ₁ := supportPMF μ)
          (μ₂ := supportPMF μ)
          (f := fun b =>
            let child := TracePosition.chanceChild (G := G) pos0 hplayer hterm hrem b
            let acc' := TracePosition.addPayoff (G := G) acc
              (Position.chanceEdgePayoff (G := G) pos0.toPosition child.state)
            self₁ child
              (by
                simpa [child, TracePosition.chanceChild_remaining, Nat.pred_eq_sub_one] using
                  Nat.pred_lt hrem)
              acc')
          (g := fun b =>
            let child := TracePosition.chanceChild (G := G) pos0 hplayer hterm hrem b
            let acc' := TracePosition.addPayoff (G := G) acc
              (Position.chanceEdgePayoff (G := G) pos0.toPosition child.state)
            self₂ child
              (by
                simpa [child, TracePosition.chanceChild_remaining, Nat.pred_eq_sub_one] using
                  Nat.pred_lt hrem)
              acc')
          (hμ := fun b => rfl)
          (hg := fun b => hself _ _ _ _))
  | cons current rest =>
      dsimp [runBaseBranch]
      let p : PlayerIx := playerEquiv (ι := ι) current
      have hp : origPlayer (ι := ι) p = current := by
        simp [p, origPlayer, playerEquiv]
      let hI : pos0.player? = some (origPlayer (ι := ι) p) := by
        simpa [hp] using
          player_eq_some_of_base_cons (G := G) (pos := pos0) hstate hrem horder
      let Ipos :
          {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)} :=
        ⟨pos0, hI⟩
      exact
        (bind_eq_bind_of_equiv
          (e := Equiv.refl _)
          (μ₁ := translateBehavioralProfile (G := G) σ p
            (infosetOfPosition (G := G) Ipos))
          (μ₂ := translateBehavioralProfile (G := G) σ p
            (infosetOfPosition (G := G) Ipos))
          (f := fun a =>
            let a' := (viewIndexEquivPositionIndex (G := G) Ipos) a
            let child := Position.TracePosition.decisionChild (G := G) Ipos a'
            self₁ child
              (by
                simpa [child, Ipos, Position.TracePosition.decisionChild_remaining,
                  Nat.pred_eq_sub_one] using Nat.pred_lt hrem)
              acc)
          (g := fun a =>
            let a' := (viewIndexEquivPositionIndex (G := G) Ipos) a
            let child := Position.TracePosition.decisionChild (G := G) Ipos a'
            self₂ child
              (by
                simpa [child, Ipos, Position.TracePosition.decisionChild_remaining,
                  Nat.pred_eq_sub_one] using Nat.pred_lt hrem)
              acc)
          (hμ := fun a => rfl)
          (hg := fun a => hself _ _ _ _))

omit [∀ i, DecidableEq (Act i)] [Fact G.LegalObservable]
  [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
  [Fintype PubObs] [DecidableEq PubObs] in
theorem traceBaseBranch_congr
    {k : Nat}
    (pos0 : TracePosition G k)
    {self₁ self₂ : (child : TracePosition G k) → child.remaining < pos0.remaining →
      TracePosition.PayoffVec (G := G) k → PMF (TraceOutcome (G := G) k)}
    (σ : G.LegalBehavioralProfile)
    {w : W}
    (hstate : pos0.state = .base w)
    (hrem : pos0.remaining ≠ 0)
    (hterm : ¬ (SG G).terminal pos0.state)
    (acc : TracePosition.PayoffVec (G := G) k)
    (order : List ι) (horder : G.orderedActive w = order)
    (hself : ∀ child h₁ h₂ acc', self₁ child h₁ acc' = self₂ child h₂ acc') :
    traceBaseBranch (G := G) pos0 self₁ σ hstate hrem hterm acc order horder =
      traceBaseBranch (G := G) pos0 self₂ σ hstate hrem hterm acc order horder := by
  cases order with
  | nil =>
      dsimp [traceBaseBranch]
      let hplayer : pos0.player? = none := by
        simpa using
          player_eq_none_of_base_empty (G := G) (pos := pos0) hstate hrem horder
      let μ := TracePosition.liveChancePMF (G := G) pos0 hplayer hterm hrem
      exact
        (bind_eq_bind_of_equiv
          (e := Equiv.refl _)
          (μ₁ := supportPMF μ)
          (μ₂ := supportPMF μ)
          (f := fun b =>
            let child := TracePosition.chanceChild (G := G) pos0 hplayer hterm hrem b
            let acc' := TracePosition.addPayoff (G := G) acc
              (Position.chanceEdgePayoff (G := G) pos0.toPosition child.state)
            self₁ child
              (by
                simpa [child, TracePosition.chanceChild_remaining, Nat.pred_eq_sub_one] using
                  Nat.pred_lt hrem)
              acc')
          (g := fun b =>
            let child := TracePosition.chanceChild (G := G) pos0 hplayer hterm hrem b
            let acc' := TracePosition.addPayoff (G := G) acc
              (Position.chanceEdgePayoff (G := G) pos0.toPosition child.state)
            self₂ child
              (by
                simpa [child, TracePosition.chanceChild_remaining, Nat.pred_eq_sub_one] using
                  Nat.pred_lt hrem)
              acc')
          (hμ := fun b => rfl)
          (hg := fun b => hself _ _ _ _))
  | cons current rest =>
      dsimp [traceBaseBranch]
      let p : PlayerIx := playerEquiv (ι := ι) current
      have hp : origPlayer (ι := ι) p = current := by
        simp [p, origPlayer, playerEquiv]
      let hI : pos0.player? = some (origPlayer (ι := ι) p) := by
        simpa [hp] using
          player_eq_some_of_base_cons (G := G) (pos := pos0) hstate hrem horder
      let Ipos :
          {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)} :=
        ⟨pos0, hI⟩
      exact
        (bind_eq_bind_of_equiv
          (e := Equiv.refl _)
          (μ₁ := Position.translateBehavioralProfile (G := G) σ p Ipos)
          (μ₂ := Position.translateBehavioralProfile (G := G) σ p Ipos)
          (f := fun a =>
            let child := Position.TracePosition.decisionChild (G := G) Ipos a
            self₁ child
              (by
                simpa [child, Ipos, Position.TracePosition.decisionChild_remaining,
                  Nat.pred_eq_sub_one] using Nat.pred_lt hrem)
              acc)
          (g := fun a =>
            let child := Position.TracePosition.decisionChild (G := G) Ipos a
            self₂ child
              (by
                simpa [child, Ipos, Position.TracePosition.decisionChild_remaining,
                  Nat.pred_eq_sub_one] using Nat.pred_lt hrem)
              acc)
          (hμ := fun a => rfl)
          (hg := fun a => hself _ _ _ _))

omit [∀ i, DecidableEq (Act i)] [Fact G.LegalObservable]
  [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
  [Fintype PubObs] [DecidableEq PubObs] in
/-- Evaluation of the trace-indexed EFG base branch agrees with the explicit
trace run-distribution branch, assuming recursive children agree. -/
theorem traceTreeBaseBranch_evalDist_eq_traceBaseBranch
    {k : Nat}
    (pos0 : TracePosition G k)
    {selfTree : (child : TracePosition G k) → child.remaining < pos0.remaining →
      TracePosition.PayoffVec (G := G) k →
      GameTree (traceInfoStructure (G := G) k) (TraceOutcome (G := G) k)}
    {selfDist : (child : TracePosition G k) → child.remaining < pos0.remaining →
      TracePosition.PayoffVec (G := G) k → PMF (TraceOutcome (G := G) k)}
    (σ : G.LegalBehavioralProfile)
    {w : W}
    (hstate : pos0.state = .base w)
    (hrem : pos0.remaining ≠ 0)
    (hterm : ¬ (SG G).terminal pos0.state)
    (acc : TracePosition.PayoffVec (G := G) k)
    (order : List ι) (horder : G.orderedActive w = order)
    (hself : ∀ child htree hdist acc',
      (selfTree child htree acc').evalDist
          (Position.translateBehavioralProfile (G := G) σ) =
        selfDist child hdist acc') :
    (AugmentedEFGBridge.traceTreeBaseBranch (G := G) pos0 selfTree
        hstate hrem hterm acc order horder).evalDist
        (Position.translateBehavioralProfile (G := G) σ) =
      traceBaseBranch (G := G) pos0 selfDist σ
        hstate hrem hterm acc order horder := by
  cases order with
  | nil =>
      dsimp [AugmentedEFGBridge.traceTreeBaseBranch, traceBaseBranch]
      let hplayer : pos0.player? = none := by
        simpa using
          player_eq_none_of_base_empty (G := G) (pos := pos0) hstate hrem horder
      let μ := TracePosition.liveChancePMF (G := G) pos0 hplayer hterm hrem
      exact
        (bind_eq_bind_of_equiv
          (e := Equiv.refl _)
          (μ₁ := supportPMF μ)
          (μ₂ := supportPMF μ)
          (f := fun b =>
            let child := TracePosition.chanceChild (G := G) pos0 hplayer hterm hrem b
            let acc' := TracePosition.addPayoff (G := G) acc
              (Position.chanceEdgePayoff (G := G) pos0.toPosition child.state)
            (selfTree child
              (by
                simpa [child, TracePosition.chanceChild_remaining, Nat.pred_eq_sub_one] using
                  Nat.pred_lt hrem)
              acc').evalDist (Position.translateBehavioralProfile (G := G) σ))
          (g := fun b =>
            let child := TracePosition.chanceChild (G := G) pos0 hplayer hterm hrem b
            let acc' := TracePosition.addPayoff (G := G) acc
              (Position.chanceEdgePayoff (G := G) pos0.toPosition child.state)
            selfDist child
              (by
                simpa [child, TracePosition.chanceChild_remaining, Nat.pred_eq_sub_one] using
                  Nat.pred_lt hrem)
              acc')
          (hμ := fun b => rfl)
          (hg := fun b => hself _ _ _ _))
  | cons current rest =>
      dsimp [AugmentedEFGBridge.traceTreeBaseBranch, traceBaseBranch]
      let p : PlayerIx := playerEquiv (ι := ι) current
      have hp : origPlayer (ι := ι) p = current := by
        simp [p, origPlayer, playerEquiv]
      let hI : pos0.player? = some (origPlayer (ι := ι) p) := by
        simpa [hp] using
          player_eq_some_of_base_cons (G := G) (pos := pos0) hstate hrem horder
      let Ipos :
          {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)} :=
        ⟨pos0, hI⟩
      exact
        (bind_eq_bind_of_equiv
          (e := Equiv.refl _)
          (μ₁ := Position.translateBehavioralProfile (G := G) σ p Ipos)
          (μ₂ := Position.translateBehavioralProfile (G := G) σ p Ipos)
          (f := fun a =>
            let child := Position.TracePosition.decisionChild (G := G) Ipos a
            (selfTree child
              (by
                simpa [child, Ipos, Position.TracePosition.decisionChild_remaining,
                  Nat.pred_eq_sub_one] using Nat.pred_lt hrem)
              acc).evalDist (Position.translateBehavioralProfile (G := G) σ))
          (g := fun a =>
            let child := Position.TracePosition.decisionChild (G := G) Ipos a
            selfDist child
              (by
                simpa [child, Ipos, Position.TracePosition.decisionChild_remaining,
                  Nat.pred_eq_sub_one] using Nat.pred_lt hrem)
              acc)
          (hμ := fun a => rfl)
          (hg := fun a => hself _ _ _ _))

omit [∀ i, DecidableEq (Act i)] [∀ i, DecidableEq (PrivObs i)] [DecidableEq PubObs] in
/-- Evaluation of the semantic-view EFG base branch agrees with the explicit
semantic run-distribution branch, assuming recursive children agree. -/
theorem treeBaseBranch_evalDist_eq_runBaseBranch
    {k : Nat}
    (pos0 : TracePosition G k)
    {selfTree : (child : TracePosition G k) → child.remaining < pos0.remaining →
      TracePosition.PayoffVec (G := G) k →
      GameTree (infoStructure (G := G) k) (Outcome (G := G) k)}
    {selfDist : (child : TracePosition G k) → child.remaining < pos0.remaining →
      TracePosition.PayoffVec (G := G) k → PMF (Outcome (G := G) k)}
    (σ : G.LegalBehavioralProfile)
    {w : W}
    (hstate : pos0.state = .base w)
    (hrem : pos0.remaining ≠ 0)
    (hterm : ¬ (SG G).terminal pos0.state)
    (acc : TracePosition.PayoffVec (G := G) k)
    (order : List ι) (horder : G.orderedActive w = order)
    (hself : ∀ child htree hdist acc',
      (selfTree child htree acc').evalDist
          (translateBehavioralProfile (G := G) σ) =
        selfDist child hdist acc') :
    (treeBaseBranch (G := G) pos0 selfTree
        hstate hrem hterm acc order horder).evalDist
        (translateBehavioralProfile (G := G) σ) =
      runBaseBranch (G := G) pos0 selfDist σ
        hstate hrem hterm acc order horder := by
  cases order with
  | nil =>
      dsimp [treeBaseBranch, runBaseBranch]
      let hplayer : pos0.player? = none := by
        simpa using
          player_eq_none_of_base_empty (G := G) (pos := pos0) hstate hrem horder
      let μ := TracePosition.liveChancePMF (G := G) pos0 hplayer hterm hrem
      exact
        (bind_eq_bind_of_equiv
          (e := Equiv.refl _)
          (μ₁ := supportPMF μ)
          (μ₂ := supportPMF μ)
          (f := fun b =>
            let child := TracePosition.chanceChild (G := G) pos0 hplayer hterm hrem b
            let acc' := TracePosition.addPayoff (G := G) acc
              (Position.chanceEdgePayoff (G := G) pos0.toPosition child.state)
            (selfTree child
              (by
                simpa [child, TracePosition.chanceChild_remaining, Nat.pred_eq_sub_one] using
                  Nat.pred_lt hrem)
              acc').evalDist (translateBehavioralProfile (G := G) σ))
          (g := fun b =>
            let child := TracePosition.chanceChild (G := G) pos0 hplayer hterm hrem b
            let acc' := TracePosition.addPayoff (G := G) acc
              (Position.chanceEdgePayoff (G := G) pos0.toPosition child.state)
            selfDist child
              (by
                simpa [child, TracePosition.chanceChild_remaining, Nat.pred_eq_sub_one] using
                  Nat.pred_lt hrem)
              acc')
          (hμ := fun b => rfl)
          (hg := fun b => hself _ _ _ _))
  | cons current rest =>
      dsimp [treeBaseBranch, runBaseBranch]
      let p : PlayerIx := playerEquiv (ι := ι) current
      have hp : origPlayer (ι := ι) p = current := by
        simp [p, origPlayer, playerEquiv]
      let hI : pos0.player? = some (origPlayer (ι := ι) p) := by
        simpa [hp] using
          player_eq_some_of_base_cons (G := G) (pos := pos0) hstate hrem horder
      let Ipos :
          {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)} :=
        ⟨pos0, hI⟩
      exact
        (bind_eq_bind_of_equiv
          (e := Equiv.refl _)
          (μ₁ := translateBehavioralProfile (G := G) σ p (infosetOfPosition (G := G) Ipos))
          (μ₂ := translateBehavioralProfile (G := G) σ p (infosetOfPosition (G := G) Ipos))
          (f := fun a =>
            let a' := (viewIndexEquivPositionIndex (G := G) Ipos) a
            let child := Position.TracePosition.decisionChild (G := G) Ipos a'
            (selfTree child
              (by
                simpa [child, Ipos, Position.TracePosition.decisionChild_remaining,
                  Nat.pred_eq_sub_one] using Nat.pred_lt hrem)
              acc).evalDist (translateBehavioralProfile (G := G) σ))
          (g := fun a =>
            let a' := (viewIndexEquivPositionIndex (G := G) Ipos) a
            let child := Position.TracePosition.decisionChild (G := G) Ipos a'
            selfDist child
              (by
                simpa [child, Ipos, Position.TracePosition.decisionChild_remaining,
                  Nat.pred_eq_sub_one] using Nat.pred_lt hrem)
              acc)
          (hμ := fun a => rfl)
          (hg := fun a => hself _ _ _ _))

noncomputable def runDistAccum
    {k : Nat} (σ : G.LegalBehavioralProfile) (pos : TracePosition G k)
    (acc : TracePosition.PayoffVec (G := G) k) :
    PMF (Outcome (G := G) k) :=
  if hrem : pos.remaining = 0 then
    PMF.pure (pos, acc)
  else if hterm : (SG G).terminal pos.state then
    PMF.pure (pos, acc)
  else
    match pos with
    | ⟨state, trail, remaining, hremaining, hlen, hchain, hlast⟩ =>
    match state with
    | .base w =>
        let pos0 : TracePosition G k :=
          ⟨.base w, trail, remaining, hremaining, hlen, hchain, hlast⟩
        have hrem0 : pos0.remaining ≠ 0 := by
          simpa [pos0] using hrem
        have hterm0 : ¬ (SG G).terminal pos0.state := by
          simpa [pos0] using hterm
        runBaseBranch (G := G) pos0 (fun child hchild acc' => runDistAccum σ child acc') σ
          (by rfl) hrem0 hterm0 acc (G.orderedActive w) rfl
    | .decide w chosen current rest hvalid =>
        let pos0 : TracePosition G k :=
          ⟨.decide w chosen current rest hvalid, trail, remaining, hremaining, hlen, hchain, hlast⟩
        have hrem0 : pos0.remaining ≠ 0 := by
          simpa [pos0] using hrem
        let p : PlayerIx := playerEquiv (ι := ι) current
        have hp : origPlayer (ι := ι) p = current := by
          simp [p, origPlayer, playerEquiv]
        let hI : pos0.player? = some (origPlayer (ι := ι) p) := by
          simpa [hp] using
            player_eq_some_of_decide (G := G) (pos := pos0) (by rfl) hrem0
        let Ipos :
            {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)} :=
          ⟨pos0, hI⟩
        (translateBehavioralProfile (G := G) σ p (infosetOfPosition (G := G) Ipos)).bind
          (fun a =>
            let a' := (viewIndexEquivPositionIndex (G := G) Ipos) a
            runDistAccum σ (Position.TracePosition.decisionChild (G := G) Ipos a') acc)
    | .chance w ga =>
        let pos0 : TracePosition G k :=
          ⟨.chance w ga, trail, remaining, hremaining, hlen, hchain, hlast⟩
        have hrem0 : pos0.remaining ≠ 0 := by
          simpa [pos0] using hrem
        have hterm0 : ¬ (SG G).terminal pos0.state := by
          simpa [pos0] using hterm
        let hplayer : pos0.player? = none := by
          simpa [pos0] using
            player_eq_none_of_chance (G := G) (pos := pos0) (by rfl) hrem0
        let μ := TracePosition.liveChancePMF (G := G) pos0 hplayer hterm0 hrem0
        (supportPMF μ).bind
          (fun b =>
            let child := TracePosition.chanceChild (G := G) pos0 hplayer hterm0 hrem0 b
            let acc' := TracePosition.addPayoff (G := G) acc
              (Position.chanceEdgePayoff (G := G) pos0.toPosition child.state)
            runDistAccum σ child acc')
termination_by pos.remaining
decreasing_by
  all_goals
    first
    | assumption
    | have hlt : remaining - 1 < remaining :=
        Nat.sub_lt (Nat.pos_of_ne_zero hrem) (by decide)
      simpa [Ipos, pos0, Position.TracePosition.decisionChild_remaining] using hlt
    | simpa [Ipos, Position.TracePosition.decisionChild_remaining,
        TracePosition.chanceChild_remaining, Nat.pred_eq_sub_one] using
        Nat.pred_lt hrem
    | simpa [Position.TracePosition.decisionChild_remaining,
        TracePosition.chanceChild_remaining, Nat.pred_eq_sub_one] using
        Nat.pred_lt hrem

noncomputable def traceRunDistAccum
    {k : Nat} (σ : G.LegalBehavioralProfile) (pos : TracePosition G k)
    (acc : TracePosition.PayoffVec (G := G) k) :
    PMF (TraceOutcome (G := G) k) :=
  if hrem : pos.remaining = 0 then
    PMF.pure (pos, acc)
  else if hterm : (SG G).terminal pos.state then
    PMF.pure (pos, acc)
  else
    match pos with
    | ⟨state, trail, remaining, hremaining, hlen, hchain, hlast⟩ =>
    match state with
    | .base w =>
        let pos0 : TracePosition G k :=
          ⟨.base w, trail, remaining, hremaining, hlen, hchain, hlast⟩
        have hrem0 : pos0.remaining ≠ 0 := by
          simpa [pos0] using hrem
        have hterm0 : ¬ (SG G).terminal pos0.state := by
          simpa [pos0] using hterm
        traceBaseBranch (G := G) pos0 (fun child hchild acc' => traceRunDistAccum σ child acc') σ
          (by rfl) hrem0 hterm0 acc (G.orderedActive w) rfl
    | .decide w chosen current rest hvalid =>
        let pos0 : TracePosition G k :=
          ⟨.decide w chosen current rest hvalid, trail, remaining, hremaining, hlen, hchain, hlast⟩
        have hrem0 : pos0.remaining ≠ 0 := by
          simpa [pos0] using hrem
        let p : PlayerIx := playerEquiv (ι := ι) current
        have hp : origPlayer (ι := ι) p = current := by
          simp [p, origPlayer, playerEquiv]
        let hI : pos0.player? = some (origPlayer (ι := ι) p) := by
          simpa [hp] using
            player_eq_some_of_decide (G := G) (pos := pos0) (by rfl) hrem0
        let Ipos :
            {pos : TracePosition G k // pos.player? = some (origPlayer (ι := ι) p)} :=
          ⟨pos0, hI⟩
        (Position.translateBehavioralProfile (G := G) σ p Ipos).bind
          (fun a =>
            traceRunDistAccum σ (Position.TracePosition.decisionChild (G := G) Ipos a) acc)
    | .chance w ga =>
        let pos0 : TracePosition G k :=
          ⟨.chance w ga, trail, remaining, hremaining, hlen, hchain, hlast⟩
        have hrem0 : pos0.remaining ≠ 0 := by
          simpa [pos0] using hrem
        have hterm0 : ¬ (SG G).terminal pos0.state := by
          simpa [pos0] using hterm
        let hplayer : pos0.player? = none := by
          simpa [pos0] using
            player_eq_none_of_chance (G := G) (pos := pos0) (by rfl) hrem0
        let μ := TracePosition.liveChancePMF (G := G) pos0 hplayer hterm0 hrem0
        (supportPMF μ).bind
          (fun b =>
            let child := TracePosition.chanceChild (G := G) pos0 hplayer hterm0 hrem0 b
            let acc' := TracePosition.addPayoff (G := G) acc
              (Position.chanceEdgePayoff (G := G) pos0.toPosition child.state)
            traceRunDistAccum σ child acc')
termination_by pos.remaining
decreasing_by
  all_goals
    first
    | assumption
    | simpa [Ipos, Position.TracePosition.decisionChild_remaining,
        TracePosition.chanceChild_remaining, Nat.pred_eq_sub_one] using
        Nat.pred_lt hrem
    | simpa [Position.TracePosition.decisionChild_remaining,
        TracePosition.chanceChild_remaining, Nat.pred_eq_sub_one] using
        Nat.pred_lt hrem

omit [∀ i, DecidableEq (Act i)] [∀ i, DecidableEq (PrivObs i)] [DecidableEq PubObs] in
theorem runDistAccum_eq_traceRunDistAccum
    {k : Nat} (σ : G.LegalBehavioralProfile) (pos : TracePosition G k)
    (acc : TracePosition.PayoffVec (G := G) k) :
    runDistAccum (G := G) σ pos acc =
      traceRunDistAccum (G := G) σ pos acc := by
  let P : Nat → Prop := fun n =>
    ∀ (pos : TracePosition G k) (acc : TracePosition.PayoffVec (G := G) k),
      pos.remaining = n →
        runDistAccum (G := G) σ pos acc =
          traceRunDistAccum (G := G) σ pos acc
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro pos acc hn
        rw [runDistAccum, traceRunDistAccum]
        by_cases hrem : pos.remaining = 0
        · simp [hrem]
        · simp [hrem]
          by_cases hterm : (SG G).terminal pos.state
          · simp [hterm]
          · simp [hterm]
            match pos with
            | ⟨state, trail, remaining, hremaining, hlen, hchain, hlast⟩ =>
            match state with
            | .base w =>
                let pos0 : TracePosition G k :=
                  ⟨.base w, trail, remaining, hremaining, hlen, hchain, hlast⟩
                have hrem0 : pos0.remaining ≠ 0 := by
                  simpa [pos0] using hrem
                have hterm0 : ¬ (SG G).terminal pos0.state := by
                  simpa [pos0] using hterm
                exact
                  runBaseBranch_eq_traceBaseBranch (G := G) pos0 σ
                    (by rfl) hrem0 hterm0 acc (G.orderedActive w) rfl
                    (by
                      intro child hsem htrace acc'
                      exact ih child.remaining
                        (by
                          rw [← hn]
                          simpa [pos0] using hsem)
                        child acc' rfl)
            | .decide w chosen current rest hvalid =>
                let pos0 : TracePosition G k :=
                  ⟨.decide w chosen current rest hvalid, trail, remaining,
                    hremaining, hlen, hchain, hlast⟩
                have hrem0 : pos0.remaining ≠ 0 := by
                  simpa [pos0] using hrem
                let p : PlayerIx := playerEquiv (ι := ι) current
                have hp : origPlayer (ι := ι) p = current := by
                  simp [p, origPlayer, playerEquiv]
                let hI : pos0.player? = some (origPlayer (ι := ι) p) := by
                  simpa [hp] using
                    player_eq_some_of_decide (G := G) (pos := pos0) (by rfl) hrem0
                let Ipos :
                    {pos : TracePosition G k //
                      pos.player? = some (origPlayer (ι := ι) p)} :=
                  ⟨pos0, hI⟩
                exact
                  (bind_eq_bind_of_equiv
                    (e := viewIndexEquivPositionIndex (G := G) Ipos)
                    (μ₁ := translateBehavioralProfile (G := G) σ p
                      (infosetOfPosition (G := G) Ipos))
                    (μ₂ := Position.translateBehavioralProfile (G := G) σ p Ipos)
                    (f := fun a =>
                      runDistAccum (G := G) σ
                        (Position.TracePosition.decisionChild (G := G) Ipos
                          ((viewIndexEquivPositionIndex (G := G) Ipos) a))
                        acc)
                    (g := fun a =>
                      traceRunDistAccum (G := G) σ
                        (Position.TracePosition.decisionChild (G := G) Ipos a)
                        acc)
                    (hμ := fun a =>
                      translateBehavioralStrategy_infosetOfPosition_apply (G := G) σ Ipos a)
                    (hg := fun a =>
                      let child := Position.TracePosition.decisionChild (G := G) Ipos
                        ((viewIndexEquivPositionIndex (G := G) Ipos) a)
                      ih child.remaining
                        (by
                          have hlt : child.remaining < pos0.remaining := by
                            simpa [child, Ipos, Position.TracePosition.decisionChild_remaining,
                              Nat.pred_eq_sub_one] using Nat.pred_lt hrem0
                          rw [← hn]
                          simpa [pos0] using hlt)
                        child acc rfl))
            | .chance w ga =>
                let pos0 : TracePosition G k :=
                  ⟨.chance w ga, trail, remaining, hremaining, hlen, hchain, hlast⟩
                have hrem0 : pos0.remaining ≠ 0 := by
                  simpa [pos0] using hrem
                have hterm0 : ¬ (SG G).terminal pos0.state := by
                  simpa [pos0] using hterm
                let hplayer : pos0.player? = none := by
                  simpa [pos0] using
                    player_eq_none_of_chance (G := G) (pos := pos0) (by rfl) hrem0
                let μ := TracePosition.liveChancePMF (G := G) pos0 hplayer hterm0 hrem0
                exact
                  (bind_eq_bind_of_equiv
                    (e := Equiv.refl _)
                    (μ₁ := supportPMF μ)
                    (μ₂ := supportPMF μ)
                    (f := fun b =>
                      let child := TracePosition.chanceChild (G := G) pos0 hplayer hterm0 hrem0 b
                      let acc' := TracePosition.addPayoff (G := G) acc
                        (Position.chanceEdgePayoff (G := G) pos0.toPosition child.state)
                      runDistAccum (G := G) σ child acc')
                    (g := fun b =>
                      let child := TracePosition.chanceChild (G := G) pos0 hplayer hterm0 hrem0 b
                      let acc' := TracePosition.addPayoff (G := G) acc
                        (Position.chanceEdgePayoff (G := G) pos0.toPosition child.state)
                      traceRunDistAccum (G := G) σ child acc')
                    (hμ := fun b => rfl)
                    (hg := fun b =>
                      let child := TracePosition.chanceChild (G := G) pos0 hplayer hterm0 hrem0 b
                      let acc' := TracePosition.addPayoff (G := G) acc
                        (Position.chanceEdgePayoff (G := G) pos0.toPosition child.state)
                      ih child.remaining
                        (by
                          have hlt : child.remaining < pos0.remaining := by
                            simpa [child, TracePosition.chanceChild_remaining,
                              Nat.pred_eq_sub_one] using Nat.pred_lt hrem0
                          rw [← hn]
                          simpa [pos0] using hlt)
                        child acc' rfl))
  exact hP pos.remaining pos acc rfl

omit [∀ i, DecidableEq (Act i)] [Fact G.LegalObservable]
  [∀ i, Fintype (PrivObs i)] [∀ i, DecidableEq (PrivObs i)]
  [Fintype PubObs] [DecidableEq PubObs] in
/-- The trace-indexed EFG tree evaluates to the explicit trace run
distribution. This theorem connects the structural EFG unrolling to the
state-first execution recursion. -/
theorem traceTreeFromAccum_evalDist_eq_traceRunDistAccum
    {k : Nat} (σ : G.LegalBehavioralProfile) (pos : TracePosition G k)
    (acc : TracePosition.PayoffVec (G := G) k) :
    (AugmentedEFGBridge.traceTreeFromAccum (G := G) pos acc).evalDist
        (Position.translateBehavioralProfile (G := G) σ) =
      traceRunDistAccum (G := G) σ pos acc := by
  let P : Nat → Prop := fun n =>
    ∀ (pos : TracePosition G k) (acc : TracePosition.PayoffVec (G := G) k),
      pos.remaining = n →
        (AugmentedEFGBridge.traceTreeFromAccum (G := G) pos acc).evalDist
            (Position.translateBehavioralProfile (G := G) σ) =
          traceRunDistAccum (G := G) σ pos acc
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro pos acc hn
        rw [AugmentedEFGBridge.traceTreeFromAccum, traceRunDistAccum]
        by_cases hrem : pos.remaining = 0
        · simp [hrem]
        · simp [hrem]
          by_cases hterm : (SG G).terminal pos.state
          · simp [hterm]
          · simp [hterm]
            match pos with
            | ⟨state, trail, remaining, hremaining, hlen, hchain, hlast⟩ =>
            match state with
            | .base w =>
                let pos0 : TracePosition G k :=
                  ⟨.base w, trail, remaining, hremaining, hlen, hchain, hlast⟩
                have hrem0 : pos0.remaining ≠ 0 := by
                  simpa [pos0] using hrem
                have hterm0 : ¬ (SG G).terminal pos0.state := by
                  simpa [pos0] using hterm
                exact
                  traceTreeBaseBranch_evalDist_eq_traceBaseBranch (G := G) pos0 σ
                    (by rfl) hrem0 hterm0 acc (G.orderedActive w) rfl
                    (by
                      intro child htree hdist acc'
                      exact ih child.remaining
                        (by
                          rw [← hn]
                          simpa [pos0] using htree)
                        child acc' rfl)
            | .decide w chosen current rest hvalid =>
                let pos0 : TracePosition G k :=
                  ⟨.decide w chosen current rest hvalid, trail, remaining, hremaining, hlen,
                    hchain, hlast⟩
                have hrem0 : pos0.remaining ≠ 0 := by
                  simpa [pos0] using hrem
                let p : PlayerIx := playerEquiv (ι := ι) current
                have hp : origPlayer (ι := ι) p = current := by
                  simp [p, origPlayer, playerEquiv]
                let hI : pos0.player? = some (origPlayer (ι := ι) p) := by
                  simpa [hp] using
                    player_eq_some_of_decide (G := G) (pos := pos0) (by rfl) hrem0
                let Ipos :
                    {pos : TracePosition G k //
                      pos.player? = some (origPlayer (ι := ι) p)} :=
                  ⟨pos0, hI⟩
                exact
                  (bind_eq_bind_of_equiv
                    (e := Equiv.refl _)
                    (μ₁ := Position.translateBehavioralProfile (G := G) σ p Ipos)
                    (μ₂ := Position.translateBehavioralProfile (G := G) σ p Ipos)
                    (f := fun a =>
                      (AugmentedEFGBridge.traceTreeFromAccum (G := G)
                        (Position.TracePosition.decisionChild (G := G) Ipos a)
                        acc).evalDist (Position.translateBehavioralProfile (G := G) σ))
                    (g := fun a =>
                      traceRunDistAccum (G := G) σ
                        (Position.TracePosition.decisionChild (G := G) Ipos a)
                        acc)
                    (hμ := fun a => rfl)
                    (hg := fun a =>
                      let child := Position.TracePosition.decisionChild (G := G) Ipos a
                      ih child.remaining
                        (by
                          have hlt : child.remaining < pos0.remaining := by
                            simpa [child, Ipos, Position.TracePosition.decisionChild_remaining,
                              Nat.pred_eq_sub_one] using Nat.pred_lt hrem0
                          rw [← hn]
                          simpa [pos0] using hlt)
                        child acc rfl))
            | .chance w ga =>
                let pos0 : TracePosition G k :=
                  ⟨.chance w ga, trail, remaining, hremaining, hlen, hchain, hlast⟩
                have hrem0 : pos0.remaining ≠ 0 := by
                  simpa [pos0] using hrem
                have hterm0 : ¬ (SG G).terminal pos0.state := by
                  simpa [pos0] using hterm
                let hplayer : pos0.player? = none := by
                  simpa [pos0] using
                    player_eq_none_of_chance (G := G) (pos := pos0) (by rfl) hrem0
                let μ := TracePosition.liveChancePMF (G := G) pos0 hplayer hterm0 hrem0
                exact
                  (bind_eq_bind_of_equiv
                    (e := Equiv.refl _)
                    (μ₁ := supportPMF μ)
                    (μ₂ := supportPMF μ)
                    (f := fun b =>
                      let child := TracePosition.chanceChild (G := G) pos0 hplayer hterm0 hrem0 b
                      let acc' := TracePosition.addPayoff (G := G) acc
                        (Position.chanceEdgePayoff (G := G) pos0.toPosition child.state)
                      (AugmentedEFGBridge.traceTreeFromAccum (G := G) child acc').evalDist
                        (Position.translateBehavioralProfile (G := G) σ))
                    (g := fun b =>
                      let child := TracePosition.chanceChild (G := G) pos0 hplayer hterm0 hrem0 b
                      let acc' := TracePosition.addPayoff (G := G) acc
                        (Position.chanceEdgePayoff (G := G) pos0.toPosition child.state)
                      traceRunDistAccum (G := G) σ child acc')
                    (hμ := fun b => rfl)
                    (hg := fun b =>
                      let child := TracePosition.chanceChild (G := G) pos0 hplayer hterm0 hrem0 b
                      let acc' := TracePosition.addPayoff (G := G) acc
                        (Position.chanceEdgePayoff (G := G) pos0.toPosition child.state)
                      ih child.remaining
                        (by
                          have hlt : child.remaining < pos0.remaining := by
                            simpa [child, TracePosition.chanceChild_remaining,
                              Nat.pred_eq_sub_one] using Nat.pred_lt hrem0
                          rw [← hn]
                          simpa [pos0] using hlt)
                        child acc' rfl))
  exact hP pos.remaining pos acc rfl

omit [∀ i, DecidableEq (Act i)] [∀ i, DecidableEq (PrivObs i)] [DecidableEq PubObs] in
/-- The semantic-view EFG tree evaluates to the explicit semantic run
distribution. This is the same structural theorem as the trace version, but
with player-view infosets and the translated semantic behavioral profile. -/
theorem treeFromAccum_evalDist_eq_runDistAccum
    {k : Nat} (σ : G.LegalBehavioralProfile) (pos : TracePosition G k)
    (acc : TracePosition.PayoffVec (G := G) k) :
    (treeFromAccum (G := G) pos acc).evalDist
        (translateBehavioralProfile (G := G) σ) =
      runDistAccum (G := G) σ pos acc := by
  let P : Nat → Prop := fun n =>
    ∀ (pos : TracePosition G k) (acc : TracePosition.PayoffVec (G := G) k),
      pos.remaining = n →
        (treeFromAccum (G := G) pos acc).evalDist
            (translateBehavioralProfile (G := G) σ) =
          runDistAccum (G := G) σ pos acc
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro pos acc hn
        rw [treeFromAccum, runDistAccum]
        by_cases hrem : pos.remaining = 0
        · simp [hrem]
        · simp [hrem]
          by_cases hterm : (SG G).terminal pos.state
          · simp [hterm]
          · simp [hterm]
            match pos with
            | ⟨state, trail, remaining, hremaining, hlen, hchain, hlast⟩ =>
            match state with
            | .base w =>
                let pos0 : TracePosition G k :=
                  ⟨.base w, trail, remaining, hremaining, hlen, hchain, hlast⟩
                have hrem0 : pos0.remaining ≠ 0 := by
                  simpa [pos0] using hrem
                have hterm0 : ¬ (SG G).terminal pos0.state := by
                  simpa [pos0] using hterm
                exact
                  treeBaseBranch_evalDist_eq_runBaseBranch (G := G) pos0 σ
                    (by rfl) hrem0 hterm0 acc (G.orderedActive w) rfl
                    (by
                      intro child htree hdist acc'
                      exact ih child.remaining
                        (by
                          rw [← hn]
                          simpa [pos0] using htree)
                        child acc' rfl)
            | .decide w chosen current rest hvalid =>
                let pos0 : TracePosition G k :=
                  ⟨.decide w chosen current rest hvalid, trail, remaining, hremaining, hlen,
                    hchain, hlast⟩
                have hrem0 : pos0.remaining ≠ 0 := by
                  simpa [pos0] using hrem
                let p : PlayerIx := playerEquiv (ι := ι) current
                have hp : origPlayer (ι := ι) p = current := by
                  simp [p, origPlayer, playerEquiv]
                let hI : pos0.player? = some (origPlayer (ι := ι) p) := by
                  simpa [hp] using
                    player_eq_some_of_decide (G := G) (pos := pos0) (by rfl) hrem0
                let Ipos :
                    {pos : TracePosition G k //
                      pos.player? = some (origPlayer (ι := ι) p)} :=
                  ⟨pos0, hI⟩
                exact
                  (bind_eq_bind_of_equiv
                    (e := Equiv.refl _)
                    (μ₁ := translateBehavioralProfile (G := G) σ p
                      (infosetOfPosition (G := G) Ipos))
                    (μ₂ := translateBehavioralProfile (G := G) σ p
                      (infosetOfPosition (G := G) Ipos))
                    (f := fun a =>
                      let a' := (viewIndexEquivPositionIndex (G := G) Ipos) a
                      (treeFromAccum (G := G)
                        (Position.TracePosition.decisionChild (G := G) Ipos a')
                        acc).evalDist (translateBehavioralProfile (G := G) σ))
                    (g := fun a =>
                      let a' := (viewIndexEquivPositionIndex (G := G) Ipos) a
                      runDistAccum (G := G) σ
                        (Position.TracePosition.decisionChild (G := G) Ipos a')
                        acc)
                    (hμ := fun a => rfl)
                    (hg := fun a =>
                      let a' := (viewIndexEquivPositionIndex (G := G) Ipos) a
                      let child := Position.TracePosition.decisionChild (G := G) Ipos a'
                      ih child.remaining
                        (by
                          have hlt : child.remaining < pos0.remaining := by
                            simpa [child, Ipos, Position.TracePosition.decisionChild_remaining,
                              Nat.pred_eq_sub_one] using Nat.pred_lt hrem0
                          rw [← hn]
                          simpa [pos0] using hlt)
                        child acc rfl))
            | .chance w ga =>
                let pos0 : TracePosition G k :=
                  ⟨.chance w ga, trail, remaining, hremaining, hlen, hchain, hlast⟩
                have hrem0 : pos0.remaining ≠ 0 := by
                  simpa [pos0] using hrem
                have hterm0 : ¬ (SG G).terminal pos0.state := by
                  simpa [pos0] using hterm
                let hplayer : pos0.player? = none := by
                  simpa [pos0] using
                    player_eq_none_of_chance (G := G) (pos := pos0) (by rfl) hrem0
                let μ := TracePosition.liveChancePMF (G := G) pos0 hplayer hterm0 hrem0
                exact
                  (bind_eq_bind_of_equiv
                    (e := Equiv.refl _)
                    (μ₁ := supportPMF μ)
                    (μ₂ := supportPMF μ)
                    (f := fun b =>
                      let child := TracePosition.chanceChild (G := G) pos0 hplayer hterm0 hrem0 b
                      let acc' := TracePosition.addPayoff (G := G) acc
                        (Position.chanceEdgePayoff (G := G) pos0.toPosition child.state)
                      (treeFromAccum (G := G) child acc').evalDist
                        (translateBehavioralProfile (G := G) σ))
                    (g := fun b =>
                      let child := TracePosition.chanceChild (G := G) pos0 hplayer hterm0 hrem0 b
                      let acc' := TracePosition.addPayoff (G := G) acc
                        (Position.chanceEdgePayoff (G := G) pos0.toPosition child.state)
                      runDistAccum (G := G) σ child acc')
                    (hμ := fun b => rfl)
                    (hg := fun b =>
                      let child := TracePosition.chanceChild (G := G) pos0 hplayer hterm0 hrem0 b
                      let acc' := TracePosition.addPayoff (G := G) acc
                        (Position.chanceEdgePayoff (G := G) pos0.toPosition child.state)
                      ih child.remaining
                        (by
                          have hlt : child.remaining < pos0.remaining := by
                            simpa [child, TracePosition.chanceChild_remaining,
                              Nat.pred_eq_sub_one] using Nat.pred_lt hrem0
                          rw [← hn]
                          simpa [pos0] using hlt)
                        child acc' rfl))
  exact hP pos.remaining pos acc rfl

omit [∀ i, DecidableEq (Act i)] [∀ i, DecidableEq (PrivObs i)] [DecidableEq PubObs] in
/-- The semantic-view EFG and trace-indexed EFG induce the same payoff-outcome
law under behavior profiles translated from the same legal FOSG profile. -/
theorem treeFromAccum_evalDist_eq_traceTreeFromAccum_evalDist
    {k : Nat} (σ : G.LegalBehavioralProfile) (pos : TracePosition G k)
    (acc : TracePosition.PayoffVec (G := G) k) :
    (treeFromAccum (G := G) pos acc).evalDist
        (translateBehavioralProfile (G := G) σ) =
      (AugmentedEFGBridge.traceTreeFromAccum (G := G) pos acc).evalDist
        (Position.translateBehavioralProfile (G := G) σ) := by
  calc
    (treeFromAccum (G := G) pos acc).evalDist
        (translateBehavioralProfile (G := G) σ)
        = runDistAccum (G := G) σ pos acc :=
          treeFromAccum_evalDist_eq_runDistAccum (G := G) σ pos acc
    _ = traceRunDistAccum (G := G) σ pos acc :=
          runDistAccum_eq_traceRunDistAccum (G := G) σ pos acc
    _ = (AugmentedEFGBridge.traceTreeFromAccum (G := G) pos acc).evalDist
        (Position.translateBehavioralProfile (G := G) σ) :=
          (traceTreeFromAccum_evalDist_eq_traceRunDistAccum (G := G) σ pos acc).symm

omit [∀ i, DecidableEq (Act i)] [∀ i, DecidableEq (PrivObs i)] [DecidableEq PubObs] in
@[simp] theorem toPlainTraceEFGAtHorizon_outcomeKernel_eq_trace
    (σ : G.LegalBehavioralProfile) (k : Nat) :
    (toPlainTraceEFGAtHorizon (G := G) k).toKernelGame.outcomeKernel
        (translateBehavioralProfile (G := G) σ) =
      (AugmentedEFGBridge.toPlainTraceEFGAtHorizon (G := G) k).toKernelGame.outcomeKernel
        (Position.translateBehavioralProfile (G := G) σ) := by
  simpa [EFGGame.toKernelGame, toPlainTraceEFGAtHorizon,
    AugmentedEFGBridge.toPlainTraceEFGAtHorizon, treeFrom,
    AugmentedEFGBridge.traceTreeFrom] using
    treeFromAccum_evalDist_eq_traceTreeFromAccum_evalDist (G := G) σ
      (TracePosition.root (G := G) k) (TracePosition.zeroPayoff (G := G))

omit [∀ i, DecidableEq (Act i)] [∀ i, DecidableEq (PrivObs i)] [DecidableEq PubObs] in
/-- Utility distributions agree between the semantic-view EFG bridge and the
trace-indexed EFG bridge. This is the payoff-facing corollary of the outcome
kernel equality; both bridges use the same `TraceOutcome` payoff component. -/
@[simp] theorem toPlainTraceEFGAtHorizon_udist_eq_trace
    (σ : G.LegalBehavioralProfile) (k : Nat) :
    (toPlainTraceEFGAtHorizon (G := G) k).toKernelGame.udist
        (translateBehavioralProfile (G := G) σ) =
      (AugmentedEFGBridge.toPlainTraceEFGAtHorizon (G := G) k).toKernelGame.udist
        (Position.translateBehavioralProfile (G := G) σ) := by
  unfold KernelGame.udist
  rw [toPlainTraceEFGAtHorizon_outcomeKernel_eq_trace (G := G) σ k]
  simp [EFGGame.toKernelGame, toPlainTraceEFGAtHorizon,
    AugmentedEFGBridge.toPlainTraceEFGAtHorizon]
  rfl

omit [∀ i, DecidableEq (Act i)] [∀ i, DecidableEq (PrivObs i)] [DecidableEq PubObs] in
/-- Expected utilities agree between the semantic-view EFG bridge and the
trace-indexed EFG bridge for each EFG player index. -/
@[simp] theorem toPlainTraceEFGAtHorizon_eu_eq_trace
    (σ : G.LegalBehavioralProfile) (k : Nat) (p : PlayerIx) :
    (toPlainTraceEFGAtHorizon (G := G) k).toKernelGame.eu
        (translateBehavioralProfile (G := G) σ) p =
      (AugmentedEFGBridge.toPlainTraceEFGAtHorizon (G := G) k).toKernelGame.eu
        (Position.translateBehavioralProfile (G := G) σ) p := by
  unfold KernelGame.eu
  rw [toPlainTraceEFGAtHorizon_outcomeKernel_eq_trace (G := G) σ k]
  simp [EFGGame.toKernelGame, toPlainTraceEFGAtHorizon,
    AugmentedEFGBridge.toPlainTraceEFGAtHorizon]

end Semantic

end AugmentedEFGBridge
end FOSG
end GameTheory
