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

theorem player_eq_none_of_base_empty
    {k : Nat} {pos : TracePosition G k} {w : W}
    (hstate : pos.state = .base w)
    (hrem : pos.remaining ≠ 0)
    (hEmpty : G.orderedActive w = []) :
    pos.player? = none := by
  simp [TracePosition.player?, TracePosition.toPosition, Position.player?,
    Position.isTruncated, hrem, hstate, hEmpty]

theorem player_eq_some_of_base_cons
    {k : Nat} {pos : TracePosition G k} {w : W} {current : ι} {rest : List ι}
    (hstate : pos.state = .base w)
    (hrem : pos.remaining ≠ 0)
    (horder : G.orderedActive w = current :: rest) :
    pos.player? = some current := by
  simp [TracePosition.player?, TracePosition.toPosition, Position.player?,
    Position.isTruncated, hrem, hstate, horder]

theorem player_eq_some_of_decide
    {k : Nat} {pos : TracePosition G k}
    {w : W} {chosen : JointAction Act} {current : ι} {rest : List ι}
    {hvalid : G.ValidDecision w chosen current rest}
    (hstate : pos.state = .decide w chosen current rest hvalid)
    (hrem : pos.remaining ≠ 0) :
    pos.player? = some current := by
  simp [TracePosition.player?, TracePosition.toPosition, Position.player?,
    Position.isTruncated, hrem, hstate]

theorem player_eq_none_of_chance
    {k : Nat} {pos : TracePosition G k} {w : W} {ga : G.LegalAction w}
    (hstate : pos.state = .chance w ga)
    (hrem : pos.remaining ≠ 0) :
    pos.player? = none := by
  simp [TracePosition.player?, TracePosition.toPosition, Position.player?,
    Position.isTruncated, hrem, hstate]

end Semantic

end AugmentedEFGBridge
end FOSG
end GameTheory
