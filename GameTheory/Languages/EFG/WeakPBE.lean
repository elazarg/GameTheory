module

/-
# Weak perfect Bayesian equilibrium for extensive-form games

This solution leaf specializes Protocol's whole-policy terminal rationality
and positive-mass Bayes consistency. The EFG syntax remains independent of
solution concepts.
-/

public import GameTheory.Languages.EFG
public import GameTheory.Protocol.WeakPBE

@[expose] public section

noncomputable section

namespace GameTheory.Languages.EFG.Game

open GameTheory.Protocol

universe uι us ua up uq uk

variable {ι : Type uι} (G : Game.{uι, us, ua, up, uq, uk} ι)

/-- Weak PBE is the canonical Protocol predicate on an EFG assessment. -/
abbrev IsWeakPBE [DecidableEq ι]
    (antichain : G.information.DecisionInformationAntichain)
    (assessment : G.information.BehavioralAssessment)
    (certificate : G.execution.WellFoundedHistories)
    (payoff : ι → G.History → ℝ) : Prop :=
  assessment.IsWeakPBE antichain certificate payoff

end GameTheory.Languages.EFG.Game
