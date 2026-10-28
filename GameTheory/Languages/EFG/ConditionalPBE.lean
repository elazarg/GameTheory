module

/-
# Conditional-probability perfect Bayesian equilibrium for extensive games

This solution leaf specializes the canonical Protocol assessment and common
conditional-probability system to an extensive-form game.
-/

public import GameTheory.Languages.EFG
public import GameTheory.Protocol.ConditionalPBE

@[expose] public section

noncomputable section

namespace GameTheory.Languages.EFG.Game

universe uι us ua up uq uk

variable {ι : Type uι} (G : Game.{uι, us, ua, up, uq, uk} ι)

/-- The EFG specialization retains the common off-path conditional beliefs
and the certificate that Nature is explicitly represented. -/
abbrev IsConditionalPBE [DecidableEq ι]
    (assessment : G.information.BehavioralAssessment)
    (certificate : G.execution.WellFoundedHistories)
    (payoff : ι → G.History → ℝ) : Prop :=
  assessment.IsConditionalPBE G.information certificate payoff

end GameTheory.Languages.EFG.Game
