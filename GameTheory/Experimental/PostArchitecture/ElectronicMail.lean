/-
# EXP-048: finite Electronic Mail as a static Bayesian/Epistemic bridge

The public Electronic Mail example owns the single canonical endpoint law and
setoid posterior model. This gate consumes its mutual-belief threshold and
Bayes-Nash deviation controls.
-/

import GameTheory.Examples.ElectronicMail

namespace GameTheory.Experimental.PostArchitecture.ElectronicMail

open GameTheory GameTheory.Epistemic

example {threshold : ℝ} (hthreshold : threshold ≤ 1) :
    GameTheory.Examples.ElectronicMail.EmailWorld.bothConfirmed ∈
      mutualPBelief
        GameTheory.Examples.ElectronicMail.worldPrior
        GameTheory.Examples.ElectronicMail.emailPartition
        threshold
        GameTheory.Examples.ElectronicMail.attackStateEvent :=
  GameTheory.Examples.ElectronicMail.bothConfirmed_mem_mutualPBelief_attackStateEvent
    hthreshold

example :
    ¬ IsNash
      GameTheory.Examples.ElectronicMail.game.toForm
      (euPreference GameTheory.Examples.ElectronicMail.game.utility)
      GameTheory.Examples.ElectronicMail.attackOnMessage :=
  GameTheory.Examples.ElectronicMail.attackOnMessage_not_isNash

end GameTheory.Experimental.PostArchitecture.ElectronicMail
