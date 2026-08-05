/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.OneStepDeviationSafePublicCoinSelector

/-!
# Uniform equilibrium after one public draw into absorbing children

This file closes the complete verification chain for a concrete
nontrivial class of stochastic games.  From the initial state, every joint
action induces the same public one-step draw.  The draw is supported on
absorbing states, grouped into finitely many public children.

Each absorbing child has an adaptive potential equilibrium certificate.
The deviation-safe public selector transports those certificates through
the initial draw.  The parent target is their exact expectation, so the
generic verification theorem yields a uniform equilibrium payoff.

This is stronger than treating the initial state as absorbing: its stage
payoff and action profile may be arbitrary, and its transition may be a
nondegenerate lottery over several absorbing continuation games.  The
finite initial prefix disappears from every long-run average.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math Math.Probability Math.ProbabilityMassFunction

variable {ι Child : Type} {G : StochasticGame ι}

namespace OneStepDeviationSafePublicCoinData

variable [Fintype ι] [DecidableEq ι]
  [Finite G.State] [∀ i, Finite (G.Act i)]
  [∀ i, Nonempty (G.Act i)]
  [Finite Child]

/-- An action-independent public draw into absorbing child states has an
adaptive potential equilibrium certificate at its initial state.

`entry_terminal` says that every named child is represented by an
absorbing state.  `terminal_entry` says that every terminal state that can
occur in the selector is the representative of its public observation.
Together they identify the selector leaves with the child certificates. -/
theorem exists_isAdaptivePotentialEquilibriumCertificate_of_absorbingChildren
    (data : OneStepDeviationSafePublicCoinData G Child)
    (entry : Child → G.State)
    (entry_terminal :
      ∀ child, data.terminal (entry child))
    (terminal_entry :
      ∀ state, data.terminal state →
        state = entry (data.observe state)) :
    ∃ parentTarget : Payoff ι,
      G.IsAdaptivePotentialEquilibriumCertificate
        data.initial parentTarget := by
  letI : Fintype Child := Fintype.ofFinite Child
  have childExists :
      ∀ child : Child,
        ∃ childTarget : Payoff ι,
          G.IsAdaptivePotentialEquilibriumCertificate
            (entry child) childTarget := by
    intro child
    apply G.isAdaptivePotentialEquilibriumCertificate_of_isAbsorbingState
    intro action
    exact data.transition_terminal
      (entry child) (entry_terminal child) action
  choose childTarget childCertificate using childExists
  obtain ⟨stageNash, _stageNashEquilibrium⟩ :=
    G.exists_isMixedStageNash
  let selection : G.BehaviorProfile :=
    G.stationaryBehaviorProfile (stageNash data.initial)
  let parentTarget : Payoff ι :=
    fun who =>
      expect (PMF.map data.observe data.kernel)
        (fun child => childTarget child who)
  refine ⟨parentTarget, ?_⟩
  intro error error_pos
  apply data.isAdaptivePotentialCertificateAt_of_exactExpectedTarget
    entry childTarget selection parentTarget error error_pos
    terminal_entry
  · intro who
    rfl
  · intro child childError childError_pos
    exact childCertificate child childError childError_pos

/-- Uniform equilibrium payoffs exist after an action-independent public
draw into finitely many absorbing child states. -/
theorem exists_uniformEquilibriumPayoff_of_absorbingChildren
    (data : OneStepDeviationSafePublicCoinData G Child)
    (entry : Child → G.State)
    (entry_terminal :
      ∀ child, data.terminal (entry child))
    (terminal_entry :
      ∀ state, data.terminal state →
        state = entry (data.observe state)) :
    ∃ parentTarget : Payoff ι,
      G.IsUniformEquilibriumPayoff data.initial parentTarget := by
  obtain ⟨parentTarget, certificate⟩ :=
    data.exists_isAdaptivePotentialEquilibriumCertificate_of_absorbingChildren
      entry entry_terminal terminal_entry
  exact
    ⟨parentTarget,
      G.isUniformEquilibriumPayoff_of_isAdaptivePotentialEquilibriumCertificate
        data.initial parentTarget certificate⟩

end OneStepDeviationSafePublicCoinData
end StochasticGame
end GameTheory
