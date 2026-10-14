module

/-
# Finite multi-round games

Public entry point for finite monitoring games.  The native constructor compiles
directly to Protocol/FOSG and introduces no parallel runner, history, policy,
probability, or equilibrium concept.
-/

public import GameTheory.Languages.MultiRound.Monitoring

@[expose] public section

namespace GameTheory.Languages.MultiRound

end GameTheory.Languages.MultiRound
