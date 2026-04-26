import GameTheory.Languages.MultiRound.Syntax
import GameTheory.Languages.MultiRound.SOS
import GameTheory.Languages.MultiRound.Compile
import GameTheory.Languages.MultiRound.CompileObs
import GameTheory.Languages.MultiRound.Kuhn

/-!
# GameTheory.Languages.MultiRound.Theorems

Thin public theorem interface for MultiRound.

This file exposes only reductions from the native protocol presentation to the
compiled semantic layer. Substantive game-theoretic ports should land in the
generic theorem files and then be re-exported here.
-/
