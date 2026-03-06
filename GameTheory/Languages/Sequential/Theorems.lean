import GameTheory.Languages.Sequential.Syntax
import GameTheory.Languages.Sequential.SOS
import GameTheory.Languages.Sequential.Compile
import GameTheory.Theorems.Sequential

/-!
# GameTheory.Languages.Sequential.Theorems

Thin public theorem interface for Sequential.

This file exposes only reductions from the native protocol presentation to the
compiled semantic layer. Substantive game-theoretic ports should land in the
generic theorem files and then be re-exported here.
-/
