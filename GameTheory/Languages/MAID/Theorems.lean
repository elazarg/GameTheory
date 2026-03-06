import GameTheory.Languages.MAID.Syntax
import GameTheory.Languages.MAID.SOS
import GameTheory.Languages.MAID.Compile
import GameTheory.Theorems.MAID

/-!
# GameTheory.Languages.MAID.Theorems

Thin public theorem interface for MAID.

This file exposes only reductions from native frontier semantics to the compiled
semantic layer. Substantive game-theoretic ports should land in generic theorem
files and then be re-exported here.
-/
