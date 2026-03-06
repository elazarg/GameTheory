import GameTheory.Theorems  -- just to make the dependency order clear
import GameTheory.Compilers.NFG
import GameTheory.Compilers.EFG
import GameTheory.Compilers.MAID
import GameTheory.Compilers.Protocol

/-!
# GameTheory.Compilers

Language-to-semantics compilers. Each compiler maps a language-level object to
`InfoModel`, and where common-knowledge controllers are supplied, further to
`InfoGame`.
-/
