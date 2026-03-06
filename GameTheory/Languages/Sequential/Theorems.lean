import GameTheory.Languages.Sequential.Syntax
import GameTheory.Languages.Sequential.SOS
import GameTheory.Languages.Sequential.Compile

/-!
# GameTheory.Languages.Sequential.Theorems

Thin public theorem interface for Sequential.

The eventual goal is for this file to expose only reductions through the
compiled `InfoModel` / `InfoGame` semantics. The old protocol-level proofs are
kept only as non-importable reference text under `ephemeral/`.
-/
