import GameTheory.Languages.Sequential.Syntax

/-!
# GameTheory.Languages.Sequential.SOS

Current sequential protocol semantics lives directly on the protocol syntax.
This file is the public landing point for the language-native SOS layer, so the
later compile-vs-SOS proofs can sit between `Syntax` and `Compile`.
-/
