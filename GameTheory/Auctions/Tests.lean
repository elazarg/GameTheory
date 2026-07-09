/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Auctions.Vickrey

/-!
# GameTheory.Auctions.Tests

Compilation validation entrypoint for auction modules.
-/

namespace GameTheory.Auctions.Tests

noncomputable section

example (v : Bool → ℝ) : (vickreyGame v).IsNash v :=
  vickrey_truthful_isNash v

example (v : Bool → ℝ) (who : Bool) : (vickreyGame v).IsDominant who (v who) :=
  vickrey_truthful_isDominant v who

end

end GameTheory.Auctions.Tests
