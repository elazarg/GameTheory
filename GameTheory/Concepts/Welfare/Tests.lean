/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Welfare.WelfareTheorems

/-!
# Welfare Concept Tests

Compilation tests for welfare and team-game exports.
-/

namespace GameTheory.Concepts.Welfare.Tests

noncomputable section

def teamGame : KernelGame Bool :=
  KernelGame.ofPureEU (fun _ : Bool => Bool) (fun σ _ => if σ true then (1 : ℝ) else 0)

theorem teamGame_isTeamGame : teamGame.IsTeamGame := by
  intro σ i j
  rfl

def profile : KernelGame.Profile teamGame :=
  fun _ => true

example :
    teamGame.socialWelfare profile = Fintype.card Bool * teamGame.eu profile true :=
  teamGame_isTeamGame.socialWelfare_eq profile true

example : teamGame.socialWelfare profile ≥ 0 := by
  apply KernelGame.socialWelfare_nonneg_of_nonneg_eu
  intro i
  simp [teamGame, profile]

end

end GameTheory.Concepts.Welfare.Tests
