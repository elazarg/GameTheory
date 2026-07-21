/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Welfare.WelfareTheorems
import GameTheory.Concepts.Welfare.FolkTheorem.Geometry

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

example {G : KernelGame Bool} [Finite (KernelGame.Profile G)]
    (r : Payoff Bool) (margin : ℝ) :
    IsCompact (G.individuallyRationalInnerApproximation r margin) :=
  G.isCompact_individuallyRationalInnerApproximation r margin

example (G : KernelGame Bool) (r : Payoff Bool) :
    G.strictIndividuallyRationalPayoffSet r =
      ⋃ margin : {x : ℝ // 0 < x},
        G.individuallyRationalInnerApproximation r margin :=
  G.strictIndividuallyRationalPayoffSet_eq_iUnion_innerApproximations r

example (G : KernelGame Bool) :
    G.HasFullDimensionalFeasibleSet ↔
      (interior G.feasibleSet).Nonempty :=
  G.hasFullDimensionalFeasibleSet_iff_interior_nonempty

example (G : KernelGame Bool) (r : Payoff Bool) :
    (intrinsicInterior ℝ (G.strictIndividuallyRationalPayoffSet r)).Nonempty ↔
      (G.strictIndividuallyRationalPayoffSet r).Nonempty :=
  G.intrinsicInterior_strictIndividuallyRationalPayoffSet_nonempty_iff r

example (G : KernelGame Bool) (r : Payoff Bool) :
    (interior (G.strictIndividuallyRationalPayoffSet r)).Nonempty ↔
      G.HasFullDimensionalFeasibleSet ∧
        (G.strictIndividuallyRationalPayoffSet r).Nonempty :=
  G.interior_strictIndividuallyRationalPayoffSet_nonempty_iff r

end

end GameTheory.Concepts.Welfare.Tests
