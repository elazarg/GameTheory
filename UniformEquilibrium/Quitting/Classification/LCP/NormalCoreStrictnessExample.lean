/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.NormalCore

/-!
# The corrected normal core can be smaller than the first layer

This finite quitting table is a concrete diagnostic for the distinct-witness
normal-player recursion.  Its normalized singleton comparison matrix is

```text
      owner 0  1  2
row 0       0  1  1
row 1      -1  0  1
row 2       1 -1  0
```

The first screen retains players `1` and `2`: player `1` uses the already
deleted player `0` as witness, while player `2` uses player `1`.  Repeating
the screen removes `1`, then `2`, so the stabilized corrected core is empty.
Thus replacing the recursive core by the one-step normal-player set changes
the index set even for a three-player singleton comparison table.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification
namespace NormalCoreStrictnessExample

open Finset

abbrev Player := Fin 3

/-- A three-player normalized singleton comparison matrix with a strict
first-layer/core separation. -/
def comparisonMatrix : Player → Player → ℝ :=
  fun who owner =>
    if who = 0 then
      if owner = 0 then 0 else 1
    else if who = 1 then
      if owner = 0 then -1 else if owner = 1 then 0 else 1
    else
      if owner = 1 then -1 else if owner = 2 then 0 else 1

/-- A quitting reward table realizing `comparisonMatrix`.  Only singleton
terminal rewards matter for this diagnostic; all larger coalitions receive
zero. -/
def reward : {S : Finset Player // S.Nonempty} → Payoff Player := fun S =>
  if S.1 = {0} then ![0, -1, 1]
  else if S.1 = {1} then ![1, 0, -1]
  else if S.1 = {2} then ![1, 1, 0]
  else 0

/-- The quitting table realizes the displayed comparison matrix exactly. -/
theorem normalizedSoloMatrix_eq_comparisonMatrix :
    normalizedSoloMatrix reward = comparisonMatrix := by
  rw [normalizedSoloMatrix_eq_projectiveLCPMatrix]
  funext who owner
  fin_cases who <;> fin_cases owner <;>
    norm_num [quittingProjectiveLCPMatrix,
      quittingProjectiveSingletonTerminal, reward, comparisonMatrix,
      Fin.ext_iff]

/-- The ordinary one-step screen keeps precisely players `1` and `2`. -/
theorem normalLayer_one :
    normalLayer comparisonMatrix 1 = {1, 2} := by
  have hzero : (0 : Player) ∉ normalLayer comparisonMatrix 1 := by
    intro h
    obtain ⟨_, witness, _, hne, hle⟩ :=
      (mem_normalLayer_succ comparisonMatrix 0 0).mp h
    fin_cases witness
    · exact hne rfl
    · norm_num [comparisonMatrix, Fin.ext_iff] at hle
    · norm_num [comparisonMatrix, Fin.ext_iff] at hle
  have hone : (1 : Player) ∈ normalLayer comparisonMatrix 1 := by
    apply (mem_normalLayer_succ comparisonMatrix 0 1).2
    constructor
    · simp
    · refine ⟨(0 : Player), by simp, ?_, ?_⟩
      · decide
      · norm_num [comparisonMatrix, Fin.ext_iff]
  have htwo : (2 : Player) ∈ normalLayer comparisonMatrix 1 := by
    apply (mem_normalLayer_succ comparisonMatrix 0 2).2
    constructor
    · simp
    · refine ⟨(1 : Player), by simp, ?_, ?_⟩
      · decide
      · norm_num [comparisonMatrix, Fin.ext_iff]
  ext who
  fin_cases who <;> simp [hzero, hone, htwo]

/-- After re-screening within the first layer, only player `2` remains. -/
theorem normalLayer_two :
    normalLayer comparisonMatrix 2 = {2} := by
  have hzero : (0 : Player) ∉ normalLayer comparisonMatrix 2 := by
    intro h
    have hprev := (normalLayer_succ_subset comparisonMatrix 1) h
    rw [normalLayer_one] at hprev
    simp at hprev
  have hone : (1 : Player) ∉ normalLayer comparisonMatrix 2 := by
    intro h
    obtain ⟨_, witness, hwitness, hne, hle⟩ :=
      (mem_normalLayer_succ comparisonMatrix 1 1).mp h
    rw [normalLayer_one] at hwitness
    fin_cases witness
    · simp at hwitness
    · exact hne rfl
    · norm_num [comparisonMatrix, Fin.ext_iff] at hle
  have htwo : (2 : Player) ∈ normalLayer comparisonMatrix 2 := by
    apply (mem_normalLayer_succ comparisonMatrix 1 2).2
    constructor
    · rw [normalLayer_one]; simp
    · refine ⟨(1 : Player), ?_, ?_, ?_⟩
      · rw [normalLayer_one]; simp
      · decide
      · norm_num [comparisonMatrix, Fin.ext_iff]
  ext who
  fin_cases who <;> simp [hzero, hone, htwo]

/-- The next corrected layer is empty because no distinct witness remains. -/
theorem normalLayer_three :
    normalLayer comparisonMatrix 3 = ∅ := by
  ext who
  constructor
  · intro h
    obtain ⟨hwho, witness, hwitness, hne, _⟩ :=
      (mem_normalLayer_succ comparisonMatrix 2 who).mp h
    rw [normalLayer_two] at hwho hwitness
    have hwho2 : who = 2 := by simpa using hwho
    have hwitness2 : witness = 2 := by simpa using hwitness
    exact False.elim (hne (hwitness2.trans hwho2.symm))
  · intro h
    simp at h

/-- The stabilized corrected core is empty. -/
theorem normalCore_eq_empty : normalCore comparisonMatrix = ∅ := by
  ext who
  constructor
  · intro hwho
    have hthree := (mem_normalCore comparisonMatrix who).mp hwho 3
    rw [normalLayer_three] at hthree
    simp at hthree
  · simp

/-- The iterated corrected core is a strict subset of the ordinary one-step
normal-player screen. -/
theorem normalCore_ssubset_normalLayer_one :
    normalCore comparisonMatrix ⊂ normalLayer comparisonMatrix 1 := by
  rw [normalCore_eq_empty, normalLayer_one]
  simp

/-- Game-facing form of the same strict separation, using the normalized
singleton matrix of the explicit quitting reward table. -/
theorem reward_normalCore_ssubset_normalLayer_one :
    normalCore (normalizedSoloMatrix reward) ⊂
      normalLayer (normalizedSoloMatrix reward) 1 := by
  rw [normalizedSoloMatrix_eq_comparisonMatrix]
  exact normalCore_ssubset_normalLayer_one

end NormalCoreStrictnessExample
end QuittingLCPClassification
end GameTheory

namespace GameTheory.QuittingLCPClassification.NormalCoreStrictnessExample

#print axioms reward_normalCore_ssubset_normalLayer_one

end GameTheory.QuittingLCPClassification.NormalCoreStrictnessExample
