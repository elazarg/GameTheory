/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Boundary.Repair.DisjunctionCounterexample

/-!
# The repaired disjunction: a third branch for the isolated negative coordinate

`QuittingDisjunctionCounterexample.lean` refutes the two-branch carrier

    `IsQuittingZeroSolo reward ∨ HasAdmissibleAbsorbingQuittingCycle reward`

with the weight `r({1}) = r({2}) = (1, -1)`, `r({1,2}) = (0, 1)`.  That weight
fails both branches through one nameable configuration and no other: its
absorbing cycles all isolate coordinate `2`, whose solo weight `r_2({2}) = -1`
is negative.  This file names that configuration as a third branch and proves
the repaired disjunction over the weights the argument can see.

## The third branch

`HasIsolatedNegativeAbsorbingQuittingCycle reward` says: some absorbing cyclic
continuation block (the same `IsQuittingCyclicContinuationBlock` notion as in
`QuittingCyclePinnedDebt.lean`) has a coordinate `who` that is *isolated* --
every opponent silent at every phase, `IsQuittingIsolatedWindow` of
`QuittingCycleIsolatedCoordinate.lean` -- with `r_who({who}) < 0`.

That file already pins down everything about this configuration:

* the anchored companion mismatch there is **exactly** `-r_who({who})`
  (`quittingCyclicContinuationBlock_mismatch_eq_of_isolated`, restated as
  `quittingIsolatedNegativeCycle_mismatch_eq` below), and the block's own value
  at `who` is `r_who({who})` itself; and
* an absorbing block isolates **at most one** coordinate
  (`eq_of_isQuittingIsolatedWindow_of_cyclicBlock`), so the branch speaks of a
  unique coordinate and the mismatch value is unambiguous.

## Exhaustiveness, and its scope

`quittingCycle_zeroSolo_or_admissible_or_isolatedNegative` proves: **for every
weight admitting some absorbing cyclic continuation block**, one of the three
branches holds.  The engine is the block-level dichotomy
`isQuittingCycleAdmissible_or_isolated_negative`: at a fixed block, either every
coordinate satisfies `IsQuittingCycleZeroDeviationMismatchAt` -- which *is*
admissibility -- or some coordinate fails both of its disjuncts, so its cyclic
deleted product is `1` and its solo weight is negative.  A deleted product equal
to one is exactly isolation
(`isQuittingIsolatedRoot_of_deletedContinueMass_eq_one`, step 1 of
`QuittingCycleIsolatedCoordinate.lean`, packaged here as
`prod_fixedOpponentsContinueMass_eq_one_iff_isQuittingIsolatedWindow`), so the
failure is the isolated-negative configuration and nothing else.  That this is
the only way the *mismatch itself* can be nonzero is the separate landed
characterization `quittingCyclicContinuationBlock_mismatch_characterization`;
the exhaustiveness proof here does not consume it, it consumes the same step-1
equivalence the characterization is built on.

The hypothesis is not decoration.  Weights admitting **no** absorbing
complementary cycle of any period are not covered by any of the three branches
as stated, and that residue is genuinely open here: this repository does not
prove that every weight admits an absorbing complementary cycle.  The usual
argument -- take discounted complementary rows and let the discount tend to one,
then some limit absorbs -- rests on an external attribution that has **not** been
audited in this repository.  So the trichotomy below is conditional, and must
not be quoted as an unconditional statement about all weights.

## What the repair does not buy

Sufficiency is known for only two of the three branches.  Zero-solo delivers a
uniform equilibrium payoff (`quittingGame_isUniformEquilibriumPayoff_zero_of_zeroSolo`)
and so does an admissible absorbing cycle
(`exists_uniformEquilibriumPayoff_of_admissible_quittingCyclicContinuationBlock`).
The isolated-negative branch has **no** sufficiency theorem: a weight landing
there is not thereby known to have a uniform equilibrium payoff.  Repairing the
carrier's exhaustiveness therefore does not close the finite-quitting
conjecture, and nothing here should be read as doing so.

## Mutual exclusivity

The three branches are *exhaustive but not exclusive*
(`quittingThreeBranch_not_mutually_exclusive`): zero-solo overlaps both of the
other two, witnessed by machine-checked examples.  What *is* exclusive is the
pairing at a fixed block: an admissible cycle has no isolated negative
coordinate (`not_isQuittingCycleAdmissible_of_isolated_negative`), which is the
exact content of admissibility.  The weight-level branches quantify over
different blocks, so they can and do overlap.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The third branch -/

/-- A weight **admits an isolated negative absorbing cycle** when some absorbing
cyclic continuation block has a coordinate that is isolated at every phase --
every opponent silent -- and whose solo-quit weight `r_who({who})` is strictly
negative.

This is the configuration that the refuted two-branch disjunction missed: by
`quittingCyclicContinuationBlock_mismatch_characterization` it is the *only*
way for the anchored companion mismatch of an absorbing block to be nonzero. -/
def HasIsolatedNegativeAbsorbingQuittingCycle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∃ (terminal : Payoff ι) (period : ℕ)
    (block : QuittingFiniteNashBellmanPath ι (period + 1)) (who : ι),
    IsQuittingCyclicContinuationBlock reward terminal (period + 1) block ∧
      IsQuittingIsolatedWindow
        (quittingFiniteNashBellmanPathRoots (period + 1) block) who (period + 1) ∧
      reward (quittingSingletonTerminal who) who < 0

/-! ## What the branch pins down

Nothing in this section is new mathematics: it records, in the shape the branch
uses, the two facts `QuittingCycleIsolatedCoordinate.lean` already proves about
this configuration. -/

/-- **The branch determines the mismatch.**  At an isolated coordinate of
negative solo weight the anchored companion mismatch of an absorbing block is
exactly `-r_who({who})`, a strictly positive number. -/
theorem quittingIsolatedNegativeCycle_mismatch_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : Payoff ι) (period : ℕ)
    (block : QuittingFiniteNashBellmanPath ι period)
    (hblock : IsQuittingCyclicContinuationBlock reward terminal period block)
    {who : ι}
    (hiso : IsQuittingIsolatedWindow
      (quittingFiniteNashBellmanPathRoots period block) who period)
    (hneg : reward (quittingSingletonTerminal who) who < 0)
    (anchorLimit : ℝ)
    (hanchor : Filter.Tendsto
      (fun N : ℕ =>
        (quittingCompanionComposite reward
          (quittingFiniteNashBellmanPathRoots period block) who 0
          period)^[N] (quittingPositiveSingletonDebtCap reward who))
      Filter.atTop (nhds anchorLimit)) :
    anchorLimit - terminal who = -reward (quittingSingletonTerminal who) who := by
  rw [quittingCyclicContinuationBlock_mismatch_eq_of_isolated reward terminal
    period block hblock hiso anchorLimit hanchor,
    max_eq_right (by linarith)]

/-- **The branch determines the block's value.**  At the isolated coordinate the
block reproduces the solo weight itself, which the branch makes negative. -/
theorem quittingIsolatedNegativeCycle_value_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : Payoff ι) (period : ℕ)
    (block : QuittingFiniteNashBellmanPath ι period)
    (hblock : IsQuittingCyclicContinuationBlock reward terminal period block)
    {who : ι}
    (hiso : IsQuittingIsolatedWindow
      (quittingFiniteNashBellmanPathRoots period block) who period) :
    terminal who = reward (quittingSingletonTerminal who) who :=
  quittingCyclicContinuationBlock_value_eq_soloReward_of_isolated reward terminal
    period block hblock hiso

/-- **The branch's coordinate is unique.**  An absorbing block isolates at most
one coordinate, so the mismatch value `-r_who({who})` the branch reports is
unambiguous. -/
theorem quittingIsolatedNegativeCycle_coordinate_unique
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : Payoff ι) (period : ℕ)
    (block : QuittingFiniteNashBellmanPath ι period)
    (hblock : IsQuittingCyclicContinuationBlock reward terminal period block)
    {who other : ι}
    (hwho : IsQuittingIsolatedWindow
      (quittingFiniteNashBellmanPathRoots period block) who period)
    (hother : IsQuittingIsolatedWindow
      (quittingFiniteNashBellmanPathRoots period block) other period) :
    who = other :=
  eq_of_isQuittingIsolatedWindow_of_cyclicBlock reward terminal period block
    hblock hwho hother

/-! ## The cycle of a block, read on its root sequence -/

omit [DecidableEq ι] in
/-- The admissibility predicate reads the block through
`quittingCyclicContinuationBlockCycle`; the mismatch characterization reads it
through `quittingFiniteNashBellmanPathRoots`.  They agree. -/
theorem quittingCyclicContinuationBlockCycle_eq_pathRoots (period : ℕ)
    (block : QuittingFiniteNashBellmanPath ι (period + 1))
    (stage : Fin (period + 1)) :
    quittingCyclicContinuationBlockCycle period block stage =
      quittingFiniteNashBellmanPathRoots (period + 1) block stage.val := by
  rw [quittingFiniteNashBellmanPathRoots_of_lt (period + 1) block stage.val
    stage.isLt]
  rfl

/-- The stationary deleted continue mass consumed by `IsQuittingCycleAdmissible`
is the deleted survival factor of `QuittingCycleMismatchContraction.lean`. -/
theorem quittingStationaryFixedOpponentsContinueMass_eq_deletedContinueMass
    (root : ι → PMF Bool) (who : ι) :
    quittingStationaryFixedOpponentsContinueMass root who =
      quittingRootDeletedContinueMass root who := rfl

/-- **The admissibility product is the isolation test.**  The cyclic product of
deleted continue masses is one exactly when the coordinate is isolated at every
phase of the block. -/
theorem prod_fixedOpponentsContinueMass_eq_one_iff_isQuittingIsolatedWindow
    (period : ℕ) (block : QuittingFiniteNashBellmanPath ι (period + 1))
    (who : ι) :
    (∏ stage : Fin (period + 1),
        quittingStationaryFixedOpponentsContinueMass
          (quittingCyclicContinuationBlockCycle period block stage) who) = 1 ↔
      IsQuittingIsolatedWindow
        (quittingFiniteNashBellmanPathRoots (period + 1) block) who
        (period + 1) := by
  classical
  constructor
  · intro hprod time htime
    have hfactor := eq_one_of_prod_eq_one_of_mem
      (f := fun stage : Fin (period + 1) ↦
        quittingStationaryFixedOpponentsContinueMass
          (quittingCyclicContinuationBlockCycle period block stage) who)
      (fun stage _ ↦ quittingRootDeletedContinueMass_nonneg _ who)
      (fun stage _ ↦ quittingRootDeletedContinueMass_le_one _ who)
      hprod (a := (⟨time, htime⟩ : Fin (period + 1))) (Finset.mem_univ _)
    rw [quittingStationaryFixedOpponentsContinueMass_eq_deletedContinueMass,
      quittingCyclicContinuationBlockCycle_eq_pathRoots] at hfactor
    exact isQuittingIsolatedRoot_of_deletedContinueMass_eq_one hfactor
  · intro hiso
    refine Finset.prod_eq_one fun stage _ ↦ ?_
    rw [quittingStationaryFixedOpponentsContinueMass_eq_deletedContinueMass,
      quittingCyclicContinuationBlockCycle_eq_pathRoots]
    exact quittingRootDeletedContinueMass_eq_one_of_isolated
      (hiso stage.val stage.isLt)

/-! ## Exhaustiveness at a fixed block -/

/-- **The block-level dichotomy.**  Any cyclic continuation block is either
admissible or exhibits an isolated coordinate of negative solo weight.  There is
no third possibility: failure of `IsQuittingCycleZeroDeviationMismatchAt` at a
coordinate says exactly that the cyclic deleted product fails to contract and
the solo weight is negative, and a non-contracting product is one, which is
isolation.

Absorption of the block is not used; only the cycle it carries. -/
theorem isQuittingCycleAdmissible_or_isolated_negative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (period : ℕ)
    (block : QuittingFiniteNashBellmanPath ι (period + 1)) :
    IsQuittingCycleAdmissible reward
        (quittingCyclicContinuationBlockCycle period block) ∨
      ∃ who : ι,
        IsQuittingIsolatedWindow
            (quittingFiniteNashBellmanPathRoots (period + 1) block) who
            (period + 1) ∧
          reward (quittingSingletonTerminal who) who < 0 := by
  classical
  by_cases hadmissible : ∀ who : ι, IsQuittingCycleZeroDeviationMismatchAt reward
      (quittingCyclicContinuationBlockCycle period block) who
  · exact Or.inl hadmissible
  · right
    obtain ⟨who, hwho⟩ := not_forall.mp hadmissible
    have hnotcontract : ¬ (∏ stage : Fin (period + 1),
        quittingStationaryFixedOpponentsContinueMass
          (quittingCyclicContinuationBlockCycle period block stage) who) < 1 :=
      fun hcontract ↦ hwho (Or.inl hcontract)
    have hneg : reward (quittingSingletonTerminal who) who < 0 :=
      lt_of_not_ge fun hnonneg ↦ hwho (Or.inr hnonneg)
    have hle : (∏ stage : Fin (period + 1),
        quittingStationaryFixedOpponentsContinueMass
          (quittingCyclicContinuationBlockCycle period block stage) who) ≤ 1 :=
      Finset.prod_le_one
        (fun stage _ ↦ quittingRootDeletedContinueMass_nonneg _ who)
        (fun stage _ ↦ quittingRootDeletedContinueMass_le_one _ who)
    have hprod : (∏ stage : Fin (period + 1),
        quittingStationaryFixedOpponentsContinueMass
          (quittingCyclicContinuationBlockCycle period block stage) who) = 1 :=
      le_antisymm hle (not_lt.mp hnotcontract)
    exact ⟨who,
      (prod_fixedOpponentsContinueMass_eq_one_iff_isQuittingIsolatedWindow period
        block who).mp hprod, hneg⟩

/-- **The block-level exclusivity.**  An admissible cycle has no isolated
coordinate of negative solo weight -- admissibility is exactly the absence of
that configuration. -/
theorem not_isQuittingCycleAdmissible_of_isolated_negative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (period : ℕ)
    (block : QuittingFiniteNashBellmanPath ι (period + 1)) {who : ι}
    (hiso : IsQuittingIsolatedWindow
      (quittingFiniteNashBellmanPathRoots (period + 1) block) who (period + 1))
    (hneg : reward (quittingSingletonTerminal who) who < 0) :
    ¬ IsQuittingCycleAdmissible reward
      (quittingCyclicContinuationBlockCycle period block) := by
  intro hadmissible
  have hprod :=
    (prod_fixedOpponentsContinueMass_eq_one_iff_isQuittingIsolatedWindow period
      block who).mpr hiso
  rcases hadmissible who with hcontract | hnonneg
  · rw [hprod] at hcontract
    exact lt_irrefl 1 hcontract
  · linarith

/-! ## The repaired disjunction -/

/-- **The two cycle branches are exhaustive over weights with an absorbing
cycle.**  Any absorbing cyclic continuation block is itself a witness for one of
the two. -/
theorem hasAdmissible_or_hasIsolatedNegative_of_cyclicContinuation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcycle : ∃ terminal : Payoff ι, IsQuittingCyclicContinuation reward terminal) :
    HasAdmissibleAbsorbingQuittingCycle reward ∨
      HasIsolatedNegativeAbsorbingQuittingCycle reward := by
  obtain ⟨terminal, period, block, hblock⟩ := hcycle
  rcases isQuittingCycleAdmissible_or_isolated_negative reward period block with
    hadmissible | ⟨who, hiso, hneg⟩
  · exact Or.inl ⟨terminal, period, block, hblock, hadmissible⟩
  · exact Or.inr ⟨terminal, period, block, who, hblock, hiso, hneg⟩

/-- **The repaired three-branch disjunction.**

Every weight admitting *some* absorbing cyclic continuation block is zero-solo,
or admits an admissible absorbing cycle, or admits an absorbing cycle isolating
a coordinate of negative solo weight.

`HEADLINE` — the repair of the carrier refuted by
`not_forall_isQuittingZeroSolo_or_hasAdmissibleAbsorbingQuittingCycle`: adding
the isolated-negative branch makes the disjunction exhaustive on every weight
that admits an absorbing cycle at all, since the only way admissibility can fail
at a block is the isolated-negative configuration, whose mismatch is then
exactly `-r_who({who})` by `quittingIsolatedNegativeCycle_mismatch_eq`.  It does
**not** give an existence theorem: sufficiency is known for the zero-solo and
admissible branches only, the isolated-negative branch has no sufficiency
theorem, and weights admitting no absorbing complementary cycle of any period
are outside the hypothesis and remain open. -/
theorem quittingCycle_zeroSolo_or_admissible_or_isolatedNegative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcycle : ∃ terminal : Payoff ι, IsQuittingCyclicContinuation reward terminal) :
    IsQuittingZeroSolo reward ∨
      HasAdmissibleAbsorbingQuittingCycle reward ∨
      HasIsolatedNegativeAbsorbingQuittingCycle reward :=
  Or.inr (hasAdmissible_or_hasIsolatedNegative_of_cyclicContinuation reward hcycle)

/-! ## The refutation witness lies in the new branch

Everything used here is already built in
`QuittingDisjunctionCounterexample.lean`; this section is assembly. -/

namespace QuittingDisjunctionCounterexample

/-- **The counterexample weight is in the third branch.**  Its witness block --
coordinate `2` quitting with probability one against the value `(1, -1)`,
coordinate `1` silent -- isolates coordinate `2`, whose solo weight is
`r_2({2}) = -1 < 0`. -/
theorem hasIsolatedNegativeAbsorbingQuittingCycle_reward :
    HasIsolatedNegativeAbsorbingQuittingCycle reward :=
  ⟨witnessValue, 0, witnessBlock, true, witnessBlock_isCyclicContinuationBlock,
    witnessBlock_isIsolated, by
      rw [reward_singleton_true_self]; norm_num⟩

/-- **The third branch is exactly what the refutation needed.**  The
counterexample weight fails both original branches and lands in the new one, so
the repair is neither vacuous nor avoidable. -/
theorem not_zeroSolo_and_not_admissible_and_isolatedNegative :
    ¬ IsQuittingZeroSolo reward ∧
      ¬ HasAdmissibleAbsorbingQuittingCycle reward ∧
      HasIsolatedNegativeAbsorbingQuittingCycle reward :=
  ⟨not_isQuittingZeroSolo_reward, not_hasAdmissibleAbsorbingQuittingCycle_reward,
    hasIsolatedNegativeAbsorbingQuittingCycle_reward⟩

end QuittingDisjunctionCounterexample

/-! ## The branches overlap: exhaustive, not exclusive

Two machine-checked overlaps.  The first reuses the regression weight of
`QuittingCycleIsolatedCoordinate.lean` -- every entry `0` except
`r_true({true}) = -1` -- which is zero-solo and lands in the isolated-negative
branch.  The second is the zero weight, which is zero-solo and admits an
admissible absorbing cycle (its solo weights are `0`, so every cycle is
admissible on the nonnegativity disjunct). -/

namespace QuittingIsolatedNegativeSoloRegression

/-- The regression weight is zero-solo: `r_false({false}) = 0` and
`r_true({true}) = -1`. -/
theorem isQuittingZeroSolo_reward : IsQuittingZeroSolo reward := by
  intro who
  cases who with
  | false => simp [reward]
  | true => rw [soloReward_true_true]; norm_num

/-- ... and it lands in the isolated-negative branch. -/
theorem hasIsolatedNegativeAbsorbingQuittingCycle_reward :
    HasIsolatedNegativeAbsorbingQuittingCycle reward :=
  ⟨value, 0, quittingRowBlock value root, true, isCyclicContinuationBlock,
    isIsolated, by rw [soloReward_true_true]; norm_num⟩

end QuittingIsolatedNegativeSoloRegression

namespace QuittingZeroWeightAdmissibleCycle

/-- The zero weight: every table entry vanishes. -/
def reward : {S : Finset Bool // S.Nonempty} → Payoff Bool := fun _ _ ↦ 0

@[simp] theorem reward_apply (S : {S : Finset Bool // S.Nonempty}) (who : Bool) :
    reward S who = 0 := rfl

/-- The owner `true` quits with probability one; `false` continues surely. -/
def hazard : PMF Bool := PMF.pure true

/-- The witness row: the solo-quitter row owned by `true`. -/
def root : Bool → PMF Bool := quittingSoloStationaryRoot true hazard

/-- The witness value, the zero vector. -/
def value : Payoff Bool := quittingSoloReward reward true

theorem value_eq_successor :
    value = quittingRootSuccessorPayoff reward value root :=
  (quittingRootSuccessorPayoff_soloStationaryRoot_self reward true hazard).symm

theorem isEndpointNash : IsεQuittingRootEndpointNash reward value 0 root := by
  refine isεQuittingRootEndpointNash_soloStationaryRoot reward true hazard ?_
  intro other _
  simp [quittingSoloReward, quittingSingletonCollisionReward]

theorem absorptionMass_pos : 0 < quittingRootAbsorptionMass root := by
  rw [root, quittingRootAbsorptionMass_soloStationaryRoot, hazard]
  simp

theorem abs_value_le : ∀ who, |value who| ≤ quittingRewardBound reward :=
  fun who ↦
    abs_reward_le_quittingRewardBound reward (quittingSingletonTerminal true) who

/-- The witness row is an absorbing exact cyclic continuation block. -/
theorem isCyclicContinuationBlock :
    IsQuittingCyclicContinuationBlock reward value 1
      (quittingRowBlock value root) :=
  quittingRowBlock_isQuittingCyclicContinuationBlock reward value root
    abs_value_le value_eq_successor isEndpointNash absorptionMass_pos

/-- Its cycle is admissible on the nonnegativity disjunct: every solo weight of
the zero table is `0`. -/
theorem isCycleAdmissible :
    IsQuittingCycleAdmissible reward
      (quittingCyclicContinuationBlockCycle 0 (quittingRowBlock value root)) :=
  fun _ ↦ Or.inr (by simp)

/-- The zero weight is zero-solo. -/
theorem isQuittingZeroSolo_reward : IsQuittingZeroSolo reward := fun _ ↦ by simp

/-- ... and it admits an admissible absorbing cycle. -/
theorem hasAdmissibleAbsorbingQuittingCycle_reward :
    HasAdmissibleAbsorbingQuittingCycle reward :=
  ⟨value, 0, quittingRowBlock value root, isCyclicContinuationBlock,
    isCycleAdmissible⟩

end QuittingZeroWeightAdmissibleCycle

/-- **The three branches are exhaustive but not mutually exclusive.**  Zero-solo
overlaps the admissible branch (the zero weight) and the isolated-negative
branch (the regression weight of `QuittingCycleIsolatedCoordinate.lean`), so
`quittingCycle_zeroSolo_or_admissible_or_isolatedNegative` cannot be sharpened
to an "exactly one" statement.  What *is* exclusive is the pairing at a fixed
block: `not_isQuittingCycleAdmissible_of_isolated_negative`. -/
theorem quittingThreeBranch_not_mutually_exclusive :
    (∃ reward : {S : Finset Bool // S.Nonempty} → Payoff Bool,
        IsQuittingZeroSolo reward ∧
          HasAdmissibleAbsorbingQuittingCycle reward) ∧
      ∃ reward : {S : Finset Bool // S.Nonempty} → Payoff Bool,
        IsQuittingZeroSolo reward ∧
          HasIsolatedNegativeAbsorbingQuittingCycle reward :=
  ⟨⟨QuittingZeroWeightAdmissibleCycle.reward,
      QuittingZeroWeightAdmissibleCycle.isQuittingZeroSolo_reward,
      QuittingZeroWeightAdmissibleCycle.hasAdmissibleAbsorbingQuittingCycle_reward⟩,
    ⟨QuittingIsolatedNegativeSoloRegression.reward,
      QuittingIsolatedNegativeSoloRegression.isQuittingZeroSolo_reward,
      QuittingIsolatedNegativeSoloRegression.hasIsolatedNegativeAbsorbingQuittingCycle_reward⟩⟩

end GameTheory
