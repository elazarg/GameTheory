/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Voting.LiquidDemocracy
import GameTheory.Mechanism.MedianVoter

/-!
# Liquid median

The one-dimensional instance of liquid democracy: ballots are points on the
line, and the effective ballots are aggregated by the weighted median
(`Math/WeightedMedian.lean`). This is the delegative counterpart of the
median-voter setting (`Mechanism/MedianVoter.lean`): casters' ballots enter
the median with multiplicity their guru weight.

## Main definitions

* `Voting.effectivePosition` — a caster's ballot on the line (non-casters
  carry weight `0`, so their value is immaterial to the weighted notions)
* `Voting.IsLiquidMedian` / `Voting.liquidMedian` — weighted-median outcome of
  a delegation profile

## Main results

* `isLiquidMedian_liquidMedian` — a liquid median always exists
* `liquidMedian_directProfile` — on all-cast profiles the liquid median is the
  electorate's `medianIdeal`, recovering the median-voter setting
* `isLiquidMedian_directProfile_iff` — the predicate-level correspondence
-/

namespace GameTheory.Voting

open DelegationProfile

variable {ι : Type*}

/-- The effective position of a voter on the line: the ballot they cast
directly. Non-casters carry weight `0`, so the default value never affects a
weighted-median notion. -/
noncomputable def effectivePosition (d : DelegationProfile ι ℝ) (i : ι) : ℝ :=
  (d.directBallot i).getD 0

@[simp] theorem effectivePosition_directProfile (p : ι → ℝ) :
    effectivePosition (directProfile p) = p := by
  funext i
  simp [effectivePosition, directBallot, directProfile]

variable [Fintype ι]

/-- `x` is a liquid median of the delegation profile: a weighted median of the
casters' ballots under guru weights. -/
def IsLiquidMedian (d : DelegationProfile ι ℝ) (x : ℝ) : Prop :=
  Math.IsWeightedMedian (effectivePosition d) d.weight x

/-- The canonical liquid median of a delegation profile. -/
noncomputable def liquidMedian [Nonempty ι] (d : DelegationProfile ι ℝ) : ℝ :=
  Math.weightedMedian (effectivePosition d) d.weight

/-- A liquid median always exists: the canonical choice is one. -/
theorem isLiquidMedian_liquidMedian [Nonempty ι] (d : DelegationProfile ι ℝ) :
    IsLiquidMedian d (liquidMedian d) :=
  Math.isWeightedMedian_weightedMedian _ _

/-- On an all-cast profile the liquid median is the electorate's median ideal
point: the delegative rule restricts to the median-voter setting. -/
theorem liquidMedian_directProfile [Nonempty ι] (p : ι → ℝ) :
    liquidMedian (directProfile p) = medianIdeal p := by
  rw [liquidMedian, effectivePosition_directProfile, medianIdeal]
  congr 1
  funext j
  exact weight_directProfile p j

/-- Predicate form of the direct-profile correspondence. -/
theorem isLiquidMedian_directProfile_iff (p : ι → ℝ) (x : ℝ) :
    IsLiquidMedian (directProfile p) x ↔ Math.IsWeightedMedian p (fun _ => 1) x := by
  have hw : (directProfile p).weight = fun _ => (1 : ℕ) :=
    funext (weight_directProfile p)
  rw [IsLiquidMedian, effectivePosition_directProfile, hw]

end GameTheory.Voting
