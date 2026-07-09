/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Voting.LiquidDemocracy
import GameTheory.Mechanism.SocialChoice.MedianVoter

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
directly. Non-casters carry weight `0`, so the default value never affects the
weighted-median predicate, and whenever some voter casts the canonical
`liquidMedian` is attained at a cast ballot (`exists_casts_liquidMedian`). -/
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

/-- The canonical liquid median of a delegation profile. When some voter casts
it is one of the cast ballots (`exists_casts_liquidMedian`); on the degenerate
profile where every voter abstains, all weights vanish, every real is
vacuously a liquid median, and the canonical choice falls back to the least
effective position. -/
noncomputable def liquidMedian [Nonempty ι] (d : DelegationProfile ι ℝ) : ℝ :=
  Math.weightedMedian (effectivePosition d) d.weight

/-- A liquid median always exists: the canonical choice is one. -/
theorem isLiquidMedian_liquidMedian [Nonempty ι] (d : DelegationProfile ι ℝ) :
    IsLiquidMedian d (liquidMedian d) :=
  Math.isWeightedMedian_weightedMedian _ _

/-- Whenever some voter casts, the canonical liquid median is one of the cast
ballots — the `effectivePosition` default never determines it. -/
theorem exists_casts_liquidMedian [Nonempty ι] {d : DelegationProfile ι ℝ}
    {j₀ : ι} (hc : d.IsCaster j₀) :
    ∃ j b, d.Casts j b ∧ liquidMedian d = b := by
  have hW : 0 < Math.totalWeight d.weight :=
    Finset.sum_pos' (fun _ _ => Nat.zero_le _)
      ⟨j₀, Finset.mem_univ j₀, lt_of_lt_of_le one_pos hc.one_le_weight⟩
  obtain ⟨a, hwa, hpa⟩ :=
    Math.exists_pos_weight_eq_weightedMedian (pos := effectivePosition d) hW
  have hca : d.IsCaster a := by
    by_contra h
    rw [weight_eq_zero_of_not_isCaster h] at hwa
    exact lt_irrefl 0 hwa
  obtain ⟨b, hb⟩ := hca
  refine ⟨a, b, hb, ?_⟩
  rw [liquidMedian, ← hpa, effectivePosition, directBallot_eq_some_iff.mpr hb]
  rfl

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
