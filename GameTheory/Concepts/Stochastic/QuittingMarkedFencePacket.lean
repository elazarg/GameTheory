/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Tactic

/-!
# Finite marked fence packets

This file isolates the finite weighted selection argument used by the
player-marked boundary-root analysis of quitting games.  A sufficiently
negative mean owner reward forces quantitative mass on a marked loss event.
That mass either already lies on a good boundary packet, or one fixed
non-owner player occurs with quantitatively large mass as a newly negative
marked quitter.

The result is deliberately division-free.  In particular, it remains useful
at intermediate stages where positivity of a denominator has not yet been
packaged for Lean.  It is only a one-step selection result: iterating it can
force a repeated player name, but does not by itself identify recurrent
charts, values, or continuation states.
-/

namespace GameTheory

namespace QuittingMarkedFencePacket

/-- Total weight of a predicate in a finite packet. -/
noncomputable def packetMass {Ω : Type*} [Fintype Ω]
    (weight : Ω → ℝ) (P : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if P ω then weight ω else 0

/-- The owner loses at least half of the threshold at this mark.  The
division-free form is useful in the arithmetic proof below. -/
def IsOwnerLoss {Ω : Type*} (θ : ℝ) (ownerReward : Ω → ℝ) (ω : Ω) : Prop :=
  2 * ownerReward ω ≤ -θ

/-- A loss mark is good when every marked quitter is still strictly above
the negative threshold. -/
def IsGoodBoundary {ι Ω : Type*} (θ : ℝ) (ownerReward : Ω → ℝ)
    (quitters : Ω → Finset ι) (value : Ω → ι → ℝ) (ω : Ω) : Prop :=
  IsOwnerLoss θ ownerReward ω ∧
    ∀ j ∈ quitters ω, -θ < value ω j

/-- Player `j` is a new negative owner at a loss mark when `j` is marked as
quitting and its current continuation value is at most `-θ`. -/
def IsNewNegativeOwner {ι Ω : Type*} (θ : ℝ) (ownerReward : Ω → ℝ)
    (quitters : Ω → Finset ι) (value : Ω → ι → ℝ) (j : ι) (ω : Ω) : Prop :=
  IsOwnerLoss θ ownerReward ω ∧
    j ∈ quitters ω ∧ value ω j ≤ -θ

/-- A negative weighted mean and a pointwise lower reward bound force mass on
the half-threshold loss event.  No division is used in the conclusion. -/
theorem theta_le_two_mul_packetMass_ownerLoss
    {Ω : Type*} [Fintype Ω]
    (weight ownerReward : Ω → ℝ) (θ M : ℝ)
    (hweight : ∀ ω, 0 ≤ weight ω)
    (hweight_sum : ∑ ω, weight ω = 1)
    (htheta : 0 ≤ θ)
    (hreward_lower : ∀ ω, -M ≤ ownerReward ω)
    (hmean : ∑ ω, weight ω * ownerReward ω ≤ -θ) :
    θ ≤ 2 * M * packetMass weight (IsOwnerLoss θ ownerReward) := by
  classical
  have hpoint (ω : Ω) :
      -θ * weight ω -
          (if IsOwnerLoss θ ownerReward ω then 2 * M * weight ω else 0)
        ≤ 2 * (weight ω * ownerReward ω) := by
    by_cases hloss : IsOwnerLoss θ ownerReward ω
    · rw [if_pos hloss]
      have hmul := mul_le_mul_of_nonneg_left (hreward_lower ω) (hweight ω)
      nlinarith [mul_nonneg htheta (hweight ω)]
    · rw [if_neg hloss]
      have hre : -θ ≤ 2 * ownerReward ω :=
        le_of_lt (lt_of_not_ge hloss)
      have hmul := mul_le_mul_of_nonneg_right hre (hweight ω)
      nlinarith
  have hsum_point :=
    Finset.sum_le_sum (s := Finset.univ) (fun ω _ => hpoint ω)
  have hlower :
      -θ - 2 * M * packetMass weight (IsOwnerLoss θ ownerReward)
        ≤ 2 * ∑ ω, weight ω * ownerReward ω := by
    calc
      -θ - 2 * M * packetMass weight (IsOwnerLoss θ ownerReward) =
          ∑ ω, (-θ * weight ω -
            (if IsOwnerLoss θ ownerReward ω then 2 * M * weight ω else 0)) := by
              simp only [packetMass, Finset.sum_sub_distrib]
              rw [← Finset.mul_sum, hweight_sum, mul_one]
              congr 1
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro ω _
              by_cases hloss : IsOwnerLoss θ ownerReward ω <;>
                simp [hloss]
      _ ≤ ∑ ω, 2 * (weight ω * ownerReward ω) := hsum_point
      _ = 2 * ∑ ω, weight ω * ownerReward ω := by
        rw [Finset.mul_sum]
  have hupper : 2 * ∑ ω, weight ω * ownerReward ω ≤ 2 * (-θ) :=
    mul_le_mul_of_nonneg_left hmean (by norm_num)
  linarith

/-- In any nonempty finite family, some entry is at least the average, stated
without division. -/
theorem exists_sum_le_card_mul
    {α : Type*}
    (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) :
    ∃ a ∈ s, ∑ b ∈ s, f b ≤ (s.card : ℝ) * f a := by
  classical
  by_contra h
  push Not at h
  obtain ⟨a, ha⟩ := hs
  have hsum_lt :
      ∑ b ∈ s, (s.card : ℝ) * f b <
        ∑ _b ∈ s, ∑ c ∈ s, f c := by
    apply Finset.sum_lt_sum
    · intro b hb
      exact (h b hb).le
    · exact ⟨a, ha, h a ha⟩
  have hirrefl :
      (s.card : ℝ) * (∑ b ∈ s, f b) <
        (s.card : ℝ) * (∑ b ∈ s, f b) := by
    calc
      (s.card : ℝ) * (∑ b ∈ s, f b) =
          ∑ b ∈ s, (s.card : ℝ) * f b := by
            rw [Finset.mul_sum]
      _ < ∑ _b ∈ s, ∑ c ∈ s, f c := hsum_lt
      _ = (s.card : ℝ) * (∑ b ∈ s, f b) := by
        simp [nsmul_eq_mul]
  exact (lt_irrefl _ hirrefl)

/-- The finite marked-packet dichotomy.

If the owner's weighted mean reward is at most `-θ`, then either good boundary
marks have mass at least `θ / (4M)` in division-free form, or one fixed
non-owner player has new-negative marked mass at least
`θ / (4M * (|ι| - 1))`, again in division-free form.  The cardinality is
written exactly as `card (univ.erase owner)`, avoiding cast subtraction.
-/
theorem marked_packet_dichotomy
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι] [Fintype Ω]
    (owner : ι) (weight ownerReward : Ω → ℝ)
    (quitters : Ω → Finset ι) (value : Ω → ι → ℝ) (θ M : ℝ)
    (hweight : ∀ ω, 0 ≤ weight ω)
    (hweight_sum : ∑ ω, weight ω = 1)
    (htheta : 0 ≤ θ) (hM : 0 ≤ M)
    (hreward_lower : ∀ ω, -M ≤ ownerReward ω)
    (hmean : ∑ ω, weight ω * ownerReward ω ≤ -θ)
    (howner_not_quitter : ∀ ω, owner ∉ quitters ω) :
    θ ≤ 4 * M * packetMass weight
        (IsGoodBoundary θ ownerReward quitters value) ∨
      ∃ j ∈ (Finset.univ.erase owner : Finset ι),
        θ ≤ 4 * M * ((Finset.univ.erase owner : Finset ι).card : ℝ) *
          packetMass weight
            (IsNewNegativeOwner θ ownerReward quitters value j) := by
  classical
  let players : Finset ι := Finset.univ.erase owner
  let lossMass : ℝ := packetMass weight (IsOwnerLoss θ ownerReward)
  let goodMass : ℝ := packetMass weight
    (IsGoodBoundary θ ownerReward quitters value)
  let badMass : ι → ℝ := fun j => packetMass weight
    (IsNewNegativeOwner θ ownerReward quitters value j)
  have hloss : θ ≤ 2 * M * lossMass := by
    exact theta_le_two_mul_packetMass_ownerLoss weight ownerReward θ M
      hweight hweight_sum htheta hreward_lower hmean
  have hcover_point (ω : Ω) :
      (if IsOwnerLoss θ ownerReward ω then weight ω else 0) ≤
        (if IsGoodBoundary θ ownerReward quitters value ω then weight ω else 0) +
          ∑ j ∈ players,
            if IsNewNegativeOwner θ ownerReward quitters value j ω
            then weight ω else 0 := by
    by_cases hlossω : IsOwnerLoss θ ownerReward ω
    · by_cases hgoodω : IsGoodBoundary θ ownerReward quitters value ω
      · rw [if_pos hlossω, if_pos hgoodω]
        exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => by
          split <;> simp [hweight ω])
      · have hnotall :
            ¬ ∀ j ∈ quitters ω, -θ < value ω j := by
          intro hall
          exact hgoodω ⟨hlossω, hall⟩
        push Not at hnotall
        obtain ⟨j, hjquit, hjvalue⟩ := hnotall
        have hjne : j ≠ owner := by
          intro hjo
          subst j
          exact howner_not_quitter ω hjquit
        have hjplayers : j ∈ players := by
          simp [players, hjne]
        have hjbad :
            IsNewNegativeOwner θ ownerReward quitters value j ω :=
          ⟨hlossω, hjquit, hjvalue⟩
        have hsingle :
            weight ω ≤ ∑ k ∈ players,
              if IsNewNegativeOwner θ ownerReward quitters value k ω
              then weight ω else 0 := by
          calc
            weight ω =
                (if IsNewNegativeOwner θ ownerReward quitters value j ω
                  then weight ω else 0) := by simp [hjbad]
            _ ≤ ∑ k ∈ players,
                if IsNewNegativeOwner θ ownerReward quitters value k ω
                then weight ω else 0 := by
              refine Finset.single_le_sum
                (s := players)
                (f := fun k =>
                  if IsNewNegativeOwner θ ownerReward quitters value k ω
                  then weight ω else 0) ?_ hjplayers
              intro k _
              by_cases hkbad :
                  IsNewNegativeOwner θ ownerReward quitters value k ω <;>
                simp [hkbad, hweight ω]
        simpa [hlossω, hgoodω] using hsingle
    · have hnotgood :
          ¬ IsGoodBoundary θ ownerReward quitters value ω :=
        fun hgood => hlossω hgood.1
      rw [if_neg hlossω, if_neg hnotgood]
      exact add_nonneg (le_refl 0) (Finset.sum_nonneg fun _ _ => by
        split <;> simp [hweight ω])
  have hcover : lossMass ≤ goodMass + ∑ j ∈ players, badMass j := by
    have hsum_cover :=
      Finset.sum_le_sum (s := Finset.univ) (fun ω _ => hcover_point ω)
    dsimp only [lossMass, goodMass, badMass, packetMass]
    calc
      (∑ ω, if IsOwnerLoss θ ownerReward ω then weight ω else 0) ≤
          ∑ ω,
            ((if IsGoodBoundary θ ownerReward quitters value ω
                then weight ω else 0) +
              ∑ j ∈ players,
                if IsNewNegativeOwner θ ownerReward quitters value j ω
                then weight ω else 0) := hsum_cover
      _ = (∑ ω, if IsGoodBoundary θ ownerReward quitters value ω
              then weight ω else 0) +
            ∑ j ∈ players, ∑ ω,
              if IsNewNegativeOwner θ ownerReward quitters value j ω
              then weight ω else 0 := by
        rw [Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_comm]
  by_cases hgood : θ ≤ 4 * M * goodMass
  · left
    simpa [goodMass] using hgood
  · right
    have hgood_lt : 4 * M * goodMass < θ := lt_of_not_ge hgood
    have hscale_nonneg : 0 ≤ 2 * M := mul_nonneg (by norm_num) hM
    have hscaled_cover :
        2 * M * lossMass ≤ 2 * M * (goodMass + ∑ j ∈ players, badMass j) :=
      mul_le_mul_of_nonneg_left hcover hscale_nonneg
    have hbad_total : θ ≤ 4 * M * ∑ j ∈ players, badMass j := by
      nlinarith
    have hplayers : players.Nonempty := by
      obtain ⟨j, hjne⟩ := exists_ne owner
      exact ⟨j, by simp [players, hjne]⟩
    obtain ⟨j, hjplayers, hjaverage⟩ :=
      exists_sum_le_card_mul players hplayers badMass
    refine ⟨j, ?_, ?_⟩
    · simpa [players] using hjplayers
    · have hfactor_nonneg : 0 ≤ 4 * M := mul_nonneg (by norm_num) hM
      have hscaled_average :=
        mul_le_mul_of_nonneg_left hjaverage hfactor_nonneg
      calc
        θ ≤ 4 * M * ∑ k ∈ players, badMass k := hbad_total
        _ ≤ 4 * M * (players.card : ℝ) * badMass j := by
          nlinarith
        _ = 4 * M * ((Finset.univ.erase owner : Finset ι).card : ℝ) *
              packetMass weight
                (IsNewNegativeOwner θ ownerReward quitters value j) := by
          rfl

end QuittingMarkedFencePacket

end GameTheory
