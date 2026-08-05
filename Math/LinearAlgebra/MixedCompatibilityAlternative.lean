/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.LinearAlgebra.MixedCompatibilityCharge
import Mathlib.Algebra.BigOperators.Field

/-!
# Normalized mixed compatibility alternative

Suppose every player's subsystem of a finite family of weak linear
inequalities is feasible.  Then exactly one of the following positive
outcomes is available:

* the whole coupled system is feasible;
* there is a normalized nonnegative Farkas balance with strictly positive
  certificate value whose player-constraint support contains constraints
  owned by two distinct players.

The normalization uses only multiplier mass on player constraints.  Common
facet multipliers are not counted.  The second branch is therefore a
concrete genuinely mixed obstruction, not merely an arbitrary infeasibility
proof.

This theorem does not turn the obstruction into a continuation witness,
rank descent, or a discharged account.  It identifies the exact finite
mixed-player leaf that remains when separate player feasibility does not
glue.
-/

open Finset BigOperators

namespace Math
namespace LinearAlgebra

noncomputable section

variable {Facet Player : Type*}
  [Fintype Facet] [Fintype Player] [Nonempty Player]
variable {Constraint : Player → Type*}
  [∀ player, Fintype (Constraint player)]
variable {n : ℕ}

/-- A normalized coupled Farkas obstruction whose player-constraint
support contains two explicitly named, differently owned constraints. -/
structure NormalizedGenuinelyMixedCompatibilityObstruction
    (facetNormal : Facet → Fin n → ℝ)
    (facetRhs : Facet → ℝ)
    (playerNormal : ∀ player, Constraint player → Fin n → ℝ)
    (playerRhs : ∀ player, Constraint player → ℝ) where
  multiplier : CoupledRow Facet Player Constraint → ℝ
  isNonnegativeBalance :
    IsNonnegativeBalance
      (coupledNormal facetNormal playerNormal) multiplier
  playerMass_eq_one :
    coupledRelaxedMultiplierMass multiplier = 1
  value_pos :
    0 < ∑ row, multiplier row *
      coupledRelaxedRhs facetRhs playerRhs 0 row
  firstOwner : Player
  firstConstraint : Constraint firstOwner
  secondOwner : Player
  secondConstraint : Constraint secondOwner
  owners_ne : firstOwner ≠ secondOwner
  firstMultiplier_pos :
    0 < multiplier (Sum.inr ⟨firstOwner, firstConstraint⟩)
  secondMultiplier_pos :
    0 < multiplier (Sum.inr ⟨secondOwner, secondConstraint⟩)

namespace NormalizedGenuinelyMixedCompatibilityObstruction

variable
    {facetNormal : Facet → Fin n → ℝ}
    {facetRhs : Facet → ℝ}
    {playerNormal : ∀ player, Constraint player → Fin n → ℝ}
    {playerRhs : ∀ player, Constraint player → ℝ}

omit [Nonempty Player] in
/-- A normalized mixed obstruction is incompatible with a simultaneous
continuation witness. -/
theorem not_coupledFeasible
    (O : NormalizedGenuinelyMixedCompatibilityObstruction
      facetNormal facetRhs playerNormal playerRhs) :
    ¬IsFeasible
      (coupledNormal facetNormal playerNormal)
      (coupledRelaxedRhs facetRhs playerRhs 0) := by
  intro feasible
  have nonpositive :=
    weightedRhs_nonpos_of_feasible_balance
      (coupledNormal facetNormal playerNormal)
      (coupledRelaxedRhs facetRhs playerRhs 0)
      feasible O.multiplier O.isNonnegativeBalance
  exact (not_lt_of_ge nonpositive) O.value_pos

omit [Nonempty Player] in
/-- At every point satisfying the common facets, a normalized mixed
obstruction exposes an actual player-owned constraint whose deficit is at
least the full certificate value. -/
theorem exists_playerConstraintDeficit_ge_value
    (O : NormalizedGenuinelyMixedCompatibilityObstruction
      facetNormal facetRhs playerNormal playerRhs)
    (x : Fin n → ℝ)
    (hfacet : ∀ facet,
      facetRhs facet ≤ rowEval facetNormal facet x) :
    ∃ player, ∃ constraint,
      (∑ row, O.multiplier row *
        coupledRelaxedRhs facetRhs playerRhs 0 row) ≤
      playerRhs player constraint -
        rowEval (playerNormal player) constraint x := by
  let edge :
      Σ player, Constraint player :=
    ⟨O.firstOwner, O.firstConstraint⟩
  let nonemptyEdges : Nonempty (Σ player, Constraint player) :=
    ⟨edge⟩
  letI := nonemptyEdges
  exact exists_playerConstraintDeficit_ge_coupledWeightedRhs
    facetNormal facetRhs playerNormal playerRhs
    O.multiplier O.isNonnegativeBalance O.playerMass_eq_one x hfacet

end NormalizedGenuinelyMixedCompatibilityObstruction

omit [Fintype Facet] [Nonempty Player] in
private theorem all_player_multipliers_zero_of_mass_zero
    {u : CoupledRow Facet Player Constraint → ℝ}
    (hu_nonnegative : ∀ row, 0 ≤ u row)
    (hmass : coupledRelaxedMultiplierMass u = 0) :
    ∀ player constraint, u (Sum.inr ⟨player, constraint⟩) = 0 := by
  have ownerMass_nonnegative :
      ∀ player, 0 ≤ ∑ constraint,
        u (Sum.inr ⟨player, constraint⟩) := by
    intro player
    exact Finset.sum_nonneg fun constraint _ =>
      hu_nonnegative (Sum.inr ⟨player, constraint⟩)
  have ownerMass_zero :
      ∀ player, (∑ constraint,
        u (Sum.inr ⟨player, constraint⟩)) = 0 := by
    intro player
    exact congrFun
      ((Fintype.sum_eq_zero_iff_of_nonneg
        ownerMass_nonnegative).mp hmass) player
  intro player constraint
  exact congrFun
    ((Fintype.sum_eq_zero_iff_of_nonneg
      (fun other =>
        hu_nonnegative (Sum.inr ⟨player, other⟩))).mp
      (ownerMass_zero player)) constraint

private theorem playerMass_pos_of_positive_certificate
    (facetNormal : Facet → Fin n → ℝ)
    (facetRhs : Facet → ℝ)
    (playerNormal : ∀ player, Constraint player → Fin n → ℝ)
    (playerRhs : ∀ player, Constraint player → ℝ)
    (hplayerFeasible : ∀ player, IsFeasible
      (playerSubsystemNormal facetNormal playerNormal player)
      (playerSubsystemRelaxedRhs facetRhs playerRhs 0 player))
    (u : CoupledRow Facet Player Constraint → ℝ)
    (hu : IsNonnegativeBalance
      (coupledNormal facetNormal playerNormal) u)
    (hpositive :
      0 < ∑ row, u row *
        coupledRelaxedRhs facetRhs playerRhs 0 row) :
    0 < coupledRelaxedMultiplierMass u := by
  have mass_nonnegative :
      0 ≤ coupledRelaxedMultiplierMass u := by
    exact Finset.sum_nonneg fun player _ =>
      Finset.sum_nonneg fun constraint _ =>
        hu.1 (Sum.inr ⟨player, constraint⟩)
  apply lt_of_le_of_ne mass_nonnegative
  intro mass_eq_zero
  have player_zero :=
    all_player_multipliers_zero_of_mass_zero hu.1 mass_eq_zero.symm
  let owner : Player := Classical.choice inferInstance
  let localMultiplier :
      PlayerRow Facet Constraint owner → ℝ
    | Sum.inl facet => u (Sum.inl facet)
    | Sum.inr _ => 0
  have localBalance :
      IsNonnegativeBalance
        (playerSubsystemNormal facetNormal playerNormal owner)
        localMultiplier := by
    constructor
    · intro row
      rcases row with facet | constraint
      · exact hu.1 (Sum.inl facet)
      · simp [localMultiplier]
    · intro coordinate
      have global := hu.2 coordinate
      rw [Fintype.sum_sum_type, Fintype.sum_sigma] at global
      simp_rw [player_zero] at global
      rw [Fintype.sum_sum_type]
      simpa [localMultiplier, playerSubsystemNormal,
        coupledNormal] using global
  have local_nonpositive :=
    weightedRhs_nonpos_of_feasible_balance
      (playerSubsystemNormal facetNormal playerNormal owner)
      (playerSubsystemRelaxedRhs facetRhs playerRhs 0 owner)
      (hplayerFeasible owner) localMultiplier localBalance
  have value_eq :
      (∑ row, localMultiplier row *
        playerSubsystemRelaxedRhs facetRhs playerRhs 0 owner row) =
      ∑ row, u row *
        coupledRelaxedRhs facetRhs playerRhs 0 row := by
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type,
      Fintype.sum_sigma]
    simp [localMultiplier, playerSubsystemRelaxedRhs,
      coupledRelaxedRhs, player_zero]
  rw [value_eq] at local_nonpositive
  exact (not_lt_of_ge local_nonpositive) hpositive

omit [Nonempty Player] in
private theorem exists_two_owned_positive_multipliers
    (facetNormal : Facet → Fin n → ℝ)
    (facetRhs : Facet → ℝ)
    (playerNormal : ∀ player, Constraint player → Fin n → ℝ)
    (playerRhs : ∀ player, Constraint player → ℝ)
    (hplayerFeasible : ∀ player, IsFeasible
      (playerSubsystemNormal facetNormal playerNormal player)
      (playerSubsystemRelaxedRhs facetRhs playerRhs 0 player))
    (u : CoupledRow Facet Player Constraint → ℝ)
    (hu : IsNonnegativeBalance
      (coupledNormal facetNormal playerNormal) u)
    (hmass : coupledRelaxedMultiplierMass u = 1)
    (hpositive :
      0 < ∑ row, u row *
        coupledRelaxedRhs facetRhs playerRhs 0 row) :
    ∃ firstOwner firstConstraint secondOwner secondConstraint,
      firstOwner ≠ secondOwner ∧
      0 < u (Sum.inr ⟨firstOwner, firstConstraint⟩) ∧
      0 < u (Sum.inr ⟨secondOwner, secondConstraint⟩) := by
  have first_exists :
      ∃ owner constraint,
        0 < u (Sum.inr ⟨owner, constraint⟩) := by
    by_contra none_positive
    push Not at none_positive
    have all_zero :
        ∀ owner constraint,
          u (Sum.inr ⟨owner, constraint⟩) = 0 := by
      intro owner constraint
      exact le_antisymm (none_positive owner constraint)
        (hu.1 (Sum.inr ⟨owner, constraint⟩))
    simp [coupledRelaxedMultiplierMass, all_zero] at hmass
  obtain ⟨firstOwner, firstConstraint, first_positive⟩ := first_exists
  refine ⟨firstOwner, firstConstraint, ?_⟩
  by_contra no_second
  push Not at no_second
  have other_zero :
      ∀ owner, owner ≠ firstOwner →
        ∀ constraint,
          u (Sum.inr ⟨owner, constraint⟩) = 0 := by
    intro owner owners_ne constraint
    exact le_antisymm
      (no_second owner constraint owners_ne.symm first_positive)
      (hu.1 (Sum.inr ⟨owner, constraint⟩))
  let localMultiplier :
      PlayerRow Facet Constraint firstOwner → ℝ
    | Sum.inl facet => u (Sum.inl facet)
    | Sum.inr constraint =>
        u (Sum.inr ⟨firstOwner, constraint⟩)
  have localBalance :
      IsNonnegativeBalance
        (playerSubsystemNormal facetNormal playerNormal firstOwner)
        localMultiplier := by
    constructor
    · intro row
      rcases row with facet | constraint
      · exact hu.1 (Sum.inl facet)
      · exact hu.1 (Sum.inr ⟨firstOwner, constraint⟩)
    · intro coordinate
      have global := hu.2 coordinate
      rw [Fintype.sum_sum_type, Fintype.sum_sigma] at global
      simp only [coupledNormal] at global
      have other_terms_zero :
          (∑ owner, ∑ constraint,
            u (Sum.inr ⟨owner, constraint⟩) *
              playerNormal owner constraint coordinate) =
          ∑ constraint,
            u (Sum.inr ⟨firstOwner, constraint⟩) *
              playerNormal firstOwner constraint coordinate := by
        classical
        apply Finset.sum_eq_single firstOwner
        · intro owner _ owner_ne
          simp [other_zero owner owner_ne]
        · simp
      rw [other_terms_zero] at global
      rw [Fintype.sum_sum_type]
      simpa [localMultiplier, playerSubsystemNormal,
        coupledNormal] using global
  have local_nonpositive :=
    weightedRhs_nonpos_of_feasible_balance
      (playerSubsystemNormal facetNormal playerNormal firstOwner)
      (playerSubsystemRelaxedRhs facetRhs playerRhs 0 firstOwner)
      (hplayerFeasible firstOwner) localMultiplier localBalance
  have value_eq :
      (∑ row, localMultiplier row *
        playerSubsystemRelaxedRhs
          facetRhs playerRhs 0 firstOwner row) =
      ∑ row, u row *
        coupledRelaxedRhs facetRhs playerRhs 0 row := by
    classical
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type,
      Fintype.sum_sigma]
    have other_rhs_zero :
        (∑ owner, ∑ constraint,
          u (Sum.inr ⟨owner, constraint⟩) *
            playerRhs owner constraint) =
        ∑ constraint,
          u (Sum.inr ⟨firstOwner, constraint⟩) *
            playerRhs firstOwner constraint := by
      apply Finset.sum_eq_single firstOwner
      · intro owner _ owner_ne
        simp [other_zero owner owner_ne]
      · simp
    simp only [localMultiplier, playerSubsystemRelaxedRhs,
      coupledRelaxedRhs]
    simp only [sub_zero]
    rw [other_rhs_zero]
  rw [value_eq] at local_nonpositive
  exact (not_lt_of_ge local_nonpositive) hpositive

/-- **Exact normalized mixed-player compatibility alternative.**

If every player-specific subsystem is feasible, then either the coupled
system is feasible, or infeasibility is witnessed by a normalized positive
Farkas balance with two explicitly named constraints owned by distinct
players. -/
theorem coupledFeasible_or_normalizedGenuinelyMixedObstruction
    (facetNormal : Facet → Fin n → ℝ)
    (facetRhs : Facet → ℝ)
    (playerNormal : ∀ player, Constraint player → Fin n → ℝ)
    (playerRhs : ∀ player, Constraint player → ℝ)
    (hplayerFeasible : ∀ player, IsFeasible
      (playerSubsystemNormal facetNormal playerNormal player)
      (playerSubsystemRelaxedRhs facetRhs playerRhs 0 player)) :
    IsFeasible
      (coupledNormal facetNormal playerNormal)
      (coupledRelaxedRhs facetRhs playerRhs 0) ∨
    Nonempty
      (NormalizedGenuinelyMixedCompatibilityObstruction
        facetNormal facetRhs playerNormal playerRhs) := by
  by_cases coupledFeasible :
      IsFeasible
        (coupledNormal facetNormal playerNormal)
        (coupledRelaxedRhs facetRhs playerRhs 0)
  · exact Or.inl coupledFeasible
  · right
    obtain ⟨raw, raw_nonnegative, raw_balance, raw_positive⟩ :=
      (theorem_of_alternative
        (coupledNormal facetNormal playerNormal)
        (coupledRelaxedRhs facetRhs playerRhs 0)).mp
          coupledFeasible
    have raw_mass_pos :=
      playerMass_pos_of_positive_certificate
        facetNormal facetRhs playerNormal playerRhs
        hplayerFeasible raw ⟨raw_nonnegative, raw_balance⟩
        raw_positive
    let multiplier :
        CoupledRow Facet Player Constraint → ℝ :=
      fun row => raw row / coupledRelaxedMultiplierMass raw
    have normalizedBalance :
        IsNonnegativeBalance
          (coupledNormal facetNormal playerNormal) multiplier := by
      constructor
      · intro row
        exact div_nonneg (raw_nonnegative row) raw_mass_pos.le
      · intro coordinate
        calc
          (∑ row, multiplier row *
              coupledNormal
                facetNormal playerNormal row coordinate) =
              (∑ row, raw row *
                coupledNormal
                  facetNormal playerNormal row coordinate) /
                coupledRelaxedMultiplierMass raw := by
                  simp only [multiplier, div_mul_eq_mul_div]
                  rw [Finset.sum_div]
          _ = 0 := by rw [raw_balance coordinate, zero_div]
    have normalizedMass :
        coupledRelaxedMultiplierMass multiplier = 1 := by
      unfold coupledRelaxedMultiplierMass multiplier
      simp_rw [← Finset.sum_div]
      exact div_self (ne_of_gt raw_mass_pos)
    have normalizedValue :
        0 < ∑ row, multiplier row *
          coupledRelaxedRhs facetRhs playerRhs 0 row := by
      calc
        0 <
            (∑ row, raw row *
              coupledRelaxedRhs facetRhs playerRhs 0 row) /
              coupledRelaxedMultiplierMass raw :=
          div_pos raw_positive raw_mass_pos
        _ = ∑ row, multiplier row *
            coupledRelaxedRhs facetRhs playerRhs 0 row := by
              simp only [multiplier, div_mul_eq_mul_div]
              rw [Finset.sum_div]
    obtain ⟨firstOwner, firstConstraint,
        secondOwner, secondConstraint,
        owners_ne, first_positive, second_positive⟩ :=
      exists_two_owned_positive_multipliers
        facetNormal facetRhs playerNormal playerRhs
        hplayerFeasible multiplier normalizedBalance
        normalizedMass normalizedValue
    exact ⟨{
      multiplier := multiplier
      isNonnegativeBalance := normalizedBalance
      playerMass_eq_one := normalizedMass
      value_pos := normalizedValue
      firstOwner := firstOwner
      firstConstraint := firstConstraint
      secondOwner := secondOwner
      secondConstraint := secondConstraint
      owners_ne := owners_ne
      firstMultiplier_pos := first_positive
      secondMultiplier_pos := second_positive
    }⟩

end

end LinearAlgebra
end Math
