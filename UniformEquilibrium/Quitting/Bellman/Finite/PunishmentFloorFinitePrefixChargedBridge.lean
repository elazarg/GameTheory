/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorChargedPotential
import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorFinitePrefix

/-!
# Finite-prefix dichotomy to reachable charged potentials

Every path from the punishment-floor anchor in the boxed charged relation is
an exact finite punishment-floor prefix: its states provide the values, its
predecessor roots provide the rows, and its abstract charge is exactly the
prefix absorption charge.  The unconditional finite-prefix dichotomy can
therefore be transported to the full reachable charged relation.

The resulting alternative is exact: either the quitting game already has a
uniform-equilibrium payoff, or every path in the punishment-floor reachable
Nash--Bellman relation has finite budget and the canonical budget-to-go is a
bounded potential.  The second branch is an accounting certificate only; it
does not realize a strategic tail or consume a prefix.  In particular, an
ordinary exact predecessor path does not carry the calibration, marked packet,
debt, and stopping-obstacle coherence required to define a marked absorption
cylinder; no map to that compactification is asserted here.
-/

noncomputable section

namespace GameTheory

open Math.ChargedPathBudget

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingPunishmentFloorBoxPath

private abbrev BoxRelation :=
  quittingPunishmentFloorBoxChargedRelation reward

/-- Payoff state at a finite charged-path time.  Values past the path horizon
are filled by its final state and are semantically irrelevant. -/
def value : {source target : QuittingPunishmentFloorBoxState reward} →
    BoxRelation.Path source target → ℕ → Payoff ι
  | _, _, .nil state, _ => state.1.1
  | _, _, .cons edge _, 0 => edge.tail.1.1
  | _, _, .cons _ rest, time + 1 => value rest time

/-- Root performing a finite charged-path update.  Roots at and past the
horizon are harmless fillers. -/
def root : {source target : QuittingPunishmentFloorBoxState reward} →
    BoxRelation.Path source target → ℕ → ι → PMF Bool
  | _, _, .nil state, _ => quittingRootOfSimplex state.1.2
  | _, _, .cons edge _, 0 => edge.root
  | _, _, .cons _ rest, time + 1 => root rest time

/-- The first decoded value is the source payoff. -/
@[simp] theorem value_zero
    {source target : QuittingPunishmentFloorBoxState reward}
    (path : BoxRelation.Path source target) :
    value path 0 = source.1.1 := by
  cases path <;> rfl

/-- Every decoded value through the horizon stays in the canonical reward
box. -/
theorem value_mem
    {source target : QuittingPunishmentFloorBoxState reward}
    (path : BoxRelation.Path source target)
    (time : ℕ) (htime : time ≤ path.length) :
    value path time ∈ quittingPunishmentFloorForwardCarrier reward := by
  induction path generalizing time with
  | nil state =>
      have hzero : time = 0 := by simpa using htime
      subst time
      exact state.2
  | cons edge rest ih =>
      cases time with
      | zero => exact edge.tail.2
      | succ time =>
          apply ih time
          simpa only [ChargedRelation.Path.length_cons, Nat.succ_le_succ_iff]
            using htime

/-- Decoded values obey the exact forward Bellman recursion. -/
theorem policy
    {source target : QuittingPunishmentFloorBoxState reward}
    (path : BoxRelation.Path source target)
    (time : ℕ) (htime : time < path.length) :
    value path (time + 1) =
      quittingRootSuccessorPayoff reward (value path time) (root path time) := by
  induction path generalizing time with
  | nil state => simp at htime
  | cons edge rest ih =>
      cases time with
      | zero =>
          simpa only [value, root, value_zero,
            quittingPunishmentFloorBoxChargedRelation,
            QuittingPunishmentFloorBoxEdge.root] using edge.exactEdge.1
      | succ time =>
          apply ih time
          simpa only [ChargedRelation.Path.length_cons, Nat.succ_lt_succ_iff]
            using htime

/-- Every decoded predecessor root is exact Nash against its source value. -/
theorem exactNash
    {source target : QuittingPunishmentFloorBoxState reward}
    (path : BoxRelation.Path source target)
    (time : ℕ) (htime : time < path.length) :
    IsεQuittingRootNash reward (value path time) 0 (root path time) := by
  induction path generalizing time with
  | nil state => simp at htime
  | cons edge rest ih =>
      cases time with
      | zero =>
          exact (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
            reward edge.tail.1.1 edge.root).1 edge.exactEdge.2
      | succ time =>
          apply ih time
          simpa only [ChargedRelation.Path.length_cons, Nat.succ_lt_succ_iff]
            using htime

/-- Decoding preserves total absorption charge exactly. -/
theorem sum_absorptionMass_root_eq_chargeSum
    {source target : QuittingPunishmentFloorBoxState reward}
    (path : BoxRelation.Path source target) :
    (∑ time ∈ Finset.range path.length,
        quittingRootAbsorptionMass (root path time)) = path.chargeSum := by
  induction path with
  | nil state => simp
  | cons edge rest ih =>
      rw [ChargedRelation.Path.length_cons, Finset.sum_range_succ']
      simp only [root, ih, ChargedRelation.Path.chargeSum_cons]
      change rest.chargeSum + quittingRootAbsorptionMass edge.root =
        edge.absorptionCharge + rest.chargeSum
      rw [QuittingPunishmentFloorBoxEdge.absorptionCharge]
      exact add_comm _ _

/-- Convert an anchored charged path into the general exact finite-prefix
certificate without changing roots, values, horizon, or charge. -/
def toFinitePrefix
    {target : QuittingPunishmentFloorBoxState reward}
    (path : BoxRelation.Path
      (quittingPunishmentFloorBoxAnchor reward) target) :
    QuittingPunishmentFloorFinitePrefix reward where
  roots := root path
  value := value path
  horizon := path.length
  value_mem := fun time htime => value_mem path time htime
  anchor_floor := by
    intro who
    rw [value_zero]
    rfl
  policy := fun time htime => policy path time htime
  exactNash := fun time htime => exactNash path time htime

/-- The converted exact prefix has precisely the charged-path charge. -/
@[simp] theorem toFinitePrefix_charge
    {target : QuittingPunishmentFloorBoxState reward}
    (path : BoxRelation.Path
      (quittingPunishmentFloorBoxAnchor reward) target) :
    (toFinitePrefix path).charge = path.chargeSum := by
  exact sum_absorptionMass_root_eq_chargeSum path

end QuittingPunishmentFloorBoxPath

/-- A common charge bound on the general finite-prefix certificates bounds
every exact boxed predecessor path from the punishment floor. -/
theorem hasAnchoredChargeBound_of_finitePrefixChargeBound
    {chargeBound : ℝ}
    (hbound : ∀ cert : QuittingPunishmentFloorFinitePrefix reward,
      cert.charge ≤ chargeBound) :
    HasQuittingPunishmentFloorAnchoredChargeBound reward chargeBound := by
  intro target path
  rw [← QuittingPunishmentFloorBoxPath.toFinitePrefix_charge path]
  exact hbound (QuittingPunishmentFloorBoxPath.toFinitePrefix path)

/-- **Direct charged-relation alternative.**  Every finite quitting game
either has a uniform-equilibrium payoff or its full punishment-floor reachable
exact Nash--Bellman relation has finite absorption-charge budget. -/
theorem quittingGame_uniformPayoff_or_punishmentFloorReachable_hasFiniteBudget
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
      (quittingPunishmentFloorReachableChargedRelation reward).HasFiniteBudget := by
  rcases quittingGame_uniformPayoff_or_bounded_floorPrefixCharge
    reward with hpayoff | ⟨chargeBound, _, hbound⟩
  · exact Or.inl hpayoff
  · exact Or.inr
      (quittingPunishmentFloorReachable_hasFiniteBudget_of_anchoredChargeBound
        (hasAnchoredChargeBound_of_finitePrefixChargeBound hbound))

/-- **Direct bounded-potential alternative.**  In the non-uniform-payoff
branch the canonical reachable budget-to-go is already a bounded potential. -/
theorem quittingGame_uniformPayoff_or_punishmentFloorReachable_boundedPotential
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
      ∃ Φ : QuittingPunishmentFloorReachableState reward → ℝ,
        (quittingPunishmentFloorReachableChargedRelation reward).IsBoundedPotential Φ := by
  rcases quittingGame_uniformPayoff_or_punishmentFloorReachable_hasFiniteBudget
    reward with hpayoff | hbudget
  · exact Or.inl hpayoff
  · exact Or.inr
      ⟨(quittingPunishmentFloorReachableChargedRelation reward).value,
        (quittingPunishmentFloorReachableChargedRelation reward).value_isBoundedPotential
          hbudget⟩

/-- The bounded-potential branch can be witnessed by the named canonical
budget-to-go potential rather than an unspecified certificate. -/
theorem quittingGame_uniformPayoff_or_punishmentFloorReachable_canonicalPotential
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
      (quittingPunishmentFloorReachableChargedRelation reward).IsBoundedPotential
        (quittingPunishmentFloorReachablePotential reward) := by
  rcases quittingGame_uniformPayoff_or_bounded_floorPrefixCharge reward with
    hpayoff | ⟨chargeBound, _, hbound⟩
  · exact Or.inl hpayoff
  · exact Or.inr
      (quittingPunishmentFloorReachablePotential_isBoundedPotential
        (hasAnchoredChargeBound_of_finitePrefixChargeBound hbound))

end GameTheory
