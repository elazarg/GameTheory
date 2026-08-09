/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Projective.FiniteForwardProjectiveLasso

/-!
# A game-level charge alternative for punishment-floor forward orbits

A punishment-floor exact forward orbit retains every predecessor choice rather
than fixing one classical selector.  Its roots satisfy the support-local exact
one-stage Nash condition, its values follow the exact Bellman update, and every
continuation remains above the coordinatewise behavioral punishment vector.

The raw compactness statement

`every orbit has finite total charge -> all orbit charges have one common bound`

is false for abstract compact serial charged relations.  It is also unnecessary
for the strategic conclusion.  The finite charged-closing compiler already
accepts a different finite packet for each requested charge target.  Therefore,
if no common all-orbit prefix bound exists, exact orbit prefixes supply the
producer required by `quittingGame_exists_uniformEquilibriumPayoff_of_finiteForwardPackets`.

The resulting theorem is the game-intrinsic disjunction:

* the quitting game has a uniform-equilibrium payoff; or
* one finite constant bounds every cumulative-charge prefix of every legal
  punishment-floor exact forward orbit.

No single orbit with divergent charge is selected or asserted.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- An arbitrary punishment-floor exact Nash--Bellman forward orbit inside one
fixed carrier.  This structure is independent of any selected predecessor
function. -/
structure QuittingPunishmentFloorForwardOrbit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : Set (Payoff ι)) where
  roots : ℕ → ι → PMF Bool
  value : ℕ → Payoff ι
  anchor : value 0 = fun who => quittingPunishmentValue reward who
  value_mem : ∀ time, value time ∈ carrier
  policy : ∀ time,
    value (time + 1) = quittingRootSuccessorPayoff reward
      (value time) (roots time)
  support : ∀ time,
    IsQuittingRootSupportApproxNash reward (value time) 0 (roots time)
  rational : ∀ target time,
    quittingPunishmentValue reward target ≤ value time target

namespace QuittingPunishmentFloorForwardOrbit

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {carrier : Set (Payoff ι)}

/-- Cumulative absorption charge through the first `horizon` stages. -/
def prefixCharge
    (orbit : QuittingPunishmentFloorForwardOrbit reward carrier)
    (horizon : ℕ) : ℝ :=
  ∑ time ∈ Finset.range horizon,
    quittingRootAbsorptionMass (orbit.roots time)

/-- Increasing the tolerance preserves the support-local approximate Nash
condition. -/
theorem supportApproxNash_mono
    (tail : Payoff ι) (root : ι → PMF Bool) {first second : ℝ}
    (herror : first ≤ second)
    (hsupport : IsQuittingRootSupportApproxNash reward tail first root) :
    IsQuittingRootSupportApproxNash reward tail second root := by
  intro who
  constructor
  · intro hquit
    have hgap := (hsupport who).1 hquit
    linarith
  · intro hcontinue
    have hgap := (hsupport who).2 hcontinue
    linarith

/-- Any finite prefix of an exact punishment-floor orbit is a finite forward
packet at every weaker support tolerance and every charge target below its
actual accumulated charge. -/
def toFiniteForwardPacket
    (orbit : QuittingPunishmentFloorForwardOrbit reward carrier)
    (horizon : ℕ) {supportError chargeTarget : ℝ}
    (hsupportError : 0 ≤ supportError)
    (hcharge : chargeTarget ≤ orbit.prefixCharge horizon) :
    QuittingFiniteForwardPacket reward carrier supportError chargeTarget where
  roots := orbit.roots
  value := orbit.value
  horizon := horizon
  value_mem := fun time _ => orbit.value_mem time
  policy := fun time _ => orbit.policy time
  support := fun time _ =>
    supportApproxNash_mono (reward := reward)
      (orbit.value time) (orbit.roots time) hsupportError (orbit.support time)
  rational := by
    intro target time _
    have hir := orbit.rational target time
    linarith
  chargeTarget_le := hcharge

end QuittingPunishmentFloorForwardOrbit

/-- One real constant bounds every cumulative-charge prefix of every legal
punishment-floor exact forward orbit. -/
def HasUniformPunishmentFloorOrbitChargeBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : Set (Payoff ι)) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ orbit : QuittingPunishmentFloorForwardOrbit reward carrier,
      ∀ horizon,
        orbit.prefixCharge horizon ≤ C

/-- **All-orbit punishment-floor charge alternative.**

Failure of one common prefix bound gives, for every requested nonnegative
charge target, a finite exact orbit prefix above that target.  Exact support
optimality and exact punishment rationality weaken to the positive tolerance
requested by the finite-forward compiler, so those target-dependent prefixes
produce a uniform-equilibrium payoff. -/
theorem
    quittingGame_uniformPayoff_or_hasUniformPunishmentFloorOrbitChargeBound
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : Set (Payoff ι)) (hcarrier : IsCompact carrier) :
    (∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
      HasUniformPunishmentFloorOrbitChargeBound reward carrier := by
  classical
  by_cases hbound :
      HasUniformPunishmentFloorOrbitChargeBound reward carrier
  · exact Or.inr hbound
  · apply Or.inl
    apply quittingGame_exists_uniformEquilibriumPayoff_of_finiteForwardPackets
      reward carrier hcarrier
    intro supportError hsupportError chargeTarget hchargeTarget
    have hlarge :
        ∃ orbit : QuittingPunishmentFloorForwardOrbit reward carrier,
          ∃ horizon,
            chargeTarget < orbit.prefixCharge horizon := by
      by_contra hnone
      apply hbound
      refine ⟨chargeTarget, hchargeTarget, ?_⟩
      intro orbit horizon
      exact le_of_not_gt fun hgt => hnone ⟨orbit, horizon, hgt⟩
    obtain ⟨orbit, horizon, hlarge⟩ := hlarge
    exact ⟨orbit.toFiniteForwardPacket horizon
      hsupportError.le hlarge.le⟩

/-- Contrapositive form: a game with no uniform-equilibrium payoff has one
common bound for all exact punishment-floor orbit prefixes. -/
theorem
    hasUniformPunishmentFloorOrbitChargeBound_of_not_uniformPayoff
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : Set (Payoff ι)) (hcarrier : IsCompact carrier)
    (hnoPayoff : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    HasUniformPunishmentFloorOrbitChargeBound reward carrier :=
  (quittingGame_uniformPayoff_or_hasUniformPunishmentFloorOrbitChargeBound
    reward carrier hcarrier).resolve_left hnoPayoff

end GameTheory
