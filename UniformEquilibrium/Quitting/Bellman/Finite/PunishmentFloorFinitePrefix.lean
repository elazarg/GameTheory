/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/

import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorForward

/-!
# Arbitrary finite punishment-floor forward prefixes

The selected predecessor orbit is only one source of finite forward packets.
This module isolates the exact finite-prefix interface itself.  A certificate
retains its common root/value chronology, exact Bellman transport, exact root
Nash edges, canonical reward-box membership, and one anchor floor.  The floor
at later dates is derived from that anchor and the exact edges; it is not a
second redundant field.

The adapter changes only the local support tolerance and charge target.  Thus
an unbounded family of exact certificates supplies the packet producer at
every positive tolerance.  The final dichotomy is consequently unconditional
for this certificate family: either the game has a uniform-equilibrium payoff,
or all such finite prefixes have one common finite nonnegative charge bound.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- An arbitrary finite exact forward prefix anchored above the coordinatewise
behavioral punishment floor.  The stored `value_mem` field is the canonical
compact-box witness; all rationality floors at later dates are derived from
`anchor_floor`, `policy`, and `exactNash`. -/
structure QuittingPunishmentFloorFinitePrefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  roots : ℕ → ι → PMF Bool
  value : ℕ → Payoff ι
  horizon : ℕ
  value_mem : ∀ time, time ≤ horizon →
    value time ∈ quittingPunishmentFloorForwardCarrier reward
  anchor_floor : ∀ who,
    quittingPunishmentValue reward who ≤ value 0 who
  policy : ∀ time, time < horizon →
    value (time + 1) = quittingRootSuccessorPayoff reward
      (value time) (roots time)
  exactNash : ∀ time, time < horizon →
    IsεQuittingRootNash reward (value time) 0 (roots time)

/-- The cumulative absorption charge of a finite prefix. -/
def QuittingPunishmentFloorFinitePrefix.charge
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (cert : QuittingPunishmentFloorFinitePrefix reward) : ℝ :=
  ∑ time ∈ Finset.range cert.horizon,
    quittingRootAbsorptionMass (cert.roots time)

theorem QuittingPunishmentFloorFinitePrefix.charge_nonneg
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (cert : QuittingPunishmentFloorFinitePrefix reward) :
    0 ≤ cert.charge := by
  unfold QuittingPunishmentFloorFinitePrefix.charge
  apply Finset.sum_nonneg
  intro time htime
  unfold quittingRootAbsorptionMass
  linarith [quittingStationaryContinueMass_le_one (cert.roots time)]

/-- The anchor floor propagates through every exact forward edge. -/
theorem quittingPunishmentValue_le_finitePrefixValue
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (cert : QuittingPunishmentFloorFinitePrefix reward)
    (time : ℕ) (htime : time ≤ cert.horizon) (who : ι) :
    quittingPunishmentValue reward who ≤ cert.value time who := by
  induction time with
  | zero => exact cert.anchor_floor who
  | succ time ih =>
      have htime_lt : time < cert.horizon := by omega
      rw [cert.policy time htime_lt]
      exact quittingPunishmentValue_le_rootSuccessorPayoff_of_tail_ge
        reward (cert.value time) (cert.roots time) who
        (ih htime_lt.le) (cert.exactNash time htime_lt)

/-- The first `horizon` steps of the canonical selected punishment-floor
predecessor orbit, viewed through the arbitrary-prefix interface.  This is a
consolidation adapter: it carries no new selection claim, but lets the orbit
use the generic packet and dichotomy theorems below. -/
def quittingPunishmentFloorForwardFinitePrefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (horizon : ℕ) : QuittingPunishmentFloorFinitePrefix reward where
  roots := quittingPunishmentFloorForwardRoot reward
  value := quittingPunishmentFloorForwardValue reward
  horizon := horizon
  value_mem := fun time _ => quittingPunishmentFloorForwardValue_mem reward time
  anchor_floor := fun who =>
    quittingPunishmentFloor_le_forwardValue reward 0 who
  policy := fun time _ => quittingPunishmentFloorForward_policy reward time
  exactNash := fun time _ => quittingPunishmentFloorForward_isZeroNash reward time

@[simp] theorem quittingPunishmentFloorForwardFinitePrefix_charge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (horizon : ℕ) :
    (quittingPunishmentFloorForwardFinitePrefix reward horizon).charge =
      ∑ time ∈ Finset.range horizon,
        quittingRootAbsorptionMass
          (quittingPunishmentFloorForwardRoot reward time) := rfl

/-- Convert an exact prefix into the packet consumed by the projective
compiler.  Exact Nash supplies the support inequalities, while the derived
floor supplies packet rationality. -/
def QuittingPunishmentFloorFinitePrefix.toForwardPacket
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (cert : QuittingPunishmentFloorFinitePrefix reward)
    (supportError : ℝ) (hsupportError : 0 ≤ supportError)
    (chargeTarget : ℝ) (hchargeTarget : chargeTarget ≤ cert.charge) :
    QuittingFiniteForwardPacket reward
      (quittingPunishmentFloorForwardCarrier reward)
      supportError chargeTarget where
  roots := cert.roots
  value := cert.value
  horizon := cert.horizon
  value_mem := cert.value_mem
  policy := cert.policy
  support := by
    intro time htime who
    have hexact := isQuittingRootSupportApproxNash_zero_of_isZeroNash
      reward (cert.value time) (cert.roots time)
      (cert.exactNash time htime)
    have hsupport := hexact who
    constructor
    · intro hquit
      have h := hsupport.1 hquit
      linarith
    · intro hcontinue
      have h := hsupport.2 hcontinue
      linarith
  rational := by
    intro target time htime
    have hfloor := quittingPunishmentValue_le_finitePrefixValue
      cert time htime target
    linarith
  chargeTarget_le := by
    simpa [QuittingPunishmentFloorFinitePrefix.charge] using hchargeTarget

/-- Arbitrarily charged exact punishment-floor prefixes produce a uniform
equilibrium payoff.  One exact prefix can be re-used at every positive local
support tolerance because exact Nash is stronger than the packet support
condition. -/
theorem quittingGame_exists_uniformPayoff_of_arbitrarilyCharged_floorPrefixes
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hproducer : ∀ chargeTarget : ℝ, 0 ≤ chargeTarget →
      Nonempty {cert : QuittingPunishmentFloorFinitePrefix reward //
        chargeTarget ≤ cert.charge}) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_finiteForwardPackets
    reward (quittingPunishmentFloorForwardCarrier reward)
      (quittingPunishmentFloorForwardCarrier_isCompact reward)
  intro supportError hsupportError chargeTarget hchargeTarget
  obtain ⟨cert, hcert⟩ := hproducer chargeTarget hchargeTarget
  exact ⟨cert.toForwardPacket supportError hsupportError.le
    chargeTarget hcert⟩

/-- If the exact-prefix family is not charge-bounded, it supplies the
arbitrarily charged producer and hence a uniform payoff. -/
theorem quittingGame_exists_uniformPayoff_of_unbounded_floorPrefixCharge
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hunbounded : ∀ chargeTarget : ℝ, 0 ≤ chargeTarget →
      ∃ cert : QuittingPunishmentFloorFinitePrefix reward,
        chargeTarget ≤ cert.charge) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformPayoff_of_arbitrarilyCharged_floorPrefixes
    reward
  intro chargeTarget hchargeTarget
  obtain ⟨cert, hcert⟩ := hunbounded chargeTarget hchargeTarget
  exact ⟨cert, hcert⟩

/-- Unconditional charge dichotomy for arbitrary exact punishment-floor
prefixes: either the quitting game has a uniform-equilibrium payoff, or all
finite prefixes in this exact family share one common nonnegative charge bound.
The bound is deliberately over the certificate family, not over arbitrary
Nash--Bellman selections lacking the retained anchor/floor semantics. -/
theorem quittingGame_uniformPayoff_or_bounded_floorPrefixCharge
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
      ∃ chargeBound : ℝ, 0 ≤ chargeBound ∧
        ∀ cert : QuittingPunishmentFloorFinitePrefix reward,
          cert.charge ≤ chargeBound := by
  classical
  by_cases hbound : ∃ chargeBound : ℝ, 0 ≤ chargeBound ∧
      ∀ cert : QuittingPunishmentFloorFinitePrefix reward,
        cert.charge ≤ chargeBound
  · exact Or.inr hbound
  · left
    apply quittingGame_exists_uniformPayoff_of_unbounded_floorPrefixCharge
      reward
    intro chargeTarget hchargeTarget
    by_contra hno
    push Not at hno
    apply hbound
    refine ⟨chargeTarget, hchargeTarget, ?_⟩
    intro cert
    exact (hno cert).le

end GameTheory
