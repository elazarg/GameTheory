/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentTwoOwnerPacketDichotomy
import UniformEquilibrium.Quitting.Paths.SupportWitnessPathCompiler

/-!
# Approximate punishment attachment at a tight two-owner boundary

An active positive-tangent owner at
`boundary = quittingPunishmentValue` blocks the exact two-owner ray because
its continuation lies below the exact punishment floor. Uniform equilibrium,
however, is approximate. The deficit is

`t * tangent first / (1 - t * mass second)`,

which tends to zero with the hazard scale. Consequently every prescribed
positive rationality error absorbs the deficit at all sufficiently small
positive scales. The stationary min--max approximation theorem then supplies
a player-specific target-closed punishment tail whose terminal value is within
the rationality error and an arbitrary positive tail slack of the exact-ray
continuation.

This is the honest approximate consumer of the tight floor. It remains
scale- and tolerance-dependent:

* the punishment row/tail may vary with the scale and requested accuracy;
* the construction is target-specific, not one common suffix for all players;
* no full behavior profile, return edge, lasso, or solved cycle is produced.

The first theorem isolates the obstruction to stronger uniformity. A single
stationary row satisfying the punishment cap at every positive accuracy would
actually attain the punishment infimum, and general quitting min--max theory
does not provide such attainment.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A single stationary row which works at every positive accuracy would
actually attain the punishment infimum. This is exactly what the general
min--max API does not provide. -/
theorem quittingStationaryPunishment_attained_of_uniform_add_error
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    (root : ι → PMF Bool)
    (huniform : ∀ ε : ℝ, 0 < ε →
      quittingStationaryUnilateralCap reward root who ≤
        quittingPunishmentValue reward who + ε) :
    quittingStationaryUnilateralCap reward root who =
      quittingPunishmentValue reward who := by
  apply le_antisymm
  · by_contra hnot
    push Not at hnot
    let ε := (quittingStationaryUnilateralCap reward root who -
      quittingPunishmentValue reward who) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    have hcap := huniform ε hε
    dsimp [ε] at hcap
    linarith
  · exact quittingPunishmentValue_le_stationaryUnilateralCap reward who root

namespace QuittingChargeTangentPacket

/-- The tight active punishment-floor deficit tends to zero with the packet
scale. -/
theorem eventually_twoOwnerPunishmentDeficit_lt
    (packet : QuittingChargeTangentPacket reward)
    (first second : ι) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      t * packet.tangent first / (1 - t * packet.mass second) < ε := by
  have hcontinuous : ContinuousAt (fun t : ℝ =>
      t * packet.tangent first / (1 - t * packet.mass second)) 0 := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · norm_num
  have hzero : (0 : ℝ) * packet.tangent first /
      (1 - (0 : ℝ) * packet.mass second) < ε := by simpa using hε
  exact hcontinuous.eventually_lt continuousAt_const hzero

/-- At a tight active punishment boundary, a sufficiently small exact-ray
continuation is individually rational up to any prescribed positive error. -/
theorem eventually_punishmentValue_sub_lt_twoOwnerContinuationRegression
    (packet : QuittingChargeTangentPacket reward)
    (first second : ι) (hne : first ≠ second)
    (hfirst : 0 < packet.mass first) (hsecond : 0 < packet.mass second)
    (houtside : ∀ owner, owner ≠ first → owner ≠ second →
      packet.mass owner = 0)
    (hcompatFirst : quittingActivePairCompatibilityResidual packet first = 0)
    (hcompatSecond : quittingActivePairCompatibilityResidual packet second = 0)
    (htight : packet.boundary first = quittingPunishmentValue reward first)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      quittingPunishmentValue reward first - ε <
        packet.twoOwnerContinuationRegression first second t first := by
  have hdeficit := packet.eventually_twoOwnerPunishmentDeficit_lt
    first second hε
  have htlt : ∀ᶠ t in 𝓝 (0 : ℝ), t < 1 :=
    continuousAt_id.eventually_lt continuousAt_const zero_lt_one
  filter_upwards [hdeficit.filter_mono nhdsWithin_le_nhds,
    htlt.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with t hdeficitAt htlt htpos
  have ht0 : 0 < t := htpos
  have hfirstLt : t * packet.mass first < 1 := by
    nlinarith [packet.mass_nonneg first, packet.twoOwner_mass_le_one first]
  have hsecondLt : t * packet.mass second < 1 := by
    nlinarith [packet.mass_nonneg second, packet.twoOwner_mass_le_one second]
  have hsurvival : quittingStationaryContinueMass
      (packet.twoOwnerRootAt first second t ht0.le htlt.le) ≠ 0 := by
    unfold twoOwnerRootAt
    rw [quittingStationaryContinueMass_rootOfHazard,
      twoOwnerHazardAt,
      continueMass_twoOwner first second
        (t * packet.mass first) (t * packet.mass second) hne]
    exact mul_ne_zero (by linarith) (by linarith)
  have hactive := packet.twoOwnerBellmanContinuationAt_active_formula
    first second t ht0.le htlt.le hne hfirst hsecond houtside
    hcompatFirst hcompatSecond hfirstLt hsecondLt hsurvival
  rw [← packet.twoOwnerBellmanContinuation_eq_continuationRegression
    first second t ht0.le htlt.le first, hactive.1, htight]
  linarith

/-- **Approximate tight-floor suffix.** For every rationality tolerance and
every positive tail slack, all sufficiently small positive points of the
exact two-owner ray possess a player-specific target-closed punishment tail.
The tail may depend on the scale and tolerance; no common multi-player suffix
or return edge is asserted. -/
theorem eventually_exists_targetClosedTail_of_tightPunishment
    (packet : QuittingChargeTangentPacket reward)
    (first second : ι) (hne : first ≠ second)
    (hfirst : 0 < packet.mass first) (hsecond : 0 < packet.mass second)
    (houtside : ∀ owner, owner ≠ first → owner ≠ second →
      packet.mass owner = 0)
    (hcompatFirst : quittingActivePairCompatibilityResidual packet first = 0)
    (hcompatSecond : quittingActivePairCompatibilityResidual packet second = 0)
    (htight : packet.boundary first = quittingPunishmentValue reward first)
    {rationalityError tailSlack : ℝ}
    (hrationalityError : 0 < rationalityError)
    (htailSlack : 0 < tailSlack) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ∃ tail : ℕ → ι → PMF Bool,
        IsQuittingTargetClosedAt reward tail first 0 ∧
        quittingRootSequenceTerminalValue reward tail first 0 ≤
          packet.twoOwnerContinuationRegression first second t first +
            rationalityError + tailSlack := by
  have hir :=
    packet.eventually_punishmentValue_sub_lt_twoOwnerContinuationRegression
      first second hne hfirst hsecond houtside hcompatFirst hcompatSecond
      htight hrationalityError
  filter_upwards [hir] with t hirAt
  exact exists_quittingTargetClosedTail_le_of_punishmentValue_sub_le
    reward first (packet.twoOwnerContinuationRegression first second t first)
    rationalityError htailSlack hirAt.le

end QuittingChargeTangentPacket

end GameTheory
