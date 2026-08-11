/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticTwoReservoirConsumer
import UniformEquilibrium.Quitting.Punishment.SoloCycleCompletion

/-!
# The exact obstruction carried by the harmonic terminal reservoir

The harmonic side of the positive-part split does not close the proof by a
solo cycle.  It certifies the opposite phenomenon.  At a minimum debt gate
the selected singleton payoff is quantitatively negative, while the
counterexample restriction puts the punishment value strictly above that
payoff.

The resulting sure-solo row is locally perfect: it is an absorbing exact
endpoint-Nash successor row whenever no outsider gains by joining.  Globally,
however, the owner is the unique noncontracting coordinate, its full
stationary cap is exactly zero, and the strict punishment moat violates the
only remaining punishment-admissibility inequality.  Thus neither the
period-one completed-cycle compiler nor an arbitrary instant-punishment tail
can consume this reservoir.

The final theorem retains the joint terminal law supplied by the
two-reservoir theorem.  It separates this exact harmonic obstruction from the
finite opponent-incidence dispatch without identifying `Never` mass with a
finite terminal row or a chronological recurrence.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A strict punishment moat rules out the constant sure-solo row as a
punishment-admissible period-one cycle.  The owner is the noncontracting
coordinate, so admissibility there is exactly the reversed moat inequality. -/
theorem not_isQuittingCyclePunishmentAdmissible_instant_of_punishmentMoat
    (owner : ι)
    (hmoat : quittingSoloReward reward owner owner <
      quittingPunishmentValue reward owner) :
    ¬ IsQuittingCyclePunishmentAdmissible reward
        (fun _ : Fin 1 => quittingInstantRoot owner) := by
  intro hadmissible
  rcases hadmissible owner with hcontracts | hpunishment
  · have hmass :
        (∏ phase : Fin 1,
            quittingStationaryFixedOpponentsContinueMass
              ((fun _ : Fin 1 => quittingInstantRoot owner) phase) owner) =
          1 := by
      rw [Fin.prod_univ_one]
      simp [quittingInstantRoot]
    rw [hmass] at hcontracts
    exact (lt_irrefl 1) hcontracts
  · have hpunishment' : quittingPunishmentValue reward owner ≤
        quittingSoloReward reward owner owner := by
      simpa [quittingSoloReward, quittingSingletonTerminal] using hpunishment
    exact (not_le_of_gt hmoat) hpunishment'

/-- Proof-carrying description of the harmonic branch at a positive minimum
debt gate.  It records both its quantitative terminal-law resource and its
exact game-facing obstruction. -/
structure QuittingHarmonicReservoirObstruction
    (source : QuittingTerminalSemanticPair ι) (owner : ι)
    (mass : QuittingTerminalOutcome ι → ℝ) (M theta : ℝ) : Prop where
  negative_source : source.1 owner ≤
    -theta * quittingTerminalSemanticDebtSum source
  never_mass : theta * quittingTerminalSemanticDebtSum source / M ≤ mass none
  no_join : IsQuittingInstantNoJoin reward owner
  punishment_moat : quittingSoloReward reward owner owner <
    quittingPunishmentValue reward owner
  local_certificate : IsεQuittingRootSuccessorCertificate reward 0
    (quittingInstantRoot owner) (quittingSoloReward reward owner)
      (quittingSoloReward reward owner)
  full_absorption : quittingRootAbsorptionMass (quittingInstantRoot owner) = 1
  owner_cap_eq_zero : quittingStationaryUnilateralCap reward
    (quittingInstantRoot owner) owner = 0
  debt_share_le_owner_full_regret :
    theta * quittingTerminalSemanticDebtSum source ≤
      quittingStationaryUnilateralCap reward (quittingInstantRoot owner) owner -
        quittingSoloReward reward owner owner
  punishment_nonpos : quittingPunishmentValue reward owner ≤ 0
  no_instant_completion : ¬ QuittingInstantPunishmentWorks reward owner
  no_periodOne_cycle_completion :
    ¬ IsQuittingCyclePunishmentAdmissible reward
        (fun _ : Fin 1 => quittingInstantRoot owner)

/-- The quantitative negative-`Never` alternative compiles to an exact
obstruction, not to a solo equilibrium.  In particular the locally exact,
fully absorbing sure-solo row has owner cap zero and at least the selected
debt share of full behavioral regret. -/
theorem quittingHarmonicReservoirObstruction_of_negativeNever
    (source : QuittingTerminalSemanticPair ι) (owner : ι)
    (mass : QuittingTerminalOutcome ι → ℝ) {M theta : ℝ}
    (hpositive : 0 < quittingTerminalSemanticDebtSum source)
    (hownerPin : source.1 owner = quittingSoloReward reward owner owner)
    (hnoJoin : IsQuittingInstantNoJoin reward owner)
    (hmoat : quittingSoloReward reward owner owner <
      quittingPunishmentValue reward owner)
    (htheta : 0 < theta)
    (hnegative : source.1 owner ≤
      -theta * quittingTerminalSemanticDebtSum source)
    (hnever : theta * quittingTerminalSemanticDebtSum source / M ≤ mass none) :
    QuittingHarmonicReservoirObstruction (reward := reward)
      source owner mass M theta := by
  have hshare : 0 < theta * quittingTerminalSemanticDebtSum source :=
    mul_pos htheta hpositive
  have hsoloNegative : quittingSoloReward reward owner owner < 0 := by
    rw [← hownerPin]
    linarith
  have hcap : quittingStationaryUnilateralCap reward
      (quittingInstantRoot owner) owner = 0 := by
    unfold quittingInstantRoot
    rw [quittingStationaryUnilateralCap_solo_owner]
    exact max_eq_right hsoloNegative.le
  have hinactive : ∀ other, other ≠ owner →
      ((PMF.pure true : PMF Bool) false).toReal *
          quittingSoloReward reward other other +
        ((PMF.pure true : PMF Bool) true).toReal *
          quittingSingletonCollisionReward reward owner other ≤
        quittingSoloReward reward owner other := by
    intro other hother
    simpa using hnoJoin other hother
  have hrow := soloStationaryRoot_isAbsorbingEquilibriumRow reward owner
    (PMF.pure true) (by simp) hinactive
  have hlocal : IsεQuittingRootSuccessorCertificate reward 0
      (quittingInstantRoot owner) (quittingSoloReward reward owner)
        (quittingSoloReward reward owner) := by
    simpa [quittingInstantRoot] using hrow.1
  have habsorption :
      quittingRootAbsorptionMass (quittingInstantRoot owner) = 1 := by
    simp [quittingInstantRoot]
  have hregret : theta * quittingTerminalSemanticDebtSum source ≤
      quittingStationaryUnilateralCap reward (quittingInstantRoot owner) owner -
        quittingSoloReward reward owner owner := by
    rw [hcap, ← hownerPin]
    linarith
  have hfloor : quittingPunishmentValue reward owner ≤ 0 := by
    have hfloorCap := quittingPunishmentValue_le_stationaryUnilateralCap
      reward owner (quittingInstantRoot owner)
    rwa [hcap] at hfloorCap
  have hnoWorks : ¬ QuittingInstantPunishmentWorks reward owner := by
    intro hworks
    have hIR := isQuittingInstantPunishmentIR_of_works reward owner hworks
    exact (not_le_of_gt hmoat) hIR
  exact
    { negative_source := hnegative
      never_mass := hnever
      no_join := hnoJoin
      punishment_moat := hmoat
      local_certificate := hlocal
      full_absorption := habsorption
      owner_cap_eq_zero := hcap
      debt_share_le_owner_full_regret := hregret
      punishment_nonpos := hfloor
      no_instant_completion := hnoWorks
      no_periodOne_cycle_completion :=
        not_isQuittingCyclePunishmentAdmissible_instant_of_punishmentMoat
          owner hmoat }

/-- **Game-facing two-reservoir alternative with the harmonic branch fully
decoded.**  Either there is a strict singleton joiner, or no outsider
gains at the singleton and the same joint reset law carries one of two
resources:

* an exact harmonic obstruction to both solo completion mechanisms; or
* the existing positive-incidence fixed-law reset dispatch.

The harmonic conclusion is intentionally a no-go certificate.  Its strict
punishment moat is the reverse of the hypothesis needed by the completed
solo-cycle theorem. -/
theorem QuittingCounterexampleRegime.exists_joiner_or_harmonicObstruction_or_resetDispatch
    (regime : QuittingCounterexampleRegime reward)
    (source : QuittingTerminalSemanticPair ι) (owner : ι) {M theta : ℝ}
    (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum source)
    (hnash : IsεQuittingRootNash reward source.1 0
      (quittingAllContinueRoot : ι → PMF Bool))
    (hgate : IsMinimumTerminalSemanticDebtGate reward source owner)
    (htheta : 0 < theta) (hthetaOne : theta < 1) :
    (∃ other, other ≠ owner ∧
        quittingSoloReward reward owner other <
          quittingSingletonCollisionReward reward owner other) ∨
      ∃ (mass : QuittingTerminalOutcome ι → ℝ)
          (cluster : QuittingTerminalSemanticPair ι),
        (cluster, mass) ∈ quittingTerminalSemanticLawCarrier reward ∧
        quittingTerminalSemanticDebt cluster owner = 0 ∧
        (QuittingHarmonicReservoirObstruction (reward := reward)
            source owner mass M theta ∨
          ((1 - theta) * quittingTerminalSemanticDebtSum source /
                (2 * M) ≤
              quittingTerminalOpponentContainingMass owner mass ∧
            ∃ other returned,
              other ≠ owner ∧
              0 < quittingTerminalOpponentIncidenceMass owner other mass ∧
              QuittingFixedLawResetDispatch (reward := reward)
                source cluster mass owner other returned)) := by
  by_cases hnoJoin : IsQuittingInstantNoJoin reward owner
  · rcases regime.exists_twoReservoir_sameLaw_resetDispatch source owner hM
        hreward hsource hminimum hpositive hnash hgate htheta hthetaOne with
      hjoin | hreservoir
    · obtain ⟨other, hother, hstrict⟩ := hjoin
      exact False.elim (not_lt_of_ge (hnoJoin other hother) hstrict)
    · right
      obtain ⟨hmoat, mass, cluster, hjoint, hreset, hharmonic | hfinite⟩ :=
        hreservoir
      · refine ⟨mass, cluster, hjoint, hreset, Or.inl ?_⟩
        have hownerPin :=
          (minimumTerminalSemantic_debtGate_ownerPin_and_debt_pos
            (reward := reward) source owner hM.le hreward hsource hminimum
              hpositive hgate).1
        exact quittingHarmonicReservoirObstruction_of_negativeNever
          source owner mass hpositive hownerPin hnoJoin hmoat htheta
            hharmonic.1 hharmonic.2
      · exact ⟨mass, cluster, hjoint, hreset, Or.inr hfinite⟩
  · left
    unfold IsQuittingInstantNoJoin at hnoJoin
    push Not at hnoJoin
    exact hnoJoin

end GameTheory
