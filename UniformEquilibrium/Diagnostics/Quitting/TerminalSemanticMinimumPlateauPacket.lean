/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAuxiliaryNashBudget
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentPacket

/-!
# Charge packets at a minimum terminal-semantic boundary

The auxiliary-target budget gives a quantitative singleton margin at every
positive minimum terminal-semantic pair.  Consequently a coordinate pinned
to its singleton reward carries the entire total semantic debt.  Two distinct
coordinates cannot both be pinned.

A charge-tangent packet whose boundary is the prescribed coordinate of such a
pair is therefore necessarily singleton-supported.  In a counterexample its
active tangent is zero, so the packet sign alternative forces a strictly
underfunded outsider.  These are exact consumers of a boundary-matched packet;
they do not produce that packet from a realizing profile or a literal prefix
stack.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## Tight coordinates at the minimum -/

/-- A singleton-tight coordinate of a positive minimum semantic pair carries
all of the pair's total debt. -/
theorem minimumTerminalSemantic_debt_eq_sum_of_singleton_tight
    (pair : QuittingTerminalSemanticPair ι) (who : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (htight : pair.1 who =
      reward (quittingSingletonTerminal who) who) :
    quittingTerminalSemanticDebt pair who =
      quittingTerminalSemanticDebtSum pair := by
  have hdebtNonneg : ∀ player,
      0 ≤ quittingTerminalSemanticDebt pair player :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward hpair
  have hcoordinateLe : quittingTerminalSemanticDebt pair who ≤
      quittingTerminalSemanticDebtSum pair := by
    unfold quittingTerminalSemanticDebtSum
    exact Finset.single_le_sum
      (fun player _ => hdebtNonneg player) (Finset.mem_univ who)
  have hmargin := minimumTerminalSemantic_singletonMargin
    (reward := reward) pair hM hreward hpair hminimum hpositive who
  have hsumLeCoordinate : quittingTerminalSemanticDebtSum pair ≤
      quittingTerminalSemanticDebt pair who := by
    unfold quittingTerminalSemanticDebt
    rw [htight]
    exact hmargin
  exact le_antisymm hcoordinateLe hsumLeCoordinate

/-- A positive minimum semantic pair has at most one singleton-tight
coordinate. -/
theorem minimumTerminalSemantic_not_two_singleton_tight
    (pair : QuittingTerminalSemanticPair ι) (first second : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hne : first ≠ second)
    (hfirst : pair.1 first =
      reward (quittingSingletonTerminal first) first)
    (hsecond : pair.1 second =
      reward (quittingSingletonTerminal second) second) : False := by
  have hdebtNonneg : ∀ player,
      0 ≤ quittingTerminalSemanticDebt pair player :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward hpair
  have hfirstDebt :=
    minimumTerminalSemantic_debt_eq_sum_of_singleton_tight
      (reward := reward) pair first hM hreward hpair hminimum hpositive hfirst
  have hsecondDebt :=
    minimumTerminalSemantic_debt_eq_sum_of_singleton_tight
      (reward := reward) pair second hM hreward hpair hminimum hpositive hsecond
  have hpairLe : quittingTerminalSemanticDebt pair first +
      quittingTerminalSemanticDebt pair second ≤
        quittingTerminalSemanticDebtSum pair := by
    calc
      quittingTerminalSemanticDebt pair first +
          quittingTerminalSemanticDebt pair second =
        ∑ player ∈ ({first, second} : Finset ι),
          quittingTerminalSemanticDebt pair player := by
            simp [hne]
      _ ≤ ∑ player ∈ (Finset.univ : Finset ι),
          quittingTerminalSemanticDebt pair player := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · exact Finset.subset_univ _
            · intro player _ _
              exact hdebtNonneg player
      _ = quittingTerminalSemanticDebtSum pair := rfl
  rw [hfirstDebt, hsecondDebt] at hpairLe
  linarith

/-! ## Boundary-matched charge packets -/

namespace QuittingChargeTangentPacket

/-- Two distinct owners cannot both have positive mass in a charge packet
whose boundary is a positive minimum prescribed payoff. -/
theorem not_two_positiveMass_of_boundary_eq_minimumTerminalSemantic
    (packet : QuittingChargeTangentPacket reward)
    (pair : QuittingTerminalSemanticPair ι) (first second : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hboundary : packet.boundary = pair.1)
    (hne : first ≠ second)
    (hfirst : 0 < packet.mass first)
    (hsecond : 0 < packet.mass second) : False := by
  have hfirstTight : pair.1 first =
      reward (quittingSingletonTerminal first) first := by
    calc
      pair.1 first = packet.boundary first :=
        congrFun hboundary.symm first
      _ = reward (quittingSingletonTerminal first) first :=
        packet.positive_mass_pins_boundary first hfirst
  have hsecondTight : pair.1 second =
      reward (quittingSingletonTerminal second) second := by
    calc
      pair.1 second = packet.boundary second :=
        congrFun hboundary.symm second
      _ = reward (quittingSingletonTerminal second) second :=
        packet.positive_mass_pins_boundary second hsecond
  exact minimumTerminalSemantic_not_two_singleton_tight
    (reward := reward) pair first second hM hreward hpair hminimum hpositive
      hne hfirstTight hsecondTight

/-- Once one owner has positive mass, every other packet mass vanishes at a
positive minimum boundary. -/
theorem mass_eq_zero_of_boundary_eq_minimumTerminalSemantic
    (packet : QuittingChargeTangentPacket reward)
    (pair : QuittingTerminalSemanticPair ι) (owner : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hboundary : packet.boundary = pair.1)
    (howner : 0 < packet.mass owner) :
    ∀ other, other ≠ owner → packet.mass other = 0 := by
  intro other hother
  apply le_antisymm
  · by_contra hnot
    have hotherPositive : 0 < packet.mass other :=
      lt_of_not_ge hnot
    exact packet.not_two_positiveMass_of_boundary_eq_minimumTerminalSemantic
      pair other owner hM hreward hpair hminimum hpositive hboundary hother
        hotherPositive howner
  · exact packet.mass_nonneg other

/-- A positive packet owner has full normalized mass at a positive minimum
boundary. -/
theorem mass_eq_one_of_boundary_eq_minimumTerminalSemantic
    (packet : QuittingChargeTangentPacket reward)
    (pair : QuittingTerminalSemanticPair ι) (owner : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hboundary : packet.boundary = pair.1)
    (howner : 0 < packet.mass owner) : packet.mass owner = 1 := by
  have hzero :=
    packet.mass_eq_zero_of_boundary_eq_minimumTerminalSemantic
      pair owner hM hreward hpair hminimum hpositive hboundary howner
  have hsum : (∑ other, packet.mass other) = packet.mass owner := by
    apply Finset.sum_eq_single owner
    · intro other _ hother
      exact hzero other hother
    · intro hnot
      exact (hnot (Finset.mem_univ owner)).elim
  rw [packet.mass_sum] at hsum
  exact hsum.symm

/-- A boundary-matched packet is a Dirac singleton mixture at any of its
positive owners. -/
theorem singletonMixture_eq_singleton_of_boundary_eq_minimumTerminalSemantic
    (packet : QuittingChargeTangentPacket reward)
    (pair : QuittingTerminalSemanticPair ι) (owner who : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hboundary : packet.boundary = pair.1)
    (howner : 0 < packet.mass owner) :
    quittingSingletonMixture reward packet.mass who =
      reward (quittingSingletonTerminal owner) who := by
  have hownerOne :=
    packet.mass_eq_one_of_boundary_eq_minimumTerminalSemantic
      pair owner hM hreward hpair hminimum hpositive hboundary howner
  have hzero :=
    packet.mass_eq_zero_of_boundary_eq_minimumTerminalSemantic
      pair owner hM hreward hpair hminimum hpositive hboundary howner
  unfold quittingSingletonMixture
  rw [Finset.sum_eq_single owner]
  · rw [hownerOne, one_mul]
  · intro other _ hother
    rw [hzero other hother, zero_mul]
  · intro hnot
    exact (hnot (Finset.mem_univ owner)).elim

/-- The tangent of the unique packet owner is zero. -/
theorem tangent_eq_zero_of_boundary_eq_minimumTerminalSemantic
    (packet : QuittingChargeTangentPacket reward)
    (pair : QuittingTerminalSemanticPair ι) (owner : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hboundary : packet.boundary = pair.1)
    (howner : 0 < packet.mass owner) : packet.tangent owner = 0 := by
  rw [packet.tangent_eq owner,
    packet.singletonMixture_eq_singleton_of_boundary_eq_minimumTerminalSemantic
      pair owner owner hM hreward hpair hminimum hpositive hboundary howner,
    packet.positive_mass_pins_boundary owner howner]
  ring

end QuittingChargeTangentPacket

/-! ## Counterexample sign consequence -/

namespace QuittingCounterexampleRegime

/-- A charge packet at a positive minimum prescribed boundary is a single
owner whose singleton exit strictly underfunds some distinct outsider. -/
theorem chargeTangentPacket_minimumBoundary_underfunds_outsider
    (regime : QuittingCounterexampleRegime reward)
    (packet : QuittingChargeTangentPacket reward)
    (pair : QuittingTerminalSemanticPair ι) (owner : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hboundary : packet.boundary = pair.1)
    (howner : 0 < packet.mass owner) :
    ∃ outsider, outsider ≠ owner ∧
      reward (quittingSingletonTerminal owner) outsider < pair.1 outsider := by
  have hzero :=
    packet.mass_eq_zero_of_boundary_eq_minimumTerminalSemantic
      pair owner hM hreward hpair hminimum hpositive hboundary howner
  have hownerTangent :=
    packet.tangent_eq_zero_of_boundary_eq_minimumTerminalSemantic
      pair owner hM hreward hpair hminimum hpositive hboundary howner
  obtain ⟨who, hwho⟩ | ⟨active, hactiveMass, hactiveTangent⟩ :=
    regime.chargeTangentPacket_underfunded_or_active_funded packet
  · have hwhoNe : who ≠ owner := by
      intro heq
      subst who
      rw [hownerTangent] at hwho
      linarith
    refine ⟨who, hwhoNe, ?_⟩
    rw [packet.tangent_eq who,
      packet.singletonMixture_eq_singleton_of_boundary_eq_minimumTerminalSemantic
        pair owner who hM hreward hpair hminimum hpositive hboundary howner,
      hboundary] at hwho
    exact sub_neg.mp hwho
  · by_cases hactiveOwner : active = owner
    · subst active
      rw [hownerTangent] at hactiveTangent
      linarith
    · rw [hzero active hactiveOwner] at hactiveMass
      linarith

end QuittingCounterexampleRegime

end GameTheory
