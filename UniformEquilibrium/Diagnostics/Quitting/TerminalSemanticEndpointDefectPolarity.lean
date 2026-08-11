/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticNashDefectMobiusIncidence
import UniformEquilibrium.Quitting.Paths.SurvivalWindowLanding

/-!
# Endpoint-defect polarity and exact coalition atomization

The one-coordinate Nash defect has two genuinely different polarities.  A
player who assigns positive probability to Quit when Continue is better
carries a Continue-directed defect.  A player who assigns positive
probability to Continue when Quit is better carries a Quit-directed defect.

The first polarity can be collected by removing Quit probability at every
favourable date.  The second cannot in general be collected by one stopping
rule.  This file records its exact finite replacement: Quit-minus-Continue is
an average, over the opponents' exact coalition atoms, of the corresponding
owner-insertion toggle.  The empty opponent coalition is the solo-versus-tail
gap.  Positive-part subadditivity therefore charges every Quit-directed
defect to finitely many state-matched solo or coalition-toggle atoms.

All row, continuation, action-probability, and coalition-probability factors
remain in the same summand.  No reset iteration, state-matched cycle, quantile
exactification, or support-enlargement conclusion is asserted here.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The two endpoint polarities -/

/-- Defect incurred by playing Quit when Continue is the better endpoint. -/
def quittingRootContinueDirectedDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) : ℝ :=
  (root who true).toReal *
    max (-quittingRootEndpointDifference reward tail root who) 0

/-- Defect incurred by playing Continue when Quit is the better endpoint. -/
def quittingRootQuitDirectedDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) : ℝ :=
  (root who false).toReal *
    max (quittingRootEndpointDifference reward tail root who) 0

theorem quittingRootContinueDirectedDefect_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    0 ≤ quittingRootContinueDirectedDefect reward tail root who :=
  mul_nonneg ENNReal.toReal_nonneg (le_max_right _ 0)

/-- Exact polarity split of a coordinate Nash defect. -/
theorem quittingRootCoordinateNashDefect_eq_polaritySum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootCoordinateNashDefect reward tail root who =
      quittingRootContinueDirectedDefect reward tail root who +
        quittingRootQuitDirectedDefect reward tail root who := by
  rw [quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart]
  simp only [quittingRootContinueDirectedDefect,
    quittingRootQuitDirectedDefect, add_comm]

/-! ## Exact opponent-coalition expansion -/

/-- Probability that the opponents' exact Quit coalition is `coalition`.
This definition is intended for coalitions contained in `univ.erase who`.
The selected player's own action probability is deliberately not included. -/
def quittingOpponentCoalitionMass
    (root : ι → PMF Bool) (who : ι) (coalition : Finset ι) : ℝ :=
  (∏ player ∈ coalition, (root player true).toReal) *
    ∏ player ∈ Finset.univ.erase who \ coalition,
      (root player false).toReal

/-- At one opponent coalition, the selected player's pure-Quit advantage is
the payoff after inserting the player minus the payoff without it.  At the
empty coalition the latter payoff is the literal tail value, so this is the
solo-versus-tail gap. -/
def quittingEndpointInsertionToggle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (who : ι) (coalition : Finset ι) : ℝ :=
  quittingStageCoalitionPayoff reward tail (insert who coalition) who -
    quittingStageCoalitionPayoff reward tail coalition who

theorem quittingOpponentCoalitionMass_nonneg
    (root : ι → PMF Bool) (who : ι) (coalition : Finset ι) :
    0 ≤ quittingOpponentCoalitionMass root who coalition := by
  exact mul_nonneg
    (Finset.prod_nonneg fun _ _ ↦ ENNReal.toReal_nonneg)
    (Finset.prod_nonneg fun _ _ ↦ ENNReal.toReal_nonneg)

/-- Pure Quit is the opponent-coalition average of the payoff after inserting
the selected player. -/
theorem quittingRootQuitPayoff_eq_sum_opponentCoalitionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootQuitPayoff reward tail root who =
      ∑ coalition ∈ (Finset.univ.erase who).powerset,
        quittingOpponentCoalitionMass root who coalition *
          quittingStageCoalitionPayoff reward tail
            (insert who coalition) who := by
  rw [quittingRootQuitPayoff_eq_sigmaValue]
  unfold sigmaValue quittingOpponentCoalitionMass
  apply Finset.sum_congr rfl
  intro coalition hcoalition
  rw [Finset.mem_powerset] at hcoalition
  have hnonempty : (insert who coalition).Nonempty :=
    Finset.insert_nonempty who coalition
  simp only [hazardOfRoot, weightOfReward,
    quittingStageCoalitionPayoff, hnonempty, dif_pos]
  simp_rw [pmfBool_false_toReal]

/-- Pure Continue is the same opponent-coalition average without inserting
the player.  The empty-coalition summand is exactly the literal tail. -/
theorem quittingRootContinuePayoff_eq_sum_opponentCoalitionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootContinuePayoff reward tail root who =
      ∑ coalition ∈ (Finset.univ.erase who).powerset,
        quittingOpponentCoalitionMass root who coalition *
          quittingStageCoalitionPayoff reward tail coalition who := by
  rw [quittingRootContinuePayoff_eq_gammaValue]
  unfold gammaValue excludedValue continueMassExcl
    quittingOpponentCoalitionMass
  let carrier := (Finset.univ.erase who).powerset
  let summand : Finset ι → ℝ := fun coalition ↦
    ((∏ player ∈ coalition, (root player true).toReal) *
      ∏ player ∈ Finset.univ.erase who \ coalition,
        (root player false).toReal) *
      quittingStageCoalitionPayoff reward tail coalition who
  have hempty : (∅ : Finset ι) ∈ carrier := by
    simp [carrier]
  change
    (∑ coalition ∈ carrier.erase ∅,
        ((∏ player ∈ coalition, (root player true).toReal) *
          ∏ player ∈ Finset.univ.erase who \ coalition,
            (1 - (root player true).toReal)) *
          weightOfReward reward coalition who) +
        (∏ player ∈ Finset.univ.erase who,
          (1 - (root player true).toReal)) * tail who =
      ∑ coalition ∈ carrier, summand coalition
  conv_rhs => rw [← Finset.add_sum_erase carrier summand hempty]
  rw [add_comm]
  refine congrArg₂ (· + ·) ?_ ?_
  · simp [summand, quittingStageCoalitionPayoff, pmfBool_false_toReal]
  · apply Finset.sum_congr rfl
    intro coalition hcoalition
    rw [Finset.mem_erase] at hcoalition
    have hnonempty : coalition.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hcoalition.1
    simp only [weightOfReward,
      quittingStageCoalitionPayoff, hnonempty, dif_pos, summand]
    simp_rw [pmfBool_false_toReal]

/-- **Exact endpoint-defect atomization.**  Quit-minus-Continue is the
opponent-coalition average of the state-matched insertion toggle. -/
theorem quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootEndpointDifference reward tail root who =
      ∑ coalition ∈ (Finset.univ.erase who).powerset,
        quittingOpponentCoalitionMass root who coalition *
          quittingEndpointInsertionToggle reward tail who coalition := by
  unfold quittingRootEndpointDifference quittingEndpointInsertionToggle
  rw [quittingRootQuitPayoff_eq_sum_opponentCoalitionMass,
    quittingRootContinuePayoff_eq_sum_opponentCoalitionMass]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro coalition _
  ring

/-- Multiplying the endpoint expansion by the probability that the player
actually played Continue gives the exact signed Quit-directed played-action
gap.  Each summand now contains every action and coalition factor occurring
in the chronological atom. -/
theorem quittingContinueProbability_mul_endpointDifference_eq_sum_atoms
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    (root who false).toReal *
        quittingRootEndpointDifference reward tail root who =
      ∑ coalition ∈ (Finset.univ.erase who).powerset,
        (root who false).toReal *
          quittingOpponentCoalitionMass root who coalition *
            quittingEndpointInsertionToggle reward tail who coalition := by
  rw [quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro coalition _
  ring

omit [Fintype ι] in
/-- The empty label in the atomization is exactly the solo reward minus the
literal continuation value. -/
theorem quittingEndpointInsertionToggle_empty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (who : ι) :
    quittingEndpointInsertionToggle reward tail who ∅ =
      reward (quittingSingletonTerminal who) who - tail who := by
  simp [quittingEndpointInsertionToggle, quittingStageCoalitionPayoff,
    quittingSingletonTerminal]

omit [Fintype ι] in
/-- A nonempty label is exactly the static payoff toggle obtained by adding
the selected player to that coalition. -/
theorem quittingEndpointInsertionToggle_of_nonempty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (who : ι) (coalition : Finset ι)
    (hcoalition : coalition.Nonempty) :
    quittingEndpointInsertionToggle reward tail who coalition =
      reward ⟨insert who coalition, Finset.insert_nonempty who coalition⟩ who -
        reward ⟨coalition, hcoalition⟩ who := by
  simp [quittingEndpointInsertionToggle, quittingStageCoalitionPayoff,
    hcoalition]

/-! ## Positive atom charges -/

/-- The actual played-Continue probability, the exact opponent-coalition
probability, and the positive part of its insertion toggle. -/
def quittingRootQuitDirectedAtom
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (who : ι) (coalition : Finset ι) : ℝ :=
  (root who false).toReal *
    quittingOpponentCoalitionMass root who coalition *
      max (quittingEndpointInsertionToggle reward tail who coalition) 0

theorem quittingRootQuitDirectedAtom_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (who : ι) (coalition : Finset ι) :
    0 ≤ quittingRootQuitDirectedAtom reward tail root who coalition := by
  exact mul_nonneg
    (mul_nonneg ENNReal.toReal_nonneg
      (quittingOpponentCoalitionMass_nonneg root who coalition))
    (le_max_right _ 0)

/-- The Quit-directed defect is bounded by the sum of its finitely many
positive solo/toggle atoms.  The only loss is cancellation between labels. -/
theorem quittingRootQuitDirectedDefect_le_sum_atoms
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootQuitDirectedDefect reward tail root who ≤
      ∑ coalition ∈ (Finset.univ.erase who).powerset,
        quittingRootQuitDirectedAtom reward tail root who coalition := by
  let carrier := (Finset.univ.erase who).powerset
  let raw : Finset ι → ℝ := fun coalition ↦
    quittingOpponentCoalitionMass root who coalition *
      quittingEndpointInsertionToggle reward tail who coalition
  let positive : Finset ι → ℝ := fun coalition ↦
    quittingOpponentCoalitionMass root who coalition *
      max (quittingEndpointInsertionToggle reward tail who coalition) 0
  have hraw : quittingRootEndpointDifference reward tail root who =
      ∑ coalition ∈ carrier, raw coalition := by
    simpa only [carrier, raw] using
      quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle
        reward tail root who
  have hsum : (∑ coalition ∈ carrier, raw coalition) ≤
      ∑ coalition ∈ carrier, positive coalition := by
    apply Finset.sum_le_sum
    intro coalition _
    exact mul_le_mul_of_nonneg_left (le_max_left _ 0)
      (quittingOpponentCoalitionMass_nonneg root who coalition)
  have hpositive : 0 ≤ ∑ coalition ∈ carrier, positive coalition := by
    exact Finset.sum_nonneg fun coalition _ ↦
      mul_nonneg (quittingOpponentCoalitionMass_nonneg root who coalition)
        (le_max_right _ 0)
  have hmax : max (quittingRootEndpointDifference reward tail root who) 0 ≤
      ∑ coalition ∈ carrier, positive coalition := by
    rw [hraw]
    exact max_le hsum hpositive
  unfold quittingRootQuitDirectedDefect quittingRootQuitDirectedAtom
  change (root who false).toReal *
      max (quittingRootEndpointDifference reward tail root who) 0 ≤
    ∑ coalition ∈ carrier,
      (root who false).toReal *
        quittingOpponentCoalitionMass root who coalition *
          max (quittingEndpointInsertionToggle reward tail who coalition) 0
  calc
    (root who false).toReal *
          max (quittingRootEndpointDifference reward tail root who) 0 ≤
        (root who false).toReal *
          (∑ coalition ∈ carrier, positive coalition) :=
      mul_le_mul_of_nonneg_left hmax ENNReal.toReal_nonneg
    _ = ∑ coalition ∈ carrier,
          (root who false).toReal *
            quittingOpponentCoalitionMass root who coalition *
              max (quittingEndpointInsertionToggle reward tail who coalition) 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro coalition _
      simp only [positive]
      ring

/-! ## Fixed-label finite occupation extraction -/

/-- A valid Quit-directed atom label: one player and one exact coalition of
that player's opponents. -/
abbrev QuittingQuitDefectAtomLabel (ι : Type) := ι × Finset ι

/-- Occupation of one displayed player/coalition atom, before imposing the
validity condition that the coalition contains only opponents. -/
def quittingFiniteQuitDefectAtomOccupationAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : ℕ → Payoff ι) (root : ℕ → ι → PMF Bool)
    (live : ℕ → ℝ) (cutoff : ℕ) (who : ι) (coalition : Finset ι) : ℝ :=
  ∑ time ∈ Finset.range cutoff,
    live time * quittingRootQuitDirectedAtom reward (tail time) (root time)
      who coalition

/-- The full chronological occupation of one fixed atom label.  Every live,
played-action, opponent-coalition, and payoff-toggle factor is explicit. -/
def quittingFiniteQuitDefectAtomOccupation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : ℕ → Payoff ι) (root : ℕ → ι → PMF Bool)
    (live : ℕ → ℝ) (cutoff : ℕ)
    (label : QuittingQuitDefectAtomLabel ι) : ℝ :=
  ∑ time ∈ Finset.range cutoff,
    if label.2 ∈ (Finset.univ.erase label.1).powerset then
      live time * quittingRootQuitDirectedAtom reward (tail time) (root time)
        label.1 label.2
    else 0

theorem quittingFiniteQuitDefectAtomOccupation_eq_at_of_mem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : ℕ → Payoff ι) (root : ℕ → ι → PMF Bool)
    (live : ℕ → ℝ) (cutoff : ℕ) (who : ι) (coalition : Finset ι)
    (hcoalition : coalition ∈ (Finset.univ.erase who).powerset) :
    quittingFiniteQuitDefectAtomOccupation reward tail root live cutoff
        (who, coalition) =
      quittingFiniteQuitDefectAtomOccupationAt reward tail root live cutoff
        who coalition := by
  simp [quittingFiniteQuitDefectAtomOccupation,
    quittingFiniteQuitDefectAtomOccupationAt, hcoalition]

/-- Total live Quit-directed defect occupation on a finite window. -/
def quittingFiniteQuitDirectedDefectOccupation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : ℕ → Payoff ι) (root : ℕ → ι → PMF Bool)
    (live : ℕ → ℝ) (cutoff : ℕ) : ℝ :=
  ∑ time ∈ Finset.range cutoff,
    live time *
      ∑ who, quittingRootQuitDirectedDefect reward (tail time) (root time) who

/-- Summing all fixed atom labels dominates the full Quit-directed defect
occupation.  This is the cutoff-free finite-label replacement for selecting
one date. -/
theorem quittingFiniteQuitDirectedDefectOccupation_le_sum_atomOccupation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : ℕ → Payoff ι) (root : ℕ → ι → PMF Bool)
    (live : ℕ → ℝ) (cutoff : ℕ)
    (hlive : ∀ time, 0 ≤ live time) :
    quittingFiniteQuitDirectedDefectOccupation reward tail root live cutoff ≤
      ∑ label : QuittingQuitDefectAtomLabel ι,
        quittingFiniteQuitDefectAtomOccupation reward tail root live cutoff label := by
  unfold quittingFiniteQuitDirectedDefectOccupation
    quittingFiniteQuitDefectAtomOccupation
  calc
    (∑ time ∈ Finset.range cutoff,
        live time * ∑ who,
          quittingRootQuitDirectedDefect reward (tail time) (root time) who) ≤
        ∑ time ∈ Finset.range cutoff,
          live time * ∑ who,
            ∑ coalition ∈ (Finset.univ.erase who).powerset,
              quittingRootQuitDirectedAtom reward (tail time) (root time)
                who coalition := by
      apply Finset.sum_le_sum
      intro time _
      apply mul_le_mul_of_nonneg_left _ (hlive time)
      apply Finset.sum_le_sum
      intro who _
      exact quittingRootQuitDirectedDefect_le_sum_atoms
        reward (tail time) (root time) who
    _ = ∑ label : QuittingQuitDefectAtomLabel ι,
          ∑ time ∈ Finset.range cutoff,
            if label.2 ∈ (Finset.univ.erase label.1).powerset then
              live time * quittingRootQuitDirectedAtom reward
                (tail time) (root time) label.1 label.2
            else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro time _
      rw [Finset.mul_sum]
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro who _
      simp
      rw [Finset.mul_sum]
      rw [← Finset.sum_filter]
      have hcarrier : (Finset.univ.erase who).powerset =
          (Finset.univ : Finset (Finset ι)).filter
            (fun coalition ↦ coalition ⊆ Finset.univ.erase who) := by
        ext coalition
        simp
      rw [hcarrier]

/-- **Finite fixed-label extraction.**  If the player type is nonempty, one
fixed solo/toggle label carries at least the average total Quit-directed
occupation.  The label count is independent of the time cutoff. -/
theorem exists_fixed_quittingQuitDefectAtomLabel
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : ℕ → Payoff ι) (root : ℕ → ι → PMF Bool)
    (live : ℕ → ℝ) (cutoff : ℕ)
    (hlive : ∀ time, 0 ≤ live time) :
    ∃ label : QuittingQuitDefectAtomLabel ι,
      quittingFiniteQuitDirectedDefectOccupation reward tail root live cutoff ≤
        (Fintype.card (QuittingQuitDefectAtomLabel ι) : ℝ) *
          quittingFiniteQuitDefectAtomOccupation reward tail root live cutoff label := by
  let labels := (Finset.univ : Finset (QuittingQuitDefectAtomLabel ι))
  have hlabels : labels.Nonempty := Finset.univ_nonempty
  obtain ⟨label, hlabelMem, hlabelMax⟩ := Finset.exists_max_image labels
    (quittingFiniteQuitDefectAtomOccupation reward tail root live cutoff) hlabels
  refine ⟨label, (quittingFiniteQuitDirectedDefectOccupation_le_sum_atomOccupation
    reward tail root live cutoff hlive).trans ?_⟩
  have hsum := labels.sum_le_card_nsmul
    (quittingFiniteQuitDefectAtomOccupation reward tail root live cutoff)
    (quittingFiniteQuitDefectAtomOccupation reward tail root live cutoff label)
    (fun other hother ↦ hlabelMax other hother)
  simpa [labels, nsmul_eq_mul, mul_comm] using hsum

/-- Sharp valid-label form of fixed-label extraction.  The first averaging
cost is the number of players and the second is exactly the number of
coalitions in that player's opponent powerset. -/
theorem exists_fixed_valid_quittingQuitDefectAtom
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : ℕ → Payoff ι) (root : ℕ → ι → PMF Bool)
    (live : ℕ → ℝ) (cutoff : ℕ)
    (hlive : ∀ time, 0 ≤ live time) :
    ∃ who coalition,
      coalition ∈ (Finset.univ.erase who).powerset ∧
      quittingFiniteQuitDirectedDefectOccupation reward tail root live cutoff ≤
        (Fintype.card ι : ℝ) *
          ((Finset.univ.erase who).powerset.card : ℝ) *
            quittingFiniteQuitDefectAtomOccupationAt reward tail root live cutoff
              who coalition := by
  let playerOccupation : ι → ℝ := fun who ↦
    ∑ coalition ∈ (Finset.univ.erase who).powerset,
      quittingFiniteQuitDefectAtomOccupationAt reward tail root live cutoff
        who coalition
  have htotal :
      quittingFiniteQuitDirectedDefectOccupation reward tail root live cutoff ≤
        ∑ who, playerOccupation who := by
    calc
      quittingFiniteQuitDirectedDefectOccupation reward tail root live cutoff ≤
          ∑ label : QuittingQuitDefectAtomLabel ι,
            quittingFiniteQuitDefectAtomOccupation reward tail root live cutoff
              label :=
        quittingFiniteQuitDirectedDefectOccupation_le_sum_atomOccupation
          reward tail root live cutoff hlive
      _ = ∑ who, playerOccupation who := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro who _
        unfold playerOccupation
        simp only [quittingFiniteQuitDefectAtomOccupation,
          quittingFiniteQuitDefectAtomOccupationAt]
        have hcarrier : (Finset.univ.erase who).powerset =
            (Finset.univ : Finset (Finset ι)).filter
              (fun coalition ↦ coalition ⊆ Finset.univ.erase who) := by
          ext coalition
          simp
        rw [hcarrier]
        simp [Finset.sum_filter, Finset.sum_comm]
  let players := (Finset.univ : Finset ι)
  obtain ⟨who, hwho, hwhoMax⟩ := Finset.exists_max_image players
    playerOccupation Finset.univ_nonempty
  have hplayerSum : (∑ player, playerOccupation player) ≤
      (Fintype.card ι : ℝ) * playerOccupation who := by
    have hbound := players.sum_le_card_nsmul playerOccupation
      (playerOccupation who) (fun player hplayer ↦ hwhoMax player hplayer)
    simpa [players, nsmul_eq_mul, mul_comm] using hbound
  let coalitions := (Finset.univ.erase who).powerset
  have hcoalitions : coalitions.Nonempty := by
    exact ⟨∅, Finset.empty_mem_powerset _⟩
  obtain ⟨coalition, hcoalition, hcoalitionMax⟩ :=
    Finset.exists_max_image coalitions
      (quittingFiniteQuitDefectAtomOccupationAt reward tail root live cutoff who)
      hcoalitions
  have hcoalitionSum : playerOccupation who ≤
      (coalitions.card : ℝ) *
        quittingFiniteQuitDefectAtomOccupationAt reward tail root live cutoff
          who coalition := by
    have hbound := coalitions.sum_le_card_nsmul
      (quittingFiniteQuitDefectAtomOccupationAt reward tail root live cutoff who)
      (quittingFiniteQuitDefectAtomOccupationAt reward tail root live cutoff
        who coalition)
      (fun other hother ↦ hcoalitionMax other hother)
    simpa [playerOccupation, coalitions, nsmul_eq_mul, mul_comm] using hbound
  refine ⟨who, coalition, ?_, ?_⟩
  · simpa [coalitions] using hcoalition
  · calc
      quittingFiniteQuitDirectedDefectOccupation reward tail root live cutoff ≤
          ∑ player, playerOccupation player := htotal
      _ ≤ (Fintype.card ι : ℝ) * playerOccupation who := hplayerSum
      _ ≤ (Fintype.card ι : ℝ) *
          ((Finset.univ.erase who).powerset.card : ℝ) *
            quittingFiniteQuitDefectAtomOccupationAt reward tail root live cutoff
              who coalition := by
        have hcard : 0 ≤ (Fintype.card ι : ℝ) := by positivity
        calc
          (Fintype.card ι : ℝ) * playerOccupation who ≤
              (Fintype.card ι : ℝ) *
                ((Finset.univ.erase who).powerset.card : ℝ) *
                  quittingFiniteQuitDefectAtomOccupationAt reward tail root live cutoff
                    who coalition := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left hcoalitionSum hcard

/-! ## A legal Continue-directed collector -/

/-- Exact finite-prefix performance difference for an arbitrary unilateral
hazard that resumes the source policy after the displayed window.  Local
advantages are evaluated against the source policy's own literal tail, while
the reach weights belong to the deviating policy. -/
theorem quittingRootSequenceHazardTerminalValue_sub_eq_sum_localAdvantages
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (hazard : ℕ → PMF Bool) :
    ∀ start fuel,
      (∀ time, start + fuel ≤ time → hazard time = roots time who) →
      quittingRootSequenceHazardTerminalValue reward roots who hazard start -
          quittingRootSequenceTerminalValue reward roots who start =
        ∑ offset ∈ Finset.range fuel,
          quittingJointSurvivalWeight
              (quittingRootSequenceUpdate roots who hazard) start offset *
            (quittingRootSuccessorPayoff reward
                (quittingRootSequenceTailVector reward roots
                  (start + offset + 1))
                (quittingRootSequenceUpdate roots who hazard
                  (start + offset)) who -
              quittingRootSuccessorPayoff reward
                (quittingRootSequenceTailVector reward roots
                  (start + offset + 1))
                (roots (start + offset)) who) := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      intro hafter
      have hagree : ∀ offset,
          quittingRootSequenceUpdate roots who hazard (start + offset) =
            roots (start + offset) := by
        intro offset
        rw [quittingRootSequenceUpdate, hafter (start + offset) (by omega)]
        exact Function.update_eq_self who (roots (start + offset))
      have hvalue := quittingRootSequenceTerminalValue_congr reward
        (quittingRootSequenceUpdate roots who hazard) roots who start hagree
      simpa [quittingRootSequenceHazardTerminalValue] using sub_eq_zero.mpr hvalue
  | succ fuel ih =>
      intro hafter
      let deviated := quittingRootSequenceUpdate roots who hazard
      have htail : ∀ time, start + 1 + fuel ≤ time →
          hazard time = roots time who := by
        intro time htime
        exact hafter time (by omega)
      have hinduction := ih (start + 1) htail
      have hy := quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector
        reward deviated who start
      have hx := quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector
        reward roots who start
      have hlinear := quittingRootSuccessorPayoff_sub_eq_continueMass_mul
        reward
          (quittingRootSequenceTailVector reward deviated (start + 1))
          (quittingRootSequenceTailVector reward roots (start + 1))
          (deviated start) who
      have hsplit := Finset.sum_range_succ'
        (fun offset ↦
          quittingJointSurvivalWeight deviated start offset *
            (quittingRootSuccessorPayoff reward
                (quittingRootSequenceTailVector reward roots
                  (start + offset + 1))
                (deviated (start + offset)) who -
              quittingRootSuccessorPayoff reward
                (quittingRootSequenceTailVector reward roots
                  (start + offset + 1))
                (roots (start + offset)) who)) fuel
      have hshift : ∀ offset ∈ Finset.range fuel,
          quittingJointSurvivalWeight deviated start (offset + 1) *
              (quittingRootSuccessorPayoff reward
                  (quittingRootSequenceTailVector reward roots
                    (start + (offset + 1) + 1))
                  (deviated (start + (offset + 1))) who -
                quittingRootSuccessorPayoff reward
                  (quittingRootSequenceTailVector reward roots
                    (start + (offset + 1) + 1))
                  (roots (start + (offset + 1))) who) =
            quittingStationaryContinueMass (deviated start) *
              (quittingJointSurvivalWeight deviated (start + 1) offset *
                (quittingRootSuccessorPayoff reward
                    (quittingRootSequenceTailVector reward roots
                      (start + 1 + offset + 1))
                    (deviated (start + 1 + offset)) who -
                  quittingRootSuccessorPayoff reward
                    (quittingRootSequenceTailVector reward roots
                      (start + 1 + offset + 1))
                    (roots (start + 1 + offset)) who)) := by
        intro offset _
        rw [show offset + 1 = 1 + offset by omega,
          quittingJointSurvivalWeight_add]
        simp only [quittingJointSurvivalWeight_eq_prod,
          Finset.prod_range_one, Nat.add_zero]
        have hindex : start + (1 + offset) = start + 1 + offset := by omega
        rw [hindex]
        ring
      change quittingRootSequenceTerminalValue reward deviated who (start + 1) -
          quittingRootSequenceTerminalValue reward roots who (start + 1) = _
        at hinduction
      change quittingRootSequenceTerminalValue reward deviated who start -
          quittingRootSequenceTerminalValue reward roots who start = _
      rw [hy, hx]
      rw [hsplit, Finset.sum_congr rfl hshift, ← Finset.mul_sum]
      simp only [quittingJointSurvivalWeight_zero_fuel, one_mul, Nat.add_zero]
      calc
        quittingRootSuccessorPayoff reward
              (quittingRootSequenceTailVector reward deviated (start + 1))
              (deviated start) who -
            quittingRootSuccessorPayoff reward
              (quittingRootSequenceTailVector reward roots (start + 1))
              (roots start) who =
          (quittingRootSuccessorPayoff reward
              (quittingRootSequenceTailVector reward roots (start + 1))
              (deviated start) who -
            quittingRootSuccessorPayoff reward
              (quittingRootSequenceTailVector reward roots (start + 1))
              (roots start) who) +
          (quittingRootSuccessorPayoff reward
              (quittingRootSequenceTailVector reward deviated (start + 1))
              (deviated start) who -
            quittingRootSuccessorPayoff reward
              (quittingRootSequenceTailVector reward roots (start + 1))
              (deviated start) who) := by ring
        _ = _ := by
          rw [hlinear]
          change _ + quittingStationaryContinueMass (deviated start) *
              (quittingRootSequenceTerminalValue reward deviated who (start + 1) -
                quittingRootSequenceTerminalValue reward roots who (start + 1)) = _
          rw [hinduction]
          ring

/-- The finite-prefix collector keeps the source marginal except at dates
where Continue is strictly better, where it plays pure Continue. -/
def quittingContinueDirectedCollectorHazard
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (cutoff : ℕ) : ℕ → PMF Bool :=
  fun time ↦
    if time < cutoff ∧
        quittingRootEndpointDifference reward
          (quittingRootSequenceTailVector reward roots (time + 1))
          (roots time) who < 0 then
      PMF.pure false
    else roots time who

theorem quittingContinueDirectedCollectorHazard_of_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (cutoff time : ℕ)
    (htime : cutoff ≤ time) :
    quittingContinueDirectedCollectorHazard reward roots who cutoff time =
      roots time who := by
  simp [quittingContinueDirectedCollectorHazard, Nat.not_lt.mpr htime]

/-- At every row the Continue collector weakly increases joint one-stage
survival, because it either preserves the marginal or forces it to Continue. -/
theorem quittingStationaryContinueMass_le_continueDirectedCollector
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (cutoff time : ℕ) :
    quittingStationaryContinueMass (roots time) ≤
      quittingStationaryContinueMass
        (Function.update (roots time) who
          (quittingContinueDirectedCollectorHazard
            reward roots who cutoff time)) := by
  by_cases hselected : time < cutoff ∧
      quittingRootEndpointDifference reward
        (quittingRootSequenceTailVector reward roots (time + 1))
        (roots time) who < 0
  · rw [quittingContinueDirectedCollectorHazard, if_pos hselected]
    exact quittingStationaryContinueMass_le_update_pure_false (roots time) who
  · rw [quittingContinueDirectedCollectorHazard, if_neg hselected,
      Function.update_eq_self]

/-- Removing Quit probability at selected dates weakly increases every
finite live-prefix weight. -/
theorem quittingJointSurvivalWeight_le_continueDirectedCollector
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (cutoff start fuel : ℕ) :
    quittingJointSurvivalWeight roots start fuel ≤
      quittingJointSurvivalWeight
        (quittingRootSequenceUpdate roots who
          (quittingContinueDirectedCollectorHazard reward roots who cutoff))
        start fuel := by
  rw [quittingJointSurvivalWeight_eq_prod,
    quittingJointSurvivalWeight_eq_prod]
  apply Finset.prod_le_prod
  · intro offset _
    exact quittingStationaryContinueMass_nonneg _
  · intro offset _
    exact quittingStationaryContinueMass_le_continueDirectedCollector
      reward roots who cutoff (start + offset)

/-- On every date inside the collection window, the collector's local
source-tail advantage is exactly the Continue-directed defect. -/
theorem quittingRootSuccessorPayoff_collector_sub_eq_continueDirectedDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (cutoff time : ℕ)
    (htime : time < cutoff) :
    quittingRootSuccessorPayoff reward
          (quittingRootSequenceTailVector reward roots (time + 1))
          (Function.update (roots time) who
            (quittingContinueDirectedCollectorHazard
              reward roots who cutoff time)) who -
        quittingRootSuccessorPayoff reward
          (quittingRootSequenceTailVector reward roots (time + 1))
          (roots time) who =
      quittingRootContinueDirectedDefect reward
        (quittingRootSequenceTailVector reward roots (time + 1))
        (roots time) who := by
  let difference := quittingRootEndpointDifference reward
    (quittingRootSequenceTailVector reward roots (time + 1))
    (roots time) who
  by_cases hbetter : difference < 0
  · have hcollector : quittingContinueDirectedCollectorHazard
        reward roots who cutoff time = PMF.pure false := by
      simp [quittingContinueDirectedCollectorHazard, htime, hbetter, difference]
    rw [hcollector]
    unfold quittingRootContinueDirectedDefect
    have hpure : quittingRootSuccessorPayoff reward
          (quittingRootSequenceTailVector reward roots (time + 1))
          (Function.update (roots time) who (PMF.pure false)) who =
        quittingRootContinuePayoff reward
          (quittingRootSequenceTailVector reward roots (time + 1))
          (roots time) who := by
      unfold quittingRootSuccessorPayoff
      rw [quittingRootExpectedPayoff_update_eq_endpointMix]
      simp
    rw [hpure, quittingRootSuccessorPayoff_eq_endpointMix]
    have hsum := quittingRoot_continueProbability_add_quitProbability
      (roots time) who
    have hmax : max (-difference) 0 = -difference := max_eq_left (by linarith)
    rw [hmax]
    change quittingRootContinuePayoff reward
          (quittingRootSequenceTailVector reward roots (time + 1))
          (roots time) who -
        ((roots time who true).toReal *
            quittingRootQuitPayoff reward
              (quittingRootSequenceTailVector reward roots (time + 1))
              (roots time) who +
          (roots time who false).toReal *
            quittingRootContinuePayoff reward
              (quittingRootSequenceTailVector reward roots (time + 1))
              (roots time) who) =
        (roots time who true).toReal * -difference
    have hdifference : difference = quittingRootQuitPayoff reward
        (quittingRootSequenceTailVector reward roots (time + 1))
        (roots time) who -
      quittingRootContinuePayoff reward
        (quittingRootSequenceTailVector reward roots (time + 1))
        (roots time) who := rfl
    rw [hdifference]
    have hquit : (roots time who true).toReal =
        1 - (roots time who false).toReal := by linarith
    rw [hquit]
    ring
  · have hcollector : quittingContinueDirectedCollectorHazard
        reward roots who cutoff time = roots time who := by
      simp [quittingContinueDirectedCollectorHazard, htime,
        not_lt.mp hbetter, difference]
    rw [hcollector, Function.update_eq_self]
    unfold quittingRootContinueDirectedDefect
    rw [max_eq_right (by linarith : -difference ≤ 0), mul_zero]
    ring

/-- **Legal multi-date Continue collector.**  There is one behavioral
deviation whose gain is exactly the sum of the Continue-directed defects,
weighted by that deviation's own live probability.  No cutoff loss or date
selection occurs. -/
theorem exists_behaviorDeviation_gain_eq_sum_continueDirectedDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (cutoff : ℕ) :
    ∃ deviation : (quittingGame reward).BehaviorStrategy who,
      quittingTerminalPayoff reward (Function.update profile who deviation) who -
          quittingTerminalPayoff reward profile who =
        ∑ time ∈ Finset.range cutoff,
          quittingJointSurvivalWeight
              (quittingRootSequenceUpdate
                (quittingProfileLiveRoot reward profile) who
                (quittingContinueDirectedCollectorHazard reward
                  (quittingProfileLiveRoot reward profile) who cutoff)) 0 time *
            quittingRootContinueDirectedDefect reward
              (quittingRootSequenceTailVector reward
                (quittingProfileLiveRoot reward profile) (time + 1))
              (quittingProfileLiveRoot reward profile time) who := by
  let roots := quittingProfileLiveRoot reward profile
  let hazard := quittingContinueDirectedCollectorHazard reward roots who cutoff
  let deviation : (quittingGame reward).BehaviorStrategy who :=
    fun time _history ↦ hazard time
  refine ⟨deviation, ?_⟩
  have hliveHazard : quittingBehaviorLiveHazard reward deviation = hazard := by
    rfl
  rw [quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue,
    quittingTerminalPayoff_eq_rootSequence_profileLiveRoot, hliveHazard]
  have hperformance :=
    quittingRootSequenceHazardTerminalValue_sub_eq_sum_localAdvantages
      reward roots who hazard 0 cutoff
      (fun time htime ↦ quittingContinueDirectedCollectorHazard_of_le
        reward roots who cutoff time (by omega))
  simp only [Nat.zero_add] at hperformance
  rw [hperformance]
  apply Finset.sum_congr rfl
  intro time htime
  simp only [quittingRootSequenceUpdate]
  rw [quittingRootSuccessorPayoff_collector_sub_eq_continueDirectedDefect
    reward roots who cutoff time (Finset.mem_range.mp htime)]

/-- The same legal collector gains at least the source-live occupation of all
Continue-directed defects.  Thus this polarity is collected without a cutoff
or date-selection factor. -/
theorem exists_behaviorDeviation_gain_ge_sum_live_continueDirectedDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (cutoff : ℕ) :
    ∃ deviation : (quittingGame reward).BehaviorStrategy who,
      (∑ time ∈ Finset.range cutoff,
          quittingJointSurvivalWeight
              (quittingProfileLiveRoot reward profile) 0 time *
            quittingRootContinueDirectedDefect reward
              (quittingRootSequenceTailVector reward
                (quittingProfileLiveRoot reward profile) (time + 1))
              (quittingProfileLiveRoot reward profile time) who) ≤
        quittingTerminalPayoff reward (Function.update profile who deviation) who -
          quittingTerminalPayoff reward profile who := by
  obtain ⟨deviation, hgain⟩ :=
    exists_behaviorDeviation_gain_eq_sum_continueDirectedDefect
      reward profile who cutoff
  refine ⟨deviation, ?_⟩
  rw [hgain]
  apply Finset.sum_le_sum
  intro time _
  exact mul_le_mul_of_nonneg_right
    (quittingJointSurvivalWeight_le_continueDirectedCollector reward
      (quittingProfileLiveRoot reward profile) who cutoff 0 time)
    (quittingRootContinueDirectedDefect_nonneg reward
      (quittingRootSequenceTailVector reward
        (quittingProfileLiveRoot reward profile) (time + 1))
      (quittingProfileLiveRoot reward profile time) who)

end GameTheory
