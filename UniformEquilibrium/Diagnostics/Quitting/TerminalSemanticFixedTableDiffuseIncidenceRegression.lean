/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticIncidenceDebtRatioRegression
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDefectCharge
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryCaps

/-!
# Fixed-table diffuse incidence with vanishing local defect

This exact three-player family separates terminal-law incidence from local
Nash defect without rescaling the reward table.  Player `0` is the reset
owner and Continues, player `1` Quits surely, and player `2` Quits with the
rational hazard `q_n = 1/(n+2)`.

The owner sees at least `1/2` displayed debtor incidence.  The only local defect
is player `1`'s missed Continue payoff, exactly `q_n`, so total Nash defect
tends to zero.  The literal semantic pair has debt `(0,q_n,0)`, yet every
exact Nash root against its displayed cap is all-Continue.

Hence even for one fixed normalized rational reward table there is no finite
linear bound from total Nash defect to fresh or carried opponent incidence.
Positive incidence alone also supplies no uniform positive defect occupation
floor.  A valid concentrated/diffuse consumer must retain additional matched
geometry, a payoff-separation margin, or a debt-scale normalization.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

namespace QuittingFixedTableDiffuseIncidenceRegression

abbrev Player := Fin 3

abbrev owner : Player := 0
abbrev debtor : Player := 1
abbrev switch : Player := 2

/-- Fixed reward table.  Owner Quit costs `-1`.  The debtor gets `1` exactly
by Continuing while the switch Quits.  The switch pays `-1` for quitting
without the debtor, but is indifferent when the debtor also Quits. -/
def reward (terminal : {S : Finset Player // S.Nonempty}) : Payoff Player :=
  fun who =>
    if who = owner then
      if owner ∈ terminal.1 then -1 else 0
    else if who = debtor then
      if debtor ∈ terminal.1 then 0
      else if switch ∈ terminal.1 then 1 else 0
    else
      if switch ∈ terminal.1 then
        if debtor ∈ terminal.1 then 0 else -1
      else 0

theorem reward_bound (terminal player) : |reward terminal player| ≤ 1 := by
  fin_cases player <;>
    by_cases howner : owner ∈ terminal.1 <;>
      by_cases hdebtor : debtor ∈ terminal.1 <;>
        by_cases hswitch : switch ∈ terminal.1 <;>
          simp [reward, owner, debtor, switch, howner, hdebtor, hswitch]

def q (n : ℕ) : ℝ := 1 / (n + 2 : ℝ)

theorem q_pos (n : ℕ) : 0 < q n := by
  unfold q
  positivity

theorem q_le_one (n : ℕ) : q n ≤ 1 := by
  unfold q
  have hn : (0 : ℝ) ≤ n := by positivity
  have hden : (0 : ℝ) < n + 2 := by linarith
  rw [div_le_one hden]
  linarith

theorem q_le_half (n : ℕ) : q n ≤ 1 / 2 := by
  unfold q
  have hn : (0 : ℝ) ≤ n := by positivity
  have hden : (0 : ℝ) < n + 2 := by linarith
  rw [div_le_iff₀ hden]
  nlinarith

def switchCoin (n : ℕ) : PMF Bool :=
  quittingHazardCoin (q n) (q_pos n).le (q_le_one n)

@[simp] theorem switchCoin_true_toReal (n : ℕ) :
    (switchCoin n true).toReal = q n := by
  simp [switchCoin]

@[simp] theorem switchCoin_false_toReal (n : ℕ) :
    (switchCoin n false).toReal = 1 - q n := by
  simp [switchCoin]

def root (n : ℕ) : Player → PMF Bool := fun who =>
  if who = owner then PMF.pure false
  else if who = debtor then PMF.pure true
  else switchCoin n

def continuation : (quittingGame reward).BehaviorProfile :=
  fun _player _time _history => PMF.pure false

def profile (n : ℕ) : (quittingGame reward).BehaviorProfile :=
  quittingRootThenContinuationProfile reward (root n) continuation

def pair (n : ℕ) : QuittingTerminalSemanticPair Player :=
  quittingTerminalSemanticPair reward (profile n)

def mass (n : ℕ) : QuittingTerminalOutcome Player → ℝ :=
  quittingTerminalOutcomeMass reward (profile n)

/-- Three-coordinate Fubini expansion for Boolean product roots. -/
theorem expect_pmfPi_fin3 (sigma : Player → PMF Bool)
    (f : (Player → Bool) → ℝ) :
    expect (pmfPi sigma) f =
      expect (sigma owner) (fun a =>
        expect (sigma debtor) (fun b =>
          expect (sigma switch) (fun c => f ![a, b, c]))) := by
  classical
  have howner : Function.update sigma owner (sigma owner) = sigma :=
    Function.update_eq_self owner sigma
  rw [← howner, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (sigma owner))
  funext a
  have hdebtor : Function.update (Function.update sigma owner (PMF.pure a))
      debtor (sigma debtor) = Function.update sigma owner (PMF.pure a) := by
    funext who
    fin_cases who <;> simp [owner, debtor]
  rw [← hdebtor, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (sigma debtor))
  funext b
  have hswitch : Function.update
      (Function.update (Function.update sigma owner (PMF.pure a))
        debtor (PMF.pure b)) switch (sigma switch) =
      Function.update (Function.update sigma owner (PMF.pure a))
        debtor (PMF.pure b) := by
    funext who
    fin_cases who <;> simp [owner, debtor, switch]
  rw [← hswitch, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (sigma switch))
  funext c
  have hpure : Function.update
      (Function.update (Function.update sigma owner (PMF.pure a))
        debtor (PMF.pure b)) switch (PMF.pure c) =
      fun who => PMF.pure (![a, b, c] who) := by
    funext who
    fin_cases who <;> simp [owner, debtor, switch]
  rw [hpure, pmfPi_pure, expect_pure]

@[simp] theorem quittingQuitters_vec3 (a b c : Bool) :
    quittingQuitters ![a, b, c] =
      (if a then {owner} else ∅) ∪
        (if b then {debtor} else ∅) ∪
          (if c then {switch} else ∅) := by
  ext who
  fin_cases who <;> cases a <;> cases b <;> cases c <;>
    simp [quittingQuitters, owner, debtor, switch]

theorem root_probabilities (n : ℕ) :
    ((root n owner true).toReal = 0) ∧
      ((root n debtor true).toReal = 1) ∧
      ((root n switch true).toReal = q n) := by
  simp [root, owner, debtor, switch]

/-! ## Exact endpoint calculations at the generating root -/

theorem generating_quitPayoff_owner (n : ℕ) :
    quittingRootQuitPayoff reward (fun _ => 0) (root n) owner = -1 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3]
  simp [root, quittingRootPayoff, reward, owner, debtor, switch, expect_eq_sum]
  ring

theorem generating_continuePayoff_owner (n : ℕ) :
    quittingRootContinuePayoff reward (fun _ => 0) (root n) owner = 0 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3]
  simp [root, quittingRootPayoff, reward, owner, debtor, switch, expect_eq_sum]

theorem generating_quitPayoff_debtor (n : ℕ) :
    quittingRootQuitPayoff reward (fun _ => 0) (root n) debtor = 0 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3]
  simp [root, quittingRootPayoff, reward, owner, debtor, switch, expect_eq_sum]

theorem generating_continuePayoff_debtor (n : ℕ) :
    quittingRootContinuePayoff reward (fun _ => 0) (root n) debtor = q n := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3]
  simp [root, quittingRootPayoff, reward, owner, debtor, switch, expect_eq_sum]

theorem generating_quitPayoff_switch (n : ℕ) :
    quittingRootQuitPayoff reward (fun _ => 0) (root n) switch = 0 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3]
  simp [root, quittingRootPayoff, reward, owner, debtor, switch, expect_eq_sum]

theorem generating_continuePayoff_switch (n : ℕ) :
    quittingRootContinuePayoff reward (fun _ => 0) (root n) switch = 0 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3]
  simp [root, quittingRootPayoff, reward, owner, debtor, switch, expect_eq_sum]

/-- The generating root has zero payoff in the owner coordinate. -/
theorem generating_successorPayoff_owner (n : ℕ) :
    quittingRootSuccessorPayoff reward (fun _ => 0) (root n) owner = 0 := by
  rw [quittingRootSuccessorPayoff_eq_endpointMix]
  rw [generating_quitPayoff_owner, generating_continuePayoff_owner]
  simp [root, owner]

/-- The generating root has zero payoff in the debtor coordinate. -/
theorem generating_successorPayoff_debtor (n : ℕ) :
    quittingRootSuccessorPayoff reward (fun _ => 0) (root n) debtor = 0 := by
  rw [quittingRootSuccessorPayoff_eq_endpointMix]
  rw [generating_quitPayoff_debtor, generating_continuePayoff_debtor]
  simp [root, owner, debtor]

/-- The generating root has zero payoff in the switch coordinate. -/
theorem generating_successorPayoff_switch (n : ℕ) :
    quittingRootSuccessorPayoff reward (fun _ => 0) (root n) switch = 0 := by
  rw [quittingRootSuccessorPayoff_eq_endpointMix]
  rw [generating_quitPayoff_switch, generating_continuePayoff_switch]
  simp [root, owner, debtor, switch]

/-- The generating root has zero payoff in every coordinate. -/
theorem generating_successorPayoff (n : ℕ) (who : Player) :
    quittingRootSuccessorPayoff reward (fun _ => 0) (root n) who = 0 := by
  fin_cases who
  · exact generating_successorPayoff_owner n
  · exact generating_successorPayoff_debtor n
  · exact generating_successorPayoff_switch n

/-- Only the sure quitter carries defect, exactly `q_n`. -/
theorem generating_coordinateNashDefect (n : ℕ) (who : Player) :
    quittingRootCoordinateNashDefect reward (fun _ => 0) (root n) who =
      if who = debtor then q n else 0 := by
  unfold quittingRootCoordinateNashDefect
  rw [generating_successorPayoff]
  fin_cases who
  · change max
        (quittingRootQuitPayoff reward (fun _ => 0) (root n) owner)
        (quittingRootContinuePayoff reward (fun _ => 0) (root n) owner) - 0 = _
    rw [generating_quitPayoff_owner, generating_continuePayoff_owner]
    simp [debtor]
  · change max
        (quittingRootQuitPayoff reward (fun _ => 0) (root n) debtor)
        (quittingRootContinuePayoff reward (fun _ => 0) (root n) debtor) - 0 = _
    rw [generating_quitPayoff_debtor, generating_continuePayoff_debtor]
    simp [debtor, max_eq_right (q_pos n).le]
  · change max
        (quittingRootQuitPayoff reward (fun _ => 0) (root n) switch)
        (quittingRootContinuePayoff reward (fun _ => 0) (root n) switch) - 0 = _
    rw [generating_quitPayoff_switch, generating_continuePayoff_switch]
    simp [debtor]

theorem generating_totalNashDefect (n : ℕ) :
    quittingRootTotalNashDefect reward (fun _ => 0) (root n) = q n := by
  unfold quittingRootTotalNashDefect
  simp_rw [generating_coordinateNashDefect]
  rw [show (Finset.univ : Finset Player) = {owner, debtor, switch} by decide]
  simp [owner, debtor, switch]

/-! ## Literal semantic pair -/

theorem continuation_eq_allContinue :
    continuation = quittingAlwaysContinueProfile reward := by
  rfl

/-- The silent continuation realizes the zero payoff and zero unilateral
envelope because every singleton quitting reward is nonpositive. -/
theorem continuation_pair_coordinates :
    quittingTerminalSemanticPair reward continuation =
      ((fun _ => 0), (fun _ => 0)) := by
  apply Prod.ext
  · funext who
    change quittingTerminalPayoff reward
      (quittingAlwaysContinueProfile reward) who = 0
    exact quittingTerminalPayoff_quittingAlwaysContinue reward who
  · funext who
    change quittingContinuationBestResponseValue reward continuation who = 0
    rw [continuation_eq_allContinue]
    change quittingRootSequenceBestResponseValue reward
      (quittingElementaryCapRoots (.never : QuittingElementaryTailCap Player))
        who = 0
    rw [quittingRootSequenceBestResponseValue_elementaryCap_never
      reward who (by norm_num) reward_bound]
    fin_cases who <;>
      simp [reward, quittingSingletonTerminal, owner, debtor, switch]

theorem pair_coordinates (n : ℕ) :
    (pair n).1 = (fun _ => 0) ∧
      (pair n).2 = ![0, q n, 0] := by
  have hprefix := quittingTerminalSemanticPair_rootThenContinuation
    reward (root n) continuation (M := 1) (by norm_num) reward_bound
  change quittingTerminalSemanticPair reward (profile n) =
      quittingTerminalSemanticPrefix reward (root n)
        (quittingTerminalSemanticPair reward continuation) at hprefix
  rw [continuation_pair_coordinates] at hprefix
  rw [show pair n = quittingTerminalSemanticPrefix reward (root n)
      ((fun _ => 0), (fun _ => 0)) by exact hprefix]
  apply And.intro
  · funext who
    simp only [quittingTerminalSemanticPrefix]
    exact generating_successorPayoff n who
  · funext who
    simp only [quittingTerminalSemanticPrefix]
    fin_cases who
    · unfold quittingRootQuitPayoff quittingRootContinuePayoff
        quittingRootExpectedPayoff
      rw [expect_pmfPi_fin3, expect_pmfPi_fin3]
      simp [root, quittingRootPayoff, reward, owner, debtor, switch, expect_eq_sum]
    · unfold quittingRootQuitPayoff quittingRootContinuePayoff
        quittingRootExpectedPayoff
      rw [expect_pmfPi_fin3, expect_pmfPi_fin3]
      simpa [root, quittingRootPayoff, reward, owner, debtor, switch,
        expect_eq_sum] using (q_pos n).le
    · unfold quittingRootQuitPayoff quittingRootContinuePayoff
        quittingRootExpectedPayoff
      rw [expect_pmfPi_fin3, expect_pmfPi_fin3]
      simp [root, quittingRootPayoff, reward, owner, debtor, switch, expect_eq_sum]

theorem pair_mass_mem_carrier (n : ℕ) :
    (pair n, mass n) ∈ quittingTerminalSemanticLawCarrier reward := by
  exact quittingTerminalSemanticLawPoint_mem_carrier reward (profile n)

theorem pair_debt (n : ℕ) :
    quittingTerminalSemanticDebt (pair n) owner = 0 ∧
      quittingTerminalSemanticDebtSum (pair n) = q n := by
  rcases pair_coordinates n with ⟨hpayoff, hcap⟩
  constructor
  · simp [quittingTerminalSemanticDebt, hpayoff, hcap, owner]
  · unfold quittingTerminalSemanticDebtSum
    rw [show (Finset.univ : Finset Player) = {owner, debtor, switch} by decide]
    simp [quittingTerminalSemanticDebt, hpayoff, hcap,
      owner, debtor, switch]

/-! ## Incidence -/

theorem root_singletonDebtorMass (n : ℕ) :
    quittingRootCoalitionMass (root n) {debtor} = 1 - q n := by
  unfold quittingRootCoalitionMass coalitionMass quittingRootQuitRates
  rw [show ({debtor} : Finset Player)ᶜ = {owner, switch} by decide]
  simp [root, owner, debtor, switch]

theorem root_continueMass_eq_zero (n : ℕ) :
    quittingStationaryContinueMass (root n) = 0 := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  rw [show (Finset.univ : Finset Player) = {owner, debtor, switch} by decide]
  simp [root, owner, debtor, switch]

/-- The displayed debtor-incidence coordinate is uniformly bounded below,
even though the local defect tends to zero. -/
theorem displayedIncidence_debtor_ge_half (n : ℕ) :
    1 / 2 ≤ quittingTerminalOpponentIncidenceMass owner debtor (mass n) := by
  have hlaw : mass n = quittingTerminalOutcomeLawPrefix (root n)
      (quittingTerminalOutcomeMass reward continuation) := by
    exact (quittingTerminalOutcomeLawPrefix_outcomeMass
      reward (root n) continuation).symm
  rw [hlaw, quittingTerminalOpponentIncidenceMass_lawPrefix]
  have hroot : 1 / 2 ≤
      quittingRootOpponentIncidenceMass owner debtor (root n) := by
    unfold quittingRootOpponentIncidenceMass
    have hmem : quittingSingletonTerminal debtor ∈
        Finset.univ.filter
          (fun terminal : {S : Finset Player // S.Nonempty} =>
            debtor ∈ terminal.val ∧ debtor ≠ owner) := by
      simp [quittingSingletonTerminal, owner, debtor]
    calc
      1 / 2 ≤ quittingRootCoalitionMass (root n) {debtor} := by
        rw [root_singletonDebtorMass]
        linarith [q_le_half n]
      _ ≤ ∑ terminal ∈ Finset.univ.filter
          (fun terminal : {S : Finset Player // S.Nonempty} =>
            debtor ∈ terminal.val ∧ debtor ≠ owner),
            quittingRootCoalitionMass (root n) terminal.val := by
        exact Finset.single_le_sum
          (fun terminal _ =>
            MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg
              (root n) terminal.val)
          hmem
  rw [root_continueMass_eq_zero]
  simpa using hroot

theorem totalOpponentIncidence_ge_half (n : ℕ) :
    1 / 2 ≤ quittingTerminalTotalOpponentIncidenceMass owner (mass n) := by
  unfold quittingTerminalTotalOpponentIncidenceMass
  have hmem : debtor ∈ Finset.univ.erase owner := by simp [owner, debtor]
  calc
    1 / 2 ≤ quittingTerminalOpponentIncidenceMass owner debtor (mass n) :=
      displayedIncidence_debtor_ge_half n
    _ ≤ ∑ other ∈ Finset.univ.erase owner,
        quittingTerminalOpponentIncidenceMass owner other (mass n) := by
      exact Finset.single_le_sum
        (f := fun other =>
          quittingTerminalOpponentIncidenceMass owner other (mass n))
        (fun other _ => by
          exact Finset.sum_nonneg fun terminal _ =>
            quittingAbsorbedMassLimit_nonneg reward (profile n) terminal)
        hmem

/-! ## Unique cap Nash root -/

theorem cap_endpointDifference_owner (n : ℕ) (candidate : Player → PMF Bool) :
    quittingRootEndpointDifference reward (pair n).2 candidate owner = -1 := by
  have hdebtorSum := quittingRoot_continueProbability_add_quitProbability
    candidate debtor
  have hswitchSum := quittingRoot_continueProbability_add_quitProbability
    candidate switch
  rw [(pair_coordinates n).2]
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3, expect_pmfPi_fin3]
  simp [quittingRootPayoff, reward, owner, debtor, switch, expect_eq_sum]
  nlinarith

theorem cap_endpointDifference_switch_of_owner_debtor_continue
    (n : ℕ) (candidate : Player → PMF Bool)
    (howner : candidate owner = PMF.pure false)
    (hdebtor : candidate debtor = PMF.pure false) :
    quittingRootEndpointDifference reward (pair n).2 candidate switch = -1 := by
  rw [(pair_coordinates n).2]
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3, expect_pmfPi_fin3]
  simp [quittingRootPayoff, reward, owner, debtor, switch, howner, hdebtor]

/-- The exact cap correspondence is the singleton all-Continue root. -/
theorem exact_capNash_forces_allContinue (n : ℕ)
    (candidate : Player → PMF Bool)
    (hnash : IsεQuittingRootNash reward (pair n).2 0 candidate) :
    candidate = (quittingAllContinueRoot : Player → PMF Bool) := by
  have hendpoint : IsεQuittingRootEndpointNash reward (pair n).2 0 candidate :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward (pair n).2 candidate).mpr hnash
  have hownerZero : (candidate owner true).toReal = 0 := by
    have h := (hendpoint owner).2
    rw [cap_endpointDifference_owner] at h
    have hnonneg : 0 ≤ (candidate owner true).toReal :=
      ENNReal.toReal_nonneg
    exact le_antisymm (by nlinarith) hnonneg
  have howner : candidate owner = PMF.pure false :=
    pmf_eq_pure_false_of_apply_true_toReal_eq_zero _ hownerZero
  have hdebtorZero : (candidate debtor true).toReal = 0 := by
    -- First force the switch to Continue conditionally after the debtor is
    -- forced; the debtor itself has a positive Continue value even before
    -- that simplification.  The direct general formula is used here.
    have hgeneral : quittingRootEndpointDifference reward (pair n).2
        candidate debtor =
      -((candidate switch true).toReal +
        (candidate switch false).toReal * q n) := by
      rw [(pair_coordinates n).2]
      unfold quittingRootEndpointDifference quittingRootQuitPayoff
        quittingRootContinuePayoff quittingRootExpectedPayoff
      rw [expect_pmfPi_fin3, expect_pmfPi_fin3]
      simp [quittingRootPayoff, reward, owner, debtor, switch, howner,
        expect_eq_sum]
    have h := (hendpoint debtor).2
    rw [hgeneral] at h
    have hpositive : 0 < (candidate switch true).toReal +
        (candidate switch false).toReal * q n := by
      have hsum := quittingRoot_continueProbability_add_quitProbability
        candidate switch
      have hq := q_pos n
      have ht := ENNReal.toReal_nonneg (a := candidate switch true)
      have hf := ENNReal.toReal_nonneg (a := candidate switch false)
      by_cases hquit : 0 < (candidate switch true).toReal
      · exact add_pos_of_pos_of_nonneg hquit (mul_nonneg hf hq.le)
      · have hquitZero : (candidate switch true).toReal = 0 := by
          exact le_antisymm (le_of_not_gt hquit) ht
        have hcontinueOne : (candidate switch false).toReal = 1 := by
          linarith
        rw [hquitZero, hcontinueOne, zero_add, one_mul]
        exact hq
    have hnonneg : 0 ≤ (candidate debtor true).toReal :=
      ENNReal.toReal_nonneg
    exact le_antisymm (by nlinarith) hnonneg
  have hdebtor : candidate debtor = PMF.pure false :=
    pmf_eq_pure_false_of_apply_true_toReal_eq_zero _ hdebtorZero
  have hswitchDiff := cap_endpointDifference_switch_of_owner_debtor_continue
    n candidate howner hdebtor
  have hswitchZero : (candidate switch true).toReal = 0 := by
    have h := (hendpoint switch).2
    rw [hswitchDiff] at h
    have hnonneg : 0 ≤ (candidate switch true).toReal :=
      ENNReal.toReal_nonneg
    exact le_antisymm (by nlinarith) hnonneg
  have hswitch : candidate switch = PMF.pure false :=
    pmf_eq_pure_false_of_apply_true_toReal_eq_zero _ hswitchZero
  funext who
  fin_cases who
  · simpa [quittingAllContinueRoot, owner] using howner
  · simpa [quittingAllContinueRoot, debtor] using hdebtor
  · simpa [quittingAllContinueRoot, switch] using hswitch

/-- Complete fixed-table passport. -/
theorem fixedTable_incidence_ge_half_defect_eq_q_uniqueAllContinue (n : ℕ) :
    (pair n, mass n) ∈ quittingTerminalSemanticLawCarrier reward ∧
      quittingTerminalSemanticDebt (pair n) owner = 0 ∧
      quittingTerminalSemanticDebtSum (pair n) = q n ∧
      1 / 2 ≤ quittingTerminalTotalOpponentIncidenceMass owner (mass n) ∧
      quittingRootTotalNashDefect reward (fun _ => 0) (root n) = q n ∧
      ∀ candidate : Player → PMF Bool,
        IsεQuittingRootNash reward (pair n).2 0 candidate →
          candidate = (quittingAllContinueRoot : Player → PMF Bool) := by
  exact ⟨pair_mass_mem_carrier n, (pair_debt n).1, (pair_debt n).2,
    totalOpponentIncidence_ge_half n, generating_totalNashDefect n,
    exact_capNash_forces_allContinue n⟩

/-- No finite constant controls the fixed table's terminal-law incidence by
its local Nash defect.  This is stronger than a reward-normalized scaling
counterexample because `reward` is unchanged throughout the family. -/
theorem no_fixedTable_linear_incidence_le_totalNashDefect :
    ¬ ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ,
        quittingTerminalTotalOpponentIncidenceMass owner (mass n) ≤
          C * quittingRootTotalNashDefect
            reward (fun _ => 0) (root n) := by
  rintro ⟨C, hC, hbound⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * C)
  have hden : (0 : ℝ) < n + 2 := by positivity
  have hratio : C / (n + 2 : ℝ) < 1 / 2 := by
    rw [div_lt_iff₀ hden]
    nlinarith
  have hlower := totalOpponentIncidence_ge_half n
  have hupper := hbound n
  rw [generating_totalNashDefect] at hupper
  have hscale : C * q n = C / (n + 2 : ℝ) := by
    unfold q
    ring
  rw [hscale] at hupper
  linarith

end QuittingFixedTableDiffuseIncidenceRegression

end GameTheory
