/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeCoalitionLocks
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeOffDiagonalStaticOrientationDispatch
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceReturn
import UniformEquilibrium.Quitting.Classification.PlayerReindex

/-!
# A four-player cyclic plateau candidate

This is a bounded search object, not a counterexample to uniform-equilibrium
existence.  Four pure sure-exit profiles run around one Boolean square.  Two
players alternate as strict best-response movers, a permanent host carries a
second unit of debt at every phase, and an observer is passive.  Total debt is
therefore exactly two throughout the literal unilateral reset cycle.

At every phase, the behavioral cap is the same vector `(1,1,0,0)`.  The host
and observer strictly Continue at every product root.  Once they Continue,
both movers strictly Continue as well, so all-Continue is the unique exact
cap--Nash root.  In particular, none of the four cycling pure roots is itself
an exact cap--Nash operation.

All singleton rewards are nonpositive, hence every punishment value is
nonpositive.  The experiment deliberately claims only a positive floor on
its displayed finite four-profile family.  It makes no positive-minimum claim
about the full terminal-semantic carrier.

The sharp global fence is explicit: the literal all-Continue profile is an
exact terminal Nash equilibrium and its terminal semantic pair has zero debt.
Thus this file is a negative search control.  It isolates both failures of
the tempting cyclic construction: exact cap/state admissibility and a
positive global semantic floor.  Debt circulation by itself is compatible
with neither missing property.
-/

noncomputable section

namespace GameTheory
namespace FourPlayerCyclicPlateauCandidate

open Math.Probability Math.PMFProduct
open QuittingSureSetOwnerRepair

abbrev Player := Fin 4
abbrev Phase := Fin 4

abbrev first : Player := 0
abbrev second : Player := 1
abbrev host : Player := 2
abbrev observer : Player := 3

/-- The Gray-code square, with `host` present at every phase. -/
def phaseCoalition : Phase → Finset Player :=
  ![{host}, {first, host}, {first, second, host}, {second, host}]

def phaseMover : Phase → Player := ![first, second, first, second]

def nextPhase : Phase → Phase := ![1, 2, 3, 0]

@[simp] theorem phaseCoalition_zero : phaseCoalition 0 = {host} := rfl
@[simp] theorem phaseCoalition_one : phaseCoalition 1 = {first, host} := rfl
@[simp] theorem phaseCoalition_two :
    phaseCoalition 2 = {first, second, host} := rfl
@[simp] theorem phaseCoalition_three :
    phaseCoalition 3 = {second, host} := rfl

@[simp] theorem phaseMover_zero : phaseMover 0 = first := rfl
@[simp] theorem phaseMover_one : phaseMover 1 = second := rfl
@[simp] theorem phaseMover_two : phaseMover 2 = first := rfl
@[simp] theorem phaseMover_three : phaseMover 3 = second := rfl

@[simp] theorem nextPhase_zero : nextPhase 0 = 1 := rfl
@[simp] theorem nextPhase_one : nextPhase 1 = 2 := rfl
@[simp] theorem nextPhase_two : nextPhase 2 = 3 := rfl
@[simp] theorem nextPhase_three : nextPhase 3 = 0 := rfl

theorem phaseCoalition_nonempty (phase : Phase) :
    (phaseCoalition phase).Nonempty := by
  fin_cases phase <;> simp [phaseCoalition, host]

theorem phaseMover_toggle (phase : Phase) :
    phaseCoalition (nextPhase phase) =
      if phaseMover phase ∈ phaseCoalition phase then
        (phaseCoalition phase).erase (phaseMover phase)
      else insert (phaseMover phase) (phaseCoalition phase) := by
  fin_cases phase <;> ext who <;> fin_cases who <;>
    decide

/-- Rational payoff table.  On the host face, the two movers play the
four-cycle.  The host strictly prefers leaving every displayed coalition,
and the observer strictly prefers remaining outside.  Off the host face, a
mover receives `-1` for joining and `0` for staying out. -/
def reward (terminal : {S : Finset Player // S.Nonempty}) : Payoff Player :=
  fun who =>
    if who = observer then
      if observer ∈ terminal.1 then -1 else 0
    else if who = host then
      if host ∈ terminal.1 then -1 else 0
    else if host ∈ terminal.1 then
      if who = first then
        if (first ∈ terminal.1) = (second ∈ terminal.1) then 0 else 1
      else
        if (first ∈ terminal.1) = (second ∈ terminal.1) then 1 else 0
    else if who ∈ terminal.1 then -1 else 0

theorem reward_bound (terminal player) : |reward terminal player| ≤ 1 := by
  unfold reward
  split_ifs <;> norm_num

def root (phase : Phase) : Player → PMF Bool :=
  quittingPureSetRoot (phaseCoalition phase)

def profile (phase : Phase) : (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward (root phase)

def pair (phase : Phase) : QuittingTerminalSemanticPair Player :=
  quittingTerminalSemanticPair reward (profile phase)

def mass (phase : Phase) : QuittingTerminalOutcome Player → ℝ :=
  quittingTerminalOutcomeMass reward (profile phase)

def phaseTerminal (phase : Phase) : {S : Finset Player // S.Nonempty} :=
  ⟨phaseCoalition phase, phaseCoalition_nonempty phase⟩

/-- Prescribed payoff at a phase is its sure-exit payoff. -/
theorem pair_fst (phase : Phase) (who : Player) :
    (pair phase).1 who =
      quittingSetReward reward (phaseCoalition phase) who := by
  exact quittingTerminalPayoff_pureSetRoot
    reward (phaseCoalition phase) who

/-- The all-behavior envelope at a phase is the better membership toggle. -/
theorem pair_snd (phase : Phase) (who : Player) :
    (pair phase).2 who =
      max (quittingSetReward reward (insert who (phaseCoalition phase)) who)
        (quittingSetReward reward ((phaseCoalition phase).erase who) who) := by
  change quittingContinuationBestResponseValue reward (profile phase) who = _
  have hstationary := quittingBestReplyValue_stationary reward (root phase) who
  have hcap := quittingStationaryUnilateralCap_pureSetRoot
    reward (phaseCoalition phase) who
  calc
    quittingContinuationBestResponseValue reward (profile phase) who =
        quittingBestReplyValue reward (profile phase) who := by
      rfl
    _ = quittingStationaryUnilateralCap reward (root phase) who := by
      simpa [profile] using hstationary
    _ = max
        (quittingSetReward reward (insert who (phaseCoalition phase)) who)
        (quittingSetReward reward ((phaseCoalition phase).erase who) who) := by
      simpa [root] using hcap

/-- Exact debt pattern: one unit on the current mover and one on the host. -/
theorem phase_debt (phase : Phase) (who : Player) :
    quittingTerminalSemanticDebt (pair phase) who =
      if who = host then 1 else if who = phaseMover phase then 1 else 0 := by
  rw [quittingTerminalSemanticDebt, pair_fst, pair_snd]
  fin_cases phase <;> fin_cases who <;>
    norm_num [phaseCoalition, phaseMover, reward, quittingSetReward,
      first, second, host, observer, Fin.ext_iff]

/-- The displayed finite family has the strict local debt floor `2`. -/
theorem phase_debtSum (phase : Phase) :
    quittingTerminalSemanticDebtSum (pair phase) = 2 := by
  unfold quittingTerminalSemanticDebtSum
  rw [show (Finset.univ : Finset Player) = {first, second, host, observer} by
    decide]
  simp [phase_debt, first, second, host, observer, phaseMover]
  fin_cases phase <;>
    norm_num [phaseMover, first, second, host, observer, Fin.ext_iff]

theorem rootCoalitionMass_pureSetRoot_self (S : Finset Player) :
    quittingRootCoalitionMass (quittingPureSetRoot S) S = 1 := by
  unfold quittingRootCoalitionMass Math.PMFProduct.coalitionMass
  have hrate : quittingRootQuitRates (quittingPureSetRoot S) =
      fun who => if who ∈ S then 1 else 0 := by
    funext who
    by_cases hwho : who ∈ S <;>
      simp [quittingRootQuitRates, quittingPureSetRoot, quittingSetAction,
        hwho]
  rw [hrate]
  have hleft : ∏ who ∈ S, (if who ∈ S then (1 : ℝ) else 0) = 1 := by
    apply Finset.prod_eq_one
    intro who hwho
    simp [hwho]
  have hright : ∏ who ∈ Sᶜ,
      (1 - if who ∈ S then (1 : ℝ) else 0) = 1 := by
    apply Finset.prod_eq_one
    intro who hwho
    have hnot : who ∉ S := Finset.mem_compl.mp hwho
    simp [hnot]
  rw [hleft, hright, one_mul]

/-- Each displayed semantic point retains a literal terminal atom of mass
one at its own coalition. -/
theorem phase_stageZero_mass_eq_one (phase : Phase) :
    quittingStageCoalitionMass reward (profile phase) 0
        (phaseTerminal phase) = 1 := by
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    quittingLiveMass_zero, one_mul]
  exact rootCoalitionMass_pureSetRoot_self (phaseCoalition phase)

theorem phase_terminalOutcomeMass_eq_one (phase : Phase) :
    mass phase (some (phaseTerminal phase)) = 1 := by
  apply le_antisymm
  · exact terminalOutcomeMass_le_one (mass phase)
      (quittingTerminalOutcomeMass_mem_stdSimplex reward (profile phase))
      (some (phaseTerminal phase))
  · exact (show (1 : ℝ) = quittingStageCoalitionMass reward
        (profile phase) 0 (phaseTerminal phase) by
          symm
          exact phase_stageZero_mass_eq_one phase).trans_le
      (quittingStageCoalitionMass_le_terminalOutcomeMass
        reward (profile phase) 0 (phaseTerminal phase))

/-- Consecutive profiles differ in only the named mover's complete strategy.
This is a literal unilateral reset cycle, not merely a semantic cycle. -/
theorem update_profile_phaseMover (phase : Phase) :
    Function.update (profile phase) (phaseMover phase)
        (profile (nextPhase phase) (phaseMover phase)) =
      profile (nextPhase phase) := by
  funext who time history
  fin_cases phase <;> fin_cases who <;>
    simp [profile, root, phaseCoalition, phaseMover, nextPhase,
      quittingStationaryProfile, StochasticGame.stationaryBehaviorProfile,
      quittingPureSetRoot, quittingSetAction, first, second, host]

/-- Every reset mover gains exactly one unit. -/
theorem phaseMover_payoff_gain (phase : Phase) :
    (pair (nextPhase phase)).1 (phaseMover phase) -
        (pair phase).1 (phaseMover phase) = 1 := by
  rw [pair_fst, pair_fst]
  fin_cases phase
  · change quittingSetReward reward {first, host} first -
      quittingSetReward reward {host} first = 1
    norm_num [reward, quittingSetReward, first, second, host, observer,
      Fin.ext_iff]
  · change quittingSetReward reward {first, second, host} second -
      quittingSetReward reward {first, host} second = 1
    norm_num [reward, quittingSetReward, first, second, host, observer,
      Fin.ext_iff]
  · change quittingSetReward reward {second, host} first -
      quittingSetReward reward {first, second, host} first = 1
    norm_num [reward, quittingSetReward, first, second, host, observer,
      Fin.ext_iff]
  · change quittingSetReward reward {host} second -
      quittingSetReward reward {second, host} second = 1
    norm_num [reward, quittingSetReward, first, second, host, observer,
      Fin.ext_iff]

/-- The reset kills its mover's debt exactly. -/
theorem nextPhase_mover_debt_eq_zero (phase : Phase) :
    quittingTerminalSemanticDebt (pair (nextPhase phase))
        (phaseMover phase) = 0 := by
  fin_cases phase
  · change quittingTerminalSemanticDebt (pair 1) first = 0
    rw [phase_debt, phaseMover_one]
    norm_num [phaseMover, first, second, host, Fin.ext_iff]
  · change quittingTerminalSemanticDebt (pair 2) second = 0
    rw [phase_debt, phaseMover_two]
    norm_num [phaseMover, first, second, host, Fin.ext_iff]
  · change quittingTerminalSemanticDebt (pair 3) first = 0
    rw [phase_debt, phaseMover_three]
    norm_num [phaseMover, first, second, host, Fin.ext_iff]
  · change quittingTerminalSemanticDebt (pair 0) second = 0
    rw [phase_debt, phaseMover_zero]
    norm_num [phaseMover, first, second, host, Fin.ext_iff]

/-- Before the reset, its named mover carries one unit of debt. -/
theorem phaseMover_debt_eq_one (phase : Phase) :
    quittingTerminalSemanticDebt (pair phase) (phaseMover phase) = 1 := by
  rw [phase_debt]
  fin_cases phase <;>
    norm_num [phaseMover, first, second, host, Fin.ext_iff]

/-- The next named mover is genuinely different from the reset owner. -/
theorem nextPhase_mover_ne (phase : Phase) :
    phaseMover (nextPhase phase) ≠ phaseMover phase := by
  fin_cases phase <;> decide

/-- The unit removed from the reset owner reappears on the next mover. -/
theorem nextPhase_nextMover_debt_eq_one (phase : Phase) :
    quittingTerminalSemanticDebt (pair (nextPhase phase))
        (phaseMover (nextPhase phase)) = 1 := by
  exact phaseMover_debt_eq_one (nextPhase phase)

/-- The host's unit debt is a fixed off-owner premium throughout the cycle. -/
theorem host_debt_eq_one (phase : Phase) :
    quittingTerminalSemanticDebt (pair phase) host = 1 := by
  simp [phase_debt]

theorem host_ne_phaseMover (phase : Phase) : host ≠ phaseMover phase := by
  fin_cases phase <;> decide

/-- The first plateau cap is exactly `(1,1,0,0)`. -/
theorem phaseZero_cap :
    (pair 0).2 = ![(1 : ℝ), 1, 0, 0] := by
  funext who
  rw [pair_snd]
  fin_cases who <;>
    norm_num [phaseCoalition, reward, quittingSetReward,
      first, second, host, observer, Fin.ext_iff]

/-- In fact the cap does not change around this cycle.  This is a sharp
failure of the requested cap-changing obstruction package. -/
theorem phase_cap (phase : Phase) :
    (pair phase).2 = ![(1 : ℝ), 1, 0, 0] := by
  funext who
  rw [pair_snd]
  fin_cases phase <;> fin_cases who <;>
    norm_num [phaseCoalition, reward, quittingSetReward,
      first, second, host, observer, Fin.ext_iff]

/-- Four-coordinate Fubini expansion for Boolean product roots. -/
theorem expect_pmfPi_fin4 (sigma : Player → PMF Bool)
    (f : (Player → Bool) → ℝ) :
    expect (pmfPi sigma) f =
      expect (sigma first) (fun a =>
        expect (sigma second) (fun b =>
          expect (sigma host) (fun c =>
            expect (sigma observer) (fun d => f ![a, b, c, d])))) := by
  classical
  have hfirst : Function.update sigma first (sigma first) = sigma :=
    Function.update_eq_self first sigma
  rw [← hfirst, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (sigma first))
  funext a
  have hsecond : Function.update (Function.update sigma first (PMF.pure a))
      second (sigma second) = Function.update sigma first (PMF.pure a) := by
    funext who
    fin_cases who <;> simp [first, second]
  rw [← hsecond, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (sigma second))
  funext b
  have hhost : Function.update
      (Function.update (Function.update sigma first (PMF.pure a))
        second (PMF.pure b)) host (sigma host) =
      Function.update (Function.update sigma first (PMF.pure a))
        second (PMF.pure b) := by
    funext who
    fin_cases who <;> simp [first, second, host]
  rw [← hhost, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (sigma host))
  funext c
  have hobserver : Function.update
      (Function.update
        (Function.update (Function.update sigma first (PMF.pure a))
          second (PMF.pure b)) host (PMF.pure c)) observer (sigma observer) =
      Function.update
        (Function.update (Function.update sigma first (PMF.pure a))
          second (PMF.pure b)) host (PMF.pure c) := by
    funext who
    fin_cases who <;> simp [first, second, host, observer]
  rw [← hobserver, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (sigma observer))
  funext d
  have hpure : Function.update
      (Function.update
        (Function.update (Function.update sigma first (PMF.pure a))
          second (PMF.pure b)) host (PMF.pure c)) observer (PMF.pure d) =
      fun who => PMF.pure (![a, b, c, d] who) := by
    funext who
    fin_cases who <;> simp [first, second, host, observer]
  rw [hpure, pmfPi_pure, expect_pure]

@[simp] theorem quittingQuitters_vec4 (a b c d : Bool) :
    quittingQuitters ![a, b, c, d] =
      (if a then {first} else ∅) ∪
        (if b then {second} else ∅) ∪
          (if c then {host} else ∅) ∪
            (if d then {observer} else ∅) := by
  ext who
  fin_cases who <;> cases a <;> cases b <;> cases c <;> cases d <;>
    simp [quittingQuitters, first, second, host, observer]

/-- Host Quit-minus-Continue is `-1` at every root against the plateau cap. -/
theorem phaseZero_endpointDifference_host (candidate : Player → PMF Bool) :
    quittingRootEndpointDifference reward (pair 0).2 candidate host = -1 := by
  have hfirstSum := quittingRoot_continueProbability_add_quitProbability
    candidate first
  have hsecondSum := quittingRoot_continueProbability_add_quitProbability
    candidate second
  have hobserverSum := quittingRoot_continueProbability_add_quitProbability
    candidate observer
  have hproduct :
      (((candidate first) false).toReal +
          ((candidate first) true).toReal) *
        (((candidate second) false).toReal +
          ((candidate second) true).toReal) *
        (((candidate observer) false).toReal +
          ((candidate observer) true).toReal) = 1 := by
    rw [hfirstSum, hsecondSum, hobserverSum]
    norm_num
  rw [phaseZero_cap]
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4, expect_pmfPi_fin4]
  simp [quittingRootPayoff, reward, first, second, host, observer,
    expect_eq_sum]
  nlinarith [hproduct]

/-- Observer Quit-minus-Continue is `-1` at every root. -/
theorem phaseZero_endpointDifference_observer
    (candidate : Player → PMF Bool) :
    quittingRootEndpointDifference reward (pair 0).2 candidate observer = -1 := by
  have hfirstSum := quittingRoot_continueProbability_add_quitProbability
    candidate first
  have hsecondSum := quittingRoot_continueProbability_add_quitProbability
    candidate second
  have hhostSum := quittingRoot_continueProbability_add_quitProbability
    candidate host
  have hproduct :
      (((candidate first) false).toReal +
          ((candidate first) true).toReal) *
        (((candidate second) false).toReal +
          ((candidate second) true).toReal) *
        (((candidate host) false).toReal +
          ((candidate host) true).toReal) = 1 := by
    rw [hfirstSum, hsecondSum, hhostSum]
    norm_num
  rw [phaseZero_cap]
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4, expect_pmfPi_fin4]
  simp [quittingRootPayoff, reward, first, second, host, observer,
    expect_eq_sum]
  nlinarith [hproduct]

/-- Once host and observer Continue, either mover has strictly negative
Quit-minus-Continue difference. -/
theorem phaseZero_endpointDifference_mover_of_background_continue
    (candidate : Player → PMF Bool) (who : Player)
    (hwho : who = first ∨ who = second)
    (hhost : candidate host = PMF.pure false)
    (hobserver : candidate observer = PMF.pure false) :
    quittingRootEndpointDifference reward (pair 0).2 candidate who < 0 := by
  rcases hwho with rfl | rfl
  · have hsecondSum := quittingRoot_continueProbability_add_quitProbability
      candidate second
    rw [phaseZero_cap]
    unfold quittingRootEndpointDifference quittingRootQuitPayoff
      quittingRootContinuePayoff quittingRootExpectedPayoff
    rw [expect_pmfPi_fin4, expect_pmfPi_fin4]
    simp [quittingRootPayoff, reward, first, second, host, observer,
      hhost, hobserver, expect_eq_sum]
    nlinarith [ENNReal.toReal_nonneg (a := candidate second false)]
  · have hfirstSum := quittingRoot_continueProbability_add_quitProbability
      candidate first
    rw [phaseZero_cap]
    unfold quittingRootEndpointDifference quittingRootQuitPayoff
      quittingRootContinuePayoff quittingRootExpectedPayoff
    rw [expect_pmfPi_fin4, expect_pmfPi_fin4]
    simp [quittingRootPayoff, reward, first, second, host, observer,
      hhost, hobserver, expect_eq_sum]
    nlinarith [ENNReal.toReal_nonneg (a := candidate first false)]

/-- The unchanged phase-zero cap has the singleton exact Nash
correspondence `{all-Continue}`. -/
theorem phaseZero_exactCapNash_forces_allContinue
    (candidate : Player → PMF Bool)
    (hnash : IsεQuittingRootNash reward (pair 0).2 0 candidate) :
    candidate = (quittingAllContinueRoot : Player → PMF Bool) := by
  have hendpoint : IsεQuittingRootEndpointNash reward (pair 0).2 0 candidate :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward (pair 0).2 candidate).mpr hnash
  have forceContinue : ∀ who,
      quittingRootEndpointDifference reward (pair 0).2 candidate who < 0 →
      candidate who = PMF.pure false := by
    intro who hnegative
    have hsupport := (hendpoint who).2
    have hnonneg : 0 ≤ (candidate who true).toReal := ENNReal.toReal_nonneg
    have hzero : (candidate who true).toReal = 0 := by
      exact le_antisymm (by nlinarith) hnonneg
    exact pmf_eq_pure_false_of_apply_true_toReal_eq_zero _ hzero
  have hhost : candidate host = PMF.pure false :=
    forceContinue host (by rw [phaseZero_endpointDifference_host]; norm_num)
  have hobserver : candidate observer = PMF.pure false :=
    forceContinue observer
      (by rw [phaseZero_endpointDifference_observer]; norm_num)
  have hfirst : candidate first = PMF.pure false :=
    forceContinue first
      (phaseZero_endpointDifference_mover_of_background_continue
        candidate first (Or.inl rfl) hhost hobserver)
  have hsecond : candidate second = PMF.pure false :=
    forceContinue second
      (phaseZero_endpointDifference_mover_of_background_continue
        candidate second (Or.inr rfl) hhost hobserver)
  funext who
  fin_cases who
  · simpa [quittingAllContinueRoot, first] using hfirst
  · simpa [quittingAllContinueRoot, second] using hsecond
  · simpa [quittingAllContinueRoot, host] using hhost
  · simpa [quittingAllContinueRoot, observer] using hobserver

theorem phaseZero_allContinue_exactCapNash :
    IsεQuittingRootNash reward (pair 0).2 0
      (quittingAllContinueRoot : Player → PMF Bool) := by
  apply quittingAllContinueRoot_isZeroNash_of_singleton_le
  intro who
  rw [phaseZero_cap]
  fin_cases who <;>
    norm_num [reward, quittingSingletonTerminal,
      first, second, host, observer, Fin.ext_iff]

theorem exactCapNash_forces_allContinue (phase : Phase)
    (candidate : Player → PMF Bool)
    (hnash : IsεQuittingRootNash reward (pair phase).2 0 candidate) :
    candidate = (quittingAllContinueRoot : Player → PMF Bool) := by
  apply phaseZero_exactCapNash_forces_allContinue candidate
  simpa only [phase_cap] using hnash

theorem root_ne_allContinue (phase : Phase) :
    root phase ≠ (quittingAllContinueRoot : Player → PMF Bool) := by
  intro heq
  have hhost := congrFun heq host
  have hmem : host ∈ phaseCoalition phase := by
    fin_cases phase <;> simp [phaseCoalition, host]
  simp [root, quittingPureSetRoot, quittingSetAction, hmem,
    quittingAllContinueRoot] at hhost
  have hprob := congrArg (fun p : PMF Bool => p true) hhost
  norm_num at hprob

/-- The four reset roots themselves are not exact cap--Nash operations.
The only exact root at their common cap is all-Continue. -/
theorem root_not_exactCapNash (phase : Phase) :
    ¬ IsεQuittingRootNash reward (pair phase).2 0 (root phase) := by
  intro hnash
  exact root_ne_allContinue phase
    (exactCapNash_forces_allContinue phase (root phase) hnash)

/-- Every singleton reward is nonpositive. -/
theorem singletonReward_nonpos (who : Player) :
    reward (quittingSingletonTerminal who) who ≤ 0 := by
  fin_cases who <;>
    norm_num [reward, quittingSingletonTerminal,
      first, second, host, observer, Fin.ext_iff]

/-- Hence the table has no positive-punishment escape for any player. -/
theorem punishmentValue_nonpos (who : Player) :
    quittingPunishmentValue reward who ≤ 0 := by
  have h := quittingPunishmentValue_le_max_solo reward who
  have hsingleton : quittingSetReward reward {who} who ≤ 0 := by
    fin_cases who <;>
      norm_num [reward, quittingSetReward,
        first, second, host, observer, Fin.ext_iff]
  rw [max_eq_right hsingleton] at h
  exact h

/-- A positive-gap deletion certificate is impossible: deleting any one of
the four players leaves a three-player quitting game, whose uniform
equilibrium theorem contradicts the retained exploitability gap. -/
theorem no_exactPlayerDeletionAtPositiveGap (owner : Player) (gap : ℝ)
    (hgap : 0 < gap) :
    ¬ HasQuittingExactPlayerDeletionAtGap reward owner gap := by
  rintro ⟨_hnonempty, hreducedGap, _hcard⟩
  let reducedReward := quittingDeletePlayerReward reward owner
  have hno : ¬ ∃ payoff : Payoff (QuittingDeletedPlayer owner),
      (quittingGame reducedReward).IsUniformEquilibriumPayoff none payoff :=
    (not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap
      reducedReward).2 ⟨gap, hgap, hreducedGap⟩
  exact hno
    (quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_three
      (by
        rw [Fintype.card_subtype_compl (fun who : Player => who = owner)]
        norm_num)
      reducedReward)

/-! ## The sharp global fence -/

/-- The literal all-Continue profile, written as the empty pure-set root. -/
def zeroProfile : (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward (quittingPureSetRoot ∅)

def zeroPair : QuittingTerminalSemanticPair Player :=
  quittingTerminalSemanticPair reward zeroProfile

/-- The empty set is a sure-exit set because every solo payoff is negative. -/
theorem empty_isQuittingSureExitSet :
    IsQuittingSureExitSet reward (∅ : Finset Player) := by
  rw [isQuittingSureExitSet_empty_iff]
  intro who
  fin_cases who <;>
    norm_num [quittingSoloReward, reward,
      first, second, host, observer, Fin.ext_iff]

/-- Consequently this table already has a literal exact terminal Nash
profile: all players Continue forever. -/
theorem zeroProfile_isExactTerminalNash :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0 zeroProfile := by
  exact (isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet
    reward ∅).2 empty_isQuittingSureExitSet

theorem zeroPair_fst (who : Player) : (zeroPair).1 who = 0 := by
  exact quittingTerminalPayoff_pureSetRoot reward ∅ who

theorem zeroPair_snd (who : Player) : (zeroPair).2 who = 0 := by
  change quittingContinuationBestResponseValue reward zeroProfile who = 0
  have hstationary := quittingBestReplyValue_stationary
    reward (quittingPureSetRoot (∅ : Finset Player)) who
  have hcap := quittingStationaryUnilateralCap_pureSetRoot
    reward (∅ : Finset Player) who
  calc
    quittingContinuationBestResponseValue reward zeroProfile who =
        quittingBestReplyValue reward zeroProfile who := by
      rfl
    _ = quittingStationaryUnilateralCap reward
        (quittingPureSetRoot (∅ : Finset Player)) who := by
      simpa [zeroProfile] using hstationary
    _ = max (quittingSetReward reward {who} who) 0 := by
      simpa using hcap
    _ = 0 := by
      rw [max_eq_right]
      fin_cases who <;>
        norm_num [reward, quittingSetReward,
          first, second, host, observer, Fin.ext_iff]

/-- The exact equilibrium is a literal zero-debt semantic carrier point.
Thus the full semantic minimum is zero; the positive value `2` above is only
a floor on the four displayed cyclic profiles. -/
theorem zeroPair_debt_eq_zero (who : Player) :
    quittingTerminalSemanticDebt zeroPair who = 0 := by
  rw [quittingTerminalSemanticDebt, zeroPair_fst, zeroPair_snd]
  norm_num

theorem zeroPair_debtSum_eq_zero :
    quittingTerminalSemanticDebtSum zeroPair = 0 := by
  unfold quittingTerminalSemanticDebtSum
  simp [zeroPair_debt_eq_zero]

/-- Complete finite certificate.  This is intentionally local: the first
conjunct is only the four displayed profiles, not the full semantic carrier. -/
theorem cyclicPlateau_finiteCertificate :
    (∀ phase, quittingTerminalSemanticDebtSum (pair phase) = 2) ∧
      (∀ phase,
        quittingTerminalSemanticDebt (pair (nextPhase phase))
          (phaseMover phase) = 0 ∧
        (pair (nextPhase phase)).1 (phaseMover phase) -
          (pair phase).1 (phaseMover phase) = 1 ∧
        quittingTerminalSemanticDebt (pair phase) host = 1 ∧
        host ≠ phaseMover phase) ∧
      (∀ candidate,
        IsεQuittingRootNash reward (pair 0).2 0 candidate →
          candidate = (quittingAllContinueRoot : Player → PMF Bool)) ∧
      (∀ who, quittingPunishmentValue reward who ≤ 0) := by
  exact ⟨phase_debtSum, fun phase =>
    ⟨nextPhase_mover_debt_eq_zero phase,
      phaseMover_payoff_gain phase, host_debt_eq_one phase,
      host_ne_phaseMover phase⟩,
    phaseZero_exactCapNash_forces_allContinue, punishmentValue_nonpos⟩

end FourPlayerCyclicPlateauCandidate
end GameTheory
