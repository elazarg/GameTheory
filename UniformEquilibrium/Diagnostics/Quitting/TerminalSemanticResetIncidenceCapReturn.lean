/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceReturn
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeStrictToggleOrbit
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticMinimumAggregateSurplusConsumer
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauMarkedExitNashificationRegression

/-!
# What fixed-law incidence produces at a reset-face minimizer

Keeping the complete terminal law through reset-face minimization repairs one
important provenance loss: a positive opponent-incidence coordinate still
contains a positive-mass absorbing coalition, and counterexample instability
gives that very coalition a strict membership toggle.

There is also a sharp dynamic dispatch.  If the returned cap fails to dominate
some singleton reward, an exact cap--Nash root can be chosen with both positive
absorption and positive survival.  Prefixing by it strictly lowers reset-face
debt while retaining positive same-law incidence.  Positive survival is not an
extra selection hypothesis: a zero-survival cap--Nash prefix would have zero
debt, contradicting the positive global minimum.

The other branch is exactly the cap-dominating all-Continue face.  Positive
incidence and even a strict toggle on a positive-mass coalition do not exclude
that face.  The final regression records this local independence explicitly.
The minimum aggregate-surplus theorem supplies a further static source
certificate, but its selected outcome need not be the incidence atom; no
chronological compiler is asserted here.
-/

noncomputable section

namespace GameTheory

open Set QuittingSureSetOwnerRepair
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The law coordinate of every joint semantic/law carrier point remains a
probability vector. -/
theorem terminalSemanticLawCarrier_mass_mem_stdSimplex
    (point : QuittingTerminalSemanticLawPoint ι)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward) :
    point.2 ∈ stdSimplex ℝ (QuittingTerminalOutcome ι) := by
  let lawSimplex : Set (QuittingTerminalSemanticLawPoint ι) :=
    Set.univ ×ˢ stdSimplex ℝ (QuittingTerminalOutcome ι)
  have hclosed : IsClosed lawSimplex :=
    isClosed_univ.prod (isClosed_stdSimplex ℝ (QuittingTerminalOutcome ι))
  have hsubset : quittingAttainableTerminalSemanticLawPoints reward ⊆
      lawSimplex := by
    rintro point ⟨profile, rfl⟩
    exact ⟨Set.mem_univ _,
      quittingTerminalOutcomeMass_mem_stdSimplex reward profile⟩
  exact (closure_minimal hsubset hclosed hpoint).2

/-- A positive opponent-incidence coordinate contains a concrete positive-law
terminal atom carrying the displayed opponent. -/
theorem exists_positiveMass_terminal_of_opponentIncidence
    (owner other : ι) (mass : QuittingTerminalOutcome ι → ℝ)
    (hmass : mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι))
    (hincidence : 0 <
      quittingTerminalOpponentIncidenceMass owner other mass) :
    ∃ terminal : {S : Finset ι // S.Nonempty},
      other ∈ terminal.val ∧ other ≠ owner ∧ 0 < mass (some terminal) := by
  let terminals := Finset.univ.filter
    (fun terminal : {S : Finset ι // S.Nonempty} =>
      other ∈ terminal.val ∧ other ≠ owner)
  have hnonneg : ∀ terminal ∈ terminals, 0 ≤ mass (some terminal) := by
    intro terminal _
    exact hmass.1 (some terminal)
  have hsum : 0 < ∑ terminal ∈ terminals, mass (some terminal) := by
    simpa only [terminals, quittingTerminalOpponentIncidenceMass] using
      hincidence
  obtain ⟨terminal, hterminal, hpositive⟩ :=
    (Finset.sum_pos_iff_of_nonneg hnonneg).mp hsum
  have hfilter := (Finset.mem_filter.mp hterminal).2
  exact ⟨terminal, hfilter.1, hfilter.2, hpositive⟩

/-- In a counterexample regime the incidence atom itself has a strict static
membership-toggle blocker. -/
theorem QuittingCounterexampleRegime.exists_supportedStrictToggle_of_incidence
    (regime : QuittingCounterexampleRegime reward)
    (owner other : ι) (mass : QuittingTerminalOutcome ι → ℝ)
    (hmass : mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι))
    (hincidence : 0 <
      quittingTerminalOpponentIncidenceMass owner other mass) :
    ∃ terminal : {S : Finset ι // S.Nonempty},
      other ∈ terminal.val ∧ 0 < mass (some terminal) ∧
        ((∃ member ∈ terminal.val,
            quittingSetReward reward terminal.val member <
              quittingSetReward reward (terminal.val.erase member) member) ∨
          ∃ outsider ∉ terminal.val,
            quittingSetReward reward terminal.val outsider <
              quittingSetReward reward
                (insert outsider terminal.val) outsider) := by
  obtain ⟨terminal, hother, _hne, hmassPositive⟩ :=
    exists_positiveMass_terminal_of_opponentIncidence
      owner other mass hmass hincidence
  exact ⟨terminal, hother, hmassPositive,
    regime.terminalCoalition_has_strictToggle terminal⟩

/-- **Fixed-law reset dispatch.**

The returned reset-face point retains the whole law, the positive displayed
incidence, and the opposite-face transfer.  Its incidence atom has a strict
counterexample toggle.  Dynamically, either an absorbing, positive-survival
cap--Nash prefix strictly lowers debt and retains positive incidence, or the
cap correspondence contains the all-Continue fixed point. -/
theorem QuittingCounterexampleRegime.exists_fixedLaw_resetFace_dispatch
    (regime : QuittingCounterexampleRegime reward)
    (source target : QuittingTerminalSemanticPair ι)
    (mass : QuittingTerminalOutcome ι → ℝ)
    (owner other : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (hsourcePositive : 0 < quittingTerminalSemanticDebtSum source)
    (htarget : (target, mass) ∈ quittingTerminalSemanticLawCarrier reward)
    (hreset : quittingTerminalSemanticDebt target owner = 0)
    (hincidence : 0 <
      quittingTerminalOpponentIncidenceMass owner other mass) :
    ∃ returned : QuittingTerminalSemanticPair ι,
      (returned, mass) ∈ quittingTerminalSemanticLawCarrier reward ∧
      returned ∈ quittingTerminalSemanticCarrier reward ∧
      quittingTerminalSemanticDebt returned owner = 0 ∧
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum returned ∧
      quittingTerminalSemanticDebtSum returned ≤
        quittingTerminalSemanticDebtSum target ∧
      quittingTerminalSemanticDebt source owner ≤
        ∑ player ∈ Finset.univ.erase owner,
          quittingTerminalSemanticDebtChange source returned player ∧
      (∃ terminal : {S : Finset ι // S.Nonempty},
        other ∈ terminal.val ∧ 0 < mass (some terminal) ∧
          ((∃ member ∈ terminal.val,
              quittingSetReward reward terminal.val member <
                quittingSetReward reward (terminal.val.erase member) member) ∨
            ∃ outsider ∉ terminal.val,
              quittingSetReward reward terminal.val outsider <
                quittingSetReward reward
                  (insert outsider terminal.val) outsider)) ∧
      ((∃ root : ι → PMF Bool,
          IsεQuittingRootNash reward returned.2 0 root ∧
          0 < quittingRootAbsorptionMass root ∧
          0 < quittingStationaryContinueMass root ∧
          quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPrefix reward root returned) <
            quittingTerminalSemanticDebtSum returned ∧
          (quittingTerminalSemanticPrefix reward root returned,
              quittingTerminalOutcomeLawPrefix root mass) ∈
            quittingTerminalSemanticLawCarrier reward ∧
          quittingTerminalSemanticDebt
              (quittingTerminalSemanticPrefix reward root returned) owner = 0 ∧
          0 < quittingTerminalOpponentIncidenceMass owner other
            (quittingTerminalOutcomeLawPrefix root mass)) ∨
        (IsεQuittingRootNash reward returned.2 0
            (quittingAllContinueRoot : ι → PMF Bool) ∧
          quittingTerminalSemanticPrefix reward quittingAllContinueRoot
            returned = returned)) := by
  obtain ⟨returned, hjoint, hreturnedCarrier, hreturnedReset, hsourceLe,
      hreturnedLe, _hmoment, _htransferEq, htransfer⟩ :=
    exists_fixedLaw_resetFace_minimizer
      reward source target mass owner hM hreward hminimum htarget hreset
  have hmassSimplex : mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι) :=
    terminalSemanticLawCarrier_mass_mem_stdSimplex
      (point := (returned, mass)) hjoint
  have htoggle := regime.exists_supportedStrictToggle_of_incidence
    owner other mass hmassSimplex hincidence
  have hreturnedPositive : 0 < quittingTerminalSemanticDebtSum returned :=
    hsourcePositive.trans_le hsourceLe
  have hdispatch := resetExcursion_absorbingReturn_or_allContinue_capFace
    (reward := reward) source returned owner hM hreward hminimum
      hreturnedCarrier hreturnedReset hreturnedPositive
  refine ⟨returned, hjoint, hreturnedCarrier, hreturnedReset, hsourceLe,
    hreturnedLe, htransfer, htoggle, ?_⟩
  rcases hdispatch with hreturn | hcap
  · left
    obtain ⟨root, hnash, habsorbs, hstrict, hprefixedReset, _htransfer⟩ :=
      hreturn
    let prefixed := quittingTerminalSemanticPrefix reward root returned
    let prefixedMass := quittingTerminalOutcomeLawPrefix root mass
    have hprefixedCarrier : prefixed ∈
        quittingTerminalSemanticCarrier reward :=
      quittingTerminalSemanticPrefix_mem_carrier
        reward root returned hM hreward hreturnedCarrier
    have hprefixedLower : quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum prefixed :=
      hminimum prefixed hprefixedCarrier
    have hscale : quittingTerminalSemanticDebtSum prefixed =
        quittingStationaryContinueMass root *
          quittingTerminalSemanticDebtSum returned :=
      quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_of_capNash
        (reward := reward) returned root hnash
    have hcontinueNonneg : 0 ≤ quittingStationaryContinueMass root :=
      quittingStationaryContinueMass_nonneg root
    have hcontinue : 0 < quittingStationaryContinueMass root := by
      nlinarith
    have hprefixedJoint : (prefixed, prefixedMass) ∈
        quittingTerminalSemanticLawCarrier reward := by
      exact quittingTerminalSemanticLawPrefix_mem_carrier
        reward root (returned, mass) hM hreward hjoint
    have hprefixedIncidence : 0 <
        quittingTerminalOpponentIncidenceMass owner other prefixedMass :=
      positive_incidence_lawPrefix_of_positive_continueMass
        owner other root mass hcontinue hincidence
    exact ⟨root, hnash, habsorbs, hcontinue, hstrict,
      hprefixedJoint, hprefixedReset, hprefixedIncidence⟩
  · exact Or.inr hcap

/-- Aggregate surplus can be carried alongside the fixed-law dispatch at the
minimum source.  The conclusion deliberately keeps the source outcome and the
reset incidence atom separate: the current theory does not identify them. -/
theorem QuittingCounterexampleRegime.exists_fixedLaw_dispatch_and_sourceAggregate
    (regime : QuittingCounterexampleRegime reward)
    (source target : QuittingTerminalSemanticPair ι)
    (mass : QuittingTerminalOutcome ι → ℝ)
    (owner other : ι) (players : Finset ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (hsourcePositive : 0 < quittingTerminalSemanticDebtSum source)
    (htarget : (target, mass) ∈ quittingTerminalSemanticLawCarrier reward)
    (hreset : quittingTerminalSemanticDebt target owner = 0)
    (hincidence : 0 <
      quittingTerminalOpponentIncidenceMass owner other mass) :
    (∃ returned,
      (returned, mass) ∈ quittingTerminalSemanticLawCarrier reward ∧
      quittingTerminalSemanticDebt returned owner = 0 ∧
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum returned) ∧
    ((∑ who ∈ players,
        (quittingTerminalSemanticDebtSum source -
          quittingTerminalSemanticDebt source who)) ≤
        ∑ who ∈ players,
          (0 - reward (quittingSingletonTerminal who) who) ∨
      ∃ terminal : {S : Finset ι // S.Nonempty},
        (∑ who ∈ players,
            (quittingTerminalSemanticDebtSum source -
              quittingTerminalSemanticDebt source who)) ≤
            ∑ who ∈ players,
              (reward terminal who -
                reward (quittingSingletonTerminal who) who) ∧
          ((∃ member ∈ terminal.val,
              quittingSetReward reward terminal.val member <
                quittingSetReward reward (terminal.val.erase member) member) ∨
            ∃ outsider ∉ terminal.val,
              quittingSetReward reward terminal.val outsider <
                quittingSetReward reward
                  (insert outsider terminal.val) outsider)) := by
  obtain ⟨returned, hjoint, _hcarrier, hresetReturned, hsourceLe,
      _hreturnedLe, _htransfer, _htoggle, _hdispatch⟩ :=
    regime.exists_fixedLaw_resetFace_dispatch source target mass owner other
      hM hreward hminimum hsourcePositive htarget hreset hincidence
  exact ⟨⟨returned, hjoint, hresetReturned, hsourceLe⟩,
    regime.exists_neverBudget_or_blockedCoalition_exact
      source players hM hreward hsource hminimum hsourcePositive⟩

/-! ## Sharp local regression for the cap-dominating branch -/

namespace QuittingResetIncidenceCapRegression

open Math.Probability Math.PMFProduct

/-- Reuse the marked two-player reward table. -/
abbrev regressionReward :=
  QuittingMarkedExitNashificationRegression.reward

/-- An arbitrary literal all-Continue continuation; the first-stage collision
absorbs surely, so none of its later coordinates affect the regression. -/
def continuation : (quittingGame regressionReward).BehaviorProfile :=
  fun _player _time _history => PMF.pure false

/-- Both players Quit surely at the literal first stage. -/
abbrev collisionRoot : Bool → PMF Bool :=
  QuittingMarkedExitNashificationRegression.markedCollisionRoot

/-- The executable collision profile. -/
def profile : (quittingGame regressionReward).BehaviorProfile :=
  quittingRootThenContinuationProfile regressionReward collisionRoot continuation

/-- Its exact terminal semantic pair. -/
def pair : QuittingTerminalSemanticPair Bool :=
  quittingTerminalSemanticPair regressionReward profile

/-- Its exact complete terminal-outcome law. -/
def mass : QuittingTerminalOutcome Bool → ℝ :=
  quittingTerminalOutcomeMass regressionReward profile

theorem reward_bound (terminal player) :
    |regressionReward terminal player| ≤ 1 := by
  by_cases hfalse : false ∈ terminal.1 <;>
    by_cases htrue : true ∈ terminal.1 <;>
      cases player <;>
        simp [regressionReward,
          QuittingMarkedExitNashificationRegression.reward, hfalse, htrue]

/-- The literal collision has prescribed payoff `(1,0)` and behavioral
envelope `(1,1)`. -/
theorem pair_coordinates :
    pair.1 false = 1 ∧ pair.1 true = 0 ∧
      pair.2 false = 1 ∧ pair.2 true = 1 := by
  have hprefix := quittingTerminalSemanticPair_rootThenContinuation
    regressionReward collisionRoot continuation (M := 1) (by norm_num)
      reward_bound
  change quittingTerminalSemanticPair regressionReward profile =
      quittingTerminalSemanticPrefix regressionReward collisionRoot
        (quittingTerminalSemanticPair regressionReward continuation) at hprefix
  rw [show pair = quittingTerminalSemanticPrefix regressionReward collisionRoot
      (quittingTerminalSemanticPair regressionReward continuation) by
    exact hprefix]
  simp only [quittingTerminalSemanticPrefix]
  constructor
  · rw [quittingRootSuccessorPayoff_eq_endpointMix]
    unfold quittingRootQuitPayoff quittingRootContinuePayoff
      quittingRootExpectedPayoff
    rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
    norm_num [collisionRoot,
      QuittingMarkedExitNashificationRegression.markedCollisionRoot,
      quittingRootPayoff, regressionReward,
      QuittingMarkedExitNashificationRegression.reward]
  constructor
  · rw [quittingRootSuccessorPayoff_eq_endpointMix]
    unfold quittingRootQuitPayoff quittingRootContinuePayoff
      quittingRootExpectedPayoff
    rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
    norm_num [collisionRoot,
      QuittingMarkedExitNashificationRegression.markedCollisionRoot,
      quittingRootPayoff, regressionReward,
      QuittingMarkedExitNashificationRegression.reward]
  constructor
  · unfold quittingRootQuitPayoff quittingRootContinuePayoff
      quittingRootExpectedPayoff
    rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool,
      QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
    norm_num [collisionRoot,
      QuittingMarkedExitNashificationRegression.markedCollisionRoot,
      quittingRootPayoff, regressionReward,
      QuittingMarkedExitNashificationRegression.reward]
  · unfold quittingRootQuitPayoff quittingRootContinuePayoff
      quittingRootExpectedPayoff
    rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool,
      QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
    norm_num [collisionRoot,
      QuittingMarkedExitNashificationRegression.markedCollisionRoot,
      quittingRootPayoff, regressionReward,
      QuittingMarkedExitNashificationRegression.reward]

/-- The collision pair is a literal joint semantic/law carrier point. -/
theorem pair_mass_mem_carrier :
    (pair, mass) ∈ quittingTerminalSemanticLawCarrier regressionReward := by
  exact quittingTerminalSemanticLawPoint_mem_carrier regressionReward profile

/-- The marked coordinate is reset, while the other coordinate carries one
unit of debt. -/
theorem reset_and_positiveDebt :
    quittingTerminalSemanticDebt pair false = 0 ∧
      quittingTerminalSemanticDebt pair true = 1 ∧
      quittingTerminalSemanticDebtSum pair = 1 := by
  rcases pair_coordinates with ⟨huFalse, huTrue, hbFalse, hbTrue⟩
  constructor
  · simp [quittingTerminalSemanticDebt, huFalse, hbFalse]
  constructor
  · simp [quittingTerminalSemanticDebt, huTrue, hbTrue]
  · simp [quittingTerminalSemanticDebtSum,
      quittingTerminalSemanticDebt, huFalse, huTrue, hbFalse, hbTrue]

/-- The same literal law gives the marked player unit incidence of the other
player. -/
theorem opponentIncidence_eq_one :
    quittingTerminalOpponentIncidenceMass false true mass = 1 := by
  have hlaw : mass = quittingTerminalOutcomeLawPrefix collisionRoot
      (quittingTerminalOutcomeMass regressionReward continuation) := by
    exact (quittingTerminalOutcomeLawPrefix_outcomeMass
      regressionReward collisionRoot continuation).symm
  rw [hlaw, quittingTerminalOpponentIncidenceMass_lawPrefix]
  let fullTerminal : {S : Finset Bool // S.Nonempty} :=
    ⟨Finset.univ, by simp⟩
  have hfilter : Finset.univ.filter
      (fun terminal : {S : Finset Bool // S.Nonempty} =>
        true ∈ terminal.val ∧ true ≠ false) =
      {quittingSingletonTerminal true, fullTerminal} := by
    decide
  unfold quittingRootOpponentIncidenceMass
  rw [hfilter]
  have hne : quittingSingletonTerminal true ≠ fullTerminal := by
    decide
  rw [Finset.sum_insert (by simpa using hne), Finset.sum_singleton]
  have hsingle : quittingRootCoalitionMass collisionRoot
      (quittingSingletonTerminal true).val = 0 := by
    change quittingRootCoalitionMass collisionRoot {true} = 0
    unfold quittingRootCoalitionMass
    have hcomp : ({true} : Finset Bool)ᶜ = {false} := by decide
    rw [coalitionMass, hcomp]
    norm_num [collisionRoot,
      QuittingMarkedExitNashificationRegression.markedCollisionRoot,
      quittingRootQuitRates]
  have hfull : quittingRootCoalitionMass collisionRoot fullTerminal.val = 1 := by
    change quittingRootCoalitionMass collisionRoot Finset.univ = 1
    unfold quittingRootCoalitionMass
    have hcomp : (Finset.univ : Finset Bool)ᶜ = ∅ := by decide
    rw [coalitionMass, hcomp]
    norm_num [collisionRoot,
      QuittingMarkedExitNashificationRegression.markedCollisionRoot,
      quittingRootQuitRates]
  have hcontinue : quittingStationaryContinueMass collisionRoot = 0 := by
    norm_num [collisionRoot,
    QuittingMarkedExitNashificationRegression.markedCollisionRoot,
      quittingStationaryContinueMass, quittingAllContinueAction]
  rw [hsingle, hfull, hcontinue]
  norm_num

/-- The positive-mass collision has a strict toggle: player `true` gains by
leaving it. -/
theorem collision_has_strict_leave_toggle :
    quittingSetReward regressionReward (Finset.univ : Finset Bool) true <
      quittingSetReward regressionReward
        ((Finset.univ : Finset Bool).erase true) true := by
  norm_num [quittingSetReward, regressionReward,
    QuittingMarkedExitNashificationRegression.reward]

/-- Nevertheless every singleton own reward is dominated by the collision
pair's cap.  Thus incidence plus a supported strict toggle does not force a
singleton cap violation. -/
theorem singleton_le_cap (who : Bool) :
    regressionReward (quittingSingletonTerminal who) who ≤ pair.2 who := by
  rcases pair_coordinates with ⟨_huFalse, _huTrue, hbFalse, hbTrue⟩
  cases who
  · rw [hbFalse]
    norm_num [regressionReward,
      QuittingMarkedExitNashificationRegression.reward,
      quittingSingletonTerminal]
  · rw [hbTrue]
    norm_num [regressionReward,
      QuittingMarkedExitNashificationRegression.reward,
      quittingSingletonTerminal]

/-- Against the displayed cap, player `true` gets zero from Quit at every
root. -/
theorem cap_quitPayoff_true (root : Bool → PMF Bool) :
    quittingRootQuitPayoff regressionReward pair.2 root true = 0 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, regressionReward,
    QuittingMarkedExitNashificationRegression.reward]

/-- Against the displayed cap, player `true` gets one from Continue at every
root. -/
theorem cap_continuePayoff_true (root : Bool → PMF Bool) :
    quittingRootContinuePayoff regressionReward pair.2 root true = 1 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
  have hsum := quittingRoot_continueProbability_add_quitProbability root false
  have hc : (root false false).toReal = 1 - (root false true).toReal := by
    linarith
  have hb := pair_coordinates.2.2.2
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, regressionReward,
    QuittingMarkedExitNashificationRegression.reward, hc, hb]

/-- Player `true` therefore strictly prefers Continue, independently of the
other marginal. -/
theorem cap_endpointDifference_true (root : Bool → PMF Bool) :
    quittingRootEndpointDifference regressionReward pair.2 root true = -1 := by
  rw [quittingRootEndpointDifference, cap_quitPayoff_true,
    cap_continuePayoff_true]
  norm_num

/-- Once player `true` Continues purely, player `false` strictly prefers
Continue by two units against the displayed cap. -/
theorem cap_endpointDifference_false_of_true_continue
    (root : Bool → PMF Bool) (htrue : root true = PMF.pure false) :
    quittingRootEndpointDifference regressionReward pair.2 root false = -2 := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool,
    QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
  have hb := pair_coordinates.2.2.1
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, regressionReward,
    QuittingMarkedExitNashificationRegression.reward, htrue, hb]
  norm_num

/-- **Exact cap no-go.**  Every exact cap--Nash root is all-Continue.  Thus
the positive same-law incidence and its supported strict toggle produce no
absorbing cap selection in this fully co-realized local example. -/
theorem exact_capNash_forces_allContinue
    (root : Bool → PMF Bool)
    (hnash : IsεQuittingRootNash regressionReward pair.2 0 root) :
    root = (quittingAllContinueRoot : Bool → PMF Bool) := by
  have hendpoint : IsεQuittingRootEndpointNash
      regressionReward pair.2 0 root :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      regressionReward pair.2 root).mpr hnash
  have htrueZero : (root true true).toReal = 0 := by
    have h := (hendpoint true).2
    rw [cap_endpointDifference_true] at h
    exact le_antisymm (by linarith) ENNReal.toReal_nonneg
  have htrue : root true = PMF.pure false :=
    pmf_eq_pure_false_of_apply_true_toReal_eq_zero (root true) htrueZero
  have hfalseDiff := cap_endpointDifference_false_of_true_continue root htrue
  have hfalseZero : (root false true).toReal = 0 := by
    have h := (hendpoint false).2
    rw [hfalseDiff] at h
    exact le_antisymm (by linarith) ENNReal.toReal_nonneg
  have hfalse : root false = PMF.pure false :=
    pmf_eq_pure_false_of_apply_true_toReal_eq_zero (root false) hfalseZero
  funext who
  cases who
  · simpa [quittingAllContinueRoot] using hfalse
  · simpa [quittingAllContinueRoot] using htrue

/-- Consequently no exact cap root supplies a zero-tolerance return from any
abstract source with total debt below the collision pair's unit debt. -/
theorem no_zeroTolerance_capNashReturnSelection
    (source : QuittingTerminalSemanticPair Bool)
    (hsource : quittingTerminalSemanticDebtSum source < 1) :
    ¬ ∃ root : Bool → PMF Bool,
      IsQuittingCapNashResetReturnSelection
        (reward := regressionReward) source pair root 0 := by
  rintro ⟨root, hnash, hcharge⟩
  have hroot := exact_capNash_forces_allContinue root hnash
  rw [hroot, quittingRootAbsorptionMass_allContinueRoot] at hcharge
  have hdebt := reset_and_positiveDebt.2.2
  rw [hdebt] at hcharge
  norm_num at hcharge
  linarith

/-- The complete local obstruction in one statement. -/
theorem positive_incidence_and_toggle_but_only_allContinue_capNash :
    (pair, mass) ∈ quittingTerminalSemanticLawCarrier regressionReward ∧
      quittingTerminalSemanticDebt pair false = 0 ∧
      quittingTerminalSemanticDebtSum pair = 1 ∧
      quittingTerminalOpponentIncidenceMass false true mass = 1 ∧
      quittingSetReward regressionReward (Finset.univ : Finset Bool) true <
        quittingSetReward regressionReward
          ((Finset.univ : Finset Bool).erase true) true ∧
      (∀ who, regressionReward (quittingSingletonTerminal who) who ≤
        pair.2 who) ∧
      ∀ root : Bool → PMF Bool,
        IsεQuittingRootNash regressionReward pair.2 0 root →
          root = (quittingAllContinueRoot : Bool → PMF Bool) := by
  exact ⟨pair_mass_mem_carrier, reset_and_positiveDebt.1,
    reset_and_positiveDebt.2.2, opponentIncidence_eq_one,
    collision_has_strict_leave_toggle, singleton_le_cap,
    exact_capNash_forces_allContinue⟩

end QuittingResetIncidenceCapRegression

end GameTheory
