/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.PublicCoinSelectionPhase
import GameTheory.Concepts.Stochastic.PublicFixedPrefixAccounting
import GameTheory.Concepts.Stochastic.FiniteChildAdaptivePotentialFamily

/-!
# Fixed-depth adaptive-potential splice data

This file assembles the concrete profile and potential objects for a
fixed-depth deviation-safe public selection phase followed by one of finitely
many child adaptive-potential systems.

The root expectations after the selection depth disintegrate into
expectations of the selected raw child systems, including under arbitrary
unilateral deviations.  The finite selector charge and averaged child
charges are combined into one explicit Cesàro budget.  The final constructor
returns an `AdaptivePotentialSystemAt` for the parent target.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability Math.ProbabilityMassFunction

variable {ι Child : Type} {G : StochasticGame ι}

/-- Use a prefix potential before a fixed depth and the selected child's
local potential afterwards. -/
def fixedDepthHistoryPotential (fuel : ℕ)
    (prefixPotential : G.HistoryPotential)
    (childPotential : G.Hist fuel → G.HistoryPotential) :
    G.HistoryPotential :=
  fun time history =>
    if htime : time < fuel then
      prefixPotential time history
    else
      let hle : fuel ≤ time := Nat.le_of_not_gt htime
      let base := G.terminalPrefixLE hle history
      let suffix := G.terminalSuffixLE hle history
      childPotential base (time - fuel) suffix

theorem fixedDepthHistoryPotential_before
    {fuel time : ℕ} (prefixPotential : G.HistoryPotential)
    (childPotential : G.Hist fuel → G.HistoryPotential)
    (htime : time < fuel) (history : G.Hist time) :
    G.fixedDepthHistoryPotential fuel prefixPotential childPotential
        time history =
      prefixPotential time history := by
  simp [fixedDepthHistoryPotential, htime]

theorem fixedDepthHistoryPotential_appendHist
    {fuel suffixLength : ℕ}
    (prefixPotential : G.HistoryPotential)
    (childPotential : G.Hist fuel → G.HistoryPotential)
    (base : G.Hist fuel) (suffix : G.Hist suffixLength)
    (hstart : suffix.StartsAt base.2) :
    G.fixedDepthHistoryPotential fuel prefixPotential childPotential
        (fuel + suffixLength) (G.appendHist base suffix) =
      childPotential base suffixLength suffix := by
  rw [fixedDepthHistoryPotential]
  simp only [Nat.not_lt.mpr (Nat.le_add_right fuel suffixLength),
    ↓reduceDIte]
  congr 2
  · exact G.terminalPrefixLE_appendHist base suffix hstart
  · exact Nat.add_sub_cancel_left fuel suffixLength
  · exact G.terminalSuffixLE_appendHist_heq base suffix

/-- Child terminal targets supplied by the three initial adaptive
potentials.  They need not coincide, so they are kept separate. -/
def FiniteChildAdaptivePotentialFamily.lowerTerminalTarget
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] [Fintype Child]
    {entry : Child → G.State} {target : Child → Payoff ι}
    {error : ℝ}
    (family :
      G.FiniteChildAdaptivePotentialFamily entry target error) :
    Child → ι → ℝ :=
  fun child who =>
    (family.system child).lowerPotential who
      0 (G.emptyHist (entry child))

def FiniteChildAdaptivePotentialFamily.upperTerminalTarget
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] [Fintype Child]
    {entry : Child → G.State} {target : Child → Payoff ι}
    {error : ℝ}
    (family :
      G.FiniteChildAdaptivePotentialFamily entry target error) :
    Child → ι → ℝ :=
  fun child who =>
    (family.system child).upperPotential who
      0 (G.emptyHist (entry child))

def FiniteChildAdaptivePotentialFamily.deviationTerminalTarget
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] [Fintype Child]
    {entry : Child → G.State} {target : Child → Payoff ι}
    {error : ℝ}
    (family :
      G.FiniteChildAdaptivePotentialFamily entry target error) :
    Child → ι → ℝ :=
  fun child who =>
    (family.system child).deviationPotential who
      0 (G.emptyHist (entry child))

/-- Concrete fixed-depth profile and the three spliced potentials. -/
structure FixedDepthAdaptivePotentialSplice
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] [Fintype Child]
    {entry : Child → G.State} {target : Child → Payoff ι}
    {childError : ℝ}
    (selector : DeviationSafePublicCoinSelector G Child)
    (family :
      G.FiniteChildAdaptivePotentialFamily entry target childError)
    (selection : G.BehaviorProfile) (initial : G.State)
    (fuel : ℕ) where
  fuel_covers_rank : selector.process.rank initial ≤ fuel
  terminal_entry :
    ∀ state, selector.process.terminal state →
      state = entry (selector.process.observe state)

namespace FixedDepthAdaptivePotentialSplice

variable [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ i, Finite (G.Act i)] [Fintype Child]
  {entry : Child → G.State} {target : Child → Payoff ι}
  {childError : ℝ}
  {selector : DeviationSafePublicCoinSelector G Child}
  {family :
    G.FiniteChildAdaptivePotentialFamily entry target childError}
  {selection : G.BehaviorProfile} {initial : G.State} {fuel : ℕ}

/-- The child observed from a fixed-depth terminal public history. -/
def observeBase (_splice :
    G.FixedDepthAdaptivePotentialSplice selector family
      selection initial fuel) :
    G.Hist fuel → Child :=
  fun base => selector.process.observe base.2

/-- Raw child profiles indexed by fixed-depth terminal histories. -/
def childProfile (splice :
    G.FixedDepthAdaptivePotentialSplice selector family
      selection initial fuel) :
    G.Hist fuel → G.BehaviorProfile :=
  family.observedTerminalProfile splice.observeBase

/-- The globally defined behavior profile: selection first, then canonical
fixed-depth child dispatch. -/
def profile (splice :
    G.FixedDepthAdaptivePotentialSplice selector family
      selection initial fuel) :
    G.BehaviorProfile :=
  G.terminalChildDispatcher fuel selection splice.childProfile

def lowerPotential (splice :
    G.FixedDepthAdaptivePotentialSplice selector family
      selection initial fuel) (who : ι) :
    G.HistoryPotential :=
  G.fixedDepthHistoryPotential fuel
    (selector.terminalTargetHistoryPotential
      family.lowerTerminalTarget who)
    (fun base =>
      (family.system (splice.observeBase base)).lowerPotential who)

def upperPotential (splice :
    G.FixedDepthAdaptivePotentialSplice selector family
      selection initial fuel) (who : ι) :
    G.HistoryPotential :=
  G.fixedDepthHistoryPotential fuel
    (selector.terminalTargetHistoryPotential
      family.upperTerminalTarget who)
    (fun base =>
      (family.system (splice.observeBase base)).upperPotential who)

def deviationPotential (splice :
    G.FixedDepthAdaptivePotentialSplice selector family
      selection initial fuel) (who : ι) :
    G.HistoryPotential :=
  G.fixedDepthHistoryPotential fuel
    (selector.terminalTargetHistoryPotential
      family.deviationTerminalTarget who)
    (fun base =>
      (family.system (splice.observeBase base)).deviationPotential who)

/-- Every reachable fixed-depth base has the selected child's entry state. -/
theorem entry_eq_of_mem_support
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    (phaseProfile : G.BehaviorProfile)
    (base : G.Hist fuel)
    (hbase : base ∈ (G.histDist phaseProfile initial fuel).support) :
    base.2 = entry (splice.observeBase base) := by
  apply splice.terminal_entry
  exact selector.terminal_of_mem_support_histDist
    phaseProfile initial fuel splice.fuel_covers_rank base hbase

/-- After a fixed-depth base, the global profile is the canonical completion
of the selected raw child profile. -/
theorem afterHistoryProfile_eq_canonical
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    (base : G.Hist fuel) :
    G.afterHistoryProfile splice.profile base =
      G.canonicalTerminalChildProfile fuel selection
        splice.childProfile base :=
  rfl

/-- The rebased spliced potential agrees with the selected raw child
potential on every genuine suffix. -/
theorem afterHistoryPotential_lower_eq_on_startsAt
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    (base : G.Hist fuel) (who : ι)
    {length : ℕ} (history : G.Hist length)
    (hstart : history.StartsAt base.2) :
    G.afterHistoryPotential (splice.lowerPotential who) base
        length history =
      (family.system (splice.observeBase base)).lowerPotential who
        length history := by
  rw [G.afterHistoryPotential_apply]
  unfold lowerPotential
  exact G.fixedDepthHistoryPotential_appendHist
    _ _ base history hstart

theorem afterHistoryPotential_upper_eq_on_startsAt
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    (base : G.Hist fuel) (who : ι)
    {length : ℕ} (history : G.Hist length)
    (hstart : history.StartsAt base.2) :
    G.afterHistoryPotential (splice.upperPotential who) base
        length history =
      (family.system (splice.observeBase base)).upperPotential who
        length history := by
  rw [G.afterHistoryPotential_apply]
  unfold upperPotential
  exact G.fixedDepthHistoryPotential_appendHist
    _ _ base history hstart

theorem afterHistoryPotential_deviation_eq_on_startsAt
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    (base : G.Hist fuel) (who : ι)
    {length : ℕ} (history : G.Hist length)
    (hstart : history.StartsAt base.2) :
    G.afterHistoryPotential (splice.deviationPotential who) base
        length history =
      (family.system (splice.observeBase base)).deviationPotential who
        length history := by
  rw [G.afterHistoryPotential_apply]
  unfold deviationPotential
  exact G.fixedDepthHistoryPotential_appendHist
    _ _ base history hstart

/-- Generic root-to-child expectation decomposition after the selection
depth. -/
theorem expectedHistoryValue_add_eq_expect_child
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    (rootPotential : G.HistoryPotential)
    (childPotential : Child → G.HistoryPotential)
    (hpotential : ∀ base length (history : G.Hist length),
      history.StartsAt base.2 →
        G.afterHistoryPotential rootPotential base length history =
          childPotential (splice.observeBase base) length history)
    (length : ℕ) :
    G.expectedHistoryValue splice.profile initial rootPotential
        (fuel + length) =
      expect (G.histDist splice.profile initial fuel) fun base =>
        G.expectedHistoryValue
          (family.profile (splice.observeBase base))
          (entry (splice.observeBase base))
          (childPotential (splice.observeBase base)) length := by
  rw [G.expectedHistoryValue_add_eq_expect_afterHistory]
  apply expect_congr_on_support
  intro base hbase
  have hentry := splice.entry_eq_of_mem_support
    splice.profile base hbase
  have hagree :=
    G.profilesAgreeOnStartsAt_canonicalTerminalChildProfile
      fuel selection splice.childProfile base
  have hvalue :=
    G.expectedHistoryValue_eq_of_profilesAndPotentialsAgreeOnStartsAt
      hagree
      (G.afterHistoryPotential rootPotential base)
      (childPotential (splice.observeBase base))
      (hpotential base) length
  rw [splice.afterHistoryProfile_eq_canonical]
  rw [← hentry]
  exact hvalue

theorem expectedHistoryValue_lower_add_eq_expect_child
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    (who : ι) (length : ℕ) :
    G.expectedHistoryValue splice.profile initial
        (splice.lowerPotential who) (fuel + length) =
      expect (G.histDist splice.profile initial fuel) fun base =>
        G.expectedHistoryValue
          (family.profile (splice.observeBase base))
          (entry (splice.observeBase base))
          ((family.system
            (splice.observeBase base)).lowerPotential who) length := by
  exact splice.expectedHistoryValue_add_eq_expect_child
    (splice.lowerPotential who)
    (fun child => (family.system child).lowerPotential who)
    (fun base _ history hstart =>
      splice.afterHistoryPotential_lower_eq_on_startsAt
        base who history hstart)
    length

theorem expectedHistoryValue_upper_add_eq_expect_child
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    (who : ι) (length : ℕ) :
    G.expectedHistoryValue splice.profile initial
        (splice.upperPotential who) (fuel + length) =
      expect (G.histDist splice.profile initial fuel) fun base =>
        G.expectedHistoryValue
          (family.profile (splice.observeBase base))
          (entry (splice.observeBase base))
          ((family.system
            (splice.observeBase base)).upperPotential who) length := by
  exact splice.expectedHistoryValue_add_eq_expect_child
    (splice.upperPotential who)
    (fun child => (family.system child).upperPotential who)
    (fun base _ history hstart =>
      splice.afterHistoryPotential_upper_eq_on_startsAt
        base who history hstart)
    length

theorem expectedHistoryValue_deviation_add_eq_expect_child
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    (who : ι) (deviation : G.BehaviorStrategy who)
    (length : ℕ) :
    G.expectedHistoryValue
        (Function.update splice.profile who deviation) initial
        (splice.deviationPotential who) (fuel + length) =
      expect
        (G.histDist
          (Function.update splice.profile who deviation)
          initial fuel) fun base =>
        G.expectedHistoryValue
          (Function.update
            (family.profile (splice.observeBase base)) who
            (G.afterHistoryStrategy deviation base))
          (entry (splice.observeBase base))
          ((family.system
            (splice.observeBase base)).deviationPotential who)
          length := by
  rw [G.expectedHistoryValue_add_eq_expect_afterHistory]
  apply expect_congr_on_support
  intro base hbase
  have hentry := splice.entry_eq_of_mem_support
    (Function.update splice.profile who deviation) base hbase
  have hprofile :=
    G.afterHistoryProfile_update_terminalChildDispatcher_canonical
      fuel selection splice.childProfile base who deviation
  have hprofile' :
      G.afterHistoryProfile
          (Function.update splice.profile who deviation) base =
        Function.update
          (G.canonicalTerminalChildProfile fuel selection
            splice.childProfile base)
          who (G.afterHistoryStrategy deviation base) := by
    simpa [profile] using hprofile
  have hagree :=
    (G.profilesAgreeOnStartsAt_canonicalTerminalChildProfile
      fuel selection splice.childProfile base).update who
        (G.afterHistoryStrategy deviation base)
  have hvalue :=
    G.expectedHistoryValue_eq_of_profilesAndPotentialsAgreeOnStartsAt
      hagree
      (G.afterHistoryPotential (splice.deviationPotential who) base)
      ((family.system
        (splice.observeBase base)).deviationPotential who)
      (fun _ history hstart =>
        splice.afterHistoryPotential_deviation_eq_on_startsAt
          base who history hstart)
      length
  rw [hprofile']
  let childDeviation :=
    G.afterHistoryStrategy deviation base
  let childPotential :=
    (family.system
      (splice.observeBase base)).deviationPotential who
  have hstate :
      G.expectedHistoryValue
          (Function.update
            (family.profile (splice.observeBase base)) who
            childDeviation)
          base.2 childPotential length =
        G.expectedHistoryValue
          (Function.update
            (family.profile (splice.observeBase base)) who
            childDeviation)
          (entry (splice.observeBase base)) childPotential length :=
    congrArg
      (fun state =>
        G.expectedHistoryValue
          (Function.update
            (family.profile (splice.observeBase base)) who
            childDeviation)
          state childPotential length)
      hentry
  exact hvalue.trans hstate

omit [DecidableEq ι] in
/-- Stage-payoff expectations also disintegrate at a deterministic public
prefix. -/
theorem expectedStagePayoff_add_eq_expect_afterHistory
    (rootProfile : G.BehaviorProfile) (rootInitial : G.State)
    (prefixLength suffixLength : ℕ) (who : ι) :
    G.expectedStagePayoff rootProfile rootInitial
        (prefixLength + suffixLength) who =
      expect (G.histDist rootProfile rootInitial prefixLength) fun base =>
        G.expectedStagePayoff
          (G.afterHistoryProfile rootProfile base) base.2
          suffixLength who := by
  unfold expectedStagePayoff
  rw [G.histDist_add_eq_bind_histDistAfter, expect_bind]
  apply congrArg (expect (G.histDist rootProfile rootInitial prefixLength))
  funext base
  unfold histDistAfter
  rw [expect_map]
  rfl

/-- The prescribed root stage payoff after the prefix is the prefix-law
average of the selected raw child stage payoffs. -/
theorem expectedStagePayoff_add_eq_expect_child
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    (who : ι) (length : ℕ) :
    G.expectedStagePayoff splice.profile initial (fuel + length) who =
      expect (G.histDist splice.profile initial fuel) fun base =>
        G.expectedStagePayoff
          (family.profile (splice.observeBase base))
          (entry (splice.observeBase base)) length who := by
  rw [expectedStagePayoff_add_eq_expect_afterHistory]
  apply expect_congr_on_support
  intro base hbase
  have hentry := splice.entry_eq_of_mem_support
    splice.profile base hbase
  have hagree :=
    G.profilesAgreeOnStartsAt_canonicalTerminalChildProfile
      fuel selection splice.childProfile base
  have hvalue :=
    G.expectedStagePayoff_eq_of_profilesAgreeOnStartsAt
      hagree length who
  rw [splice.afterHistoryProfile_eq_canonical]
  rw [← hentry]
  exact hvalue

/-- The same stage-payoff decomposition holds after an arbitrary unilateral
root deviation, with the deviation rebased into each selected child. -/
theorem expectedStagePayoff_deviation_add_eq_expect_child
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    (who : ι) (deviation : G.BehaviorStrategy who)
    (length : ℕ) :
    G.expectedStagePayoff
        (Function.update splice.profile who deviation)
        initial (fuel + length) who =
      expect
        (G.histDist
          (Function.update splice.profile who deviation)
          initial fuel) fun base =>
        G.expectedStagePayoff
          (Function.update
            (family.profile (splice.observeBase base)) who
            (G.afterHistoryStrategy deviation base))
          (entry (splice.observeBase base)) length who := by
  rw [expectedStagePayoff_add_eq_expect_afterHistory]
  apply expect_congr_on_support
  intro base hbase
  have hentry := splice.entry_eq_of_mem_support
    (Function.update splice.profile who deviation) base hbase
  have hprofile :=
    G.afterHistoryProfile_update_terminalChildDispatcher_canonical
      fuel selection splice.childProfile base who deviation
  have hprofile' :
      G.afterHistoryProfile
          (Function.update splice.profile who deviation) base =
        Function.update
          (G.canonicalTerminalChildProfile fuel selection
            splice.childProfile base)
          who (G.afterHistoryStrategy deviation base) := by
    simpa [profile] using hprofile
  have hagree :=
    (G.profilesAgreeOnStartsAt_canonicalTerminalChildProfile
      fuel selection splice.childProfile base).update who
        (G.afterHistoryStrategy deviation base)
  have hvalue :=
    G.expectedStagePayoff_eq_of_profilesAgreeOnStartsAt
      hagree length who
  rw [hprofile']
  rw [← hentry]
  exact hvalue

/-- Prescribed lower charge averaged over the fixed-depth public prefix. -/
def suffixLowerCharge
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    (who : ι) (length : ℕ) : ℝ :=
  expect (G.histDist splice.profile initial fuel) fun base =>
    (family.system (splice.observeBase base)).lowerCharge who length

/-- Prescribed upper charge averaged over the fixed-depth public prefix. -/
def suffixUpperCharge
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    (who : ι) (length : ℕ) : ℝ :=
  expect (G.histDist splice.profile initial fuel) fun base =>
    (family.system (splice.observeBase base)).upperCharge who length

/-- Unilateral-deviation charge averaged over the deviating prefix law.
Each child sees the root deviation rebased after the realized prefix. -/
def suffixDeviationCharge
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    (who : ι) (deviation : G.BehaviorStrategy who)
    (length : ℕ) : ℝ :=
  expect
    (G.histDist
      (Function.update splice.profile who deviation)
      initial fuel) fun base =>
    (family.system (splice.observeBase base)).deviationCharge who
      (G.afterHistoryStrategy deviation base) length

/-- Explicit numerical and parent-target hypotheses for the fixed-depth
splice.  These are precisely the inputs used to construct the three finite
selection-prefix systems and to absorb their fixed cost. -/
structure Bounds
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    (parentTarget : Payoff ι) (parentError prefixError : ℝ)
    (payoffBound targetBound : ℝ) (accountingHorizon : ℕ) : Prop where
  lower_parent : ∀ who,
    |expect (selector.process.value initial)
        (fun child => family.lowerTerminalTarget child who) -
      parentTarget who| ≤ parentError
  upper_parent : ∀ who,
    |expect (selector.process.value initial)
        (fun child => family.upperTerminalTarget child who) -
      parentTarget who| ≤ parentError
  deviation_parent : ∀ who,
    |expect (selector.process.value initial)
        (fun child => family.deviationTerminalTarget child who) -
      parentTarget who| ≤ parentError
  payoff_bound : ∀ state action who,
    |G.stagePayoff state action who| ≤ payoffBound
  lower_target_bound : ∀ child who,
    |family.lowerTerminalTarget child who| ≤ targetBound
  upper_target_bound : ∀ child who,
    |family.upperTerminalTarget child who| ≤ targetBound
  deviation_target_bound : ∀ child who,
    |family.deviationTerminalTarget child who| ≤ targetBound
  payoffBound_nonneg : 0 ≤ payoffBound
  targetBound_nonneg : 0 ≤ targetBound
  childError_nonneg : 0 ≤ childError
  prefixError_nonneg : 0 ≤ prefixError
  error_budget : childError + prefixError ≤ parentError
  accountingHorizon_pos : 0 < accountingHorizon
  fuel_le_accountingHorizon : fuel ≤ accountingHorizon
  prefix_cost :
    (fuel : ℝ) * (payoffBound + targetBound) ≤
      (accountingHorizon : ℝ) * prefixError

/-- The lower finite-prefix system, with the child lower initial potentials
as terminal targets. -/
def lowerSelectionSystem
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    {parentTarget : Payoff ι} {parentError prefixError : ℝ}
    {payoffBound targetBound : ℝ} {accountingHorizon : ℕ}
    (bounds :
      splice.Bounds parentTarget parentError prefixError
        payoffBound targetBound accountingHorizon) :
    DeviationSafePublicCoinSelector.SelectionPhaseSystemAt
      selector family.lowerTerminalTarget
      splice.profile initial parentTarget parentError fuel
      payoffBound targetBound :=
  selector.toSelectionPhaseSystemAt family.lowerTerminalTarget
    splice.profile initial parentTarget parentError fuel
    payoffBound targetBound splice.fuel_covers_rank
    bounds.lower_parent bounds.payoff_bound
    bounds.lower_target_bound bounds.payoffBound_nonneg
    bounds.targetBound_nonneg

/-- The upper finite-prefix system, with the child upper initial potentials
as terminal targets. -/
def upperSelectionSystem
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    {parentTarget : Payoff ι} {parentError prefixError : ℝ}
    {payoffBound targetBound : ℝ} {accountingHorizon : ℕ}
    (bounds :
      splice.Bounds parentTarget parentError prefixError
        payoffBound targetBound accountingHorizon) :
    DeviationSafePublicCoinSelector.SelectionPhaseSystemAt
      selector family.upperTerminalTarget
      splice.profile initial parentTarget parentError fuel
      payoffBound targetBound :=
  selector.toSelectionPhaseSystemAt family.upperTerminalTarget
    splice.profile initial parentTarget parentError fuel
    payoffBound targetBound splice.fuel_covers_rank
    bounds.upper_parent bounds.payoff_bound
    bounds.upper_target_bound bounds.payoffBound_nonneg
    bounds.targetBound_nonneg

/-- The deviation finite-prefix system, with the child deviation initial
potentials as terminal targets. -/
def deviationSelectionSystem
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    {parentTarget : Payoff ι} {parentError prefixError : ℝ}
    {payoffBound targetBound : ℝ} {accountingHorizon : ℕ}
    (bounds :
      splice.Bounds parentTarget parentError prefixError
        payoffBound targetBound accountingHorizon) :
    DeviationSafePublicCoinSelector.SelectionPhaseSystemAt
      selector family.deviationTerminalTarget
      splice.profile initial parentTarget parentError fuel
      payoffBound targetBound :=
  selector.toSelectionPhaseSystemAt family.deviationTerminalTarget
    splice.profile initial parentTarget parentError fuel
    payoffBound targetBound splice.fuel_covers_rank
    bounds.deviation_parent bounds.payoff_bound
    bounds.deviation_target_bound bounds.payoffBound_nonneg
    bounds.targetBound_nonneg

/-- Global lower scalar charge: the concrete selection charge before the
fixed depth and the averaged child charge afterwards. -/
def lowerCharge
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    {parentTarget : Payoff ι} {parentError prefixError : ℝ}
    {payoffBound targetBound : ℝ} {accountingHorizon : ℕ}
    (bounds :
      splice.Bounds parentTarget parentError prefixError
        payoffBound targetBound accountingHorizon)
    (who : ι) (time : ℕ) : ℝ :=
  if time < fuel then
    G.expectedHistoryValue splice.profile initial
      ((splice.lowerSelectionSystem bounds).lowerCharge who) time
  else
    splice.suffixLowerCharge who (time - fuel)

/-- Global upper scalar charge. -/
def upperCharge
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    {parentTarget : Payoff ι} {parentError prefixError : ℝ}
    {payoffBound targetBound : ℝ} {accountingHorizon : ℕ}
    (bounds :
      splice.Bounds parentTarget parentError prefixError
        payoffBound targetBound accountingHorizon)
    (who : ι) (time : ℕ) : ℝ :=
  if time < fuel then
    G.expectedHistoryValue splice.profile initial
      ((splice.upperSelectionSystem bounds).upperCharge who) time
  else
    splice.suffixUpperCharge who (time - fuel)

/-- Global unilateral-deviation scalar charge. -/
def deviationCharge
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    {parentTarget : Payoff ι} {parentError prefixError : ℝ}
    {payoffBound targetBound : ℝ} {accountingHorizon : ℕ}
    (bounds :
      splice.Bounds parentTarget parentError prefixError
        payoffBound targetBound accountingHorizon)
    (who : ι) (deviation : G.BehaviorStrategy who)
    (time : ℕ) : ℝ :=
  if time < fuel then
    G.expectedHistoryValue
      (Function.update splice.profile who deviation) initial
      ((splice.deviationSelectionSystem bounds).deviationCharge
        who deviation) time
  else
    splice.suffixDeviationCharge who deviation (time - fuel)

/-- At the splice depth, the lower child potential is exactly the lower
selection terminal-target potential in root expectation. -/
theorem expectedHistoryValue_lower_fuel_eq_selection
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    (who : ι) :
    G.expectedHistoryValue splice.profile initial
        (splice.lowerPotential who) fuel =
      G.expectedHistoryValue splice.profile initial
        (selector.terminalTargetHistoryPotential
          family.lowerTerminalTarget who) fuel := by
  have hdecompose :=
    splice.expectedHistoryValue_lower_add_eq_expect_child who 0
  simp only [Nat.add_zero] at hdecompose
  rw [hdecompose]
  unfold expectedHistoryValue
  apply expect_congr_on_support
  intro base hbase
  rw [G.histDist_zero, expect_pure]
  symm
  exact selector.terminalTargetHistoryPotential_eq_of_mem_support
    family.lowerTerminalTarget splice.profile initial fuel
    splice.fuel_covers_rank who base hbase

/-- At the splice depth, the upper child potential is exactly the upper
selection terminal-target potential in root expectation. -/
theorem expectedHistoryValue_upper_fuel_eq_selection
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    (who : ι) :
    G.expectedHistoryValue splice.profile initial
        (splice.upperPotential who) fuel =
      G.expectedHistoryValue splice.profile initial
        (selector.terminalTargetHistoryPotential
          family.upperTerminalTarget who) fuel := by
  have hdecompose :=
    splice.expectedHistoryValue_upper_add_eq_expect_child who 0
  simp only [Nat.add_zero] at hdecompose
  rw [hdecompose]
  unfold expectedHistoryValue
  apply expect_congr_on_support
  intro base hbase
  rw [G.histDist_zero, expect_pure]
  symm
  exact selector.terminalTargetHistoryPotential_eq_of_mem_support
    family.upperTerminalTarget splice.profile initial fuel
    splice.fuel_covers_rank who base hbase

/-- Under any unilateral deviation, the child deviation potential at the
splice depth is the deviation selection terminal-target potential. -/
theorem expectedHistoryValue_deviation_fuel_eq_selection
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    (who : ι) (deviation : G.BehaviorStrategy who) :
    G.expectedHistoryValue
        (Function.update splice.profile who deviation) initial
        (splice.deviationPotential who) fuel =
      G.expectedHistoryValue
        (Function.update splice.profile who deviation) initial
        (selector.terminalTargetHistoryPotential
          family.deviationTerminalTarget who) fuel := by
  have hdecompose :=
    splice.expectedHistoryValue_deviation_add_eq_expect_child
      who deviation 0
  simp only [Nat.add_zero] at hdecompose
  rw [hdecompose]
  unfold expectedHistoryValue
  apply expect_congr_on_support
  intro base hbase
  rw [G.histDist_zero, expect_pure]
  symm
  exact selector.terminalTargetHistoryPotential_eq_of_mem_support
    family.deviationTerminalTarget
    (Function.update splice.profile who deviation)
    initial fuel splice.fuel_covers_rank who base hbase

/-- A uniform normalized bound on a finite family of scalar charge
sequences remains valid after averaging over any probability law. -/
theorem normalized_expect_charge_le
    {A : Type} [Finite A] (law : PMF A)
    (charge : A → ℕ → ℝ) (length : ℕ) (error : ℝ)
    (hcharge : ∀ a,
      (length : ℝ)⁻¹ *
          ∑ time ∈ Finset.range length, charge a time ≤ error) :
    (length : ℝ)⁻¹ *
        ∑ time ∈ Finset.range length,
          expect law (fun a => charge a time) ≤
      error := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  have hsum :
      ∑ time ∈ Finset.range length,
          expect law (fun a => charge a time) =
        expect law fun a =>
          ∑ time ∈ Finset.range length, charge a time := by
    simp only [expect_eq_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
  rw [hsum, ← expect_const_mul]
  calc
    expect law (fun a =>
        (length : ℝ)⁻¹ *
          ∑ time ∈ Finset.range length, charge a time) ≤
      expect law (fun _ => error) := by
        apply expect_mono
        exact hcharge
    _ = error := expect_const _ _

/-- The averaged prescribed lower suffix charge inherits the child
Cesàro bound. -/
theorem suffixLowerCharge_cesaro
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    (who : ι) (length : ℕ)
    (hlength : family.commonHorizon ≤ length) :
    (length : ℝ)⁻¹ *
        ∑ time ∈ Finset.range length,
          splice.suffixLowerCharge who time ≤
      childError := by
  unfold suffixLowerCharge
  apply normalized_expect_charge_le
  intro base
  exact (family.system
    (splice.observeBase base)).lower_charge_cesaro who length
      (le_trans (family.horizon_le_common _) hlength)

/-- The averaged prescribed upper suffix charge inherits the child
Cesàro bound. -/
theorem suffixUpperCharge_cesaro
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    (who : ι) (length : ℕ)
    (hlength : family.commonHorizon ≤ length) :
    (length : ℝ)⁻¹ *
        ∑ time ∈ Finset.range length,
          splice.suffixUpperCharge who time ≤
      childError := by
  unfold suffixUpperCharge
  apply normalized_expect_charge_le
  intro base
  exact (family.system
    (splice.observeBase base)).upper_charge_cesaro who length
      (le_trans (family.horizon_le_common _) hlength)

/-- The averaged arbitrary-deviation suffix charge inherits the child
Cesàro bound uniformly over every rebased deviation. -/
theorem suffixDeviationCharge_cesaro
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    (who : ι) (deviation : G.BehaviorStrategy who)
    (length : ℕ) (hlength : family.commonHorizon ≤ length) :
    (length : ℝ)⁻¹ *
        ∑ time ∈ Finset.range length,
          splice.suffixDeviationCharge who deviation time ≤
      childError := by
  unfold suffixDeviationCharge
  apply normalized_expect_charge_le
  intro base
  exact (family.system
    (splice.observeBase base)).deviation_charge_cesaro who
      (G.afterHistoryStrategy deviation base) length
      (le_trans (family.horizon_le_common _) hlength)

/-- The complete lower scalar charge obeys the parent error budget once
the child horizon and the fixed-prefix accounting horizon are both met. -/
theorem lowerCharge_cesaro_add
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    {parentTarget : Payoff ι} {parentError prefixError : ℝ}
    {payoffBound targetBound : ℝ} {accountingHorizon : ℕ}
    (bounds :
      splice.Bounds parentTarget parentError prefixError
        payoffBound targetBound accountingHorizon)
    (who : ι) (suffixLength : ℕ)
    (hsuffix : family.commonHorizon ≤ suffixLength)
    (haccounting : accountingHorizon ≤ fuel + suffixLength) :
    ((fuel + suffixLength : ℕ) : ℝ)⁻¹ *
        ∑ time ∈ Finset.range (fuel + suffixLength),
          splice.lowerCharge bounds who time ≤
      parentError := by
  have hsuffixPos : 0 < suffixLength :=
    lt_of_lt_of_le
      (lt_of_lt_of_le Nat.zero_lt_two family.commonHorizon_ge_two)
      hsuffix
  have hprefix :
      ∑ time ∈ Finset.range fuel,
          G.expectedHistoryValue splice.profile initial
            ((splice.lowerSelectionSystem bounds).lowerCharge who)
            time ≤
        (accountingHorizon : ℝ) * prefixError := by
    exact ((splice.lowerSelectionSystem bounds).lower_charge_sum
      who fuel le_rfl).trans bounds.prefix_cost
  have hcombined :=
    normalized_fixedPrefixScalarCharge_le
      fuel suffixLength accountingHorizon
      (fun time =>
        G.expectedHistoryValue splice.profile initial
          ((splice.lowerSelectionSystem bounds).lowerCharge who)
          time)
      (splice.suffixLowerCharge who)
      prefixError childError hsuffixPos haccounting
      bounds.prefixError_nonneg bounds.childError_nonneg
      hprefix
      (splice.suffixLowerCharge_cesaro who suffixLength hsuffix)
  have hbudget : prefixError + childError ≤ parentError := by
    linarith [bounds.error_budget]
  have hglobal :
      ((fuel + suffixLength : ℕ) : ℝ)⁻¹ *
          ∑ time ∈ Finset.range (fuel + suffixLength),
            splice.lowerCharge bounds who time ≤
        prefixError + childError := by
    simpa [lowerCharge, fixedPrefixScalarCharge] using hcombined
  exact hglobal.trans hbudget

/-- The complete upper scalar charge obeys the same parent budget. -/
theorem upperCharge_cesaro_add
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    {parentTarget : Payoff ι} {parentError prefixError : ℝ}
    {payoffBound targetBound : ℝ} {accountingHorizon : ℕ}
    (bounds :
      splice.Bounds parentTarget parentError prefixError
        payoffBound targetBound accountingHorizon)
    (who : ι) (suffixLength : ℕ)
    (hsuffix : family.commonHorizon ≤ suffixLength)
    (haccounting : accountingHorizon ≤ fuel + suffixLength) :
    ((fuel + suffixLength : ℕ) : ℝ)⁻¹ *
        ∑ time ∈ Finset.range (fuel + suffixLength),
          splice.upperCharge bounds who time ≤
      parentError := by
  have hsuffixPos : 0 < suffixLength :=
    lt_of_lt_of_le
      (lt_of_lt_of_le Nat.zero_lt_two family.commonHorizon_ge_two)
      hsuffix
  have hprefix :
      ∑ time ∈ Finset.range fuel,
          G.expectedHistoryValue splice.profile initial
            ((splice.upperSelectionSystem bounds).upperCharge who)
            time ≤
        (accountingHorizon : ℝ) * prefixError := by
    exact ((splice.upperSelectionSystem bounds).upper_charge_sum
      who fuel le_rfl).trans bounds.prefix_cost
  have hcombined :=
    normalized_fixedPrefixScalarCharge_le
      fuel suffixLength accountingHorizon
      (fun time =>
        G.expectedHistoryValue splice.profile initial
          ((splice.upperSelectionSystem bounds).upperCharge who)
          time)
      (splice.suffixUpperCharge who)
      prefixError childError hsuffixPos haccounting
      bounds.prefixError_nonneg bounds.childError_nonneg
      hprefix
      (splice.suffixUpperCharge_cesaro who suffixLength hsuffix)
  have hbudget : prefixError + childError ≤ parentError := by
    linarith [bounds.error_budget]
  have hglobal :
      ((fuel + suffixLength : ℕ) : ℝ)⁻¹ *
          ∑ time ∈ Finset.range (fuel + suffixLength),
            splice.upperCharge bounds who time ≤
        prefixError + childError := by
    simpa [upperCharge, fixedPrefixScalarCharge] using hcombined
  exact hglobal.trans hbudget

/-- The complete arbitrary-deviation scalar charge obeys the same parent
budget uniformly over every root deviation. -/
theorem deviationCharge_cesaro_add
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    {parentTarget : Payoff ι} {parentError prefixError : ℝ}
    {payoffBound targetBound : ℝ} {accountingHorizon : ℕ}
    (bounds :
      splice.Bounds parentTarget parentError prefixError
        payoffBound targetBound accountingHorizon)
    (who : ι) (deviation : G.BehaviorStrategy who)
    (suffixLength : ℕ)
    (hsuffix : family.commonHorizon ≤ suffixLength)
    (haccounting : accountingHorizon ≤ fuel + suffixLength) :
    ((fuel + suffixLength : ℕ) : ℝ)⁻¹ *
        ∑ time ∈ Finset.range (fuel + suffixLength),
          splice.deviationCharge bounds who deviation time ≤
      parentError := by
  have hsuffixPos : 0 < suffixLength :=
    lt_of_lt_of_le
      (lt_of_lt_of_le Nat.zero_lt_two family.commonHorizon_ge_two)
      hsuffix
  have hprefix :
      ∑ time ∈ Finset.range fuel,
          G.expectedHistoryValue
            (Function.update splice.profile who deviation) initial
            ((splice.deviationSelectionSystem bounds).deviationCharge
              who deviation) time ≤
        (accountingHorizon : ℝ) * prefixError := by
    exact ((splice.deviationSelectionSystem bounds).deviation_charge_sum
      who deviation fuel le_rfl).trans bounds.prefix_cost
  have hcombined :=
    normalized_fixedPrefixScalarCharge_le
      fuel suffixLength accountingHorizon
      (fun time =>
        G.expectedHistoryValue
          (Function.update splice.profile who deviation) initial
          ((splice.deviationSelectionSystem bounds).deviationCharge
            who deviation) time)
      (splice.suffixDeviationCharge who deviation)
      prefixError childError hsuffixPos haccounting
      bounds.prefixError_nonneg bounds.childError_nonneg
      hprefix
      (splice.suffixDeviationCharge_cesaro
        who deviation suffixLength hsuffix)
  have hbudget : prefixError + childError ≤ parentError := by
    linarith [bounds.error_budget]
  have hglobal :
      ((fuel + suffixLength : ℕ) : ℝ)⁻¹ *
          ∑ time ∈ Finset.range (fuel + suffixLength),
            splice.deviationCharge bounds who deviation time ≤
        prefixError + childError := by
    simpa [deviationCharge, fixedPrefixScalarCharge] using hcombined
  exact hglobal.trans hbudget

omit [DecidableEq ι] [Fintype Child] in
/-- The selector terminal-target potential has constant expectation under
every behavior profile. -/
theorem expectedHistoryValue_terminalTarget_succ_eq
    [Finite Child]
    (terminalTarget : Child → ι → ℝ)
    (rootProfile : G.BehaviorProfile) (who : ι) (time : ℕ) :
    G.expectedHistoryValue rootProfile initial
        (selector.terminalTargetHistoryPotential terminalTarget who)
        (time + 1) =
      G.expectedHistoryValue rootProfile initial
        (selector.terminalTargetHistoryPotential terminalTarget who)
        time := by
  rw [G.expectedHistoryValue_succ]
  unfold expectedHistoryValue
  apply congrArg (expect (G.histDist rootProfile initial time))
  funext history
  exact selector.historyContinuationEU_terminalTargetHistoryPotential_eq
    terminalTarget rootProfile who history

/-- Before the splice depth, the lower spliced potential is the selector
terminal-target potential. -/
theorem expectedHistoryValue_lower_eq_selection_of_lt
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    (who : ι) (time : ℕ) (htime : time < fuel) :
    G.expectedHistoryValue splice.profile initial
        (splice.lowerPotential who) time =
      G.expectedHistoryValue splice.profile initial
        (selector.terminalTargetHistoryPotential
          family.lowerTerminalTarget who) time := by
  unfold expectedHistoryValue
  apply congrArg (expect (G.histDist splice.profile initial time))
  funext history
  exact G.fixedDepthHistoryPotential_before _ _ htime history

/-- Before the splice depth, the upper spliced potential is the selector
terminal-target potential. -/
theorem expectedHistoryValue_upper_eq_selection_of_lt
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    (who : ι) (time : ℕ) (htime : time < fuel) :
    G.expectedHistoryValue splice.profile initial
        (splice.upperPotential who) time =
      G.expectedHistoryValue splice.profile initial
        (selector.terminalTargetHistoryPotential
          family.upperTerminalTarget who) time := by
  unfold expectedHistoryValue
  apply congrArg (expect (G.histDist splice.profile initial time))
  funext history
  exact G.fixedDepthHistoryPotential_before _ _ htime history

/-- Before the splice depth, the deviation spliced potential is the selector
terminal-target potential under the deviating law. -/
theorem expectedHistoryValue_deviation_eq_selection_of_lt
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    (who : ι) (deviation : G.BehaviorStrategy who)
    (time : ℕ) (htime : time < fuel) :
    G.expectedHistoryValue
        (Function.update splice.profile who deviation) initial
        (splice.deviationPotential who) time =
      G.expectedHistoryValue
        (Function.update splice.profile who deviation) initial
        (selector.terminalTargetHistoryPotential
          family.deviationTerminalTarget who) time := by
  unfold expectedHistoryValue
  apply congrArg
    (expect
      (G.histDist
        (Function.update splice.profile who deviation) initial time))
  funext history
  exact G.fixedDepthHistoryPotential_before _ _ htime history

/-- The lower spliced potential is a submartingale throughout the finite
selection prefix, including the terminal boundary. -/
theorem lower_submartingale_of_lt
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    (who : ι) (time : ℕ) (htime : time < fuel) :
    G.expectedHistoryValue splice.profile initial
        (splice.lowerPotential who) time ≤
      G.expectedHistoryValue splice.profile initial
        (splice.lowerPotential who) (time + 1) := by
  rw [splice.expectedHistoryValue_lower_eq_selection_of_lt
    who time htime]
  by_cases hnext : time + 1 < fuel
  · rw [splice.expectedHistoryValue_lower_eq_selection_of_lt
      who (time + 1) hnext]
    exact le_of_eq
      (expectedHistoryValue_terminalTarget_succ_eq
        (selector := selector) (initial := initial)
        family.lowerTerminalTarget splice.profile who time).symm
  · have heq : time + 1 = fuel := by omega
    rw [heq, splice.expectedHistoryValue_lower_fuel_eq_selection]
    have hconstant :=
      expectedHistoryValue_terminalTarget_succ_eq
        (selector := selector) (initial := initial)
        family.lowerTerminalTarget splice.profile who time
    exact le_of_eq (by simpa only [heq] using hconstant.symm)

/-- The upper spliced potential is a supermartingale throughout the finite
selection prefix, including the terminal boundary. -/
theorem upper_supermartingale_of_lt
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    (who : ι) (time : ℕ) (htime : time < fuel) :
    G.expectedHistoryValue splice.profile initial
        (splice.upperPotential who) (time + 1) ≤
      G.expectedHistoryValue splice.profile initial
        (splice.upperPotential who) time := by
  rw [splice.expectedHistoryValue_upper_eq_selection_of_lt
    who time htime]
  by_cases hnext : time + 1 < fuel
  · rw [splice.expectedHistoryValue_upper_eq_selection_of_lt
      who (time + 1) hnext]
    exact le_of_eq
      (expectedHistoryValue_terminalTarget_succ_eq
        (selector := selector) (initial := initial)
        family.upperTerminalTarget splice.profile who time)
  · have heq : time + 1 = fuel := by omega
    rw [heq, splice.expectedHistoryValue_upper_fuel_eq_selection]
    have hconstant :=
      expectedHistoryValue_terminalTarget_succ_eq
        (selector := selector) (initial := initial)
        family.upperTerminalTarget splice.profile who time
    exact le_of_eq (by simpa only [heq] using hconstant)

/-- The deviation spliced potential is a supermartingale throughout the
finite selection prefix, including the terminal boundary. -/
theorem deviation_supermartingale_of_lt
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    (who : ι) (deviation : G.BehaviorStrategy who)
    (time : ℕ) (htime : time < fuel) :
    G.expectedHistoryValue
        (Function.update splice.profile who deviation) initial
        (splice.deviationPotential who) (time + 1) ≤
      G.expectedHistoryValue
        (Function.update splice.profile who deviation) initial
        (splice.deviationPotential who) time := by
  rw [splice.expectedHistoryValue_deviation_eq_selection_of_lt
    who deviation time htime]
  by_cases hnext : time + 1 < fuel
  · rw [splice.expectedHistoryValue_deviation_eq_selection_of_lt
      who deviation (time + 1) hnext]
    exact le_of_eq
      (expectedHistoryValue_terminalTarget_succ_eq
        (selector := selector) (initial := initial)
        family.deviationTerminalTarget
        (Function.update splice.profile who deviation) who time)
  · have heq : time + 1 = fuel := by omega
    rw [heq,
      splice.expectedHistoryValue_deviation_fuel_eq_selection]
    have hconstant :=
      expectedHistoryValue_terminalTarget_succ_eq
        (selector := selector) (initial := initial)
        family.deviationTerminalTarget
        (Function.update splice.profile who deviation) who time
    exact le_of_eq (by simpa only [heq] using hconstant)

/-- The lower parent stage inequality holds throughout the selection
prefix with the concrete scalar selection charge. -/
theorem lower_stage_of_lt
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    {parentTarget : Payoff ι} {parentError prefixError : ℝ}
    {payoffBound targetBound : ℝ} {accountingHorizon : ℕ}
    (bounds :
      splice.Bounds parentTarget parentError prefixError
        payoffBound targetBound accountingHorizon)
    (who : ι) (time : ℕ) (htime : time < fuel) :
    G.expectedHistoryValue splice.profile initial
        (splice.lowerPotential who) time ≤
      G.expectedStagePayoff splice.profile initial time who +
        splice.lowerCharge bounds who time := by
  rw [splice.expectedHistoryValue_lower_eq_selection_of_lt
    who time htime]
  rw [lowerCharge, if_pos htime]
  unfold expectedHistoryValue expectedStagePayoff
  simpa only [lowerSelectionSystem,
    DeviationSafePublicCoinSelector.toSelectionPhaseSystemAt,
    expect_add] using
    expect_mono (G.histDist splice.profile initial time) _ _
      (fun history =>
        (splice.lowerSelectionSystem bounds).lower_stage
          who time history htime)

/-- The upper parent stage inequality holds throughout the selection
prefix. -/
theorem upper_stage_of_lt
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    {parentTarget : Payoff ι} {parentError prefixError : ℝ}
    {payoffBound targetBound : ℝ} {accountingHorizon : ℕ}
    (bounds :
      splice.Bounds parentTarget parentError prefixError
        payoffBound targetBound accountingHorizon)
    (who : ι) (time : ℕ) (htime : time < fuel) :
    G.expectedStagePayoff splice.profile initial time who ≤
      G.expectedHistoryValue splice.profile initial
          (splice.upperPotential who) time +
        splice.upperCharge bounds who time := by
  rw [splice.expectedHistoryValue_upper_eq_selection_of_lt
    who time htime]
  rw [upperCharge, if_pos htime]
  unfold expectedHistoryValue expectedStagePayoff
  simpa only [upperSelectionSystem,
    DeviationSafePublicCoinSelector.toSelectionPhaseSystemAt,
    expect_add] using
    expect_mono (G.histDist splice.profile initial time) _ _
      (fun history =>
        (splice.upperSelectionSystem bounds).upper_stage
          who time history htime)

/-- The unilateral-deviation parent stage inequality holds throughout the
selection prefix. -/
theorem deviation_stage_of_lt
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    {parentTarget : Payoff ι} {parentError prefixError : ℝ}
    {payoffBound targetBound : ℝ} {accountingHorizon : ℕ}
    (bounds :
      splice.Bounds parentTarget parentError prefixError
        payoffBound targetBound accountingHorizon)
    (who : ι) (deviation : G.BehaviorStrategy who)
    (time : ℕ) (htime : time < fuel) :
    G.expectedStagePayoff
        (Function.update splice.profile who deviation)
        initial time who ≤
      G.expectedHistoryValue
          (Function.update splice.profile who deviation) initial
          (splice.deviationPotential who) time +
        splice.deviationCharge bounds who deviation time := by
  rw [splice.expectedHistoryValue_deviation_eq_selection_of_lt
    who deviation time htime]
  rw [deviationCharge, if_pos htime]
  unfold expectedHistoryValue expectedStagePayoff
  simpa only [deviationSelectionSystem,
    DeviationSafePublicCoinSelector.toSelectionPhaseSystemAt,
    expect_add] using
    expect_mono
      (G.histDist
        (Function.update splice.profile who deviation) initial time)
      _ _
      (fun history =>
        (splice.deviationSelectionSystem bounds).deviation_stage
          who deviation time history htime)

/-- The global lower initial potential satisfies the parent target bound,
including the zero-fuel case. -/
theorem lower_initial
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    {parentTarget : Payoff ι} {parentError prefixError : ℝ}
    {payoffBound targetBound : ℝ} {accountingHorizon : ℕ}
    (bounds :
      splice.Bounds parentTarget parentError prefixError
        payoffBound targetBound accountingHorizon)
    (who : ι) :
    |splice.lowerPotential who 0 (G.emptyHist initial) -
        parentTarget who| ≤ parentError := by
  have hsystem :=
    (splice.lowerSelectionSystem bounds).lower_initial who
  by_cases hfuel : fuel = 0
  · subst fuel
    have heq :=
      splice.expectedHistoryValue_lower_fuel_eq_selection who
    rw [G.expectedHistoryValue_zero,
      G.expectedHistoryValue_zero] at heq
    rw [heq]
    simpa only [lowerSelectionSystem,
      DeviationSafePublicCoinSelector.toSelectionPhaseSystemAt]
      using hsystem
  · have hzero : 0 < fuel := Nat.pos_of_ne_zero hfuel
    simpa only [lowerPotential,
      G.fixedDepthHistoryPotential_before _ _ hzero,
      lowerSelectionSystem,
      DeviationSafePublicCoinSelector.toSelectionPhaseSystemAt]
      using hsystem

/-- The global upper initial potential satisfies the parent target bound. -/
theorem upper_initial
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    {parentTarget : Payoff ι} {parentError prefixError : ℝ}
    {payoffBound targetBound : ℝ} {accountingHorizon : ℕ}
    (bounds :
      splice.Bounds parentTarget parentError prefixError
        payoffBound targetBound accountingHorizon)
    (who : ι) :
    |splice.upperPotential who 0 (G.emptyHist initial) -
        parentTarget who| ≤ parentError := by
  have hsystem :=
    (splice.upperSelectionSystem bounds).upper_initial who
  by_cases hfuel : fuel = 0
  · subst fuel
    have heq :=
      splice.expectedHistoryValue_upper_fuel_eq_selection who
    rw [G.expectedHistoryValue_zero,
      G.expectedHistoryValue_zero] at heq
    rw [heq]
    simpa only [upperSelectionSystem,
      DeviationSafePublicCoinSelector.toSelectionPhaseSystemAt]
      using hsystem
  · have hzero : 0 < fuel := Nat.pos_of_ne_zero hfuel
    simpa only [upperPotential,
      G.fixedDepthHistoryPotential_before _ _ hzero,
      upperSelectionSystem,
      DeviationSafePublicCoinSelector.toSelectionPhaseSystemAt]
      using hsystem

/-- The global deviation initial potential satisfies the parent target
bound. -/
theorem deviation_initial
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    {parentTarget : Payoff ι} {parentError prefixError : ℝ}
    {payoffBound targetBound : ℝ} {accountingHorizon : ℕ}
    (bounds :
      splice.Bounds parentTarget parentError prefixError
        payoffBound targetBound accountingHorizon)
    (who : ι) :
    |splice.deviationPotential who 0 (G.emptyHist initial) -
        parentTarget who| ≤ parentError := by
  have hsystem :=
    (splice.deviationSelectionSystem bounds).deviation_initial who
  by_cases hfuel : fuel = 0
  · subst fuel
    let deviation := splice.profile who
    have heq :=
      splice.expectedHistoryValue_deviation_fuel_eq_selection
        who deviation
    rw [G.expectedHistoryValue_zero,
      G.expectedHistoryValue_zero] at heq
    rw [heq]
    simpa only [deviationSelectionSystem,
      DeviationSafePublicCoinSelector.toSelectionPhaseSystemAt]
      using hsystem
  · have hzero : 0 < fuel := Nat.pos_of_ne_zero hfuel
    simpa only [deviationPotential,
      G.fixedDepthHistoryPotential_before _ _ hzero,
      deviationSelectionSystem,
      DeviationSafePublicCoinSelector.toSelectionPhaseSystemAt]
      using hsystem

/-- Child lower submartingales average to the root lower submartingale at
every suffix time. -/
theorem lower_submartingale_add
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    (who : ι) (length : ℕ) :
    G.expectedHistoryValue splice.profile initial
        (splice.lowerPotential who) (fuel + length) ≤
      G.expectedHistoryValue splice.profile initial
        (splice.lowerPotential who) (fuel + length + 1) := by
  rw [show fuel + length + 1 = fuel + (length + 1) by omega]
  rw [splice.expectedHistoryValue_lower_add_eq_expect_child]
  rw [splice.expectedHistoryValue_lower_add_eq_expect_child]
  apply expect_mono
  intro base
  exact
    (family.system (splice.observeBase base)).lower_submartingale
      who length

/-- Child upper supermartingales average to the root upper
supermartingale at every suffix time. -/
theorem upper_supermartingale_add
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    (who : ι) (length : ℕ) :
    G.expectedHistoryValue splice.profile initial
        (splice.upperPotential who) (fuel + length + 1) ≤
      G.expectedHistoryValue splice.profile initial
        (splice.upperPotential who) (fuel + length) := by
  rw [show fuel + length + 1 = fuel + (length + 1) by omega]
  rw [splice.expectedHistoryValue_upper_add_eq_expect_child]
  rw [splice.expectedHistoryValue_upper_add_eq_expect_child]
  apply expect_mono
  intro base
  exact
    (family.system (splice.observeBase base)).upper_supermartingale
      who length

/-- Child unilateral-deviation supermartingales average to the root
deviation supermartingale at every suffix time. -/
theorem deviation_supermartingale_add
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    (who : ι) (deviation : G.BehaviorStrategy who)
    (length : ℕ) :
    G.expectedHistoryValue
        (Function.update splice.profile who deviation) initial
        (splice.deviationPotential who) (fuel + length + 1) ≤
      G.expectedHistoryValue
        (Function.update splice.profile who deviation) initial
        (splice.deviationPotential who) (fuel + length) := by
  rw [show fuel + length + 1 = fuel + (length + 1) by omega]
  rw [splice.expectedHistoryValue_deviation_add_eq_expect_child]
  rw [splice.expectedHistoryValue_deviation_add_eq_expect_child]
  apply expect_mono
  intro base
  exact
    (family.system
      (splice.observeBase base)).deviation_supermartingale who
        (G.afterHistoryStrategy deviation base) length

/-- The prescribed lower stage inequality survives fixed-depth
disintegration with the averaged child charge. -/
theorem lower_stage_add
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    (who : ι) (length : ℕ) :
    G.expectedHistoryValue splice.profile initial
        (splice.lowerPotential who) (fuel + length) ≤
      G.expectedStagePayoff splice.profile initial
          (fuel + length) who +
        splice.suffixLowerCharge who length := by
  rw [splice.expectedHistoryValue_lower_add_eq_expect_child]
  rw [splice.expectedStagePayoff_add_eq_expect_child]
  unfold suffixLowerCharge
  rw [← expect_add]
  apply expect_mono
  intro base
  exact (family.system (splice.observeBase base)).lower_stage
    who length

/-- The prescribed upper stage inequality survives fixed-depth
disintegration with the averaged child charge. -/
theorem upper_stage_add
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    (who : ι) (length : ℕ) :
    G.expectedStagePayoff splice.profile initial
        (fuel + length) who ≤
      G.expectedHistoryValue splice.profile initial
          (splice.upperPotential who) (fuel + length) +
        splice.suffixUpperCharge who length := by
  rw [splice.expectedHistoryValue_upper_add_eq_expect_child]
  rw [splice.expectedStagePayoff_add_eq_expect_child]
  unfold suffixUpperCharge
  rw [← expect_add]
  apply expect_mono
  intro base
  exact (family.system (splice.observeBase base)).upper_stage
    who length

/-- The arbitrary-deviation stage inequality survives fixed-depth
disintegration with the averaged rebased child charge. -/
theorem deviation_stage_add
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    (who : ι) (deviation : G.BehaviorStrategy who)
    (length : ℕ) :
    G.expectedStagePayoff
        (Function.update splice.profile who deviation)
        initial (fuel + length) who ≤
      G.expectedHistoryValue
          (Function.update splice.profile who deviation) initial
          (splice.deviationPotential who) (fuel + length) +
        splice.suffixDeviationCharge who deviation length := by
  rw [splice.expectedHistoryValue_deviation_add_eq_expect_child]
  rw [splice.expectedStagePayoff_deviation_add_eq_expect_child]
  unfold suffixDeviationCharge
  rw [← expect_add]
  apply expect_mono
  intro base
  exact (family.system
    (splice.observeBase base)).deviation_stage who
      (G.afterHistoryStrategy deviation base) length

/-- A deterministic deviation-safe selection prefix followed by any finite
family of child adaptive systems is itself an adaptive system.  The only
loss is the explicitly allocated fixed-prefix error. -/
def toAdaptivePotentialSystemAt
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    {parentTarget : Payoff ι} {parentError prefixError : ℝ}
    {payoffBound targetBound : ℝ} {accountingHorizon : ℕ}
    (bounds :
      splice.Bounds parentTarget parentError prefixError
        payoffBound targetBound accountingHorizon) :
    G.AdaptivePotentialSystemAt splice.profile initial
      parentTarget parentError where
  horizon :=
    Nat.max accountingHorizon (fuel + family.commonHorizon)
  lowerPotential := splice.lowerPotential
  upperPotential := splice.upperPotential
  deviationPotential := splice.deviationPotential
  lowerCharge := splice.lowerCharge bounds
  upperCharge := splice.upperCharge bounds
  deviationCharge := splice.deviationCharge bounds
  horizon_ge_two := by
    exact le_trans family.commonHorizon_ge_two
      (le_trans (Nat.le_add_left family.commonHorizon fuel)
        (Nat.le_max_right _ _))
  lower_initial := splice.lower_initial bounds
  upper_initial := splice.upper_initial bounds
  deviation_initial := splice.deviation_initial bounds
  lower_submartingale := by
    intro who time
    by_cases htime : time < fuel
    · exact splice.lower_submartingale_of_lt who time htime
    · have hle : fuel ≤ time := Nat.le_of_not_gt htime
      have hbound :=
        splice.lower_submartingale_add who (time - fuel)
      rw [Nat.add_sub_of_le hle] at hbound
      exact hbound
  lower_stage := by
    intro who time
    by_cases htime : time < fuel
    · exact splice.lower_stage_of_lt bounds who time htime
    · have hle : fuel ≤ time := Nat.le_of_not_gt htime
      have hcharge :
          splice.lowerCharge bounds who time =
            splice.suffixLowerCharge who (time - fuel) := by
        simp [lowerCharge, htime]
      rw [hcharge]
      have hbound := splice.lower_stage_add who (time - fuel)
      rw [Nat.add_sub_of_le hle] at hbound
      exact hbound
  upper_supermartingale := by
    intro who time
    by_cases htime : time < fuel
    · exact splice.upper_supermartingale_of_lt who time htime
    · have hle : fuel ≤ time := Nat.le_of_not_gt htime
      have hbound :=
        splice.upper_supermartingale_add who (time - fuel)
      rw [Nat.add_sub_of_le hle] at hbound
      exact hbound
  upper_stage := by
    intro who time
    by_cases htime : time < fuel
    · exact splice.upper_stage_of_lt bounds who time htime
    · have hle : fuel ≤ time := Nat.le_of_not_gt htime
      have hcharge :
          splice.upperCharge bounds who time =
            splice.suffixUpperCharge who (time - fuel) := by
        simp [upperCharge, htime]
      rw [hcharge]
      have hbound := splice.upper_stage_add who (time - fuel)
      rw [Nat.add_sub_of_le hle] at hbound
      exact hbound
  deviation_supermartingale := by
    intro who deviation time
    by_cases htime : time < fuel
    · exact splice.deviation_supermartingale_of_lt
        who deviation time htime
    · have hle : fuel ≤ time := Nat.le_of_not_gt htime
      have hbound :=
        splice.deviation_supermartingale_add
          who deviation (time - fuel)
      rw [Nat.add_sub_of_le hle] at hbound
      exact hbound
  deviation_stage := by
    intro who deviation time
    by_cases htime : time < fuel
    · exact splice.deviation_stage_of_lt
        bounds who deviation time htime
    · have hle : fuel ≤ time := Nat.le_of_not_gt htime
      have hcharge :
          splice.deviationCharge bounds who deviation time =
            splice.suffixDeviationCharge
              who deviation (time - fuel) := by
        simp [deviationCharge, htime]
      rw [hcharge]
      have hbound :=
        splice.deviation_stage_add who deviation (time - fuel)
      rw [Nat.add_sub_of_le hle] at hbound
      exact hbound
  lower_charge_cesaro := by
    intro who total htotal
    have hfuelTotal : fuel ≤ total := by
      exact le_trans (Nat.le_add_right fuel family.commonHorizon)
        (le_trans (Nat.le_max_right _ _) htotal)
    have hsuffix :
        family.commonHorizon ≤ total - fuel := by
      have hcombined : fuel + family.commonHorizon ≤ total :=
        le_trans (Nat.le_max_right _ _) htotal
      omega
    have haccounting : accountingHorizon ≤ total :=
      le_trans (Nat.le_max_left _ _) htotal
    have hbound :=
      splice.lowerCharge_cesaro_add bounds who (total - fuel)
        hsuffix (by simpa [Nat.add_sub_of_le hfuelTotal]
          using haccounting)
    simpa only [Nat.add_sub_of_le hfuelTotal] using hbound
  upper_charge_cesaro := by
    intro who total htotal
    have hfuelTotal : fuel ≤ total := by
      exact le_trans (Nat.le_add_right fuel family.commonHorizon)
        (le_trans (Nat.le_max_right _ _) htotal)
    have hsuffix :
        family.commonHorizon ≤ total - fuel := by
      have hcombined : fuel + family.commonHorizon ≤ total :=
        le_trans (Nat.le_max_right _ _) htotal
      omega
    have haccounting : accountingHorizon ≤ total :=
      le_trans (Nat.le_max_left _ _) htotal
    have hbound :=
      splice.upperCharge_cesaro_add bounds who (total - fuel)
        hsuffix (by simpa [Nat.add_sub_of_le hfuelTotal]
          using haccounting)
    simpa only [Nat.add_sub_of_le hfuelTotal] using hbound
  deviation_charge_cesaro := by
    intro who deviation total htotal
    have hfuelTotal : fuel ≤ total := by
      exact le_trans (Nat.le_add_right fuel family.commonHorizon)
        (le_trans (Nat.le_max_right _ _) htotal)
    have hsuffix :
        family.commonHorizon ≤ total - fuel := by
      have hcombined : fuel + family.commonHorizon ≤ total :=
        le_trans (Nat.le_max_right _ _) htotal
      omega
    have haccounting : accountingHorizon ≤ total :=
      le_trans (Nat.le_max_left _ _) htotal
    have hbound :=
      splice.deviationCharge_cesaro_add bounds who deviation
        (total - fuel) hsuffix
        (by simpa [Nat.add_sub_of_le hfuelTotal]
          using haccounting)
    simpa only [Nat.add_sub_of_le hfuelTotal] using hbound

end FixedDepthAdaptivePotentialSplice

end StochasticGame
end GameTheory
