/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.OrdinaryNonQProducer
import UniformEquilibrium.Quitting.AbsorptionPath.NormalizedFiniteWindowOccupation
import UniformEquilibrium.Quitting.Cycles.PeriodOneTangentAtlas

/-!
# Punctured analytic support and the corrected normal hierarchy

The projective packet remembers only the least-order quitting coordinates.
For the ordinary non-Q argument one needs the stronger fact that *every*
coordinate which is present on the punctured analytic germ belongs to the
corrected normal core.  This file starts from the exact analytic support,
where an analytic nonnegative quit rate is either identically zero or
strictly positive on a common punctured neighbourhood.

The game-theoretic induction is kept separate from the ordinary producer so
that the latter can consume the hierarchy theorem without sharing an edit
surface with its analytic-endpoint case split.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open Filter Set Topology
open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A player is present in the punctured support of a quitting Bellman germ
when its analytic quit-rate coordinate is not the zero right germ. -/
def QuittingGermEventuallyActive
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm) (who : ι) : Prop :=
  ¬∀ᶠ t in 𝓝[>] (0 : ℝ), quittingGermQuitRate g who t = 0

/-- Every punctured-support coordinate is eventually strictly positive. -/
theorem eventually_quittingGermQuitRate_pos_of_eventuallyActive
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm) {who : ι}
    (hactive : QuittingGermEventuallyActive g who) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < quittingGermQuitRate g who t := by
  rcases Math.analyticAt_eventually_eq_zero_or_pos_of_eventually_nonneg
      (analyticAt_quittingGermQuitRate g who)
      (eventually_quittingGermQuitRate_nonneg g who) with hzero | hpos
  · exact False.elim (hactive hzero)
  · exact hpos

/-- A positive endpoint marginal is present in the punctured analytic
support. -/
theorem quittingGerm_eventuallyActive_of_endpoint_quit_pos
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm) {who : ι}
    (hpositive : 0 < ((g.endpointProfile none who) true).toReal) :
    QuittingGermEventuallyActive g who := by
  intro hzero
  have hvalueZero : quittingGermQuitRate g who 0 = 0 := by
    have hlimit : Tendsto (quittingGermQuitRate g who)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (quittingGermQuitRate g who 0)) :=
      (analyticAt_quittingGermQuitRate g who).continuousAt.tendsto.mono_left
        inf_le_left
    have hzeroLimit : Tendsto (quittingGermQuitRate g who)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) :=
      tendsto_const_nhds.congr' (hzero.mono fun _ ht => ht.symm)
    exact tendsto_nhds_unique hlimit hzeroLimit
  rw [quittingGerm_endpointProfile_apply_true_toReal, hvalueZero] at hpositive
  exact lt_irrefl 0 hpositive

/-- All analytic quit coordinates have one simultaneous exact punctured
support: positive exactly on `QuittingGermEventuallyActive`. -/
theorem eventually_quittingGermQuitRate_pos_iff_eventuallyActive
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ who,
      0 < quittingGermQuitRate g who t ↔
        QuittingGermEventuallyActive g who := by
  apply Filter.eventually_all.mpr
  intro who
  by_cases hactive : QuittingGermEventuallyActive g who
  · filter_upwards
      [eventually_quittingGermQuitRate_pos_of_eventuallyActive g hactive]
      with t ht
    exact ⟨fun _ => hactive, fun _ => ht⟩
  · have hzero : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        quittingGermQuitRate g who t = 0 := by
      simpa [QuittingGermEventuallyActive] using hactive
    filter_upwards [hzero] with t ht
    exact ⟨fun hpos => False.elim ((ne_of_gt hpos) ht),
      fun h => False.elim (hactive h)⟩

/-- At an all-Continue endpoint every opponent-forced continuation mass tends
to one. -/
theorem tendsto_quittingGerm_fixedOpponentsContinueMass_one
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (hcontinue :
      quittingStationaryContinueMass (g.endpointProfile none) = 1)
    (who : ι) :
    Tendsto (fun t : ℝ =>
        ∏ other ∈ Finset.univ.erase who,
          (1 - quittingGermQuitRate g other t))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hrates : ∀ other,
      Tendsto (fun t : ℝ => 1 - quittingGermQuitRate g other t)
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    intro other
    simpa using tendsto_const_nhds.sub
      (quittingGermQuitRate_tendsto_zero_of_endpoint_allContinue
        g hcontinue other)
  simpa using tendsto_finsetProd (Finset.univ.erase who)
    (fun other _ => hrates other)

/-- If the endpoint opponents of `who` Continue surely, every one of their
analytic Quit coordinates tends to zero from the right.  Unlike the usual
all-Continue specialization, this permits `who` itself to have positive
endpoint Quit probability. -/
theorem quittingGermQuitRate_tendsto_zero_of_endpoint_fixedOpponents
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm) (who : ι)
    (hfixed : quittingStationaryFixedOpponentsContinueMass
      (g.endpointProfile none) who = 1)
    (other : ι) (hne : other ≠ who) :
    Tendsto (quittingGermQuitRate g other)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
  have hzero : quittingGermQuitRate g other 0 = 0 := by
    rw [← quittingGerm_endpointProfile_apply_true_toReal g other]
    exact quittingProbability_eq_zero_of_fixedOpponentsContinueMass_eq_one
      (g.endpointProfile none) who other hne hfixed
  have h := (analyticAt_quittingGermQuitRate g other).continuousAt.tendsto
    |>.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simpa [hzero] using h

/-! ## The exact cleared Continue inequality -/

/-- If a player has positive Quit probability at a genuine point of the
germ, complementarity identifies its value with the discounted pure-Quit
endpoint.  The pure-Continue Bellman inequality can therefore be cleared of
the positive discount factor.  This is the exact (pre-limit) inequality used
by the normal-layer induction. -/
theorem quittingGerm_forcedContinue_signal_nonpos_of_quit_pos
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) g.radius) (ht1 : t < 1)
    (who : ι) (hquit : 0 < quittingGermQuitRate g who t) :
    quittingStationaryFixedOpponentsContinueReward reward
          (quittingGermRoot g ht) who -
        (1 - quittingStationaryFixedOpponentsContinueMass
              (quittingGermRoot g ht) who *
            (1 - t ^ g.ramification)) *
          quittingStationaryFixedOpponentsQuitValue reward
            (quittingGermRoot g ht) who ≤ 0 := by
  let root := quittingGermRoot g ht
  let value := quittingGermValue g t
  let beta := 1 - t ^ g.ramification
  let quit := quittingStationaryFixedOpponentsQuitValue reward root who
  let intercept :=
    quittingStationaryFixedOpponentsContinueReward reward root who
  let mass := quittingStationaryFixedOpponentsContinueMass root who
  have hbeta : 0 < beta := quittingGerm_discountFactor_pos g ht ht1
  have hnash : IsεQuittingRootEndpointNash reward value 0 root :=
    isεQuittingRootEndpointNash_quittingGermRoot g ht ht1
  have hrootQuit : 0 < (root who true).toReal := by
    simpa [root, quittingGermRoot_apply_true_toReal g ht] using hquit
  have hquitWho :
      quittingRootQuitPayoff reward value root who =
        quittingRootSuccessorPayoff reward value root who :=
    quittingRootQuitPayoff_eq_successor_of_endpointNash_of_quit_pos
      reward value root who hnash hrootQuit
  have hvalue : value who = beta * quit := by
    have hrec := quittingGermValue_eq_smul_rootSuccessorPayoff g ht who
    have hquitStationary :
        quittingRootQuitPayoff reward value root who = quit := by
      simpa [root, quit] using
        (quittingRootQuitPayoff_eq_stationaryFixedOpponentsQuitValue'
          reward value root who)
    change value who = beta *
      quittingRootSuccessorPayoff reward value root who at hrec
    rw [← hquitWho, hquitStationary] at hrec
    exact hrec
  have hcontinue := quittingGerm_bestResponse_continue g ht who
  have hcontinueSplit :
      quittingRootContinuePayoff reward value root who =
        intercept + mass * value who := by
    simpa [root, value, intercept, mass] using
      (quittingRootContinuePayoff_eq_stationaryFixedOpponents'
        reward value root who)
  change beta *
      quittingRootContinuePayoff reward value root who ≤ value who at hcontinue
  rw [hcontinueSplit, hvalue] at hcontinue
  have this : intercept + mass * (beta * quit) ≤ quit := by
    nlinarith
  change intercept - (1 - mass * beta) * quit ≤ 0
  change intercept + mass * (beta * quit) ≤ quit at this
  linarith

/-! ## The finite sign core of one hierarchy step -/

omit [DecidableEq ι] in
/-- A nonpositive cleared Continue signal cannot be assembled from a positive
cemetery coefficient and strictly positive singleton columns.  This is the
finite-dimensional sign argument at the end of every normal-layer step; the
analytic limit only has to supply such coefficients and the exact identity.
-/
theorem exists_nonpositive_singleton_of_nonpositive_hierarchy_signal
    (M : ι → ι → ℝ) (q : ι → ℝ) (who : ι)
    (cemetery : ℝ) (singleton : ι → ℝ) (error : ℝ)
    (hq : 0 < q who)
    (hcemetery : 0 ≤ cemetery)
    (hsingleton : ∀ owner, 0 ≤ singleton owner)
    (htotal : 0 < cemetery + ∑ owner, singleton owner)
    (herror : 0 ≤ error)
    (hsignal :
      cemetery * q who + ∑ owner, singleton owner * M who owner + error ≤ 0) :
    ∃ owner, 0 < singleton owner ∧ M who owner ≤ 0 := by
  classical
  by_contra hwitness
  push Not at hwitness
  have hterms : ∀ other, 0 ≤ singleton other * M who other := by
    intro other
    by_cases hz : singleton other = 0
    · simp [hz]
    · exact mul_nonneg (hsingleton other)
        (hwitness other
          (lt_of_le_of_ne (hsingleton other) (Ne.symm hz))).le
  have hsum0 : 0 ≤ ∑ other, singleton other * M who other :=
    Finset.sum_nonneg fun other _ => hterms other
  by_cases hc : cemetery = 0
  · have hsum : 0 < ∑ owner, singleton owner := by
      rw [hc, zero_add] at htotal
      exact htotal
    obtain ⟨owner, -, howner⟩ := Finset.exists_lt_of_sum_lt
      (show ∑ _owner : ι, (0 : ℝ) < ∑ owner, singleton owner by simpa using hsum)
    have hstrict : 0 < singleton owner * M who owner :=
      mul_pos howner (hwitness owner howner)
    have hsumPos : 0 < ∑ other, singleton other * M who other :=
      Finset.sum_pos' (fun other _ => hterms other)
        ⟨owner, Finset.mem_univ owner, hstrict⟩
    rw [hc, zero_mul, zero_add] at hsignal
    linarith
  · have hcpos : 0 < cemetery := lt_of_le_of_ne hcemetery (Ne.symm hc)
    nlinarith

/-! ## The opponent first-event normalization -/

/-- A total root-valued representative of the punctured analytic root.  Its
value away from the genuine germ domain is immaterial; making it total lets
the usual filter API state limits without carrying a proof argument through
every function. -/
def quittingGermPuncturedRoot
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm) (t : ℝ) :
    ι → PMF Bool :=
  if ht : t ∈ Ioo (0 : ℝ) g.radius then quittingGermRoot g ht
  else quittingAllContinueRoot

/-- Root obtained by forcing one player to Continue along the punctured
analytic branch. -/
def quittingGermForcedContinueRoot
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm) (who : ι) (t : ℝ) :
    ι → PMF Bool :=
  Function.update (quittingGermPuncturedRoot g t) who (PMF.pure false)

theorem eventually_quittingGermPuncturedRoot_eq
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
      ∀ ht : t ∈ Ioo (0 : ℝ) g.radius,
        quittingGermPuncturedRoot g t = quittingGermRoot g ht := by
  filter_upwards [eventually_mem_Ioo_radius g] with t ht
  intro ht'
  simp [quittingGermPuncturedRoot, ht]

/-- In the opponent normalization, `none` is the discount/cemetery clock and
`some owner` is that owner's quit-rate clock, with the observed player
deleted. -/
def quittingGermOpponentClock
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm) (who : ι) :
    Option ι → ℝ → ℝ
  | none, t => t ^ g.ramification
  | some owner, t => if owner = who then 0 else quittingGermQuitRate g owner t

@[simp] theorem quittingGermOpponentClock_none
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm) (who : ι) (t : ℝ) :
    quittingGermOpponentClock g who none t = t ^ g.ramification := rfl

@[simp] theorem quittingGermOpponentClock_some
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (who owner : ι) (t : ℝ) :
    quittingGermOpponentClock g who (some owner) t =
      if owner = who then 0 else quittingGermQuitRate g owner t := rfl

theorem analyticAt_quittingGermOpponentClock
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm) (who : ι)
    (clock : Option ι) :
    AnalyticAt ℝ (quittingGermOpponentClock g who clock) 0 := by
  cases clock with
  | none => exact analyticAt_id.pow g.ramification
  | some owner =>
      by_cases howner : owner = who
      · subst owner
        change AnalyticAt ℝ
          (fun t => quittingGermOpponentClock g who (some who) t) 0
        simpa only [quittingGermOpponentClock_some, if_pos] using
          (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => (0 : ℝ)) 0)
      · change AnalyticAt ℝ
          (fun t => quittingGermOpponentClock g who (some owner) t) 0
        simpa only [quittingGermOpponentClock_some, if_neg howner] using
          analyticAt_quittingGermQuitRate g owner

theorem eventually_quittingGermOpponentClock_nonneg
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm) (who : ι)
    (clock : Option ι) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
      0 ≤ quittingGermOpponentClock g who clock t := by
  cases clock with
  | none =>
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact pow_nonneg ht.le _
  | some owner =>
      by_cases howner : owner = who
      · simp [quittingGermOpponentClock, howner]
      · simpa [quittingGermOpponentClock, howner] using
          eventually_quittingGermQuitRate_nonneg g owner

theorem not_eventually_quittingGermOpponentClock_none_eq_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm) (who : ι) :
    ¬∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
      quittingGermOpponentClock g who none t = 0 := by
  intro hzero
  have hpos : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), 0 < t :=
    self_mem_nhdsWithin
  obtain ⟨t, ht, hz⟩ :=
    (hpos.and hzero).exists
  exact (pow_ne_zero g.ramification (ne_of_gt ht)) hz

/-- Leading Taylor data for the race between discount and the opponents'
first Quit clocks.  Unlike the global projective packet, this normalization
deletes the selected player's own clock, so it also sees opponents which
vanish at a strictly faster analytic order. -/
structure QuittingGermOpponentLeadingData
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm) (who : ι) where
  jet : Math.LeadingOrderJet (quittingGermOpponentClock g who)

theorem nonempty_quittingGermOpponentLeadingData
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm) (who : ι) :
    Nonempty (QuittingGermOpponentLeadingData g who) := by
  obtain ⟨jet⟩ := Math.exists_leadingOrderJet
    (fun clock => analyticAt_quittingGermOpponentClock g who clock)
    ⟨none, not_eventually_quittingGermOpponentClock_none_eq_zero g who⟩
  exact ⟨⟨jet⟩⟩

namespace QuittingGermOpponentLeadingData

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {g : (quittingGame reward).AnalyticBellmanGerm} {who : ι}

def totalCoefficient (data : QuittingGermOpponentLeadingData g who) : ℝ :=
  ∑ clock, data.jet.cofactor clock 0

def clockWeight (data : QuittingGermOpponentLeadingData g who)
    (clock : Option ι) : ℝ :=
  data.jet.cofactor clock 0 / data.totalCoefficient

def cemeteryWeight (data : QuittingGermOpponentLeadingData g who) : ℝ :=
  data.clockWeight none

def singletonWeight (data : QuittingGermOpponentLeadingData g who)
    (owner : ι) : ℝ :=
  data.clockWeight (some owner)

theorem totalCoefficient_pos
    (data : QuittingGermOpponentLeadingData g who) :
    0 < data.totalCoefficient := by
  exact data.jet.sum_cofactor_zero_pos
    (fun clock => eventually_quittingGermOpponentClock_nonneg g who clock)

theorem clockWeight_nonneg
    (data : QuittingGermOpponentLeadingData g who) (clock : Option ι) :
    0 ≤ data.clockWeight clock := by
  exact div_nonneg
    (data.jet.cofactor_zero_nonneg
      (eventually_quittingGermOpponentClock_nonneg g who clock))
    data.totalCoefficient_pos.le

theorem cemeteryWeight_nonneg
    (data : QuittingGermOpponentLeadingData g who) :
    0 ≤ data.cemeteryWeight := data.clockWeight_nonneg none

theorem singletonWeight_nonneg
    (data : QuittingGermOpponentLeadingData g who) (owner : ι) :
    0 ≤ data.singletonWeight owner := data.clockWeight_nonneg (some owner)

@[simp] theorem singletonWeight_self
    (data : QuittingGermOpponentLeadingData g who) :
    data.singletonWeight who = 0 := by
  unfold singletonWeight clockWeight
  have hzero : data.jet.cofactor (some who) 0 = 0 := by
    by_contra hne
    have horder := data.jet.analyticOrderAt_eq_order hne
    have htop : analyticOrderAt
        (quittingGermOpponentClock g who (some who)) 0 = ⊤ := by
      rw [show quittingGermOpponentClock g who (some who) =
          (fun _ : ℝ => 0) by
        funext t
        simp]
      exact analyticOrderAt_eq_top.mpr (Filter.Eventually.of_forall fun _ => rfl)
    rw [htop] at horder
    exact WithTop.coe_ne_top horder.symm
  rw [hzero, zero_div]

theorem cemetery_add_sum_singletonWeight
    (data : QuittingGermOpponentLeadingData g who) :
    data.cemeteryWeight + ∑ owner, data.singletonWeight owner = 1 := by
  unfold cemeteryWeight singletonWeight clockWeight totalCoefficient
  have hden : (∑ clock : Option ι, data.jet.cofactor clock 0) ≠ 0 :=
    data.totalCoefficient_pos.ne'
  calc
    data.jet.cofactor none 0 / ∑ clock, data.jet.cofactor clock 0 +
          ∑ owner, data.jet.cofactor (some owner) 0 /
            ∑ clock, data.jet.cofactor clock 0 =
        (data.jet.cofactor none 0 +
          ∑ owner, data.jet.cofactor (some owner) 0) /
            ∑ clock, data.jet.cofactor clock 0 := by
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul]
      ring
    _ = (∑ clock : Option ι, data.jet.cofactor clock 0) /
          ∑ clock, data.jet.cofactor clock 0 := by
      rw [Fintype.sum_option]
    _ = 1 := div_self hden

theorem clock_div_sum_tendsto
    (data : QuittingGermOpponentLeadingData g who) (clock : Option ι) :
    Tendsto
      (fun t => quittingGermOpponentClock g who clock t /
        ∑ other, quittingGermOpponentClock g who other t)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (data.clockWeight clock)) := by
  exact data.jet.tendsto_div_sum
    (fun item => eventually_quittingGermOpponentClock_nonneg g who item) clock

theorem eventually_clock_sum_pos
    (data : QuittingGermOpponentLeadingData g who) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
      0 < ∑ clock, quittingGermOpponentClock g who clock t :=
  data.jet.eventually_sum_pos
    (fun clock => eventually_quittingGermOpponentClock_nonneg g who clock)

end QuittingGermOpponentLeadingData

/-
/-- The deleted opponent marginal Quit sum tends to zero at an all-Continue
endpoint. -/
theorem tendsto_quittingGermOpponentQuitSum_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (who : ι)
    (hfixed : quittingStationaryFixedOpponentsContinueMass
      (g.endpointProfile none) who = 1) :
    Tendsto (quittingGermOpponentQuitSum g who)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
  have htotal := tendsto_sum_quittingGermOpponentClock_zero g who hfixed
  have hdiscount := Math.tendsto_pow_nhdsGT_zero g.ramification_pos.ne'
  have h := htotal.sub hdiscount
  have h' : Tendsto
      (fun t => (∑ clock, quittingGermOpponentClock g who clock t) -
        t ^ g.ramification)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
    simpa using h
  refine h'.congr' ?_
  exact Filter.Eventually.of_forall fun t => by
    change (∑ clock, quittingGermOpponentClock g who clock t) -
      t ^ g.ramification = quittingGermOpponentQuitSum g who t
    rw [sum_quittingGermOpponentClock]
    ring

/-- Opponent absorption vanishes at an all-Continue endpoint. -/
theorem tendsto_quittingGermOpponentAbsorption_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (who : ι)
    (hfixed : quittingStationaryFixedOpponentsContinueMass
      (g.endpointProfile none) who = 1) :
    Tendsto
      (fun t => quittingRootAbsorptionMass
        (quittingGermForcedContinueRoot g who t))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun t =>
      quittingRootAbsorptionMass_nonneg _
  · exact eventually_opponentAbsorption_le_quitSum g who
  · exact tendsto_quittingGermOpponentQuitSum_zero g who hfixed

/-- Immediate quitting against the punctured root converges to the selected
player's singleton payoff. -/
theorem tendsto_quittingGermPuncturedRoot_quitValue_singleton
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (who : ι)
    (hfixed : quittingStationaryFixedOpponentsContinueMass
      (g.endpointProfile none) who = 1) :
    Tendsto
      (fun t => quittingStationaryFixedOpponentsQuitValue reward
        (quittingGermPuncturedRoot g t) who)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (reward (quittingSingletonTerminal who) who)) := by
  let difference : ℝ → ℝ := fun t =>
    quittingStationaryFixedOpponentsQuitValue reward
        (quittingGermPuncturedRoot g t) who -
      reward (quittingSingletonTerminal who) who
  have hmajor : Tendsto
      (fun t => 2 * quittingRewardBound reward *
        quittingRootAbsorptionMass (quittingGermForcedContinueRoot g who t))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
    simpa using
      (tendsto_quittingGermOpponentAbsorption_zero g who hfixed).const_mul
        (2 * quittingRewardBound reward)
  have habs : Tendsto (fun t => |difference t|)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun t => abs_nonneg _
    · exact Filter.Eventually.of_forall fun t => by
        simpa [difference, quittingGermForcedContinueRoot] using
          (abs_quittingStationaryFixedOpponentsQuitValue_sub_singleton_le
            (reward := reward) (quittingGermPuncturedRoot g t) who
            (quittingRewardBound_nonneg reward)
            (abs_reward_le_quittingRewardBound reward))
    · exact hmajor
  apply tendsto_iff_norm_sub_tendsto_zero.2
  simpa only [Real.norm_eq_abs] using habs
-/

/-
/-! ## Forced-Continue first-event reward limit -/

/-- Every forced-Continue root coordinate converges to pure Continue at an
all-Continue endpoint. -/
theorem tendsto_quittingGermForcedContinueRoot_continueProbability_one
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (who owner : ι)
    (hfixed : quittingStationaryFixedOpponentsContinueMass
      (g.endpointProfile none) who = 1) :
    Tendsto
      (fun t => ((quittingGermForcedContinueRoot g who t owner) false).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 1) := by
  have hquit : Tendsto
      (fun t => ((quittingGermForcedContinueRoot g who t owner) true).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
    by_cases howner : owner = who
    · subst owner
      simp [quittingGermForcedContinueRoot]
    · have hraw :=
          quittingGermQuitRate_tendsto_zero_of_endpoint_fixedOpponents
            g who hfixed owner howner
      refine hraw.congr' ?_
      filter_upwards
          [eventually_quittingGermForcedContinueRoot_true_toReal g who]
        with t ht
      simpa [howner] using (ht owner).symm
  have hconst : Tendsto (fun _ : ℝ => (1 : ℝ))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 1) := tendsto_const_nhds
  have h := hconst.sub hquit
  have h' : Tendsto
      (fun t => 1 -
        ((quittingGermForcedContinueRoot g who t owner) true).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 1) := by
    simpa using h
  refine h'.congr' ?_
  exact Filter.Eventually.of_forall fun t => by
    have hprob := quittingRoot_continueProbability_add_quitProbability
      (quittingGermForcedContinueRoot g who t) owner
    linarith

/-- The probability that all opponents of any owner Continue in the
forced-`who` root tends to one. -/
theorem tendsto_quittingGermForcedContinue_fixedOpponentsContinueMass_one
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (who owner : ι)
    (hfixed : quittingStationaryFixedOpponentsContinueMass
      (g.endpointProfile none) who = 1) :
    Tendsto
      (fun t => quittingStationaryFixedOpponentsContinueMass
        (quittingGermForcedContinueRoot g who t) owner)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 1) := by
  have hprod : Tendsto
      (fun t => ∏ other ∈ Finset.univ.erase owner,
        ((quittingGermForcedContinueRoot g who t other) false).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 1) := by
    simpa using tendsto_finsetProd (Finset.univ.erase owner)
      (fun other _ =>
        tendsto_quittingGermForcedContinueRoot_continueProbability_one
          g who other hfixed)
  refine hprod.congr' ?_
  exact Filter.Eventually.of_forall fun t => by
    unfold quittingStationaryFixedOpponentsContinueMass
      quittingFixedOpponentsContinueMass
    rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    simp only [Function.update, Finset.prod_ite_irrel, Finset.mem_erase,
      Finset.mem_univ, true_and]
    apply Finset.prod_congr rfl
    intro other hother
    simp [hother.1]

namespace QuittingGermOpponentLeadingData

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {g : (quittingGame reward).AnalyticBellmanGerm} {who : ι}

/-- Each forced-Continue singleton event has the clock weight prescribed by
the opponent leading normalization. -/
theorem singletonCoalitionMass_div_clockSum_tendsto
    (data : QuittingGermOpponentLeadingData g who)
    (owner : ι)
    (hfixed : quittingStationaryFixedOpponentsContinueMass
      (g.endpointProfile none) who = 1) :
    Tendsto
      (fun t => quittingRootCoalitionMass
          (quittingGermForcedContinueRoot g who t) {owner} /
            ∑ clock, quittingGermOpponentClock g who clock t)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (data.singletonWeight owner)) := by
  have hcontinueMass :=
    tendsto_quittingGermForcedContinue_fixedOpponentsContinueMass_one
      g who owner hfixed
  have hclock := data.clock_div_sum_tendsto (some owner)
  have h := hcontinueMass.mul hclock
  refine h.congr' ?_
  filter_upwards
      [eventually_quittingGermForcedContinueRoot_true_toReal g who]
    with t hroot
  rw [quittingRootCoalitionMass_singleton_eq_opponentContinue_mul_quit]
  have hrate :
      ((quittingGermForcedContinueRoot g who t owner) true).toReal =
        quittingGermOpponentClock g who (some owner) t := by
    simpa [quittingGermOpponentClock_some] using hroot owner
  rw [hrate]
  ring

/-- Collision reward is negligible on the opponent clock scale. -/
theorem collisionReward_div_clockSum_tendsto_zero
    (data : QuittingGermOpponentLeadingData g who)
    (coordinate : ι)
    (hfixed : quittingStationaryFixedOpponentsContinueMass
      (g.endpointProfile none) who = 1) :
    Tendsto
      (fun t => rootCollisionRewardContribution reward
          (quittingGermForcedContinueRoot g who t) coordinate /
            ∑ clock, quittingGermOpponentClock g who clock t)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
  let scale : ℝ → ℝ := fun t =>
    ∑ clock, quittingGermOpponentClock g who clock t
  let error : ℝ → ℝ := fun t =>
    rootCollisionRewardContribution reward
      (quittingGermForcedContinueRoot g who t) coordinate
  let C : ℝ := quittingRewardBound reward * (Fintype.card ι).choose 2
  have hC : 0 ≤ C := mul_nonneg (quittingRewardBound_nonneg reward) (Nat.cast_nonneg _)
  have hbound : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
      |error t| ≤ C * (scale t) ^ 2 := by
    filter_upwards [eventually_opponentAbsorption_le_quitSum g who,
        eventually_quittingGermOpponentQuitSum_nonneg g who,
        self_mem_nhdsWithin]
      with t habs hquit ht
    let root := quittingGermForcedContinueRoot g who t
    have hreward := abs_rootCollisionRewardContribution_le
      reward root coordinate (abs_reward_le_quittingRewardBound reward)
    have hcollision :=
      quittingRootCollisionMass_le_choose_card_mul_absorption_sq root
    have hscaleEq : scale t =
        t ^ g.ramification + quittingGermOpponentQuitSum g who t :=
      sum_quittingGermOpponentClock g who t
    have hscaleNonneg : 0 ≤ scale t := by
      rw [hscaleEq]
      exact add_nonneg (pow_nonneg ht.le _) hquit
    have hquitScale : quittingGermOpponentQuitSum g who t ≤ scale t := by
      rw [hscaleEq]
      exact le_add_of_nonneg_left (pow_nonneg ht.le _)
    have habsScale : quittingRootAbsorptionMass root ≤ scale t :=
      habs.trans hquitScale
    have habsNonneg := quittingRootAbsorptionMass_nonneg root
    have hsquare : quittingRootAbsorptionMass root ^ 2 ≤ scale t ^ 2 :=
      (sq_le_sq₀ habsNonneg hscaleNonneg).2 habsScale
    change |error t| ≤ C * scale t ^ 2
    calc
      |error t| ≤ quittingRewardBound reward *
          quittingRootCollisionMass root := hreward
      _ ≤ quittingRewardBound reward *
          ((Fintype.card ι).choose 2 *
            quittingRootAbsorptionMass root ^ 2) := by
        gcongr
      _ ≤ C * scale t ^ 2 := by
        dsimp only [C]
        gcongr
  exact tendsto_div_zero_of_abs_le_const_mul_sq hC
    data.eventually_clock_sum_pos
    (tendsto_sum_quittingGermOpponentClock_zero g who hfixed)
    hbound

/-- The forced-Continue absorbing contribution converges, after opponent
first-event normalization, to the singleton reward mixture selected by the
opponent leading clocks. -/
theorem continueReward_div_clockSum_tendsto_singletonMix
    (data : QuittingGermOpponentLeadingData g who)
    (hfixed : quittingStationaryFixedOpponentsContinueMass
      (g.endpointProfile none) who = 1) :
    Tendsto
      (fun t => quittingStationaryFixedOpponentsContinueReward reward
          (quittingGermPuncturedRoot g t) who /
            ∑ clock, quittingGermOpponentClock g who clock t)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∑ owner, data.singletonWeight owner *
        reward (quittingSingletonTerminal owner) who)) := by
  have hsingle := tendsto_finsetSum (Finset.univ : Finset ι)
    (fun owner _ =>
      (data.singletonCoalitionMass_div_clockSum_tendsto hcontinue owner).mul
        tendsto_const_nhds)
  have hcollision := data.collisionReward_div_clockSum_tendsto_zero
    hcontinue who
  have h := hsingle.add hcollision
  refine h.congr' ?_
  filter_upwards [data.eventually_clock_sum_pos] with t hscale
  have hdecomp := quittingRootAbsorbingContribution_eq_singleton_add_collision
    reward (quittingGermForcedContinueRoot g who t) who
  unfold quittingStationaryFixedOpponentsContinueReward
    quittingFixedOpponentsContinueReward
  change quittingRootAbsorbingContribution reward
      (quittingGermForcedContinueRoot g who t) who /
        (∑ clock, quittingGermOpponentClock g who clock t) = _
  rw [hdecomp]
  field_simp [hscale.ne']
  ring

end QuittingGermOpponentLeadingData
-/

/-! ## Vanishing quadratic remainders -/

/-- A quadratic remainder is negligible after division by a positive scale
which tends to zero. -/
theorem tendsto_div_zero_of_abs_le_const_mul_sq
    {f scale : ℝ → ℝ} {C : ℝ}
    (hscalePos : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), 0 < scale t)
    (hscaleZero : Tendsto scale (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0))
    (hbound : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
      |f t| ≤ C * (scale t) ^ 2) :
    Tendsto (fun t => f t / scale t)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
  have hmajor : Tendsto (fun t => C * scale t)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
    simpa using hscaleZero.const_mul C
  have habs : Tendsto (fun t => |f t / scale t|)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun t => abs_nonneg _
    · filter_upwards [hscalePos, hbound] with t hs hb
      calc
        |f t / scale t| = |f t| / scale t := by
          rw [abs_div, abs_of_pos hs]
        _ ≤ (C * scale t ^ 2) / scale t :=
          div_le_div_of_nonneg_right hb hs.le
        _ = C * scale t := by
          field_simp [hs.ne']
    · exact hmajor
  apply tendsto_iff_norm_sub_tendsto_zero.2
  simpa only [Real.norm_eq_abs, sub_zero] using habs

/-- Sum of all opponent Quit clocks, with the observed player's coordinate
literally deleted. -/
def quittingGermOpponentQuitSum
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm) (who : ι) (t : ℝ) : ℝ :=
  ∑ owner, if owner = who then 0 else quittingGermQuitRate g owner t

/-- Exact total of the option-indexed opponent clock family. -/
theorem sum_quittingGermOpponentClock
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm) (who : ι) (t : ℝ) :
    (∑ clock, quittingGermOpponentClock g who clock t) =
      t ^ g.ramification + quittingGermOpponentQuitSum g who t := by
  rw [Fintype.sum_option]
  rfl

/-- The opponent clock total tends to zero when the selected player's
endpoint opponents Continue surely. -/
theorem tendsto_sum_quittingGermOpponentClock_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (who : ι)
    (hfixed : quittingStationaryFixedOpponentsContinueMass
      (g.endpointProfile none) who = 1) :
    Tendsto (fun t => ∑ clock, quittingGermOpponentClock g who clock t)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
  have hclock : ∀ clock : Option ι,
      Tendsto (quittingGermOpponentClock g who clock)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
    intro clock
    cases clock with
    | none =>
        change Tendsto
          (fun t => quittingGermOpponentClock g who none t)
          (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0)
        simpa only [quittingGermOpponentClock_none] using
          Math.tendsto_pow_nhdsGT_zero g.ramification_pos.ne'
    | some owner =>
        by_cases howner : owner = who
        · subst owner
          change Tendsto
            (fun t => quittingGermOpponentClock g who (some who) t)
            (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0)
          simpa only [quittingGermOpponentClock_some, if_pos] using
            (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ))
              (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0))
        · change Tendsto
            (fun t => quittingGermOpponentClock g who (some owner) t)
            (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0)
          simpa only [quittingGermOpponentClock_some, if_neg howner] using
            quittingGermQuitRate_tendsto_zero_of_endpoint_fixedOpponents
              g who hfixed owner howner
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Option ι))
    (fun clock _ => hclock clock)
  simpa using hsum

/-- On the actual punctured branch, the total root representative has the
analytic real quit rates. -/
theorem eventually_quittingGermPuncturedRoot_true_toReal
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), ∀ owner,
      ((quittingGermPuncturedRoot g t owner) true).toReal =
        quittingGermQuitRate g owner t := by
  filter_upwards [eventually_mem_Ioo_radius g] with t ht
  intro owner
  simp [quittingGermPuncturedRoot, ht,
    quittingGermRoot_apply_true_toReal g ht]

/-- After forcing `who` to Continue, its quit rate is zero and every other
rate remains the analytic coordinate. -/
theorem eventually_quittingGermForcedContinueRoot_true_toReal
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm) (who : ι) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), ∀ owner,
      ((quittingGermForcedContinueRoot g who t owner) true).toReal =
        if owner = who then 0 else quittingGermQuitRate g owner t := by
  filter_upwards [eventually_quittingGermPuncturedRoot_true_toReal g]
    with t ht
  intro owner
  by_cases howner : owner = who
  · subst owner
    simp [quittingGermForcedContinueRoot]
  · simp [quittingGermForcedContinueRoot, Function.update, howner, ht owner]

/-- Exact first-event denominator for discount versus absorption by the
opponents of `who`. -/
def quittingGermOpponentFirstEventDenominator
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm) (who : ι) (t : ℝ) : ℝ :=
  t ^ g.ramification + (1 - t ^ g.ramification) *
    quittingRootAbsorptionMass (quittingGermForcedContinueRoot g who t)

/-- The forced-opponent absorption mass differs from the sum of the opponent
quit rates only at quadratic collision order. -/
theorem eventually_abs_opponentAbsorption_sub_quitSum_le
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm) (who : ι) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
      |quittingRootAbsorptionMass
          (quittingGermForcedContinueRoot g who t) -
        quittingGermOpponentQuitSum g who t| ≤
          (quittingGermOpponentQuitSum g who t) ^ 2 / 2 := by
  filter_upwards [eventually_mem_Ioo_radius g,
      eventually_quittingGermForcedContinueRoot_true_toReal g who]
    with t ht hroot
  let rates : ι → ℝ :=
    fun owner => if owner = who then 0 else quittingGermQuitRate g owner t
  have h0 : ∀ owner, 0 ≤ rates owner := by
    intro owner
    by_cases howner : owner = who
    · simp [rates, howner]
    · simp only [rates, if_neg howner]
      exact quittingGermQuitRate_nonneg g ht owner
  have h1 : ∀ owner, rates owner ≤ 1 := by
    intro owner
    by_cases howner : owner = who
    · simp [rates, howner]
    · simp only [rates, if_neg howner]
      exact quittingGermQuitRate_le_one g ht owner
  have hmass : quittingRootAbsorptionMass
        (quittingGermForcedContinueRoot g who t) =
      1 - ∏ owner, (1 - rates owner) := by
    unfold quittingRootAbsorptionMass
    rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    congr 1
    apply Finset.prod_congr rfl
    intro owner _
    have hprob := quittingRoot_continueProbability_add_quitProbability
      (quittingGermForcedContinueRoot g who t) owner
    have hrate :
        ((quittingGermForcedContinueRoot g who t owner) true).toReal =
          rates owner := by
      simpa [rates] using hroot owner
    rw [← hrate]
    linarith
  have hbound := Math.abs_one_sub_prod_one_sub_sub_sum_le_sq_sum_div_two
    rates Finset.univ (fun owner _ => h0 owner) (fun owner _ => h1 owner)
  rw [hmass]
  simpa [quittingGermOpponentQuitSum, rates] using hbound

/-- Opponent absorption is bounded by the sum of opponent marginal Quit
rates. -/
theorem eventually_opponentAbsorption_le_quitSum
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm) (who : ι) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
      quittingRootAbsorptionMass
          (quittingGermForcedContinueRoot g who t) ≤
        quittingGermOpponentQuitSum g who t := by
  filter_upwards [eventually_mem_Ioo_radius g,
      eventually_quittingGermForcedContinueRoot_true_toReal g who]
    with t ht hroot
  let rates : ι → ℝ :=
    fun owner => if owner = who then 0 else quittingGermQuitRate g owner t
  have h0 : ∀ owner, 0 ≤ rates owner := by
    intro owner
    by_cases howner : owner = who
    · simp [rates, howner]
    · simpa [rates, howner] using quittingGermQuitRate_nonneg g ht owner
  have h1 : ∀ owner, rates owner ≤ 1 := by
    intro owner
    by_cases howner : owner = who
    · simp [rates, howner]
    · simpa [rates, howner] using quittingGermQuitRate_le_one g ht owner
  have hmass : quittingRootAbsorptionMass
        (quittingGermForcedContinueRoot g who t) =
      1 - ∏ owner, (1 - rates owner) := by
    unfold quittingRootAbsorptionMass
    rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    congr 1
    apply Finset.prod_congr rfl
    intro owner _
    have hprob := quittingRoot_continueProbability_add_quitProbability
      (quittingGermForcedContinueRoot g who t) owner
    have hrate :
        ((quittingGermForcedContinueRoot g who t owner) true).toReal =
          rates owner := by
      simpa [rates] using hroot owner
    rw [← hrate]
    linarith
  rw [hmass]
  simpa [quittingGermOpponentQuitSum, rates] using
    (Math.one_sub_prod_one_sub_le_sum rates Finset.univ
      (fun owner _ => h0 owner) (fun owner _ => h1 owner))

/-- The sum of opponent Quit rates is nonnegative on the punctured domain. -/
theorem eventually_quittingGermOpponentQuitSum_nonneg
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm) (who : ι) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
      0 ≤ quittingGermOpponentQuitSum g who t := by
  filter_upwards [eventually_mem_Ioo_radius g] with t ht
  unfold quittingGermOpponentQuitSum
  apply Finset.sum_nonneg
  intro owner _
  by_cases howner : owner = who
  · simp [howner]
  · simp only [if_neg howner]
    exact quittingGermQuitRate_nonneg g ht owner

namespace QuittingGermOpponentLeadingData

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {g : (quittingGame reward).AnalyticBellmanGerm} {who : ι}

/-- The normalized opponent marginal Quit sum converges to the total
singleton-clock weight. -/
theorem opponentQuitSum_div_clockSum_tendsto
    (data : QuittingGermOpponentLeadingData g who) :
    Tendsto
      (fun t => quittingGermOpponentQuitSum g who t /
        ∑ clock, quittingGermOpponentClock g who clock t)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∑ owner, data.singletonWeight owner)) := by
  have hsum := tendsto_finsetSum (Finset.univ : Finset ι)
    (fun owner _ => data.clock_div_sum_tendsto (some owner))
  have heq : (fun t => quittingGermOpponentQuitSum g who t /
        ∑ clock, quittingGermOpponentClock g who clock t) =
      (fun t => ∑ owner,
        quittingGermOpponentClock g who (some owner) t /
          ∑ clock, quittingGermOpponentClock g who clock t) := by
    funext t
    unfold quittingGermOpponentQuitSum
    simp only [quittingGermOpponentClock_some, div_eq_mul_inv,
      Finset.sum_mul]
  rw [heq]
  exact hsum

/-- Collision-order Bonferroni error vanishes after opponent first-event
normalization. -/
theorem opponentAbsorption_sub_quitSum_div_clockSum_tendsto_zero
    (data : QuittingGermOpponentLeadingData g who)
    (hfixed : quittingStationaryFixedOpponentsContinueMass
      (g.endpointProfile none) who = 1) :
    Tendsto
      (fun t =>
        (quittingRootAbsorptionMass
            (quittingGermForcedContinueRoot g who t) -
          quittingGermOpponentQuitSum g who t) /
            ∑ clock, quittingGermOpponentClock g who clock t)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
  let scale : ℝ → ℝ := fun t =>
    ∑ clock, quittingGermOpponentClock g who clock t
  let error : ℝ → ℝ := fun t =>
    quittingRootAbsorptionMass
        (quittingGermForcedContinueRoot g who t) -
      quittingGermOpponentQuitSum g who t
  have hbound : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
      |error t| ≤ (1 / 2 : ℝ) * (scale t) ^ 2 := by
    filter_upwards [eventually_abs_opponentAbsorption_sub_quitSum_le g who,
        eventually_quittingGermOpponentQuitSum_nonneg g who,
        self_mem_nhdsWithin]
      with t herror hquit ht
    have hscaleEq : scale t =
        t ^ g.ramification + quittingGermOpponentQuitSum g who t :=
      sum_quittingGermOpponentClock g who t
    have hdiscount : 0 ≤ t ^ g.ramification := pow_nonneg ht.le _
    have hle : quittingGermOpponentQuitSum g who t ≤ scale t := by
      rw [hscaleEq]
      linarith
    have hscaleNonneg : 0 ≤ scale t := hquit.trans hle
    have hsquare : (quittingGermOpponentQuitSum g who t) ^ 2 ≤
        (scale t) ^ 2 := (sq_le_sq₀ hquit hscaleNonneg).2 hle
    change |error t| ≤ (1 / 2 : ℝ) * scale t ^ 2
    calc
      |error t| ≤ quittingGermOpponentQuitSum g who t ^ 2 / 2 := herror
      _ ≤ scale t ^ 2 / 2 := by gcongr
      _ = (1 / 2 : ℝ) * scale t ^ 2 := by ring
  exact tendsto_div_zero_of_abs_le_const_mul_sq
    (C := (1 / 2 : ℝ))
    data.eventually_clock_sum_pos
    (tendsto_sum_quittingGermOpponentClock_zero g who hfixed)
    hbound

/-- Opponent absorption, normalized by discount plus opponent marginal Quit
mass, converges to the total singleton-clock weight. -/
theorem opponentAbsorption_div_clockSum_tendsto
    (data : QuittingGermOpponentLeadingData g who)
    (hfixed : quittingStationaryFixedOpponentsContinueMass
      (g.endpointProfile none) who = 1) :
    Tendsto
      (fun t => quittingRootAbsorptionMass
          (quittingGermForcedContinueRoot g who t) /
            ∑ clock, quittingGermOpponentClock g who clock t)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∑ owner, data.singletonWeight owner)) := by
  have h :=
    (data.opponentAbsorption_sub_quitSum_div_clockSum_tendsto_zero hfixed).add
      data.opponentQuitSum_div_clockSum_tendsto
  convert h using 1 <;> ring_nf

/-- The exact opponent first-event denominator is asymptotic to the simpler
sum of analytic clocks. -/
theorem opponentFirstEventDenominator_div_clockSum_tendsto_one
    (data : QuittingGermOpponentLeadingData g who)
    (hfixed : quittingStationaryFixedOpponentsContinueMass
      (g.endpointProfile none) who = 1) :
    Tendsto
      (fun t => quittingGermOpponentFirstEventDenominator g who t /
        ∑ clock, quittingGermOpponentClock g who clock t)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 1) := by
  have hdiscount : Tendsto (fun t : ℝ => 1 - t ^ g.ramification)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 1) := by
    simpa using tendsto_const_nhds.sub
      (Math.tendsto_pow_nhdsGT_zero g.ramification_pos.ne')
  have hcemetery := data.clock_div_sum_tendsto none
  have habsorption := data.opponentAbsorption_div_clockSum_tendsto hfixed
  have h := hcemetery.add (hdiscount.mul habsorption)
  have hlimit : data.clockWeight none +
      1 * (∑ owner, data.singletonWeight owner) = 1 := by
    simpa [cemeteryWeight] using data.cemetery_add_sum_singletonWeight
  rw [hlimit] at h
  refine h.congr' ?_
  filter_upwards [data.eventually_clock_sum_pos] with t hscale
  unfold quittingGermOpponentFirstEventDenominator
  rw [quittingGermOpponentClock_none]
  field_simp [hscale.ne']

end QuittingGermOpponentLeadingData

/-! ## Forced-Continue first-event reward limit -/

/-- Every forced-Continue root coordinate converges to pure Continue at an
all-Continue endpoint. -/
theorem tendsto_quittingGermForcedContinueRoot_continueProbability_one
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (who owner : ι)
    (hfixed : quittingStationaryFixedOpponentsContinueMass
      (g.endpointProfile none) who = 1) :
    Tendsto
      (fun t => ((quittingGermForcedContinueRoot g who t owner) false).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 1) := by
  have hquit : Tendsto
      (fun t => ((quittingGermForcedContinueRoot g who t owner) true).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
    by_cases howner : owner = who
    · subst owner
      simp [quittingGermForcedContinueRoot]
    · have hraw :=
          quittingGermQuitRate_tendsto_zero_of_endpoint_fixedOpponents
            g who hfixed owner howner
      refine hraw.congr' ?_
      filter_upwards
          [eventually_quittingGermForcedContinueRoot_true_toReal g who]
        with t ht
      simpa [howner] using (ht owner).symm
  have hconst : Tendsto (fun _ : ℝ => (1 : ℝ))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 1) := tendsto_const_nhds
  have h := hconst.sub hquit
  have h' : Tendsto
      (fun t => 1 -
        ((quittingGermForcedContinueRoot g who t owner) true).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 1) := by
    simpa using h
  refine h'.congr' ?_
  exact Filter.Eventually.of_forall fun t => by
    have hprob := quittingRoot_continueProbability_add_quitProbability
      (quittingGermForcedContinueRoot g who t) owner
    linarith

/-- The probability that all opponents of any owner Continue in the
forced-`who` root tends to one. -/
theorem tendsto_quittingGermForcedContinue_fixedOpponentsContinueMass_one
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (who owner : ι)
    (hfixed : quittingStationaryFixedOpponentsContinueMass
      (g.endpointProfile none) who = 1) :
    Tendsto
      (fun t => quittingStationaryFixedOpponentsContinueMass
        (quittingGermForcedContinueRoot g who t) owner)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 1) := by
  have hprod : Tendsto
      (fun t => ∏ other ∈ Finset.univ.erase owner,
        ((quittingGermForcedContinueRoot g who t other) false).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 1) := by
    simpa using tendsto_finsetProd (Finset.univ.erase owner)
      (fun other _ =>
        tendsto_quittingGermForcedContinueRoot_continueProbability_one
          g who other hfixed)
  refine hprod.congr' ?_
  exact Filter.Eventually.of_forall fun t => by
    change (∏ other ∈ Finset.univ.erase owner,
        ((quittingGermForcedContinueRoot g who t other) false).toReal) =
      quittingStationaryContinueMass
        (Function.update (quittingGermForcedContinueRoot g who t)
          owner (PMF.pure false))
    rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    calc
      (∏ other ∈ Finset.univ.erase owner,
          ((quittingGermForcedContinueRoot g who t other) false).toReal) =
          ∏ other ∈ Finset.univ.erase owner,
            ((Function.update (quittingGermForcedContinueRoot g who t)
              owner (PMF.pure false) other) false).toReal := by
        apply Finset.prod_congr rfl
        intro other hother
        rw [Finset.mem_erase] at hother
        simp [Function.update, hother.1]
      _ = ∏ player,
          ((Function.update (quittingGermForcedContinueRoot g who t)
            owner (PMF.pure false) player) false).toReal := by
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ owner)]
        simp

namespace QuittingGermOpponentLeadingData

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {g : (quittingGame reward).AnalyticBellmanGerm} {who : ι}

/-- Each forced-Continue singleton event has the clock weight prescribed by
the opponent leading normalization. -/
theorem singletonCoalitionMass_div_clockSum_tendsto
    (data : QuittingGermOpponentLeadingData g who)
    (owner : ι)
    (hfixed : quittingStationaryFixedOpponentsContinueMass
      (g.endpointProfile none) who = 1) :
    Tendsto
      (fun t => quittingRootCoalitionMass
          (quittingGermForcedContinueRoot g who t) {owner} /
            ∑ clock, quittingGermOpponentClock g who clock t)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (data.singletonWeight owner)) := by
  have hcontinueMass :=
    tendsto_quittingGermForcedContinue_fixedOpponentsContinueMass_one
      g who owner hfixed
  have hclock := data.clock_div_sum_tendsto (some owner)
  have h := hcontinueMass.mul hclock
  have h' : Tendsto
      (fun t => quittingStationaryFixedOpponentsContinueMass
          (quittingGermForcedContinueRoot g who t) owner *
        (quittingGermOpponentClock g who (some owner) t /
          ∑ clock, quittingGermOpponentClock g who clock t))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (data.singletonWeight owner)) := by
    simpa [singletonWeight] using h
  refine h'.congr' ?_
  filter_upwards
      [eventually_quittingGermForcedContinueRoot_true_toReal g who]
    with t hroot
  rw [quittingRootCoalitionMass_singleton_eq_opponentContinue_mul_quit]
  have hrate :
      ((quittingGermForcedContinueRoot g who t owner) true).toReal =
        quittingGermOpponentClock g who (some owner) t := by
    simpa [quittingGermOpponentClock_some] using hroot owner
  rw [hrate]
  unfold quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsContinueMass
  ring

/-- Collision reward is negligible on the opponent clock scale. -/
theorem collisionReward_div_clockSum_tendsto_zero
    (data : QuittingGermOpponentLeadingData g who)
    (coordinate : ι)
    (hfixed : quittingStationaryFixedOpponentsContinueMass
      (g.endpointProfile none) who = 1) :
    Tendsto
      (fun t => QuittingFiniteRootWindow.rootCollisionRewardContribution reward
          (quittingGermForcedContinueRoot g who t) coordinate /
            ∑ clock, quittingGermOpponentClock g who clock t)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
  let scale : ℝ → ℝ := fun t =>
    ∑ clock, quittingGermOpponentClock g who clock t
  let error : ℝ → ℝ := fun t =>
    QuittingFiniteRootWindow.rootCollisionRewardContribution reward
      (quittingGermForcedContinueRoot g who t) coordinate
  let C : ℝ := quittingRewardBound reward * (Fintype.card ι).choose 2
  have hbound : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
      |error t| ≤ C * (scale t) ^ 2 := by
    filter_upwards [eventually_opponentAbsorption_le_quitSum g who,
        eventually_quittingGermOpponentQuitSum_nonneg g who,
        self_mem_nhdsWithin]
      with t habs hquit ht
    let root := quittingGermForcedContinueRoot g who t
    have hreward := QuittingFiniteRootWindow.abs_rootCollisionRewardContribution_le
      reward root coordinate (abs_reward_le_quittingRewardBound reward)
    have hcollision :=
      quittingRootCollisionMass_le_choose_card_mul_absorption_sq root
    have hscaleEq : scale t =
        t ^ g.ramification + quittingGermOpponentQuitSum g who t :=
      sum_quittingGermOpponentClock g who t
    have hscaleNonneg : 0 ≤ scale t := by
      rw [hscaleEq]
      exact add_nonneg (pow_nonneg ht.le _) hquit
    have hquitScale : quittingGermOpponentQuitSum g who t ≤ scale t := by
      rw [hscaleEq]
      exact le_add_of_nonneg_left (pow_nonneg ht.le _)
    have habsScale : quittingRootAbsorptionMass root ≤ scale t :=
      habs.trans hquitScale
    have habsNonneg := quittingRootAbsorptionMass_nonneg root
    have hsquare : quittingRootAbsorptionMass root ^ 2 ≤ scale t ^ 2 :=
      (sq_le_sq₀ habsNonneg hscaleNonneg).2 habsScale
    change |error t| ≤ C * scale t ^ 2
    calc
      |error t| ≤ quittingRewardBound reward *
          quittingRootCollisionMass root := hreward
      _ ≤ quittingRewardBound reward *
          ((Fintype.card ι).choose 2 *
            quittingRootAbsorptionMass root ^ 2) := by
        exact mul_le_mul_of_nonneg_left hcollision
          (quittingRewardBound_nonneg reward)
      _ ≤ C * scale t ^ 2 := by
        dsimp only [C]
        ring_nf
        exact mul_le_mul_of_nonneg_left hsquare
          (mul_nonneg (quittingRewardBound_nonneg reward) (Nat.cast_nonneg _))
  exact tendsto_div_zero_of_abs_le_const_mul_sq
    data.eventually_clock_sum_pos
    (tendsto_sum_quittingGermOpponentClock_zero g who hfixed)
    hbound

/-- The forced-Continue absorbing contribution converges, after opponent
first-event normalization, to the singleton reward mixture selected by the
opponent leading clocks. -/
theorem continueReward_div_clockSum_tendsto_singletonMix
    (data : QuittingGermOpponentLeadingData g who)
    (hfixed : quittingStationaryFixedOpponentsContinueMass
      (g.endpointProfile none) who = 1) :
    Tendsto
      (fun t => quittingStationaryFixedOpponentsContinueReward reward
          (quittingGermPuncturedRoot g t) who /
            ∑ clock, quittingGermOpponentClock g who clock t)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∑ owner, data.singletonWeight owner *
        reward (quittingSingletonTerminal owner) who)) := by
  have hsingle : Tendsto
      (fun t => ∑ owner,
        (quittingRootCoalitionMass
            (quittingGermForcedContinueRoot g who t) {owner} /
              ∑ clock, quittingGermOpponentClock g who clock t) *
          reward (quittingSingletonTerminal owner) who)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∑ owner, data.singletonWeight owner *
        reward (quittingSingletonTerminal owner) who)) := by
    apply tendsto_finsetSum Finset.univ
    intro owner _
    exact (data.singletonCoalitionMass_div_clockSum_tendsto owner hfixed).mul
      tendsto_const_nhds
  have hcollision := data.collisionReward_div_clockSum_tendsto_zero
    who hfixed
  have h := hsingle.add hcollision
  have h' : Tendsto
      (fun t =>
        (∑ owner,
          (quittingRootCoalitionMass
              (quittingGermForcedContinueRoot g who t) {owner} /
                ∑ clock, quittingGermOpponentClock g who clock t) *
            reward (quittingSingletonTerminal owner) who) +
          QuittingFiniteRootWindow.rootCollisionRewardContribution reward
            (quittingGermForcedContinueRoot g who t) who /
              ∑ clock, quittingGermOpponentClock g who clock t)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∑ owner, data.singletonWeight owner *
        reward (quittingSingletonTerminal owner) who)) := by
    simpa using h
  refine h'.congr' ?_
  filter_upwards [data.eventually_clock_sum_pos] with t hscale
  have hdecomp :=
    QuittingFiniteRootWindow.quittingRootAbsorbingContribution_eq_singleton_add_collision
      reward (quittingGermForcedContinueRoot g who t) who
  unfold quittingStationaryFixedOpponentsContinueReward
    quittingFixedOpponentsContinueReward
  change _ = quittingRootAbsorbingContribution reward
      (quittingGermForcedContinueRoot g who t) who /
        (∑ clock, quittingGermOpponentClock g who clock t)
  rw [hdecomp]
  rw [add_div]
  congr 1
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro owner _
  ring

end QuittingGermOpponentLeadingData

/-- The deleted opponent marginal Quit sum tends to zero at an all-Continue
endpoint. -/
theorem tendsto_quittingGermOpponentQuitSum_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (who : ι)
    (hfixed : quittingStationaryFixedOpponentsContinueMass
      (g.endpointProfile none) who = 1) :
    Tendsto (quittingGermOpponentQuitSum g who)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
  have htotal := tendsto_sum_quittingGermOpponentClock_zero g who hfixed
  have hdiscount := Math.tendsto_pow_nhdsGT_zero g.ramification_pos.ne'
  have h := htotal.sub hdiscount
  have h' : Tendsto
      (fun t => (∑ clock, quittingGermOpponentClock g who clock t) -
        t ^ g.ramification)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
    simpa using h
  refine h'.congr' ?_
  exact Filter.Eventually.of_forall fun t => by
    change (∑ clock, quittingGermOpponentClock g who clock t) -
      t ^ g.ramification = quittingGermOpponentQuitSum g who t
    rw [sum_quittingGermOpponentClock]
    ring

/-- Opponent absorption vanishes at an all-Continue endpoint. -/
theorem tendsto_quittingGermOpponentAbsorption_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (who : ι)
    (hfixed : quittingStationaryFixedOpponentsContinueMass
      (g.endpointProfile none) who = 1) :
    Tendsto
      (fun t => quittingRootAbsorptionMass
        (quittingGermForcedContinueRoot g who t))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun t =>
      quittingRootAbsorptionMass_nonneg _
  · exact eventually_opponentAbsorption_le_quitSum g who
  · exact tendsto_quittingGermOpponentQuitSum_zero g who hfixed

/-- Immediate quitting against the punctured root converges to the selected
player's singleton payoff. -/
theorem tendsto_quittingGermPuncturedRoot_quitValue_singleton
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (who : ι)
    (hfixed : quittingStationaryFixedOpponentsContinueMass
      (g.endpointProfile none) who = 1) :
    Tendsto
      (fun t => quittingStationaryFixedOpponentsQuitValue reward
        (quittingGermPuncturedRoot g t) who)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (reward (quittingSingletonTerminal who) who)) := by
  let difference : ℝ → ℝ := fun t =>
    quittingStationaryFixedOpponentsQuitValue reward
        (quittingGermPuncturedRoot g t) who -
      reward (quittingSingletonTerminal who) who
  have hmajor : Tendsto
      (fun t => 2 * quittingRewardBound reward *
        quittingRootAbsorptionMass (quittingGermForcedContinueRoot g who t))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
    simpa using
      (tendsto_quittingGermOpponentAbsorption_zero g who hfixed).const_mul
        (2 * quittingRewardBound reward)
  have habs : Tendsto (fun t => |difference t|)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun t => abs_nonneg _
    · exact Filter.Eventually.of_forall fun t => by
        simpa [difference, quittingGermForcedContinueRoot] using
          (abs_quittingStationaryFixedOpponentsQuitValue_sub_singleton_le
            (reward := reward) (quittingGermPuncturedRoot g t) who
            (quittingRewardBound_nonneg reward)
            (abs_reward_le_quittingRewardBound reward))
    · exact hmajor
  apply tendsto_iff_norm_sub_tendsto_zero.2
  simpa only [Real.norm_eq_abs] using habs

namespace QuittingGermOpponentLeadingData

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {g : (quittingGame reward).AnalyticBellmanGerm} {who : ι}

/-- The coefficient in the cleared Continue inequality has the exact
opponent first-event denominator. -/
theorem one_sub_continueMass_mul_discount_eq_denominator
    (_data : QuittingGermOpponentLeadingData g who) (t : ℝ) :
    1 - quittingStationaryFixedOpponentsContinueMass
          (quittingGermPuncturedRoot g t) who *
        (1 - t ^ g.ramification) =
      quittingGermOpponentFirstEventDenominator g who t := by
  have hmass : quittingStationaryFixedOpponentsContinueMass
        (quittingGermPuncturedRoot g t) who =
      quittingStationaryContinueMass
        (quittingGermForcedContinueRoot g who t) := rfl
  rw [hmass]
  unfold quittingGermOpponentFirstEventDenominator
    quittingRootAbsorptionMass
  ring

/-- The cleared Continue signal, divided by the opponent clock scale,
converges to its finite singleton/cemetery mixture. -/
theorem clearedSignal_div_clockSum_tendsto
    (data : QuittingGermOpponentLeadingData g who)
    (hfixed : quittingStationaryFixedOpponentsContinueMass
      (g.endpointProfile none) who = 1) :
    Tendsto
      (fun t =>
        (quittingStationaryFixedOpponentsContinueReward reward
            (quittingGermPuncturedRoot g t) who -
          (1 - quittingStationaryFixedOpponentsContinueMass
              (quittingGermPuncturedRoot g t) who *
                (1 - t ^ g.ramification)) *
            quittingStationaryFixedOpponentsQuitValue reward
              (quittingGermPuncturedRoot g t) who) /
          ∑ clock, quittingGermOpponentClock g who clock t)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds ((∑ owner, data.singletonWeight owner *
          reward (quittingSingletonTerminal owner) who) -
        reward (quittingSingletonTerminal who) who)) := by
  have hcontinueReward := data.continueReward_div_clockSum_tendsto_singletonMix
    hfixed
  have hdenominator :=
    data.opponentFirstEventDenominator_div_clockSum_tendsto_one hfixed
  have hquit := tendsto_quittingGermPuncturedRoot_quitValue_singleton
    g who hfixed
  have h := hcontinueReward.sub (hdenominator.mul hquit)
  have h' : Tendsto
      (fun t =>
        quittingStationaryFixedOpponentsContinueReward reward
            (quittingGermPuncturedRoot g t) who /
              ∑ clock, quittingGermOpponentClock g who clock t -
          (quittingGermOpponentFirstEventDenominator g who t /
              ∑ clock, quittingGermOpponentClock g who clock t) *
            quittingStationaryFixedOpponentsQuitValue reward
              (quittingGermPuncturedRoot g t) who)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds ((∑ owner, data.singletonWeight owner *
          reward (quittingSingletonTerminal owner) who) -
        reward (quittingSingletonTerminal who) who)) := by
    simpa using h
  refine h'.congr' ?_
  filter_upwards [data.eventually_clock_sum_pos] with t hscale
  rw [data.one_sub_continueMass_mul_discount_eq_denominator t]
  field_simp [hscale.ne']

/-- An eventually active player's limiting cleared signal is nonpositive. -/
theorem singletonMix_sub_ownSolo_nonpos_of_eventuallyActive
    (data : QuittingGermOpponentLeadingData g who)
    (hfixed : quittingStationaryFixedOpponentsContinueMass
      (g.endpointProfile none) who = 1)
    (hactive : QuittingGermEventuallyActive g who) :
    (∑ owner, data.singletonWeight owner *
        reward (quittingSingletonTerminal owner) who) -
      reward (quittingSingletonTerminal who) who ≤ 0 := by
  let signal : ℝ → ℝ := fun t =>
    quittingStationaryFixedOpponentsContinueReward reward
          (quittingGermPuncturedRoot g t) who -
      (1 - quittingStationaryFixedOpponentsContinueMass
          (quittingGermPuncturedRoot g t) who *
            (1 - t ^ g.ramification)) *
        quittingStationaryFixedOpponentsQuitValue reward
          (quittingGermPuncturedRoot g t) who
  let scale : ℝ → ℝ := fun t =>
    ∑ clock, quittingGermOpponentClock g who clock t
  have hlimit := data.clearedSignal_div_clockSum_tendsto hfixed
  have hnonpos : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
      signal t / scale t ≤ 0 := by
    have hltOne : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), t < 1 :=
      (show ∀ᶠ t in nhds (0 : ℝ), t < 1 from
        Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
          nhdsWithin_le_nhds
    filter_upwards [eventually_mem_Ioo_radius g, hltOne,
        eventually_quittingGermQuitRate_pos_of_eventuallyActive g hactive,
        data.eventually_clock_sum_pos]
      with t ht ht1 hquit hscale
    have hraw := quittingGerm_forcedContinue_signal_nonpos_of_quit_pos
      g ht ht1 who hquit
    have hroot : quittingGermPuncturedRoot g t = quittingGermRoot g ht := by
      simp [quittingGermPuncturedRoot, ht]
    rw [← hroot] at hraw
    exact div_nonpos_of_nonpos_of_nonneg hraw hscale.le
  exact le_of_tendsto_of_tendsto hlimit tendsto_const_nhds hnonpos

end QuittingGermOpponentLeadingData

/-! ## Normal-layer support induction -/

/-- For a shifted germ, one punctured-active player has a nonpositive
opponent singleton comparison in the normalized leading support. -/
theorem exists_weighted_nonpositive_normalizedSoloMatrix_of_eventuallyActive
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (qfull : ι → ℝ)
    (g : (quittingGame (quittingRewardShift reward
      (fun who => quittingSoloBaseline reward who + qfull who))).AnalyticBellmanGerm)
    (who : ι)
    (hfixed : quittingStationaryFixedOpponentsContinueMass
      (g.endpointProfile none) who = 1)
    (hactive : QuittingGermEventuallyActive g who)
    (data : QuittingGermOpponentLeadingData g who)
    (hq : 0 < qfull who) :
    ∃ owner, 0 < data.singletonWeight owner ∧
      normalizedSoloMatrix reward who owner ≤ 0 := by
  let shifted := quittingRewardShift reward
    (fun player => quittingSoloBaseline reward player + qfull player)
  have hsignal := data.singletonMix_sub_ownSolo_nonpos_of_eventuallyActive
    hfixed hactive
  have hrewrite (owner : ι) :
      shifted (quittingSingletonTerminal owner) who -
          shifted (quittingSingletonTerminal who) who =
        normalizedSoloMatrix reward who owner := by
    simp [shifted, quittingRewardShift_apply, normalizedSoloMatrix,
      QuittingPayoffTable.singletonMatrix, normalizedQuittingPayoffTable,
      QuittingPayoffTable.translate, repositoryQuittingPayoffTable,
      quittingSoloBaseline]
    ring
  have hsolo : shifted (quittingSingletonTerminal who) who = -qfull who := by
    simp [shifted, quittingRewardShift_apply, quittingSoloBaseline]
  have htotal := data.cemetery_add_sum_singletonWeight
  have hsignal' : data.cemeteryWeight * qfull who +
      ∑ owner, data.singletonWeight owner *
        normalizedSoloMatrix reward who owner ≤ 0 := by
    calc
      data.cemeteryWeight * qfull who +
          ∑ owner, data.singletonWeight owner *
            normalizedSoloMatrix reward who owner =
        data.cemeteryWeight * qfull who +
          ∑ owner, data.singletonWeight owner *
            (shifted (quittingSingletonTerminal owner) who -
              shifted (quittingSingletonTerminal who) who) := by
          apply congrArg (fun x => data.cemeteryWeight * qfull who + x)
          apply Finset.sum_congr rfl
          intro owner _
          rw [hrewrite]
      _ = ∑ owner, data.singletonWeight owner *
            shifted (quittingSingletonTerminal owner) who -
          shifted (quittingSingletonTerminal who) who := by
          rw [hsolo]
          have hsum : ∑ owner, data.singletonWeight owner =
              1 - data.cemeteryWeight := by linarith
          simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
          rw [hsum]
          ring
      _ ≤ 0 := by simpa [shifted] using hsignal
  exact exists_nonpositive_singleton_of_nonpositive_hierarchy_signal
    (normalizedSoloMatrix reward) qfull who data.cemeteryWeight
    data.singletonWeight 0 hq data.cemeteryWeight_nonneg
    data.singletonWeight_nonneg
    (by rw [data.cemetery_add_sum_singletonWeight]; norm_num)
    (by norm_num) (by simpa using hsignal')

/-- A unique positive endpoint owner with positive auxiliary direction has a
distinct nonpositive normalized singleton blocker.  This is the exact
one-layer sign conclusion needed by the isolated-endpoint repair; it does
not assert recursive normal-core membership. -/
theorem exists_normalizedSoloMatrix_blocker_of_isolated_endpoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (qfull : ι → ℝ)
    (g : (quittingGame (quittingRewardShift reward
      (fun who => quittingSoloBaseline reward who + qfull who))).AnalyticBellmanGerm)
    (owner : ι)
    (howner : 0 < ((g.endpointProfile none owner) true).toReal)
    (hother : ∀ other, other ≠ owner →
      g.endpointProfile none other = PMF.pure false)
    (hq : 0 < qfull owner) :
    ∃ blocker, blocker ≠ owner ∧
      normalizedSoloMatrix reward owner blocker ≤ 0 := by
  have hactive : QuittingGermEventuallyActive g owner :=
    quittingGerm_eventuallyActive_of_endpoint_quit_pos g howner
  have hfixed : quittingStationaryFixedOpponentsContinueMass
      (g.endpointProfile none) owner = 1 := by
    have hroot : g.endpointProfile none =
        quittingSoloStationaryRoot owner (g.endpointProfile none owner) :=
      eq_quittingSoloStationaryRoot_of_others_continue hother
    rw [hroot]
    exact quittingStationaryFixedOpponentsContinueMass_solo_owner
      owner (g.endpointProfile none owner)
  obtain ⟨data⟩ := nonempty_quittingGermOpponentLeadingData g owner
  obtain ⟨blocker, hweight, hentry⟩ :=
    exists_weighted_nonpositive_normalizedSoloMatrix_of_eventuallyActive
      reward qfull g owner hfixed hactive data hq
  refine ⟨blocker, ?_, hentry⟩
  intro heq
  subst blocker
  rw [data.singletonWeight_self] at hweight
  exact (lt_irrefl 0) hweight

/-- A punctured-active coordinate has a blocker in the same normal layer.
The blocker has positive leading opponent-clock weight and hence is itself
punctured-active. -/
theorem eventuallyActive_mem_normalLayer_succ_of_mem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (q : normalCore (normalizedSoloMatrix reward) → ℝ)
    (g : (quittingGame (quittingRewardShift reward
      (fun who => quittingSoloBaseline reward who +
        extendNormalDirection (normalizedSoloMatrix reward) q who))).AnalyticBellmanGerm)
    (hcontinue : quittingStationaryContinueMass (g.endpointProfile none) = 1)
    (n : ℕ)
    (hlevel : ∀ player, QuittingGermEventuallyActive g player →
      player ∈ normalLayer (normalizedSoloMatrix reward) n)
    (who : ι) (hactive : QuittingGermEventuallyActive g who) :
    who ∈ normalLayer (normalizedSoloMatrix reward) (n + 1) := by
  let M := normalizedSoloMatrix reward
  have hwhoLevel := hlevel who hactive
  by_cases hcore : who ∈ normalCore M
  · exact (mem_normalCore M who).1 hcore (n + 1)
  · obtain ⟨data⟩ := nonempty_quittingGermOpponentLeadingData g who
    have hfixed : quittingStationaryFixedOpponentsContinueMass
        (g.endpointProfile none) who = 1 := by
      have hlower := quittingStationaryContinueMass_le_fixedOpponentsContinueMass
        (g.endpointProfile none) who
      have hupper := quittingStationaryContinueMass_le_one
        (Function.update (g.endpointProfile none) who (PMF.pure false))
      change quittingStationaryFixedOpponentsContinueMass
        (g.endpointProfile none) who ≤ 1 at hupper
      linarith
    have hq : 0 < extendNormalDirection M q who := by
      rw [extendNormalDirection_of_notMem M q hcore]
      norm_num
    obtain ⟨blocker, hweight, hentry⟩ :=
      exists_weighted_nonpositive_normalizedSoloMatrix_of_eventuallyActive
        reward (extendNormalDirection M q) g who hfixed hactive data hq
    have hblockerActive : QuittingGermEventuallyActive g blocker := by
      intro hzero
      have hclockZero : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
          quittingGermOpponentClock g who (some blocker) t = 0 := by
        filter_upwards [hzero] with t ht
        by_cases hsame : blocker = who
        · simp [quittingGermOpponentClock_some, hsame]
        · simpa [quittingGermOpponentClock_some, hsame] using ht
      have hcofactor : data.jet.cofactor (some blocker) 0 = 0 := by
        by_contra hne
        have horder := data.jet.analyticOrderAt_eq_order hne
        have htop : analyticOrderAt
            (quittingGermOpponentClock g who (some blocker)) 0 = ⊤ :=
          analyticOrderAt_eq_top.mpr
            ((Math.eventuallyEq_zero_nhdsGT_iff_nhds
              (analyticAt_quittingGermOpponentClock g who (some blocker))).mp
                hclockZero)
        rw [htop] at horder
        exact WithTop.coe_ne_top horder.symm
      unfold QuittingGermOpponentLeadingData.singletonWeight
        QuittingGermOpponentLeadingData.clockWeight at hweight
      rw [hcofactor, zero_div] at hweight
      exact (lt_irrefl 0) hweight
    have hblockerLevel := hlevel blocker hblockerActive
    have hne : blocker ≠ who := by
      intro heq
      subst blocker
      rw [data.singletonWeight_self] at hweight
      exact (lt_irrefl 0) hweight
    exact (mem_normalLayer_succ M n who).2
      ⟨hwhoLevel, blocker, hblockerLevel, hne, hentry⟩

/-- **Punctured support lies in the corrected normal core.**  This is the
fast-coordinate support theorem consumed by the ordinary non-Q producer. -/
theorem quittingGerm_eventuallyActive_mem_normalCore_of_baseline_extendShift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (q : normalCore (normalizedSoloMatrix reward) → ℝ)
    (g : (quittingGame (quittingRewardShift reward
      (fun who => quittingSoloBaseline reward who +
        extendNormalDirection (normalizedSoloMatrix reward) q who))).AnalyticBellmanGerm)
    (hcontinue : quittingStationaryContinueMass (g.endpointProfile none) = 1)
    (owner : ι) (hactive : QuittingGermEventuallyActive g owner) :
    owner ∈ normalCore (normalizedSoloMatrix reward) := by
  let M := normalizedSoloMatrix reward
  rw [mem_normalCore]
  intro n
  have hlevels : ∀ m : ℕ, ∀ player,
      QuittingGermEventuallyActive g player → player ∈ normalLayer M m := by
    intro m
    induction m with
    | zero => intro player _; simp [normalLayer]
    | succ m ih =>
        exact eventuallyActive_mem_normalLayer_succ_of_mem
          reward q g hcontinue m ih
  exact hlevels n owner hactive

end QuittingLCPClassification
end GameTheory
