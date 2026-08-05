/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.PublicSuffixHistory

/-!
# Bounded stopped public-history accounting

A bounded stopping selector applied to a full history of fixed fuel produces
a dependent pair consisting of the selected length and its public-history
prefix.  This file defines that stopped-history law, disintegrates it over
the selected length, and attaches conditional suffix laws to its terminal
histories.

The final aggregation theorem is exact for the explicitly constructed
stopped-suffix law.  A theorem for a separately constructed strategic splice
must supply equality of its suffix laws with these conditional laws; that
typed interface is stated explicitly below.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} {G : StochasticGame ι}

/-- A public history stopped at some time no greater than `fuel`. -/
abbrev BoundedStoppedHistory (G : StochasticGame ι) (fuel : ℕ) :=
  (length : Fin (fuel + 1)) × G.Hist length

/-- A deterministic bounded stopping selector on full public histories. -/
abbrev BoundedPublicStopSelector (G : StochasticGame ι) (fuel : ℕ) :=
  G.Hist fuel → Fin (fuel + 1)

/-- Recover a prefix whose length is bounded by the full history's fuel. -/
def boundedHistoryPrefix {fuel : ℕ} (history : G.Hist fuel)
    (length : Fin (fuel + 1)) : G.Hist length :=
  let hlength : length.val ≤ fuel := Nat.lt_succ_iff.mp length.isLt
  (fun index => history.1 (Fin.castLE hlength index),
    if hstrict : length.val < fuel then
      (history.1 ⟨length, hstrict⟩).1
    else
      history.2)

/-- Recover the public-history prefix chosen by a bounded selector. -/
def selectedStoppedHistory {fuel : ℕ}
    (selector : G.BoundedPublicStopSelector fuel)
    (history : G.Hist fuel) : G.BoundedStoppedHistory fuel :=
  let length := selector history
  ⟨length,
    G.boundedHistoryPrefix history length⟩

@[simp] theorem selectedStoppedHistory_fst {fuel : ℕ}
    (selector : G.BoundedPublicStopSelector fuel)
    (history : G.Hist fuel) :
    (G.selectedStoppedHistory selector history).1 = selector history :=
  rfl

/-- The law of the selected stopped public history under a fixed-fuel root
history law. -/
def stoppedHistoryLaw [Fintype ι] {fuel : ℕ}
    (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel) :
    PMF (G.BoundedStoppedHistory fuel) :=
  (G.histDist profile initial fuel).map
    (G.selectedStoppedHistory selector)

/-- The marginal law of the selected stopping length. -/
def stoppedLengthLaw [Fintype ι] {fuel : ℕ}
    (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel) :
    PMF (Fin (fuel + 1)) :=
  (G.stoppedHistoryLaw profile initial selector).map Sigma.fst

/-- The stopping-length marginal is the direct pushforward of the root
fixed-fuel history law by the selector. -/
theorem stoppedLengthLaw_eq_map_selector
    [Fintype ι] {fuel : ℕ}
    (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel) :
    G.stoppedLengthLaw profile initial selector =
      (G.histDist profile initial fuel).map selector := by
  unfold stoppedLengthLaw stoppedHistoryLaw
  rw [PMF.map_comp]
  rfl

/-- The stopped-history law disintegrates over its finite stopping-length
marginal.  The conditional law remains on the dependent stopped-history
type, avoiding any hidden cast between different history lengths. -/
theorem stoppedHistoryLaw_disintegrate_length
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    {fuel : ℕ} (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel) :
    G.stoppedHistoryLaw profile initial selector =
      (G.stoppedLengthLaw profile initial selector).bind fun length =>
        condOn (G.stoppedHistoryLaw profile initial selector)
          Sigma.fst length := by
  exact bind_pushforward_condOn_pure
    (G.stoppedHistoryLaw profile initial selector) Sigma.fst

/-- A terminality assertion on every selected root history in support passes
to the stopped-history law. -/
theorem terminal_of_mem_support_stoppedHistoryLaw
    [Fintype ι] {fuel : ℕ}
    (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel)
    (terminal : G.State → Prop)
    (hterminal : ∀ history,
      history ∈ (G.histDist profile initial fuel).support →
        terminal (G.selectedStoppedHistory selector history).2.2)
    (stopped : G.BoundedStoppedHistory fuel)
    (hstopped :
      stopped ∈
        (G.stoppedHistoryLaw profile initial selector).support) :
    terminal stopped.2.2 := by
  rw [stoppedHistoryLaw, PMF.mem_support_map_iff] at hstopped
  obtain ⟨history, hhistory, rfl⟩ := hstopped
  exact hterminal history hhistory

/-- A stopped base paired with a local suffix of fixed length. -/
abbrev StoppedHistorySuffix (G : StochasticGame ι)
    (fuel suffixLength : ℕ) :=
  (_base : G.BoundedStoppedHistory fuel) × G.Hist suffixLength

/-- First sample a stopped public history, then run the rebased profile from
that history for a fixed local suffix length.

This is a mathematical conditional splice law.  Equality with the law of an
independently constructed global dispatcher is additional strategic data. -/
def stoppedSuffixLaw [Fintype ι] {fuel : ℕ}
    (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel)
    (suffixLength : ℕ) :
    PMF (G.StoppedHistorySuffix fuel suffixLength) :=
  (G.stoppedHistoryLaw profile initial selector).bind fun base =>
    (G.histDist (G.afterHistoryProfile profile base.2) base.2.2
      suffixLength).map fun suffix => ⟨base, suffix⟩

/-- Attaching a conditional suffix preserves the stopped base marginal. -/
theorem stoppedSuffixLaw_base_marginal
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    {fuel : ℕ} (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel)
    (suffixLength : ℕ) :
    (G.stoppedSuffixLaw profile initial selector suffixLength).map
        Sigma.fst =
      G.stoppedHistoryLaw profile initial selector := by
  unfold stoppedSuffixLaw
  rw [PMF.map_bind]
  have hinter : (fun base : G.BoundedStoppedHistory fuel =>
      PMF.map Sigma.fst
        ((G.histDist (G.afterHistoryProfile profile base.2) base.2.2
          suffixLength).map fun suffix =>
            (⟨base, suffix⟩ :
              G.StoppedHistorySuffix fuel suffixLength))) =
      (fun base : G.BoundedStoppedHistory fuel => PMF.pure base) := by
    funext base
    rw [PMF.map_comp]
    change
      PMF.map (fun _suffix => base)
          (G.histDist (G.afterHistoryProfile profile base.2) base.2.2
            suffixLength) =
        PMF.pure base
    exact PMF.map_const _ _
  rw [hinter, PMF.bind_pure]

/-- The charge of a stopped base followed by a local suffix, evaluated on
the corresponding full public history of its own dependent length. -/
def stoppedSuffixCharge {fuel suffixLength : ℕ}
    (charge : G.HistoryPotential)
    (path : G.StoppedHistorySuffix fuel suffixLength) : ℝ :=
  charge (path.1.1 + suffixLength)
    (G.appendHist path.1.2 path.2)

/-- Expectation under the stopped-suffix law is exactly the stopped-law
average of the rebased conditional suffix expectations. -/
theorem expect_stoppedSuffixCharge
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    {fuel : ℕ} (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel)
    (charge : G.HistoryPotential) (suffixLength : ℕ) :
    expect (G.stoppedSuffixLaw profile initial selector suffixLength)
        (G.stoppedSuffixCharge charge) =
      expect (G.stoppedHistoryLaw profile initial selector) fun base =>
        G.expectedHistoryValue (G.afterHistoryProfile profile base.2)
          base.2.2 (G.afterHistoryPotential charge base.2)
          suffixLength := by
  unfold stoppedSuffixLaw stoppedSuffixCharge expectedHistoryValue
  rw [expect_bind]
  apply congrArg
    (expect (G.stoppedHistoryLaw profile initial selector))
  funext base
  rw [expect_map]
  rfl

/-- Support-local conditional suffix bounds aggregate over the bounded
stopped-history law. -/
theorem normalized_stopped_suffix_charge_le_expect
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    {fuel : ℕ} (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel)
    (charge : G.HistoryPotential) (horizon : ℕ)
    (error : G.BoundedStoppedHistory fuel → ℝ)
    (hbound : ∀ base,
      base ∈
          (G.stoppedHistoryLaw profile initial selector).support →
        (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
          G.expectedHistoryValue (G.afterHistoryProfile profile base.2)
            base.2.2 (G.afterHistoryPotential charge base.2) time ≤
          error base) :
    (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
        expect (G.stoppedSuffixLaw profile initial selector time)
          (G.stoppedSuffixCharge charge) ≤
      expect (G.stoppedHistoryLaw profile initial selector) error := by
  let stoppedLaw := G.stoppedHistoryLaw profile initial selector
  let localCharge : ℕ → G.BoundedStoppedHistory fuel → ℝ :=
    fun time base =>
      G.expectedHistoryValue (G.afterHistoryProfile profile base.2)
        base.2.2 (G.afterHistoryPotential charge base.2) time
  have hdecompose : ∀ time,
      expect (G.stoppedSuffixLaw profile initial selector time)
          (G.stoppedSuffixCharge charge) =
        expect stoppedLaw (localCharge time) := by
    intro time
    exact G.expect_stoppedSuffixCharge profile initial selector charge time
  have hsum :
      ∑ time ∈ Finset.range horizon,
          expect stoppedLaw (localCharge time) =
        expect stoppedLaw fun base =>
          ∑ time ∈ Finset.range horizon, localCharge time base := by
    classical
    letI : Fintype (G.BoundedStoppedHistory fuel) :=
      Fintype.ofFinite (G.BoundedStoppedHistory fuel)
    simp only [expect_eq_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro base _
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun time _ => hdecompose time, hsum]
  rw [← expect_const_mul]
  classical
  let aggregate : G.BoundedStoppedHistory fuel → ℝ :=
    fun base =>
      (horizon : ℝ)⁻¹ *
        ∑ time ∈ Finset.range horizon, localCharge time base
  have hcongr :
      expect stoppedLaw aggregate =
        expect stoppedLaw fun base =>
          if base ∈ stoppedLaw.support then aggregate base else error base :=
    expect_congr_on_support stoppedLaw _ _ fun base hbase => by
      simp [hbase]
  rw [hcongr]
  apply expect_mono
  intro base
  by_cases hbase : base ∈ stoppedLaw.support
  · simpa [aggregate, localCharge, stoppedLaw, hbase] using
      hbound base hbase
  · simp [hbase]

/-- Charge accumulated before the selected stopping history.  Every summand
is evaluated on the corresponding prefix, with its dependent length kept
explicit. -/
def stoppedPrefixCharge {fuel : ℕ} (charge : G.HistoryPotential)
    (base : G.BoundedStoppedHistory fuel) : ℝ :=
  ∑ time : Fin base.1.val,
    charge time
      (G.boundedHistoryPrefix base.2
        ⟨time, Nat.lt_trans time.isLt
          (Nat.lt_succ_self base.1)⟩)

/-- A per-stage prefix bound costs at most `fuel * bound` under the stopped
history law. -/
theorem expect_stoppedPrefixCharge_le
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    {fuel : ℕ} (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel)
    (charge : G.HistoryPotential) (bound : ℝ) (hbound : 0 ≤ bound)
    (hprefix : ∀ base,
      base ∈
          (G.stoppedHistoryLaw profile initial selector).support →
        ∀ (time : ℕ) (htime : time < base.1.val),
          charge time
              (G.boundedHistoryPrefix base.2
                ⟨time, Nat.lt_trans htime
                  (Nat.lt_succ_self base.1)⟩) ≤
            bound) :
    expect (G.stoppedHistoryLaw profile initial selector)
        (G.stoppedPrefixCharge charge) ≤
      (fuel : ℝ) * bound := by
  apply expect_le_of_le_on_support
  intro base hbase
  unfold stoppedPrefixCharge
  calc
    ∑ time : Fin base.1.val,
        charge time
          (G.boundedHistoryPrefix base.2
            ⟨time, Nat.lt_trans time.isLt
              (Nat.lt_succ_self base.1)⟩) ≤
        ∑ _time : Fin base.1.val, bound := by
          apply Finset.sum_le_sum
          intro time htime
          exact hprefix base hbase time time.isLt
    _ = (base.1 : ℝ) * bound := by simp
    _ ≤ (fuel : ℝ) * bound := by
      apply mul_le_mul_of_nonneg_right _ hbound
      exact_mod_cast Nat.lt_succ_iff.mp base.1.isLt

/-- Prefix charge plus a common local suffix horizon has the explicit
bounded-stopping splice loss `fuel * prefixBound / horizon`.

The horizon here is local time after stopping.  It does not assert an
identity with a common root calendar horizon. -/
theorem normalized_stopped_total_charge_le_expect
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    {fuel : ℕ} (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel)
    (charge : G.HistoryPotential) (horizon : ℕ)
    (prefixBound : ℝ) (hprefixBound : 0 ≤ prefixBound)
    (error : G.BoundedStoppedHistory fuel → ℝ)
    (hprefix : ∀ base,
      base ∈
          (G.stoppedHistoryLaw profile initial selector).support →
        ∀ (time : ℕ) (htime : time < base.1.val),
          charge time
              (G.boundedHistoryPrefix base.2
                ⟨time, Nat.lt_trans htime
                  (Nat.lt_succ_self base.1)⟩) ≤
            prefixBound)
    (hsuffix : ∀ base,
      base ∈
          (G.stoppedHistoryLaw profile initial selector).support →
        (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
          G.expectedHistoryValue (G.afterHistoryProfile profile base.2)
            base.2.2 (G.afterHistoryPotential charge base.2) time ≤
          error base) :
    (horizon : ℝ)⁻¹ *
        (expect (G.stoppedHistoryLaw profile initial selector)
            (G.stoppedPrefixCharge charge) +
          ∑ time ∈ Finset.range horizon,
            expect (G.stoppedSuffixLaw profile initial selector time)
              (G.stoppedSuffixCharge charge)) ≤
      expect (G.stoppedHistoryLaw profile initial selector) error +
        (horizon : ℝ)⁻¹ * (fuel : ℝ) * prefixBound := by
  have hprefixMean := G.expect_stoppedPrefixCharge_le
    profile initial selector charge prefixBound hprefixBound hprefix
  have hsuffixMean := G.normalized_stopped_suffix_charge_le_expect
    profile initial selector charge horizon error hsuffix
  have hprefixScaled :=
    mul_le_mul_of_nonneg_left hprefixMean
      (show 0 ≤ (horizon : ℝ)⁻¹ from
        inv_nonneg.mpr (Nat.cast_nonneg horizon))
  calc
    (horizon : ℝ)⁻¹ *
        (expect (G.stoppedHistoryLaw profile initial selector)
            (G.stoppedPrefixCharge charge) +
          ∑ time ∈ Finset.range horizon,
            expect (G.stoppedSuffixLaw profile initial selector time)
              (G.stoppedSuffixCharge charge)) =
        (horizon : ℝ)⁻¹ *
            expect (G.stoppedHistoryLaw profile initial selector)
              (G.stoppedPrefixCharge charge) +
          (horizon : ℝ)⁻¹ *
            ∑ time ∈ Finset.range horizon,
              expect (G.stoppedSuffixLaw profile initial selector time)
                (G.stoppedSuffixCharge charge) := by ring
    _ ≤ (horizon : ℝ)⁻¹ * ((fuel : ℝ) * prefixBound) +
          expect (G.stoppedHistoryLaw profile initial selector) error :=
      add_le_add hprefixScaled hsuffixMean
    _ = expect (G.stoppedHistoryLaw profile initial selector) error +
          (horizon : ℝ)⁻¹ * (fuel : ℝ) * prefixBound := by ring

/-- Exact typed splice hypothesis for a separately constructed strategic
continuation law.

The equality must be proved from the dispatcher and stopping selector.  It is
not implied merely by knowing the stopped terminal marginal. -/
def IsStoppedSuffixDisintegration
    [Fintype ι] {fuel : ℕ}
    (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel)
    (actualSuffixLaw :
      ∀ time, PMF (G.StoppedHistorySuffix fuel time)) : Prop :=
  ∀ time,
    actualSuffixLaw time =
      G.stoppedSuffixLaw profile initial selector time

/-- Once an actual strategic suffix law satisfies the explicit
disintegration interface, the stopped conditional charge bounds transfer to
that actual law. -/
theorem normalized_actual_stopped_suffix_charge_le_expect
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    {fuel : ℕ} (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel)
    (actualSuffixLaw :
      ∀ time, PMF (G.StoppedHistorySuffix fuel time))
    (hsplice :
      G.IsStoppedSuffixDisintegration profile initial selector
        actualSuffixLaw)
    (charge : G.HistoryPotential) (horizon : ℕ)
    (error : G.BoundedStoppedHistory fuel → ℝ)
    (hbound : ∀ base,
      base ∈
          (G.stoppedHistoryLaw profile initial selector).support →
        (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
          G.expectedHistoryValue (G.afterHistoryProfile profile base.2)
            base.2.2 (G.afterHistoryPotential charge base.2) time ≤
          error base) :
    (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
        expect (actualSuffixLaw time)
          (G.stoppedSuffixCharge charge) ≤
      expect (G.stoppedHistoryLaw profile initial selector) error := by
  have h := G.normalized_stopped_suffix_charge_le_expect
    profile initial selector charge horizon error hbound
  have heach : ∀ time,
      expect (actualSuffixLaw time)
          (G.stoppedSuffixCharge charge) =
        expect (G.stoppedSuffixLaw profile initial selector time)
          (G.stoppedSuffixCharge charge) := by
    intro time
    exact congrArg
      (fun law => expect law (G.stoppedSuffixCharge charge))
      (hsplice time)
  simp_rw [heach]
  exact h

end StochasticGame
end GameTheory
