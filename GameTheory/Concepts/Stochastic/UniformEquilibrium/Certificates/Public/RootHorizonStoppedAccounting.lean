/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Certificates.Public.StoppedHistoryAccounting

/-!
# Common-root-horizon stopped public-history accounting

For a fixed root horizon `total`, a bounded stopping history of length
`stopLength` has a dependent continuation length `total - stopLength`.
This file constructs the corresponding dependent conditional law and keeps
the cast back to `Hist total` explicit.

Causality of the stopping selector is stated as the ordinary finite stopping
time condition: the event `stopLength ≤ time` is determined by the history
prefix at `time`.  Proving that a concrete global dispatcher has the
conditional law constructed here still requires a strategic law identity;
that identity is packaged as `IsRootStoppedSuffixDisintegration`.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} {G : StochasticGame ι}

/-- Finite non-anticipation for a bounded stopping selector.  At every
bounded time, whether stopping has already occurred is determined by the
public-history prefix at that time. -/
def IsCausalBoundedStopSelector {fuel : ℕ}
    (selector : G.BoundedPublicStopSelector fuel) : Prop :=
  ∀ (time : Fin (fuel + 1)) (left right : G.Hist fuel),
    G.boundedHistoryPrefix left time =
        G.boundedHistoryPrefix right time →
      ((selector left).val ≤ time.val ↔
        (selector right).val ≤ time.val)

/-- A stopped base paired with the continuation that reaches one common root
horizon. -/
abbrev RootHorizonStoppedSuffix (G : StochasticGame ι)
    (fuel total : ℕ) :=
  (base : G.BoundedStoppedHistory fuel) ×
    G.Hist (total - base.1.val)

/-- The stopped base length is below every root horizon above the fuel. -/
theorem stoppedLength_le_rootHorizon {fuel total : ℕ}
    (hfuel : fuel ≤ total)
    (base : G.BoundedStoppedHistory fuel) :
    base.1.val ≤ total :=
  le_trans (Nat.lt_succ_iff.mp base.1.isLt) hfuel

/-- Append a dependent stopped suffix and cast its length back to the common
root horizon. -/
def rootHistoryOfStoppedSuffix {fuel total : ℕ}
    (hfuel : fuel ≤ total)
    (path : G.RootHorizonStoppedSuffix fuel total) : G.Hist total :=
  let hlength := G.stoppedLength_le_rootHorizon hfuel path.1
  let hadd :
      path.1.1.val + (total - path.1.1.val) = total :=
    Nat.add_sub_of_le hlength
  _root_.cast (congrArg G.Hist hadd)
    (G.appendHist path.1.2 path.2)

/-- First sample the bounded stopped history, then sample the profile's
conditional continuation for exactly the dependent number of stages needed
to reach the common root horizon. -/
def rootHorizonStoppedSuffixLaw
    [Fintype ι] {fuel : ℕ}
    (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel)
    (total : ℕ) :
    PMF (G.RootHorizonStoppedSuffix fuel total) :=
  (G.stoppedHistoryLaw profile initial selector).bind fun base =>
    (G.histDist (G.afterHistoryProfile profile base.2) base.2.2
      (total - base.1.val)).map fun suffix => ⟨base, suffix⟩

/-- The dependent continuation law has the original stopped-history
marginal. -/
theorem rootHorizonStoppedSuffixLaw_base_marginal
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    {fuel : ℕ} (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel) (total : ℕ) :
    (G.rootHorizonStoppedSuffixLaw profile initial selector total).map
        Sigma.fst =
      G.stoppedHistoryLaw profile initial selector := by
  unfold rootHorizonStoppedSuffixLaw
  rw [PMF.map_bind]
  have hinter : (fun base : G.BoundedStoppedHistory fuel =>
      PMF.map Sigma.fst
        ((G.histDist (G.afterHistoryProfile profile base.2) base.2.2
          (total - base.1.val)).map fun suffix =>
            (⟨base, suffix⟩ :
              G.RootHorizonStoppedSuffix fuel total))) =
      (fun base : G.BoundedStoppedHistory fuel => PMF.pure base) := by
    funext base
    rw [PMF.map_comp]
    change
      PMF.map (fun _suffix => base)
          (G.histDist (G.afterHistoryProfile profile base.2) base.2.2
            (total - base.1.val)) =
        PMF.pure base
    exact PMF.map_const _ _
  rw [hinter, PMF.bind_pure]

/-- The explicitly constructed law on root histories obtained by appending
the dependent stopped suffix. -/
def reconstructedRootHistoryLaw
    [Fintype ι] {fuel total : ℕ}
    (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel)
    (hfuel : fuel ≤ total) : PMF (G.Hist total) :=
  (G.rootHorizonStoppedSuffixLaw profile initial selector total).map
    (G.rootHistoryOfStoppedSuffix hfuel)

/-- Exact strategic interface needed to identify the actual root history law
with stopped-history conditioning.

Causality is recorded separately because it is the mathematical
non-anticipation condition on the selector.  The equality also encodes that
the global dispatcher really uses the rebased continuation profile on every
selected branch. -/
structure IsRootStoppedSuffixDisintegration
    [Fintype ι] {fuel total : ℕ}
    (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel)
    (hfuel : fuel ≤ total) : Prop where
  causal : G.IsCausalBoundedStopSelector selector
  law_eq :
    G.histDist profile initial total =
      G.reconstructedRootHistoryLaw profile initial selector hfuel

/-- Under the explicit strategic disintegration interface, a root-horizon
expectation is expectation over the dependent stopped-suffix law. -/
theorem expect_rootHistory_eq_stoppedSuffix
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    {fuel total : ℕ} (profile : G.BehaviorProfile)
    (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel)
    (hfuel : fuel ≤ total)
    (hsplice :
      G.IsRootStoppedSuffixDisintegration profile initial selector hfuel)
    (value : G.Hist total → ℝ) :
    expect (G.histDist profile initial total) value =
      expect
        (G.rootHorizonStoppedSuffixLaw profile initial selector total)
        (fun path => value (G.rootHistoryOfStoppedSuffix hfuel path)) := by
  rw [hsplice.law_eq]
  unfold reconstructedRootHistoryLaw
  rw [expect_map]

/-- Conditional expected charge accumulated from a stopped base up to one
common root horizon. -/
def rootHorizonSuffixExpectedCharge [Fintype ι] {fuel : ℕ}
    (profile : G.BehaviorProfile) (charge : G.HistoryPotential)
    (total : ℕ) (base : G.BoundedStoppedHistory fuel) : ℝ :=
  ∑ time ∈ Finset.range (total - base.1.val),
    G.expectedHistoryValue (G.afterHistoryProfile profile base.2)
      base.2.2 (G.afterHistoryPotential charge base.2) time

/-- Conditional suffix bounds with their dependent local horizons aggregate
at one common root horizon.

The strict inequality `fuel < total` ensures every selected branch has a
positive remaining local horizon. -/
theorem normalized_rootHorizon_suffix_charge_le_expect
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    {fuel total : ℕ} (profile : G.BehaviorProfile)
    (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel)
    (charge : G.HistoryPotential) (hfuel : fuel < total)
    (error : G.BoundedStoppedHistory fuel → ℝ)
    (herror : ∀ base,
      base ∈
          (G.stoppedHistoryLaw profile initial selector).support →
        0 ≤ error base)
    (hbound : ∀ base,
      base ∈
          (G.stoppedHistoryLaw profile initial selector).support →
        ((total - base.1.val : ℕ) : ℝ)⁻¹ *
            G.rootHorizonSuffixExpectedCharge profile charge total base ≤
          error base) :
    (total : ℝ)⁻¹ *
        expect (G.stoppedHistoryLaw profile initial selector)
          (G.rootHorizonSuffixExpectedCharge profile charge total) ≤
      expect (G.stoppedHistoryLaw profile initial selector) error := by
  let stoppedLaw := G.stoppedHistoryLaw profile initial selector
  let suffixCharge : G.BoundedStoppedHistory fuel → ℝ :=
    G.rootHorizonSuffixExpectedCharge profile charge total
  have htotalReal : (0 : ℝ) < total := by
    exact_mod_cast lt_of_le_of_lt (Nat.zero_le fuel) hfuel
  rw [← expect_const_mul]
  classical
  have hcongr :
      expect stoppedLaw (fun base => (total : ℝ)⁻¹ * suffixCharge base) =
        expect stoppedLaw fun base =>
          if base ∈ stoppedLaw.support then
            (total : ℝ)⁻¹ * suffixCharge base
          else error base :=
    expect_congr_on_support stoppedLaw _ _ fun base hbase => by
      simp [hbase]
  rw [hcongr]
  apply expect_mono
  intro base
  by_cases hbase : base ∈ stoppedLaw.support
  · simp only [hbase, if_true]
    have hstopFuel : base.1.val ≤ fuel :=
      Nat.lt_succ_iff.mp base.1.isLt
    have hstopTotal : base.1.val < total :=
      lt_of_le_of_lt hstopFuel hfuel
    have hremaining : 0 < total - base.1.val :=
      Nat.sub_pos_of_lt hstopTotal
    have hremainingReal :
        (0 : ℝ) < ((total - base.1.val : ℕ) : ℝ) := by
      exact_mod_cast hremaining
    have hsuffix :
        suffixCharge base ≤
          ((total - base.1.val : ℕ) : ℝ) * error base := by
      calc
        suffixCharge base =
            ((total - base.1.val : ℕ) : ℝ) *
              (((total - base.1.val : ℕ) : ℝ)⁻¹ *
                suffixCharge base) := by
              field_simp
        _ ≤ ((total - base.1.val : ℕ) : ℝ) * error base :=
          mul_le_mul_of_nonneg_left
            (by
              simpa [suffixCharge, stoppedLaw] using
                hbound base hbase)
            (le_of_lt hremainingReal)
    calc
      (total : ℝ)⁻¹ * suffixCharge base ≤
          (total : ℝ)⁻¹ *
            (((total - base.1.val : ℕ) : ℝ) * error base) :=
        mul_le_mul_of_nonneg_left hsuffix
          (inv_nonneg.mpr (le_of_lt htotalReal))
      _ ≤ (total : ℝ)⁻¹ * ((total : ℝ) * error base) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_right
            (by
              exact_mod_cast Nat.sub_le total base.1.val)
            (herror base hbase)
        · exact inv_nonneg.mpr (le_of_lt htotalReal)
      _ = error base := by
        field_simp
  · simp [hbase]

/-- Common-root-horizon prefix and suffix accounting.  The random stopping
prefix contributes at most `fuel * prefixBound / total`; every branch's
remaining suffix is measured to the same root horizon `total`. -/
theorem normalized_rootHorizon_total_charge_le_expect
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    {fuel total : ℕ} (profile : G.BehaviorProfile)
    (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel)
    (charge : G.HistoryPotential) (hfuel : fuel < total)
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
    (herror : ∀ base,
      base ∈
          (G.stoppedHistoryLaw profile initial selector).support →
        0 ≤ error base)
    (hsuffix : ∀ base,
      base ∈
          (G.stoppedHistoryLaw profile initial selector).support →
        ((total - base.1.val : ℕ) : ℝ)⁻¹ *
            G.rootHorizonSuffixExpectedCharge profile charge total base ≤
          error base) :
    (total : ℝ)⁻¹ *
        (expect (G.stoppedHistoryLaw profile initial selector)
            (G.stoppedPrefixCharge charge) +
          expect (G.stoppedHistoryLaw profile initial selector)
            (G.rootHorizonSuffixExpectedCharge profile charge total)) ≤
      expect (G.stoppedHistoryLaw profile initial selector) error +
        (total : ℝ)⁻¹ * (fuel : ℝ) * prefixBound := by
  have hprefixMean := G.expect_stoppedPrefixCharge_le
    profile initial selector charge prefixBound hprefixBound hprefix
  have hsuffixMean :=
    G.normalized_rootHorizon_suffix_charge_le_expect
      profile initial selector charge hfuel error herror hsuffix
  have hprefixScaled :=
    mul_le_mul_of_nonneg_left hprefixMean
      (show 0 ≤ (total : ℝ)⁻¹ from
        inv_nonneg.mpr (Nat.cast_nonneg total))
  calc
    (total : ℝ)⁻¹ *
        (expect (G.stoppedHistoryLaw profile initial selector)
            (G.stoppedPrefixCharge charge) +
          expect (G.stoppedHistoryLaw profile initial selector)
            (G.rootHorizonSuffixExpectedCharge profile charge total)) =
        (total : ℝ)⁻¹ *
            expect (G.stoppedHistoryLaw profile initial selector)
              (G.stoppedPrefixCharge charge) +
          (total : ℝ)⁻¹ *
            expect (G.stoppedHistoryLaw profile initial selector)
              (G.rootHorizonSuffixExpectedCharge profile charge total) := by
        ring
    _ ≤ (total : ℝ)⁻¹ * ((fuel : ℝ) * prefixBound) +
          expect (G.stoppedHistoryLaw profile initial selector) error :=
      add_le_add hprefixScaled hsuffixMean
    _ = expect (G.stoppedHistoryLaw profile initial selector) error +
          (total : ℝ)⁻¹ * (fuel : ℝ) * prefixBound := by
      ring

end StochasticGame
end GameTheory
