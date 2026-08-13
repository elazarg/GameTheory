/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.TerminalSemanticPair
import UniformEquilibrium.Quitting.Root.TailStability

/-!
# Metric and tube stability of terminal semantic prefixes

The terminal semantic prefix is nonexpansive in the coordinatewise sup
metric.  Consequently tubes around any forward-invariant semantic carrier are
forward invariant, and a positive aggregate debt floor degrades by at most
`2 * card ι` times the tube radius.

This is metric/tube infrastructure only.  It does not assert that a carrier
or its tube is semialgebraic, nor does it address finite barrier completeness.
-/

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Coordinatewise sup-distance bound between two semantic pairs. -/
def semanticPairWithin
    (δ : ℝ) (p q : QuittingTerminalSemanticPair ι) : Prop :=
  (∀ who, |p.1 who - q.1 who| ≤ δ) ∧
  (∀ who, |p.2 who - q.2 who| ≤ δ)

theorem semanticPairWithin_refl
    {δ : ℝ} (hδ : 0 ≤ δ) (p : QuittingTerminalSemanticPair ι) :
    semanticPairWithin δ p p := by
  constructor <;> intro who <;> simp [hδ]

theorem semanticPairWithin_trans
    {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    {p q r : QuittingTerminalSemanticPair ι}
    (hpq : semanticPairWithin δ p q)
    (hqr : semanticPairWithin ε q r) :
    semanticPairWithin (δ + ε) p r := by
  constructor
  · intro who
    exact (abs_sub_le _ _ _).trans (add_le_add (hpq.1 who) (hqr.1 who))
  · intro who
    exact (abs_sub_le _ _ _).trans (add_le_add (hpq.2 who) (hqr.2 who))

/-- A fixed product root acts nonexpansively on semantic pairs. -/
theorem quittingTerminalSemanticPrefix_within
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    {δ : ℝ} (hδ : 0 ≤ δ)
    {p q : QuittingTerminalSemanticPair ι}
    (hpq : semanticPairWithin δ p q) :
    semanticPairWithin δ
      (quittingTerminalSemanticPrefix reward root p)
      (quittingTerminalSemanticPrefix reward root q) := by
  constructor
  · intro who
    exact abs_quittingRootExpectedPayoff_sub_of_tail_close
      reward p.1 q.1 root who hδ (hpq.1 who)
  · intro who
    have hquit := abs_quittingRootExpectedPayoff_sub_of_tail_close
      reward p.1 q.1 (Function.update root who (PMF.pure true))
      who hδ (hpq.1 who)
    have htail : ∀ player,
        |(Function.update p.1 who (p.2 who)) player -
          (Function.update q.1 who (q.2 who)) player| ≤ δ := by
      intro player
      by_cases hplayer : player = who
      · subst player
        simp only [Function.update_self]
        exact hpq.2 who
      · simpa only [Function.update_of_ne hplayer] using hpq.1 player
    have hcontinue := abs_quittingRootExpectedPayoff_sub_of_tail_close
      reward (Function.update p.1 who (p.2 who))
      (Function.update q.1 who (q.2 who))
      (Function.update root who (PMF.pure false)) who hδ
      (htail who)
    change |max
        (quittingRootQuitPayoff reward p.1 root who)
        (quittingRootContinuePayoff reward
          (Function.update p.1 who (p.2 who)) root who) -
      max
        (quittingRootQuitPayoff reward q.1 root who)
        (quittingRootContinuePayoff reward
          (Function.update q.1 who (q.2 who)) root who)| ≤ δ
    calc
      _ ≤ max
          |quittingRootQuitPayoff reward p.1 root who -
            quittingRootQuitPayoff reward q.1 root who|
          |quittingRootContinuePayoff reward
              (Function.update p.1 who (p.2 who)) root who -
            quittingRootContinuePayoff reward
              (Function.update q.1 who (q.2 who)) root who| :=
        abs_max_sub_max_le_max _ _ _ _
      _ ≤ max δ δ := max_le
        (by simpa [quittingRootQuitPayoff] using hquit)
        (by simpa [quittingRootContinuePayoff] using hcontinue)
      _ = δ := max_self δ

theorem quittingTerminalSemanticPrefix_within_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    {p q : QuittingTerminalSemanticPair ι}
    (hpq : semanticPairWithin 0 p q) :
    quittingTerminalSemanticPrefix reward root p =
      quittingTerminalSemanticPrefix reward root q := by
  have h := quittingTerminalSemanticPrefix_within reward root (δ := 0)
    (le_refl 0) hpq
  apply Prod.ext
  · funext who
    have := h.1 who
    linarith [abs_le.mp this]
  · funext who
    have := h.2 who
    linarith [abs_le.mp this]

/-- The closed existential tube for the coordinatewise sup-distance relation. -/
def semanticPairTube
    (K : Set (QuittingTerminalSemanticPair ι)) (δ : ℝ) :
    Set (QuittingTerminalSemanticPair ι) :=
  {p | ∃ q ∈ K, semanticPairWithin δ p q}

theorem quittingTerminalSemanticPrefix_mapsTo_tube
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    {K : Set (QuittingTerminalSemanticPair ι)} {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hK : Set.MapsTo (quittingTerminalSemanticPrefix reward root) K K) :
    Set.MapsTo (quittingTerminalSemanticPrefix reward root)
      (semanticPairTube K δ) (semanticPairTube K δ) := by
  rintro p ⟨q, hq, hpq⟩
  exact ⟨quittingTerminalSemanticPrefix reward root q, hK hq,
    quittingTerminalSemanticPrefix_within reward root hδ hpq⟩

theorem quittingTerminalSemanticCarrier_mapsTo_tube
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    Set.MapsTo (quittingTerminalSemanticPrefix reward root)
      (semanticPairTube (quittingTerminalSemanticCarrier reward) δ)
      (semanticPairTube (quittingTerminalSemanticCarrier reward) δ) := by
  apply quittingTerminalSemanticPrefix_mapsTo_tube reward root hδ
  intro pair hpair
  exact quittingTerminalSemanticPrefix_mem_carrier
    reward root pair hM hreward hpair

/-- Aggregate playerwise semantic debt. -/
def semanticDebtSum (pair : QuittingTerminalSemanticPair ι) : ℝ :=
  ∑ who, quittingTerminalSemanticDebt pair who

theorem abs_semanticDebtSum_sub_le_of_within
    {p q : QuittingTerminalSemanticPair ι} {δ : ℝ}
    (hδ : 0 ≤ δ) (hpq : semanticPairWithin δ p q) :
    |semanticDebtSum p - semanticDebtSum q| ≤
      (2 * Fintype.card ι : ℝ) * δ := by
  unfold semanticDebtSum quittingTerminalSemanticDebt
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ x, ((p.2 x - p.1 x) - (q.2 x - q.1 x))| ≤
        ∑ x, |(p.2 x - p.1 x) - (q.2 x - q.1 x)| := by
      simpa using
        (Finset.abs_sum_le_sum_abs
          (fun x : ι => (p.2 x - p.1 x) - (q.2 x - q.1 x)) Finset.univ)
    _ ≤ ∑ _x : ι, (2 : ℝ) * δ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [show (p.2 i - p.1 i) - (q.2 i - q.1 i) =
          (p.2 i - q.2 i) - (p.1 i - q.1 i) by ring]
      calc
        |(p.2 i - q.2 i) - (p.1 i - q.1 i)| ≤
            |p.2 i - q.2 i| + |p.1 i - q.1 i| := by
          simpa [abs_sub_comm] using
            (abs_sub_le (p.2 i - q.2 i) 0 (p.1 i - q.1 i))
        _ ≤ δ + δ := add_le_add (hpq.2 i) (hpq.1 i)
        _ = 2 * δ := by ring
    _ = (2 * Fintype.card ι : ℝ) * δ := by
      simp [nsmul_eq_mul]
      ring

theorem semanticDebtSum_ge_floor_of_mem_tube
    {K : Set (QuittingTerminalSemanticPair ι)}
    {Dstar δ : ℝ} {p : QuittingTerminalSemanticPair ι}
    (hfloor : ∀ q ∈ K, Dstar ≤ semanticDebtSum q)
    (hp : p ∈ semanticPairTube K δ) (hδ : 0 ≤ δ) :
    Dstar - (2 * Fintype.card ι : ℝ) * δ ≤ semanticDebtSum p := by
  obtain ⟨q, hq, hpq⟩ := hp
  have hdebt := abs_semanticDebtSum_sub_le_of_within hδ hpq
  have hqfloor := hfloor q hq
  linarith [abs_le.mp hdebt]

theorem semanticDebtSum_pos_of_mem_tube_of_floor_pos
    {K : Set (QuittingTerminalSemanticPair ι)}
    {Dstar δ : ℝ} {p : QuittingTerminalSemanticPair ι}
    (hfloor : ∀ q ∈ K, Dstar ≤ semanticDebtSum q)
    (hp : p ∈ semanticPairTube K δ) (hδ : 0 ≤ δ)
    (hsmall : (2 * Fintype.card ι : ℝ) * δ < Dstar) :
    0 < semanticDebtSum p := by
  have h := semanticDebtSum_ge_floor_of_mem_tube hfloor hp hδ
  linarith

end GameTheory
