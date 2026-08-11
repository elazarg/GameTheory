/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSupportEntry
import UniformEquilibrium.Quitting.Boundary.Repair.FixedTailUniformAbsorption

/-!
# Quantitative passport for the solo semantic branch

This file exposes the finite scalar information used by counterexample
search.  A singleton gap gives an explicit lower bound on the hazard of an
exact solo row.  A uniform version along a semantic spine gives geometric
survival and a quantitative occupation error.  At the singleton tail, solo
feasibility is a closed interval cut out by affine outsider inequalities, and
every attractive tight row exposes its exact reward breakpoint.

Compactness is deliberately not rebuilt here: once compact no-plateau
selection supplies one uniform positive singleton gap, the theorems below
consume that numerical gap directly.
-/

noncomputable section

namespace GameTheory

open Math.Probability Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Maximum singleton improvement over a semantic prescribed vector.  Its
strict positivity is exactly the failure of the all-Continue root. -/
def quittingTerminalSemanticMaximumSingletonGap [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) : ℝ :=
  QuittingBoundaryHolonomy.finitePlayerMax fun who =>
    reward (quittingSingletonTerminal who) who - pair.1 who

omit [DecidableEq ι] in
theorem continuous_quittingTerminalSemanticMaximumSingletonGap [Nonempty ι] :
    Continuous (quittingTerminalSemanticMaximumSingletonGap reward) := by
  unfold quittingTerminalSemanticMaximumSingletonGap
    QuittingBoundaryHolonomy.finitePlayerMax
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro who _hwho
  fun_prop

/-- Failure of all-Continue Nash is equivalent to a strictly positive maximum
singleton gap in the direction needed by compact minimization. -/
theorem quittingTerminalSemanticMaximumSingletonGap_pos_of_not_allContinueNash
    [Nonempty ι] (pair : QuittingTerminalSemanticPair ι)
    (hno : ¬ IsεQuittingRootNash reward pair.1 0
      (quittingAllContinueRoot : ι → PMF Bool)) :
    0 < quittingTerminalSemanticMaximumSingletonGap reward pair := by
  by_contra hnot
  have hmaxNonpos :
      quittingTerminalSemanticMaximumSingletonGap reward pair ≤ 0 :=
    le_of_not_gt hnot
  apply hno
  rw [isZeroQuittingRootNash_allContinue_iff_singleton_le]
  intro who
  have hcoordinate := QuittingBoundaryHolonomy.le_finitePlayerMax
    (fun player => reward (quittingSingletonTerminal player) player -
      pair.1 player) who
  unfold quittingTerminalSemanticMaximumSingletonGap at hmaxNonpos
  linarith

/-- Compact no-plateau selection supplies one uniform positive singleton gap.
This is the compact front end for the explicit owner-hazard modulus below. -/
theorem exists_uniform_positive_maximumSingletonGap_of_compact_noPlateau
    [Nonempty ι] (fiber : Set (QuittingTerminalSemanticPair ι))
    (hcompact : IsCompact fiber) (hnonempty : fiber.Nonempty)
    (hnoPlateau : ∀ pair ∈ fiber,
      ¬ IsεQuittingRootNash reward pair.1 0
        (quittingAllContinueRoot : ι → PMF Bool)) :
    ∃ eta, 0 < eta ∧ ∀ pair ∈ fiber,
      eta ≤ quittingTerminalSemanticMaximumSingletonGap reward pair := by
  obtain ⟨pair, hpair, hmin⟩ := hcompact.exists_isMinOn hnonempty
    continuous_quittingTerminalSemanticMaximumSingletonGap.continuousOn
  refine ⟨quittingTerminalSemanticMaximumSingletonGap reward pair,
    quittingTerminalSemanticMaximumSingletonGap_pos_of_not_allContinueNash
      pair (hnoPlateau pair hpair), ?_⟩
  intro candidate hcandidate
  exact hmin hcandidate

omit [DecidableEq ι] in
/-- A lower bound on the maximum singleton gap is attained by one concrete
player, which is the blocker consumed by the fixed-tail absorption estimate. -/
theorem exists_singletonGap_ge_of_le_maximumSingletonGap
    [Nonempty ι] (pair : QuittingTerminalSemanticPair ι) (eta : ℝ)
    (heta : eta ≤ quittingTerminalSemanticMaximumSingletonGap reward pair) :
    ∃ blocker,
      pair.1 blocker ≤
        reward (quittingSingletonTerminal blocker) blocker - eta := by
  unfold quittingTerminalSemanticMaximumSingletonGap
    QuittingBoundaryHolonomy.finitePlayerMax at heta
  obtain ⟨blocker, _hblocker, hmax⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun who => reward (quittingSingletonTerminal who) who - pair.1 who)
  exact ⟨blocker, by linarith⟩

/-- A singleton gap against any player forces the displayed solo owner's
hazard above the fixed-tail absorption modulus. -/
theorem gap_div_le_soloHazard_of_isZeroRootNash
    (tail : Payoff ι) (owner blocker : ι) (hazard : PMF Bool)
    {M eta : ℝ} (hM : 0 ≤ M) (heta : 0 < eta)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hgap : tail blocker ≤
      reward (quittingSingletonTerminal blocker) blocker - eta)
    (hnash : IsεQuittingRootNash reward tail 0
      (quittingSoloStationaryRoot owner hazard)) :
    eta / (eta + 2 * M) ≤ (hazard true).toReal := by
  have hendpoint : IsεQuittingRootEndpointNash reward tail 0
      (quittingSoloStationaryRoot owner hazard) :=
    (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
      reward tail 0 (quittingSoloStationaryRoot owner hazard)).2 hnash
  simpa using
    gap_div_le_quittingRootAbsorptionMass_of_isZeroEndpointNash
      reward tail (quittingSoloStationaryRoot owner hazard) blocker
        hM heta hreward hgap hendpoint

omit [Fintype ι] [DecidableEq ι] in
/-- A uniform lower bound on the owner's Quit probability gives the expected
geometric upper bound on finite solo survival. -/
theorem quittingSoloSemanticSurvival_le_pow_of_hazard_ge
    (root : ℕ → ι → PMF Bool) (owner : ι) (rho : ℝ)
    (hrhoLeOne : rho ≤ 1)
    (hhazard : ∀ time, rho ≤ (root time owner true).toReal) :
    ∀ start fuel,
      quittingSoloSemanticSurvival root owner start fuel ≤
        (1 - rho) ^ fuel := by
  intro start fuel
  induction fuel with
  | zero => simp
  | succ fuel ih =>
      rw [show fuel + 1 = Nat.succ fuel by omega,
        quittingSoloSemanticSurvival_succ, pow_succ]
      have hmass := quittingSoloHazardMass_add (root (start + fuel) owner)
      have hcontinue :
          (root (start + fuel) owner false).toReal ≤ 1 - rho := by
        linarith [hhazard (start + fuel)]
      exact mul_le_mul ih hcontinue ENNReal.toReal_nonneg
        (pow_nonneg (sub_nonneg.mpr hrhoLeOne) fuel)

/-- Pointwise singleton gaps along an exact fixed-owner solo spine produce a
uniform owner hazard. -/
theorem quittingSoloSemanticSpine_hazard_ge_gapDiv
    (pair : ℕ → QuittingTerminalSemanticPair ι)
    (root : ℕ → ι → PMF Bool) (owner : ι)
    {M eta : ℝ} (hM : 0 ≤ M) (heta : 0 < eta)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnash : ∀ time, IsεQuittingRootNash reward (pair (time + 1)).1 0
      (root time))
    (hroot : ∀ time, root time =
      quittingSoloStationaryRoot owner (root time owner))
    (hgap : ∀ time, ∃ blocker,
      (pair (time + 1)).1 blocker ≤
        reward (quittingSingletonTerminal blocker) blocker - eta) :
    ∀ time, eta / (eta + 2 * M) ≤
      (root time owner true).toReal := by
  intro time
  obtain ⟨blocker, hblocker⟩ := hgap time
  have hbound := gap_div_le_soloHazard_of_isZeroRootNash
    (reward := reward) (pair (time + 1)).1 owner blocker
      (root time owner) hM heta hreward hblocker
  rw [← hroot time] at hbound
  exact hbound (hnash time)

/-- The same uniform singleton gap yields geometric survival on the solo
semantic spine. -/
theorem quittingSoloSemanticSpine_survival_le_gapPow
    (pair : ℕ → QuittingTerminalSemanticPair ι)
    (root : ℕ → ι → PMF Bool) (owner : ι)
    {M eta : ℝ} (hM : 0 ≤ M) (heta : 0 < eta)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnash : ∀ time, IsεQuittingRootNash reward (pair (time + 1)).1 0
      (root time))
    (hroot : ∀ time, root time =
      quittingSoloStationaryRoot owner (root time owner))
    (hgap : ∀ time, ∃ blocker,
      (pair (time + 1)).1 blocker ≤
        reward (quittingSingletonTerminal blocker) blocker - eta) :
    ∀ start fuel,
      quittingSoloSemanticSurvival root owner start fuel ≤
        (1 - eta / (eta + 2 * M)) ^ fuel := by
  have hdenom : 0 < eta + 2 * M := by positivity
  have hrhoLeOne : eta / (eta + 2 * M) ≤ 1 := by
    apply (div_le_one hdenom).2
    linarith
  exact quittingSoloSemanticSurvival_le_pow_of_hazard_ge
    root owner (eta / (eta + 2 * M)) hrhoLeOne
      (quittingSoloSemanticSpine_hazard_ge_gapDiv pair root owner
        hM heta hreward hnash hroot hgap)

/-- Quantitative occupation error on a uniformly absorbing fixed-owner solo
spine. -/
theorem abs_quittingTerminalSemanticSoloSpine_prescribed_sub_soloReward_le
    (pair : ℕ → QuittingTerminalSemanticPair ι)
    (root : ℕ → ι → PMF Bool) (owner : ι)
    {M rho : ℝ} (hM : 0 ≤ M) (hrhoLeOne : rho ≤ 1)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : ∀ time, pair time ∈ quittingTerminalSemanticCarrier reward)
    (hprefix : ∀ time, pair time = quittingTerminalSemanticPrefix reward
      (root time) (pair (time + 1)))
    (hpure : ∀ time player, player ≠ owner →
      root time player = PMF.pure false)
    (hhazard : ∀ time, rho ≤ (root time owner true).toReal)
    (start fuel : ℕ) (player : ι) :
    |(pair start).1 player - quittingSoloReward reward owner player| ≤
      2 * M * (1 - rho) ^ fuel := by
  have hfold := quittingTerminalSemanticSoloSpine_prescribed_eq_occupation
    pair root owner hprefix hpure start fuel player
  have hresidual :
      (pair start).1 player - quittingSoloReward reward owner player =
        quittingSoloSemanticSurvival root owner start fuel *
          ((pair (start + fuel)).1 player -
            quittingSoloReward reward owner player) := by
    linarith only [hfold]
  have htailBox := quittingTerminalSemanticCarrier_mem_box
    (reward := reward) (pair (start + fuel)) hM hreward
      (hpair (start + fuel))
  have htailAbs : |(pair (start + fuel)).1 player| ≤ M :=
    abs_le.mpr ⟨htailBox.1.1 player, htailBox.1.2 player⟩
  have hsoloAbs : |quittingSoloReward reward owner player| ≤ M := by
    simpa [quittingSoloReward, quittingSingletonTerminal] using
      hreward (quittingSingletonTerminal owner) player
  have hdiff : |(pair (start + fuel)).1 player -
      quittingSoloReward reward owner player| ≤ 2 * M :=
    (abs_sub _ _).trans (by linarith)
  have hsurvival := quittingSoloSemanticSurvival_le_pow_of_hazard_ge
    root owner rho hrhoLeOne hhazard start fuel
  rw [hresidual, abs_mul,
    abs_of_nonneg
      (quittingSoloSemanticSurvival_nonneg root owner start fuel)]
  calc
    quittingSoloSemanticSurvival root owner start fuel *
        |(pair (start + fuel)).1 player -
          quittingSoloReward reward owner player| ≤
        quittingSoloSemanticSurvival root owner start fuel * (2 * M) :=
      mul_le_mul_of_nonneg_left hdiff
        (quittingSoloSemanticSurvival_nonneg root owner start fuel)
    _ ≤ (1 - rho) ^ fuel * (2 * M) :=
      mul_le_mul_of_nonneg_right hsurvival (by positivity)
    _ = 2 * M * (1 - rho) ^ fuel := by ring

/-! ## Singleton-tail affine feasibility -/

/-- The outsider's Quit-minus-Continue gain when `owner` quits with rate
`rate`, all other players Continue, and the tail is the owner's singleton
reward vector. -/
def quittingSingletonTailSoloGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner outsider : ι) (rate : ℝ) : ℝ :=
  (1 - rate) * reward (quittingSingletonTerminal outsider) outsider +
    rate * reward (quittingPairJoinTerminal outsider owner) outsider -
    reward (quittingSingletonTerminal owner) outsider

/-- The search-facing feasible solo-rate set. -/
def quittingSingletonTailSoloFeasibleRates
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) : Set ℝ :=
  {rate | rate ∈ Set.Icc 0 1 ∧ ∀ outsider, outsider ≠ owner →
    quittingSingletonTailSoloGain reward owner outsider rate ≤ 0}

omit [Fintype ι] in
/-- The singleton-tail feasible set is literally a closed interval (possibly
empty): it is closed and order-connected. -/
theorem isClosed_and_ordConnected_quittingSingletonTailSoloFeasibleRates
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι) :
    IsClosed (quittingSingletonTailSoloFeasibleRates reward owner) ∧
      Set.OrdConnected (quittingSingletonTailSoloFeasibleRates reward owner) := by
  constructor
  · have hrows : IsClosed {rate : ℝ | ∀ outsider, outsider ≠ owner →
        quittingSingletonTailSoloGain reward owner outsider rate ≤ 0} := by
      simp only [Set.setOf_forall]
      apply isClosed_iInter
      intro outsider
      apply isClosed_iInter
      intro _hne
      have hcontinuous : Continuous (fun rate : ℝ =>
          quittingSingletonTailSoloGain reward owner outsider rate) := by
        unfold quittingSingletonTailSoloGain
        fun_prop
      exact isClosed_Iic.preimage hcontinuous
    exact isClosed_Icc.inter hrows
  · rw [← convex_iff_ordConnected]
    intro p hp q hq a b ha hb hab
    change a * p + b * q ∈ quittingSingletonTailSoloFeasibleRates reward owner
    refine ⟨⟨by nlinarith [hp.1.1, hq.1.1],
      by nlinarith [hp.1.2, hq.1.2]⟩, ?_⟩
    intro outsider hne
    have hpRow := hp.2 outsider hne
    have hqRow := hq.2 outsider hne
    have haffine :
        quittingSingletonTailSoloGain reward owner outsider (a * p + b * q) =
          a * quittingSingletonTailSoloGain reward owner outsider p +
            b * quittingSingletonTailSoloGain reward owner outsider q := by
      unfold quittingSingletonTailSoloGain
      have hbEq : b = 1 - a := by linarith
      rw [hbEq]
      ring
    rw [haffine]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hpRow)
      (mul_nonpos_of_nonneg_of_nonpos hb hqRow)

omit [Fintype ι] in
/-- An attractive outsider which is tight at a positive solo rate pins that
rate to an explicit finite reward breakpoint. -/
theorem quittingSingletonTailSoloRate_eq_breakpoint_of_attractive_tight
    (owner outsider : ι) (rate : ℝ) (hrate : 0 < rate)
    (hattractive :
      reward (quittingSingletonTerminal owner) outsider <
        reward (quittingSingletonTerminal outsider) outsider)
    (htight : quittingSingletonTailSoloGain reward owner outsider rate = 0) :
    0 < reward (quittingSingletonTerminal outsider) outsider -
        reward (quittingPairJoinTerminal outsider owner) outsider ∧
      rate =
        (reward (quittingSingletonTerminal outsider) outsider -
            reward (quittingSingletonTerminal owner) outsider) /
          (reward (quittingSingletonTerminal outsider) outsider -
            reward (quittingPairJoinTerminal outsider owner) outsider) := by
  have hproduct : rate *
      (reward (quittingSingletonTerminal outsider) outsider -
        reward (quittingPairJoinTerminal outsider owner) outsider) =
      reward (quittingSingletonTerminal outsider) outsider -
        reward (quittingSingletonTerminal owner) outsider := by
    unfold quittingSingletonTailSoloGain at htight
    nlinarith
  have hdenomPos : 0 <
      reward (quittingSingletonTerminal outsider) outsider -
        reward (quittingPairJoinTerminal outsider owner) outsider := by
    nlinarith
  refine ⟨hdenomPos, (eq_div_iff (ne_of_gt hdenomPos)).2 ?_⟩
  exact hproduct

omit [Fintype ι] in
/-- Deterring an attractive outsider at an interior solo rate requires a
literal collision cliff. -/
theorem quittingPairJoinReward_lt_singletonOwnerReward_of_attractive_feasible
    (owner outsider : ι) (rate : ℝ)
    (hratePos : 0 < rate) (hrateLt : rate < 1)
    (hattractive :
      reward (quittingSingletonTerminal owner) outsider <
        reward (quittingSingletonTerminal outsider) outsider)
    (hfeasible : quittingSingletonTailSoloGain reward owner outsider rate ≤ 0) :
    reward (quittingPairJoinTerminal outsider owner) outsider <
      reward (quittingSingletonTerminal owner) outsider := by
  unfold quittingSingletonTailSoloGain at hfeasible
  nlinarith

end GameTheory
