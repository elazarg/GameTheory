/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.SurvivalProduct
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticMinimumSpine
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSoloOwnerRefinement
import UniformEquilibrium.Quitting.Paths.BehaviorStoppingLaw
import UniformEquilibrium.Quitting.Root.TerminalSemanticMoment

/-!
# Occupation identities on a fixed-owner terminal-semantic spine

On the non-plateau branch of the minimum terminal-semantic chronology, one
fixed owner is the only active player.  The prescribed coordinate therefore
obeys an exact scalar occupation recursion: it is the mixture of the owner's
singleton reward and the next prescribed vector, with weights equal to the
owner's Quit and Continue probabilities.  Iterating gives a finite formula
whose residual coefficient is precisely the owner's survival product.

This identifies the remaining semantic obstruction.  If that survival
product vanishes, boundedness forces the initial prescribed vector to be the
owner's singleton reward vector.  A positive first-stage Continue probability
then propagates the equality to the next state, so the first root is already
an atomic solo endpoint equilibrium.  In a quitting counterexample this is
the isolated-negative branch.  Away from that branch, the survival product
cannot vanish: the semantic chronology necessarily retains a positive
``at infinity'' occupation mass.

Every prescribed state also lies in the finite reward-moment polytope.  Thus
away from atomic closure, the owner-tight slice of that polytope must contain
a vector distinct from the owner's singleton reward.  This is an exact finite
linear obstruction suitable for counterexample search.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.ProbabilityMassFunction
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The probability that a fixed solo owner Continues throughout a finite
window of a semantic spine. -/
def quittingSoloSemanticSurvival
    (root : ℕ → ι → PMF Bool) (owner : ι) (start fuel : ℕ) : ℝ :=
  Math.survivalProduct (fun time => (root time owner false).toReal)
    start fuel

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingSoloSemanticSurvival_zero
    (root : ℕ → ι → PMF Bool) (owner : ι) (start : ℕ) :
    quittingSoloSemanticSurvival root owner start 0 = 1 := by
  simp [quittingSoloSemanticSurvival]

omit [Fintype ι] [DecidableEq ι] in
theorem quittingSoloSemanticSurvival_succ
    (root : ℕ → ι → PMF Bool) (owner : ι) (start fuel : ℕ) :
    quittingSoloSemanticSurvival root owner start (fuel + 1) =
      quittingSoloSemanticSurvival root owner start fuel *
        (root (start + fuel) owner false).toReal := by
  exact Math.survivalProduct_succ _ _ _

omit [Fintype ι] [DecidableEq ι] in
theorem quittingSoloSemanticSurvival_add
    (root : ℕ → ι → PMF Bool) (owner : ι) (start first second : ℕ) :
    quittingSoloSemanticSurvival root owner start (first + second) =
      quittingSoloSemanticSurvival root owner start first *
        quittingSoloSemanticSurvival root owner (start + first) second := by
  exact Math.survivalProduct_add _ _ _ _

omit [Fintype ι] [DecidableEq ι] in
theorem quittingSoloSemanticSurvival_nonneg
    (root : ℕ → ι → PMF Bool) (owner : ι) (start fuel : ℕ) :
    0 ≤ quittingSoloSemanticSurvival root owner start fuel := by
  exact Math.survivalProduct_nonneg _
    (fun _ => ENNReal.toReal_nonneg) start fuel

omit [Fintype ι] [DecidableEq ι] in
theorem quittingSoloSemanticSurvival_le_one
    (root : ℕ → ι → PMF Bool) (owner : ι) (start fuel : ℕ) :
    quittingSoloSemanticSurvival root owner start fuel ≤ 1 := by
  apply Math.survivalProduct_le_one _
      (fun _ => ENNReal.toReal_nonneg) _ start fuel
  intro time
  exact ENNReal.toReal_mono ENNReal.one_ne_top
      (PMF.coe_le_one (root time owner) false) |>.trans_eq (by norm_num)

omit [Fintype ι] [DecidableEq ι] in
theorem antitone_quittingSoloSemanticSurvival
    (root : ℕ → ι → PMF Bool) (owner : ι) (start : ℕ) :
    Antitone (quittingSoloSemanticSurvival root owner start) := by
  apply antitone_nat_of_succ_le
  intro fuel
  rw [quittingSoloSemanticSurvival_succ]
  have hfactor : (root (start + fuel) owner false).toReal ≤ 1 :=
    ENNReal.toReal_mono ENNReal.one_ne_top
      (PMF.coe_le_one (root (start + fuel) owner) false) |>.trans_eq
        (by norm_num)
  exact mul_le_of_le_one_right
    (quittingSoloSemanticSurvival_nonneg root owner start fuel) hfactor

omit [Fintype ι] [DecidableEq ι] in
/-- A nonvanishing decreasing survival product has a uniform positive lower
bound. -/
theorem exists_pos_le_quittingSoloSemanticSurvival_of_not_tendsto_zero
    (root : ℕ → ι → PMF Bool) (owner : ι) (start : ℕ)
    (hnot : ¬ Tendsto (quittingSoloSemanticSurvival root owner start)
      atTop (nhds 0)) :
    ∃ lower, 0 < lower ∧ ∀ fuel,
      lower ≤ quittingSoloSemanticSurvival root owner start fuel := by
  by_contra hnone
  push Not at hnone
  apply hnot
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨threshold, hthreshold⟩ := hnone ε hε
  refine ⟨threshold, fun fuel hfuel => ?_⟩
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg
      (quittingSoloSemanticSurvival_nonneg root owner start fuel)]
  exact (antitone_quittingSoloSemanticSurvival root owner start hfuel).trans_lt
    hthreshold

/-- Carrier points inherit the same uniform coordinate box as literal
terminal semantic pairs. -/
theorem quittingTerminalSemanticCarrier_mem_box
    (pair : QuittingTerminalSemanticPair ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    pair ∈ quittingTerminalSemanticBox ι M := by
  apply (closure_minimal ?_ ?_) hpair
  · rintro candidate ⟨profile, rfl⟩
    exact quittingTerminalSemanticPair_mem_box reward profile hM hreward
  · exact (quittingTerminalSemanticBox_isCompact M).isClosed

/-- One exact solo semantic-prefix edge is the ordinary occupation mixture
of the owner's singleton reward and the next prescribed vector. -/
theorem quittingTerminalSemanticSoloSpine_prescribed_step
    (pair : ℕ → QuittingTerminalSemanticPair ι)
    (root : ℕ → ι → PMF Bool) (owner : ι)
    (hprefix : ∀ time, pair time = quittingTerminalSemanticPrefix reward
      (root time) (pair (time + 1)))
    (hpure : ∀ time player, player ≠ owner →
      root time player = PMF.pure false)
    (time : ℕ) :
    (pair time).1 = fun player =>
      (root time owner true).toReal *
          quittingSoloReward reward owner player +
        (root time owner false).toReal * (pair (time + 1)).1 player := by
  have hroot : root time =
      quittingSoloStationaryRoot owner (root time owner) :=
    eq_quittingSoloStationaryRoot_of_others_continue (hpure time)
  have hprescribed := congrArg Prod.fst (hprefix time)
  change (pair time).1 = quittingRootSuccessorPayoff reward
    (pair (time + 1)).1 (root time) at hprescribed
  rw [hroot, quittingRootSuccessorPayoff_solo] at hprescribed
  exact hprescribed

/-- Finite occupation formula for a fixed-owner semantic spine.  The only
unresolved mass after `fuel` stages is the exact owner-survival product. -/
theorem quittingTerminalSemanticSoloSpine_prescribed_eq_occupation
    (pair : ℕ → QuittingTerminalSemanticPair ι)
    (root : ℕ → ι → PMF Bool) (owner : ι)
    (hprefix : ∀ time, pair time = quittingTerminalSemanticPrefix reward
      (root time) (pair (time + 1)))
    (hpure : ∀ time player, player ≠ owner →
      root time player = PMF.pure false) :
    ∀ start fuel player,
      (pair start).1 player =
        (1 - quittingSoloSemanticSurvival root owner start fuel) *
            quittingSoloReward reward owner player +
          quittingSoloSemanticSurvival root owner start fuel *
            (pair (start + fuel)).1 player := by
  intro start fuel
  induction fuel generalizing start with
  | zero => simp
  | succ fuel ih =>
      intro player
      have hstep := congrFun
        (quittingTerminalSemanticSoloSpine_prescribed_step
          pair root owner hprefix hpure start) player
      rw [hstep, ih (start := start + 1) player]
      have hmass := quittingSoloHazardMass_add (root start owner)
      have hsurvival :
          quittingSoloSemanticSurvival root owner start (fuel + 1) =
            (root start owner false).toReal *
              quittingSoloSemanticSurvival root owner (start + 1) fuel := by
        rw [show fuel + 1 = 1 + fuel by omega,
          quittingSoloSemanticSurvival_add]
        have hone : quittingSoloSemanticSurvival root owner start 1 =
            (root start owner false).toReal := by
          simp [quittingSoloSemanticSurvival, Math.survivalProduct]
        rw [hone]
      rw [hsurvival]
      rw [show start + 1 + fuel = start + (fuel + 1) by omega]
      have hquit : (root start owner true).toReal =
          1 - (root start owner false).toReal := by
        linarith
      rw [hquit]
      ring

/-- If the owner's finite survival product vanishes, bounded semantic tails
select the owner's singleton reward as the initial prescribed vector. -/
theorem quittingTerminalSemanticSoloSpine_initial_eq_soloReward_of_survival_tendsto_zero
    (pair : ℕ → QuittingTerminalSemanticPair ι)
    (root : ℕ → ι → PMF Bool) (owner : ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : ∀ time, pair time ∈ quittingTerminalSemanticCarrier reward)
    (hprefix : ∀ time, pair time = quittingTerminalSemanticPrefix reward
      (root time) (pair (time + 1)))
    (hpure : ∀ time player, player ≠ owner →
      root time player = PMF.pure false)
    (hsurvival : Tendsto
      (quittingSoloSemanticSurvival root owner 0) atTop (nhds 0)) :
    (pair 0).1 = quittingSoloReward reward owner := by
  funext player
  let residual : ℕ → ℝ := fun fuel =>
    quittingSoloSemanticSurvival root owner 0 fuel *
      ((pair fuel).1 player - quittingSoloReward reward owner player)
  have hidentity : ∀ fuel,
      (pair 0).1 player - quittingSoloReward reward owner player =
        residual fuel := by
    intro fuel
    have hfold := quittingTerminalSemanticSoloSpine_prescribed_eq_occupation
      pair root owner hprefix hpure 0 fuel player
    dsimp only [residual]
    simp only [Nat.zero_add] at hfold
    linarith
  have htailBound : ∀ fuel,
      |(pair fuel).1 player - quittingSoloReward reward owner player| ≤
        2 * M := by
    intro fuel
    have hbox := quittingTerminalSemanticCarrier_mem_box
      (reward := reward) (pair fuel) hM hreward (hpair fuel)
    have hpairAbs : |(pair fuel).1 player| ≤ M :=
      abs_le.mpr ⟨hbox.1.1 player, hbox.1.2 player⟩
    have hsoloAbs : |quittingSoloReward reward owner player| ≤ M := by
      simpa [quittingSoloReward, quittingSingletonTerminal] using
        hreward (quittingSingletonTerminal owner) player
    exact (abs_sub _ _).trans (by linarith)
  have hsurvivalNonneg : ∀ fuel,
      0 ≤ quittingSoloSemanticSurvival root owner 0 fuel := by
    intro fuel
    exact Math.survivalProduct_nonneg _
      (fun time => ENNReal.toReal_nonneg) 0 fuel
  have hbound : ∀ fuel, |residual fuel| ≤
      quittingSoloSemanticSurvival root owner 0 fuel * (2 * M) := by
    intro fuel
    rw [abs_mul, abs_of_nonneg (hsurvivalNonneg fuel)]
    exact mul_le_mul_of_nonneg_left (htailBound fuel)
      (hsurvivalNonneg fuel)
  have hright : Tendsto (fun fuel =>
      quittingSoloSemanticSurvival root owner 0 fuel * (2 * M))
      atTop (nhds 0) := by
    simpa using hsurvival.mul_const (2 * M)
  have hresidualZero : ∀ fuel, residual fuel =
      (pair 0).1 player - quittingSoloReward reward owner player := by
    intro fuel
    exact (hidentity fuel).symm
  have hconstantBound :
      |(pair 0).1 player - quittingSoloReward reward owner player| ≤ 0 := by
    apply ge_of_tendsto' hright
    intro fuel
    simpa only [hresidualZero fuel] using hbound fuel
  exact sub_eq_zero.mp (abs_eq_zero.mp
    (le_antisymm hconstantBound (abs_nonneg _)))

/-- Equality with the owner's singleton vector propagates one step forward
whenever the owner has positive Continue probability. -/
theorem quittingTerminalSemanticSoloSpine_next_eq_soloReward
    (pair : ℕ → QuittingTerminalSemanticPair ι)
    (root : ℕ → ι → PMF Bool) (owner : ι)
    (hprefix : ∀ time, pair time = quittingTerminalSemanticPrefix reward
      (root time) (pair (time + 1)))
    (hpure : ∀ time player, player ≠ owner →
      root time player = PMF.pure false)
    (time : ℕ)
    (hcurrent : (pair time).1 = quittingSoloReward reward owner)
    (hcontinue : 0 < (root time owner false).toReal) :
    (pair (time + 1)).1 = quittingSoloReward reward owner := by
  funext player
  have hstep := congrFun
    (quittingTerminalSemanticSoloSpine_prescribed_step
      pair root owner hprefix hpure time) player
  rw [hcurrent] at hstep
  have hmass := quittingSoloHazardMass_add (root time owner)
  have hquit : (root time owner true).toReal =
      1 - (root time owner false).toReal := by
    linarith
  rw [hquit] at hstep
  have hmul :
      (root time owner false).toReal * (pair (time + 1)).1 player =
        (root time owner false).toReal *
          quittingSoloReward reward owner player := by
    calc
      _ = quittingSoloReward reward owner player -
          (1 - (root time owner false).toReal) *
            quittingSoloReward reward owner player := by
              linarith only [hstep]
      _ = _ := by ring
  apply (mul_left_cancel₀ (ne_of_gt hcontinue) :
    (root time owner false).toReal * (pair (time + 1)).1 player =
      (root time owner false).toReal *
        quittingSoloReward reward owner player → _)
  exact hmul

/-- A sure-Quit solo-owner root which is exact Nash against an arbitrary
tail is already exact endpoint Nash against the owner's singleton reward.
The arbitrary tail disappears because the owner absorbs at the first row. -/
theorem isZeroSoloEndpointNash_of_soloRoot_continue_eq_zero
    (tail : Payoff ι) (root : ι → PMF Bool) (owner : ι)
    (hnash : IsεQuittingRootNash reward tail 0 root)
    (hpure : ∀ player, player ≠ owner →
      root player = PMF.pure false)
    (hcontinue : (root owner false).toReal = 0) :
    IsεQuittingRootEndpointNash reward
      (quittingSoloReward reward owner) 0 root := by
  have hroot : root = quittingSoloStationaryRoot owner (root owner) :=
    eq_quittingSoloStationaryRoot_of_others_continue hpure
  have hquit : (root owner true).toReal = 1 := by
    linarith [quittingSoloHazardMass_add (root owner)]
  have hendpoint : IsεQuittingRootEndpointNash reward tail 0 root :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward tail root).mpr hnash
  rw [hroot]
  apply isεQuittingRootEndpointNash_soloStationaryRoot
  intro other hother
  have hlocal := (hendpoint other).1
  have hotherContinue : (root other false).toReal = 1 := by
    rw [hpure other hother]
    simp
  rw [hotherContinue, one_mul, quittingRootEndpointDifference, hroot,
    quittingRootQuitPayoff_soloStationaryRoot_other reward hother,
    quittingRootContinuePayoff_soloStationaryRoot_other reward hother,
    hcontinue, hquit] at hlocal
  rw [hcontinue, hquit]
  simpa only [zero_mul, one_mul, zero_add, add_zero, sub_nonpos] using hlocal

/-- Singleton tightness against every displayed successor of a solo semantic
spine extends to time zero by the exact occupation equation. -/
theorem quittingTerminalSemanticSoloSpine_owner_tight_all
    (pair : ℕ → QuittingTerminalSemanticPair ι)
    (root : ℕ → ι → PMF Bool) (owner : ι)
    (hprefix : ∀ time, pair time = quittingTerminalSemanticPrefix reward
      (root time) (pair (time + 1)))
    (hpure : ∀ time player, player ≠ owner →
      root time player = PMF.pure false)
    (htightNext : ∀ time,
      reward (quittingSingletonTerminal owner) owner =
        (pair (time + 1)).1 owner) :
    ∀ time, reward (quittingSingletonTerminal owner) owner =
      (pair time).1 owner := by
  intro time
  cases time with
  | succ time => exact htightNext time
  | zero =>
      have hstep := congrFun
        (quittingTerminalSemanticSoloSpine_prescribed_step
          pair root owner hprefix hpure 0) owner
      have htail : (pair 1).1 owner =
          quittingSoloReward reward owner owner := by
        simpa [quittingSoloReward, quittingSingletonTerminal] using
          (htightNext 0).symm
      rw [htail] at hstep
      have hmass := quittingSoloHazardMass_add (root 0 owner)
      have hcurrent : (pair 0).1 owner =
          quittingSoloReward reward owner owner := by
        have hmass' : (root 0 owner true).toReal +
            (root 0 owner false).toReal = 1 := by linarith
        rw [← add_mul, hmass', one_mul] at hstep
        exact hstep
      simpa [quittingSoloReward, quittingSingletonTerminal] using
        hcurrent.symm

/-- Complete owner absorption plus a positive initial Continue mass turns the
first row of a fixed-owner semantic spine into an atomic solo endpoint
equilibrium. -/
theorem isZeroSoloEndpointNash_of_terminalSemanticSoloSpine_survival_tendsto_zero
    (pair : ℕ → QuittingTerminalSemanticPair ι)
    (root : ℕ → ι → PMF Bool) (owner : ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : ∀ time, pair time ∈ quittingTerminalSemanticCarrier reward)
    (hprefix : ∀ time, pair time = quittingTerminalSemanticPrefix reward
      (root time) (pair (time + 1)))
    (hnash : ∀ time, IsεQuittingRootNash reward
      (pair (time + 1)).1 0 (root time))
    (hpure : ∀ time player, player ≠ owner →
      root time player = PMF.pure false)
    (hcontinue : 0 < (root 0 owner false).toReal)
    (hsurvival : Tendsto
      (quittingSoloSemanticSurvival root owner 0) atTop (nhds 0)) :
    IsεQuittingRootEndpointNash reward
      (quittingSoloReward reward owner) 0 (root 0) := by
  have hzero :=
    quittingTerminalSemanticSoloSpine_initial_eq_soloReward_of_survival_tendsto_zero
      pair root owner hM hreward hpair hprefix hpure hsurvival
  have hone := quittingTerminalSemanticSoloSpine_next_eq_soloReward
    pair root owner hprefix hpure 0 hzero hcontinue
  rw [← hone]
  exact (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
    reward (pair 1).1 (root 0)).mpr (hnash 0)

/-- In a counterexample, complete owner absorption on a fixed-owner semantic
spine can only land in the quantitative isolated-negative atomic branch. -/
theorem QuittingCounterexampleRegime.atomic_restrictions_of_soloSemanticSpine_survival_zero
    (regime : QuittingCounterexampleRegime reward)
    (pair : ℕ → QuittingTerminalSemanticPair ι)
    (root : ℕ → ι → PMF Bool) (owner : ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : ∀ time, pair time ∈ quittingTerminalSemanticCarrier reward)
    (hprefix : ∀ time, pair time = quittingTerminalSemanticPrefix reward
      (root time) (pair (time + 1)))
    (hnash : ∀ time, IsεQuittingRootNash reward
      (pair (time + 1)).1 0 (root time))
    (hpure : ∀ time player, player ≠ owner →
      root time player = PMF.pure false)
    (hquit : 0 < (root 0 owner true).toReal)
    (hcontinue : 0 < (root 0 owner false).toReal)
    (hsurvival : Tendsto
      (quittingSoloSemanticSurvival root owner 0) atTop (nhds 0)) :
    quittingSoloReward reward owner owner ≤ -regime.terminalGap ∧
      quittingSoloReward reward owner owner <
        quittingPunishmentValue reward owner := by
  have hendpoint :=
    isZeroSoloEndpointNash_of_terminalSemanticSoloSpine_survival_tendsto_zero
      pair root owner hM hreward hpair hprefix hnash hpure hcontinue hsurvival
  have hroot : root 0 =
      quittingSoloStationaryRoot owner (root 0 owner) :=
    eq_quittingSoloStationaryRoot_of_others_continue (hpure 0)
  constructor
  · apply regime.soloReward_le_neg_terminalGap_of_soloEndpointNash
      owner (root 0 owner) hquit
    rw [hroot] at hendpoint
    exact hendpoint
  · apply regime.soloReward_lt_punishmentValue_of_soloEndpointNash
      owner (root 0 owner) hquit
    rw [hroot] at hendpoint
    exact hendpoint

/-- **Non-atomic occupation obstruction.**  If the quantitative atomic
restriction fails, a fixed-owner counterexample spine retains a uniformly
positive amount of owner-survival mass.  Moreover its owner-tight finite
reward-moment slice contains a vector other than the owner's singleton reward.
Both conclusions are finite/searchable except for the displayed survival
lower bound. -/
theorem QuittingCounterexampleRegime.nonAtomic_soloSemanticSpine_obstructions
    (regime : QuittingCounterexampleRegime reward)
    (pair : ℕ → QuittingTerminalSemanticPair ι)
    (root : ℕ → ι → PMF Bool) (owner : ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : ∀ time, pair time ∈ quittingTerminalSemanticCarrier reward)
    (hprefix : ∀ time, pair time = quittingTerminalSemanticPrefix reward
      (root time) (pair (time + 1)))
    (hnash : ∀ time, IsεQuittingRootNash reward
      (pair (time + 1)).1 0 (root time))
    (hpure : ∀ time player, player ≠ owner →
      root time player = PMF.pure false)
    (htight : ∀ time,
      reward (quittingSingletonTerminal owner) owner =
        (pair time).1 owner)
    (hquit : 0 < (root 0 owner true).toReal)
    (hcontinue : 0 < (root 0 owner false).toReal)
    (hnotAtomic : ¬
      (quittingSoloReward reward owner owner ≤ -regime.terminalGap ∧
        quittingSoloReward reward owner owner <
          quittingPunishmentValue reward owner)) :
    (∃ lower, 0 < lower ∧ ∀ fuel,
        lower ≤ quittingSoloSemanticSurvival root owner 0 fuel) ∧
      ∃ value ∈ quittingTerminalRewardMomentSet reward,
        value owner = quittingSoloReward reward owner owner ∧
          value ≠ quittingSoloReward reward owner := by
  have hsurvival : ¬ Tendsto
      (quittingSoloSemanticSurvival root owner 0) atTop (nhds 0) := by
    intro htendsto
    exact hnotAtomic
      (regime.atomic_restrictions_of_soloSemanticSpine_survival_zero
        pair root owner hM hreward hpair hprefix hnash hpure
          hquit hcontinue htendsto)
  have hnotEndpoint : ¬ IsεQuittingRootEndpointNash reward
      (quittingSoloReward reward owner) 0 (root 0) := by
    intro hendpoint
    have hroot : root 0 =
        quittingSoloStationaryRoot owner (root 0 owner) :=
      eq_quittingSoloStationaryRoot_of_others_continue (hpure 0)
    have hendpointSolo : IsεQuittingRootEndpointNash reward
        (quittingSoloReward reward owner) 0
        (quittingSoloStationaryRoot owner (root 0 owner)) := by
      rw [← hroot]
      exact hendpoint
    apply hnotAtomic
    exact
      ⟨regime.soloReward_le_neg_terminalGap_of_soloEndpointNash
          owner (root 0 owner) hquit hendpointSolo,
        regime.soloReward_lt_punishmentValue_of_soloEndpointNash
          owner (root 0 owner) hquit hendpointSolo⟩
  refine
    ⟨exists_pos_le_quittingSoloSemanticSurvival_of_not_tendsto_zero
        root owner 0 hsurvival, (pair 1).1, ?_, ?_, ?_⟩
  · exact quittingTerminalSemanticCarrier_prescribed_mem_rewardMomentSet
      reward (pair 1) (hpair 1)
  · exact (htight 1).symm.trans (by rfl)
  · intro heq
    apply hnotEndpoint
    rw [← heq]
    exact (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward (pair 1).1 (root 0)).mpr (hnash 0)
/-- Every owner-tight state of a semantic spine lies in the corresponding
finite reward-moment slice. -/
theorem quittingTerminalSemanticSpine_prescribed_mem_ownerMomentSlice
    (pair : ℕ → QuittingTerminalSemanticPair ι) (owner : ι)
    (hpair : ∀ time, pair time ∈ quittingTerminalSemanticCarrier reward)
    (htight : ∀ time,
      reward (quittingSingletonTerminal owner) owner =
        (pair time).1 owner)
    (time : ℕ) :
    (pair time).1 ∈ quittingTerminalRewardMomentSet reward ∧
      (pair time).1 owner = quittingSoloReward reward owner owner := by
  exact ⟨quittingTerminalSemanticCarrier_prescribed_mem_rewardMomentSet
      reward (pair time) (hpair time),
    (htight time).symm.trans (by rfl)⟩

/-- If a fixed-owner spine has not already closed to an atomic endpoint at
its first row, the owner-tight reward-moment slice is nontrivial.  This is a
finite linear feasibility obstruction on the reward table. -/
theorem exists_nontrivial_ownerMomentSlice_of_soloSemanticSpine
    (pair : ℕ → QuittingTerminalSemanticPair ι)
    (root : ℕ → ι → PMF Bool) (owner : ι)
    (hpair : ∀ time, pair time ∈ quittingTerminalSemanticCarrier reward)
    (hnash : ∀ time, IsεQuittingRootNash reward
      (pair (time + 1)).1 0 (root time))
    (htight : ∀ time,
      reward (quittingSingletonTerminal owner) owner =
        (pair time).1 owner)
    (hnotAtomic : ¬ IsεQuittingRootEndpointNash reward
      (quittingSoloReward reward owner) 0 (root 0)) :
    ∃ value ∈ quittingTerminalRewardMomentSet reward,
      value owner = quittingSoloReward reward owner owner ∧
        value ≠ quittingSoloReward reward owner := by
  refine ⟨(pair 1).1,
    quittingTerminalSemanticCarrier_prescribed_mem_rewardMomentSet
      reward (pair 1) (hpair 1), ?_, ?_⟩
  · exact (htight 1).symm.trans (by rfl)
  · intro heq
    apply hnotAtomic
    rw [← heq]
    exact (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward (pair 1).1 (root 0)).mpr (hnash 0)

/-- A fixed-owner solo spine whose own survival stays uniformly positive
forces an all-Continue exact-Nash cluster point in the same minimum semantic
fiber.  Positive survival makes the stagewise owner hazards vanish; compactness
then passes root Nash to the all-Continue limit. -/
theorem exists_minimum_allContinueNash_of_soloSemanticSpine_survival_lower
    (pair : ℕ → QuittingTerminalSemanticPair ι)
    (root : ℕ → ι → PMF Bool) (owner : ι)
    {M lower : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : ∀ time, pair time ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ time candidate,
      candidate ∈ quittingTerminalSemanticCarrier reward →
      quittingTerminalSemanticDebtSum (pair time) ≤
        quittingTerminalSemanticDebtSum candidate)
    (hnash : ∀ time, IsεQuittingRootNash reward
      (pair (time + 1)).1 0 (root time))
    (hpure : ∀ time player, player ≠ owner →
      root time player = PMF.pure false)
    (hlower : 0 < lower)
    (hsurvivalLower : ∀ fuel, lower ≤
      quittingSoloSemanticSurvival root owner 0 fuel) :
    ∃ candidate : QuittingTerminalSemanticPair ι,
      candidate ∈ quittingTerminalSemanticCarrier reward ∧
      (∀ other ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum candidate ≤
          quittingTerminalSemanticDebtSum other) ∧
      IsεQuittingRootNash reward candidate.1 0
        (quittingAllContinueRoot : ι → PMF Bool) := by
  let hazard : ℕ → PMF Bool := fun time => root time owner
  have hsurvivalEq : ∀ fuel,
      quittingSoloSemanticSurvival root owner 0 fuel =
        quittingHazardSurvival hazard fuel := by
    intro fuel
    rfl
  have hquitTendsto : Tendsto (fun time => (root time owner true).toReal)
      atTop (nhds 0) := by
    have hstop := tendsto_quittingHazardStopMass_zero hazard
    have hmajor : ∀ time, (root time owner true).toReal ≤
        quittingHazardStopMass hazard time / lower := by
      intro time
      apply (le_div_iff₀ hlower).2
      rw [quittingHazardStopMass_eq_survival_mul_stop]
      have hmul := mul_le_mul_of_nonneg_right
        (show lower ≤ quittingHazardSurvival hazard time by
          rw [← hsurvivalEq]
          exact hsurvivalLower time)
        (show 0 ≤ (root time owner true).toReal by
          exact ENNReal.toReal_nonneg)
      simpa only [hazard, mul_comm] using hmul
    apply squeeze_zero
    · exact fun _ => ENNReal.toReal_nonneg
    · exact hmajor
    · simpa using hstop.div_const lower
  let simplexRoot : ℕ → QuittingRootSimplex ι :=
    fun time player => stdSimplexEquiv (root time player)
  have hsimplexRoot : Tendsto simplexRoot atTop
      (nhds (quittingAllContinueSimplexRoot : QuittingRootSimplex ι)) := by
    rw [tendsto_pi_nhds]
    intro player
    rw [tendsto_subtype_rng, tendsto_pi_nhds]
    intro action
    have hcoordinate : ∀ time,
        ((simplexRoot time player : stdSimplex ℝ Bool) : Bool → ℝ) action =
          (root time player action).toReal := by
      intro time
      exact congrFun (coe_stdSimplexEquiv_apply (root time player)) action
    have hallCoordinate :
        (((quittingAllContinueSimplexRoot : QuittingRootSimplex ι) player :
          stdSimplex ℝ Bool) : Bool → ℝ) action =
            (PMF.pure false action).toReal := by
      exact congrFun (coe_stdSimplexEquiv_apply (PMF.pure false)) action
    have hbase : Tendsto (fun time => (root time player action).toReal)
        atTop (nhds ((PMF.pure false action).toReal)) := by
      by_cases hplayer : player = owner
      · subst player
        cases action with
        | false =>
            have hcontinue : Tendsto
                (fun time => (root time owner false).toReal)
                atTop (nhds 1) := by
              have hmass : (fun time => (root time owner false).toReal) =
                  fun time => 1 - (root time owner true).toReal := by
                funext time
                linarith [quittingSoloHazardMass_add (root time owner)]
              rw [hmass]
              simpa using tendsto_const_nhds.sub hquitTendsto
            simpa using hcontinue
        | true =>
            simpa using hquitTendsto
      · simp only [hpure _ player hplayer]
        exact tendsto_const_nhds
    have hactual := hbase.congr'
      (Filter.Eventually.of_forall fun time => (hcoordinate time).symm)
    convert hactual using 1
    · rfl
    · exact congrArg nhds hallCoordinate
  obtain ⟨candidate, hcandidate, subsequence, hsubsequence,
      hcandidateLimit⟩ :=
    (quittingTerminalSemanticCarrier_isCompact reward hM hreward).tendsto_subseq
      (fun time => hpair (time + 1))
  have htailLimit : Tendsto
      (fun rank => (pair (subsequence rank + 1)).1) atTop
      (nhds candidate.1) := by
    exact continuous_fst.continuousAt.tendsto.comp hcandidateLimit
  have hrootLimit : Tendsto (fun rank => simplexRoot (subsequence rank))
      atTop
      (nhds (quittingAllContinueSimplexRoot : QuittingRootSimplex ι)) :=
    hsimplexRoot.comp hsubsequence.tendsto_atTop
  have hnashLimit : IsεQuittingRootEndpointNash reward candidate.1 0
      (quittingRootOfSimplex
        (quittingAllContinueSimplexRoot : QuittingRootSimplex ι)) := by
    apply isεQuittingRootEndpointNash_of_tendsto reward
      (fun _ : ℕ => 0)
      (fun rank => (pair (subsequence rank + 1)).1)
      (fun rank => simplexRoot (subsequence rank))
      tendsto_const_nhds htailLimit hrootLimit
    filter_upwards [] with rank
    have hlocal := (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward (pair (subsequence rank + 1)).1
        (root (subsequence rank))).mpr (hnash (subsequence rank))
    have hrootEq : quittingRootOfSimplex (simplexRoot (subsequence rank)) =
        root (subsequence rank) := by
      funext player
      exact (stdSimplexEquiv (α := Bool)).symm_apply_apply
        (root (subsequence rank) player)
    rwa [hrootEq]
  refine ⟨candidate, hcandidate, ?_, ?_⟩
  · intro other hother
    have hdebtLimit : Tendsto
        (fun rank => quittingTerminalSemanticDebtSum
          (pair (subsequence rank + 1))) atTop
        (nhds (quittingTerminalSemanticDebtSum candidate)) :=
      continuous_quittingTerminalSemanticDebtSum.continuousAt.tendsto.comp
        hcandidateLimit
    exact le_of_tendsto' hdebtLimit fun rank =>
      hminimum (subsequence rank + 1) other hother
  · rw [quittingRootOfSimplex_allContinueSimplexRoot] at hnashLimit
    exact (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward candidate.1 quittingAllContinueRoot).mp hnashLimit

/-! ## Global counterexample reduction -/

/-- The all-Continue branch of the positive minimum semantic stratum. -/
def HasPositiveMinimumTerminalSemanticPlateau
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∃ pair : QuittingTerminalSemanticPair ι,
    pair ∈ quittingTerminalSemanticCarrier reward ∧
    (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate) ∧
    (∃ who, 0 < quittingTerminalSemanticDebt pair who) ∧
    IsεQuittingRootNash reward pair.1 0
      (quittingAllContinueRoot : ι → PMF Bool) ∧
    quittingTerminalSemanticPrefix reward quittingAllContinueRoot pair = pair

/-- A positive-rate atomic solo endpoint together with its quantitative
isolated-negative and punishment obstructions. -/
def HasAtomicIsolatedNegativeSoloRow
    (regime : QuittingCounterexampleRegime reward) : Prop :=
  ∃ (owner : ι) (hazard : PMF Bool),
    0 < (hazard true).toReal ∧
    IsεQuittingRootEndpointNash reward (quittingSoloReward reward owner) 0
      (quittingSoloStationaryRoot owner hazard) ∧
    HasIsolatedNegativeAbsorbingQuittingCycle reward ∧
    quittingSoloReward reward owner owner ≤ -regime.terminalGap ∧
    quittingSoloReward reward owner owner <
      quittingPunishmentValue reward owner

/-- The genuinely non-atomic fixed-owner branch.  It retains the complete
minimum-semantic chronology, has a uniformly positive owner-survival tail,
and exposes a second point in the finite owner-tight reward-moment slice. -/
def HasPositiveSurvivalNontrivialMomentSoloSemanticSpine
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∃ (pair : ℕ → QuittingTerminalSemanticPair ι)
      (root : ℕ → ι → PMF Bool) (owner : ι) (debt lower : ℝ)
      (moment : Payoff ι),
    0 < debt ∧
    (∀ time, pair time ∈ quittingTerminalSemanticCarrier reward) ∧
    (∀ time candidate,
      candidate ∈ quittingTerminalSemanticCarrier reward →
      quittingTerminalSemanticDebtSum (pair time) ≤
        quittingTerminalSemanticDebtSum candidate) ∧
    (∀ time, pair time = quittingTerminalSemanticPrefix reward
      (root time) (pair (time + 1))) ∧
    (∀ time, IsεQuittingRootNash reward (pair (time + 1)).1 0
      (root time)) ∧
    (∀ time, ¬ IsεQuittingRootNash reward (pair time).1 0
      (quittingAllContinueRoot : ι → PMF Bool)) ∧
    (¬ ∃ candidate : QuittingTerminalSemanticPair ι,
      candidate ∈ quittingTerminalSemanticCarrier reward ∧
      (∀ other ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum candidate ≤
          quittingTerminalSemanticDebtSum other) ∧
      IsεQuittingRootNash reward candidate.1 0
        (quittingAllContinueRoot : ι → PMF Bool)) ∧
    (∀ time, quittingTerminalSemanticDebt (pair time) owner = debt) ∧
    (∀ time player, player ≠ owner →
      quittingTerminalSemanticDebt (pair time) player = 0) ∧
    (∀ time, 0 < (root time owner true).toReal) ∧
    (∀ time player, player ≠ owner →
      root time player = PMF.pure false) ∧
    (∀ time, root time =
      quittingSoloStationaryRoot owner (root time owner)) ∧
    (∀ start fuel,
      quittingOpponentSurvivalWeight root owner start fuel = 1) ∧
    (∀ time, reward (quittingSingletonTerminal owner) owner =
      (pair (time + 1)).1 owner) ∧
    (∀ time, ∃ blocker, blocker ≠ owner ∧
      (pair (time + 1)).1 blocker <
        reward (quittingSingletonTerminal blocker) blocker ∧
      quittingRootQuitPayoff reward (pair (time + 1)).1
          (root time) blocker ≤
        quittingRootContinuePayoff reward (pair (time + 1)).1
          (root time) blocker) ∧
    ¬ IsεQuittingRootEndpointNash reward
      (quittingSoloReward reward owner) 0 (root 0) ∧
    0 < lower ∧
    (∀ fuel, lower ≤
      quittingSoloSemanticSurvival root owner 0 fuel) ∧
    moment ∈ quittingTerminalRewardMomentSet reward ∧
    moment owner = quittingSoloReward reward owner owner ∧
    moment ≠ quittingSoloReward reward owner

/-- **Global minimum-semantic counterexample reduction.**  If a finite
quitting game has no uniform-equilibrium payoff, then exactly the following
search regime remains (the alternatives need not be logically disjoint):

1. a positive-debt all-Continue minimum semantic plateau;
2. a positive-rate atomic solo endpoint in the quantitative
   isolated-negative branch; or
3. a non-atomic fixed-owner minimum semantic spine with positive phantom
   survival and a nontrivial owner-tight finite reward-moment slice.

A pure-Quit first solo row is absorbed by branch 2: its arbitrary declared
tail disappears from every endpoint comparison. -/
theorem exists_semanticPlateau_or_atomicSolo_or_positiveSurvivalSpine_of_noUE
    [Nonempty ι]
    (regime : QuittingCounterexampleRegime reward)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    HasPositiveMinimumTerminalSemanticPlateau reward ∨
      HasAtomicIsolatedNegativeSoloRow regime ∨
      HasPositiveSurvivalNontrivialMomentSoloSemanticSpine reward := by
  rcases
      exists_positiveMinimumPlateau_or_fixedOwnerSoloSemanticSpine_of_no_uniformPayoff
        reward hM hreward regime.not_exists_uniformEquilibriumPayoff with
    hplateau | ⟨pair, root, owner, debt, hdebt, hpair, hminimum,
      hprefix, hnash, hnoPlateau, hnoMinimumPlateau, hownerDebt, hotherDebt, hquit,
      hpure, hrootSolo, hopponentSurvival, htightNext, hblocker⟩
  · exact Or.inl hplateau
  · right
    have htight : ∀ time,
        reward (quittingSingletonTerminal owner) owner =
          (pair time).1 owner :=
      quittingTerminalSemanticSoloSpine_owner_tight_all
        pair root owner hprefix hpure htightNext
    by_cases hendpoint : IsεQuittingRootEndpointNash reward
        (quittingSoloReward reward owner) 0 (root 0)
    · left
      let hazard := root 0 owner
      have hendpointSolo : IsεQuittingRootEndpointNash reward
          (quittingSoloReward reward owner) 0
          (quittingSoloStationaryRoot owner hazard) := by
        rw [← hrootSolo 0]
        exact hendpoint
      have hisolated :=
        exists_isolatedNegativeCycle_and_soloReward_le_neg_terminalGap
          regime owner hazard (hquit 0) hendpointSolo
      exact ⟨owner, hazard, hquit 0, hendpointSolo, hisolated.1,
        hisolated.2,
        regime.soloReward_lt_punishmentValue_of_soloEndpointNash
          owner hazard (hquit 0) hendpointSolo⟩
    · right
      have hcontinue : 0 < (root 0 owner false).toReal := by
        by_contra hnot
        have hzero : (root 0 owner false).toReal = 0 :=
          le_antisymm (le_of_not_gt hnot) ENNReal.toReal_nonneg
        exact hendpoint
          (isZeroSoloEndpointNash_of_soloRoot_continue_eq_zero
            (pair 1).1 (root 0) owner (hnash 0) (hpure 0) hzero)
      have hsurvivalNot : ¬ Tendsto
          (quittingSoloSemanticSurvival root owner 0) atTop (nhds 0) := by
        intro hsurvival
        exact hendpoint
          (isZeroSoloEndpointNash_of_terminalSemanticSoloSpine_survival_tendsto_zero
            pair root owner hM hreward hpair hprefix hnash hpure
              hcontinue hsurvival)
      obtain ⟨lower, hlower, hsurvivalLower⟩ :=
        exists_pos_le_quittingSoloSemanticSurvival_of_not_tendsto_zero
          root owner 0 hsurvivalNot
      obtain ⟨moment, hmoment, hmomentOwner, hmomentNe⟩ :=
        exists_nontrivial_ownerMomentSlice_of_soloSemanticSpine
          pair root owner hpair hnash htight hendpoint
      exact ⟨pair, root, owner, debt, lower, moment, hdebt, hpair,
        hminimum, hprefix, hnash, hnoPlateau, hnoMinimumPlateau,
        hownerDebt, hotherDebt,
        hquit, hpure, hrootSolo, hopponentSurvival, htightNext, hblocker,
        hendpoint, hlower, hsurvivalLower, hmoment, hmomentOwner, hmomentNe⟩

/-- **Two-branch global reduction.**  The apparent positive-survival
non-atomic branch of the preceding theorem is inconsistent.  Its survival
lower bound forces the owner hazards to vanish, so compactness produces an
all-Continue exact-Nash point in the minimum semantic fiber, contradicting
the branch's global no-plateau certificate.  Therefore every counterexample
already contains either a positive minimum all-Continue plateau or a
quantitative isolated-negative atomic solo row. -/
theorem exists_semanticPlateau_or_atomicSolo_of_noUE
    [Nonempty ι]
    (regime : QuittingCounterexampleRegime reward)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    HasPositiveMinimumTerminalSemanticPlateau reward ∨
      HasAtomicIsolatedNegativeSoloRow regime := by
  rcases exists_semanticPlateau_or_atomicSolo_or_positiveSurvivalSpine_of_noUE
      regime hM hreward with hplateau | hatomic | hspine
  · exact Or.inl hplateau
  · exact Or.inr hatomic
  · rcases hspine with
      ⟨pair, root, owner, debt, lower, moment, hdebt, hpair, hminimum,
        hprefix, hnash, hnoPlateau, hnoMinimumPlateau, hownerDebt,
        hotherDebt, hquit, hpure, hrootSolo, hopponentSurvival,
        htightNext, hblocker, hnotEndpoint, hlower, hsurvivalLower,
        hmoment, hmomentOwner, hmomentNe⟩
    obtain ⟨candidate, hcandidate, hcandidateMin, hnashAll⟩ :=
      exists_minimum_allContinueNash_of_soloSemanticSpine_survival_lower
        pair root owner hM hreward hpair hminimum hnash hpure
          hlower hsurvivalLower
    exact False.elim
      (hnoMinimumPlateau
        ⟨candidate, hcandidate, hcandidateMin, hnashAll⟩)

end GameTheory
