/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingMarkedFenceFirstOpponentAdapter

/-!
# Concrete suffix transfers from marked first-opponent packets

This file turns the quantitative first-opponent packet dichotomy into an
actual supported mark.  In the new-negative branch, the selected player has
strictly positive Quit probability at the displayed root, and the displayed
date is a genuine suffix of the same fixed-cutoff exact Nash--Bellman chain.

No predecessor or equilibrium selection is introduced here.  All statements
accept an arbitrary supplied finite chain; in particular, they can later be
specialized to anchored minimum-debt chains without changing the transfer
relation.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.ProbabilityMassFunction
  Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace QuittingMarkedFencePacket

/-- Positive mass of a predicate under nonnegative finite weights contains a
concrete positive-weight atom satisfying that predicate. -/
theorem exists_pos_weight_of_packetMass_pos
    {Ω : Type*} [Fintype Ω]
    (weight : Ω → ℝ) (P : Ω → Prop)
    (hweight : ∀ ω, 0 ≤ weight ω)
    (hmass : 0 < packetMass weight P) :
    ∃ ω, P ω ∧ 0 < weight ω := by
  classical
  unfold packetMass at hmass
  obtain ⟨ω, _hω, hωpos⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun candidate _ ↦ by
      by_cases hP : P candidate <;> simp [hP, hweight candidate])).mp hmass
  by_cases hP : P ω
  · exact ⟨ω, hP, by simpa [hP] using hωpos⟩
  · simp [hP] at hωpos

end QuittingMarkedFencePacket

/-- A positive raw first-opponent atom gives every displayed opponent
quitter strictly positive Quit probability in the actual root marginal. -/
theorem quittingFirstOpponent_quitProbability_pos_of_rawWeight_pos
    (roots : ℕ → ι → PMF Bool) (owner : ι) (start fuel : ℕ)
    (mark : QuittingFirstOpponentMark ι fuel) (j : ι)
    (hraw : 0 < quittingFirstOpponentRawWeight roots owner start fuel mark)
    (hj : j ∈ quittingFirstOpponentQuitters owner mark) :
    0 < (roots (start + mark.1) j true).toReal := by
  let distribution := pmfPi
    (Function.update (roots (start + mark.1)) owner (PMF.pure false))
  have hflag : quittingOpponentQuitFlag owner mark.2 = true := by
    by_contra hnot
    have hraw' := hraw
    unfold quittingFirstOpponentRawWeight at hraw'
    rw [if_neg hnot] at hraw'
    simp at hraw'
  have hsurvival0 : 0 ≤
      quittingOpponentSurvivalWeight roots owner start mark.1 :=
    quittingOpponentSurvivalWeight_nonneg roots owner start mark.1
  have hjoint0 : 0 ≤ (distribution mark.2).toReal := ENNReal.toReal_nonneg
  have hjoint : 0 < (distribution mark.2).toReal := by
    unfold quittingFirstOpponentRawWeight at hraw
    rw [if_pos hflag] at hraw
    change 0 < quittingOpponentSurvivalWeight roots owner start mark.1 *
      (distribution mark.2).toReal at hraw
    nlinarith
  have hjoint_ne : distribution mark.2 ≠ 0 := by
    intro hzero
    rw [hzero, ENNReal.toReal_zero] at hjoint
    exact (lt_irrefl 0 hjoint)
  have hsupport : mark.2 ∈ distribution.support :=
    (PMF.mem_support_iff distribution mark.2).2 hjoint_ne
  have hcoordinate : mark.2 j ∈
      (pushforward distribution (fun action ↦ action j)).support := by
    rw [pushforward, PMF.mem_support_map_iff]
    exact ⟨mark.2, hsupport, rfl⟩
  have hcoordinate' : mark.2 j ∈
      (Function.update (roots (start + mark.1)) owner
        (PMF.pure false) j).support := by
    change mark.2 j ∈
      (pushforward
        (pmfPi (Function.update (roots (start + mark.1)) owner
          (PMF.pure false))) (fun action ↦ action j)).support at hcoordinate
    rw [pmfPi_push_coord] at hcoordinate
    exact hcoordinate
  have hj_ne : j ≠ owner := (Finset.mem_erase.mp hj).1
  have hj_true : mark.2 j = true := by
    exact (Finset.mem_filter.mp (Finset.mem_erase.mp hj).2).2
  have hrootSupport : true ∈ (roots (start + mark.1) j).support := by
    simpa [hj_true, Function.update_of_ne hj_ne] using hcoordinate'
  have hroot_ne : roots (start + mark.1) j true ≠ 0 :=
    (PMF.mem_support_iff (roots (start + mark.1) j) true).1 hrootSupport
  exact ENNReal.toReal_pos hroot_ne (PMF.apply_ne_top _ _)

/-! ## Re-rooting a fixed-cutoff exact chain -/

/-- Every suffix of a fixed-cutoff exact Nash--Bellman chain satisfies the
same local zero-boundary interface, with remaining fuel `cutoff - start`. -/
theorem finiteExactQuittingNashBellmanChain_rebase
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (cutoff start : ℕ)
    (hstart : start ≤ cutoff)
    (hterminal : value cutoff = 0)
    (hpolicy : ∀ time, time < cutoff →
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time))
    (hnash : ∀ time, time < cutoff →
      IsεQuittingRootNash reward (value (time + 1)) 0 (roots time)) :
    value (start + (cutoff - start)) = 0 ∧
      (∀ offset, offset < cutoff - start →
        value (start + offset) =
          quittingRootSuccessorPayoff reward
            (value (start + offset + 1)) (roots (start + offset))) ∧
      ∀ offset, offset < cutoff - start →
        IsεQuittingRootNash reward (value (start + offset + 1)) 0
          (roots (start + offset)) := by
  have hend : start + (cutoff - start) = cutoff := Nat.add_sub_of_le hstart
  refine ⟨by simpa [hend] using hterminal, ?_, ?_⟩
  · intro offset hoffset
    exact hpolicy (start + offset) (by omega)
  · intro offset hoffset
    exact hnash (start + offset) (by omega)

/-! ## Extracting an actual one-step successor -/

/-- A negative suffix of an arbitrary bounded exact finite chain contains
either a concrete positive-weight good boundary mark, or a concrete
positive-weight new-negative opponent.  In the latter case that opponent is
genuinely active at the displayed root.

The conclusion intentionally retains the full marked action and its raw
weight.  It neither singletonizes simultaneous quitters nor chooses a new
Nash--Bellman predecessor. -/
theorem exists_goodBoundary_or_activeNegativeTransfer_of_finiteExactChain
    [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (owner : ι) (cutoff start : ℕ) (θ M : ℝ)
    (hstart : start ≤ cutoff)
    (hterminal : value cutoff = 0)
    (hpolicy : ∀ time, time < cutoff →
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time))
    (hnash : ∀ time, time < cutoff →
      IsεQuittingRootNash reward (value (time + 1)) 0 (roots time))
    (hθ : 0 < θ) (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hnegative : value start owner ≤ -θ) :
    (∃ mark : QuittingFirstOpponentMark ι (cutoff - start),
      0 < quittingFirstOpponentRawWeight roots owner start
          (cutoff - start) mark ∧
        QuittingMarkedFencePacket.IsGoodBoundary θ
          (quittingFirstOpponentOwnerReward reward owner)
          (quittingFirstOpponentQuitters owner)
          (quittingFirstOpponentValue value start) mark) ∨
      ∃ (j : ι) (mark : QuittingFirstOpponentMark ι (cutoff - start)),
        j ≠ owner ∧
        0 < quittingFirstOpponentRawWeight roots owner start
          (cutoff - start) mark ∧
        QuittingMarkedFencePacket.IsNewNegativeOwner θ
          (quittingFirstOpponentOwnerReward reward owner)
          (quittingFirstOpponentQuitters owner)
          (quittingFirstOpponentValue value start) j mark ∧
        0 < (roots (start + mark.1) j true).toReal := by
  classical
  obtain ⟨hlocalTerminal, hlocalPolicy, hlocalNash⟩ :=
    finiteExactQuittingNashBellmanChain_rebase reward roots value cutoff start
      hstart hterminal hpolicy hnash
  have hnever :=
    quittingFirstOpponentRawMean_le_value_of_finiteExactChain
      reward roots value owner start (cutoff - start)
        hlocalTerminal hlocalPolicy hlocalNash
  have hfenceMass := quittingFirstOpponentMass_pos reward roots value owner
    start (cutoff - start) θ M hθ hM hreward hnever hnegative
  have hdichotomy :=
    quittingFiniteExactChain_firstOpponent_markedFenceDichotomy
      reward roots value owner start (cutoff - start) θ M
        hlocalTerminal hlocalPolicy hlocalNash hθ hM hreward hnegative
  rcases hdichotomy with hgood | hbad
  · left
    let weight := quittingFirstOpponentWeight roots owner start
      (cutoff - start)
    let good : QuittingFirstOpponentMark ι (cutoff - start) → Prop :=
      QuittingMarkedFencePacket.IsGoodBoundary θ
      (quittingFirstOpponentOwnerReward reward owner)
      (quittingFirstOpponentQuitters owner)
      (quittingFirstOpponentValue value start)
    have hpacket0 : 0 ≤ QuittingMarkedFencePacket.packetMass weight good := by
      unfold QuittingMarkedFencePacket.packetMass
      exact Finset.sum_nonneg fun mark _ ↦ by
        by_cases hmark : good mark <;>
          simp [hmark, weight,
            quittingFirstOpponentWeight_nonneg roots owner start
              (cutoff - start) hfenceMass mark]
    have hpacketPos :
        0 < QuittingMarkedFencePacket.packetMass weight good := by
      have hscale0 : 0 ≤ 4 * M := mul_nonneg (by norm_num) hM
      by_contra hnot
      have hpacketNonpos := le_of_not_gt hnot
      have hproductNonpos :=
        mul_nonpos_of_nonneg_of_nonpos hscale0 hpacketNonpos
      linarith
    obtain ⟨mark, hmarkGood, hmarkWeight⟩ :=
      QuittingMarkedFencePacket.exists_pos_weight_of_packetMass_pos
        weight good
        (quittingFirstOpponentWeight_nonneg roots owner start
          (cutoff - start) hfenceMass) hpacketPos
    refine ⟨mark, ?_, hmarkGood⟩
    rcases (div_pos_iff.mp hmarkWeight) with hpositive | hnegative
    · exact hpositive.1
    · exact (not_lt_of_ge hfenceMass.le hnegative.2).elim
  · right
    obtain ⟨j, hjowner, hjmass⟩ := hbad
    let weight := quittingFirstOpponentWeight roots owner start
      (cutoff - start)
    let bad : QuittingFirstOpponentMark ι (cutoff - start) → Prop :=
      QuittingMarkedFencePacket.IsNewNegativeOwner θ
      (quittingFirstOpponentOwnerReward reward owner)
      (quittingFirstOpponentQuitters owner)
      (quittingFirstOpponentValue value start) j
    have hpacket0 : 0 ≤ QuittingMarkedFencePacket.packetMass weight bad := by
      unfold QuittingMarkedFencePacket.packetMass
      exact Finset.sum_nonneg fun mark _ ↦ by
        by_cases hmark : bad mark <;>
          simp [hmark, weight,
            quittingFirstOpponentWeight_nonneg roots owner start
              (cutoff - start) hfenceMass mark]
    have hpacketPos :
        0 < QuittingMarkedFencePacket.packetMass weight bad := by
      have hcard0 : 0 ≤
          ((Finset.univ.erase owner : Finset ι).card : ℝ) := by positivity
      have hscale0 :
          0 ≤ 4 * M * ((Finset.univ.erase owner : Finset ι).card : ℝ) :=
        mul_nonneg (mul_nonneg (by norm_num) hM) hcard0
      by_contra hnot
      have hpacketNonpos := le_of_not_gt hnot
      have hproductNonpos :=
        mul_nonpos_of_nonneg_of_nonpos hscale0 hpacketNonpos
      linarith
    obtain ⟨mark, hmarkBad, hmarkWeight⟩ :=
      QuittingMarkedFencePacket.exists_pos_weight_of_packetMass_pos
        weight bad
        (quittingFirstOpponentWeight_nonneg roots owner start
          (cutoff - start) hfenceMass) hpacketPos
    have hraw : 0 < quittingFirstOpponentRawWeight roots owner start
        (cutoff - start) mark := by
      rcases (div_pos_iff.mp hmarkWeight) with hpositive | hnegative
      · exact hpositive.1
      · exact (not_lt_of_ge hfenceMass.le hnegative.2).elim
    have hjne : j ≠ owner := by simpa using (Finset.mem_erase.mp hjowner).1
    refine ⟨j, mark, hjne, hraw, hmarkBad, ?_⟩
    exact quittingFirstOpponent_quitProbability_pos_of_rawWeight_pos
      roots owner start (cutoff - start) mark j hraw hmarkBad.2.1

end GameTheory
