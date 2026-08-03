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

/-- Under exact root Nash, every player who quits with positive probability
receives exactly the prescribed root payoff from the pure-Quit endpoint.
This includes the sure-Quit endpoint; no positive Continue probability is
required. -/
theorem quittingRootQuitPayoff_eq_successor_of_quitProbability_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hnash : IsεQuittingRootNash reward tail 0 root)
    (hquit : 0 < (root who true).toReal) :
    quittingRootQuitPayoff reward tail root who =
      quittingRootSuccessorPayoff reward tail root who := by
  have hendpoint :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward tail root).2 hnash
  have hdifference0 : 0 ≤
      quittingRootEndpointDifference reward tail root who := by
    exact nonneg_of_mul_nonneg_left
      (by simpa [mul_comm] using (hendpoint who).2) hquit
  have hcontinue0 : 0 ≤ (root who false).toReal := ENNReal.toReal_nonneg
  have hproduct0 : (root who false).toReal *
      quittingRootEndpointDifference reward tail root who = 0 := by
    apply le_antisymm
    · simpa using (hendpoint who).1
    · exact mul_nonneg hcontinue0 hdifference0
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  have hquitProbability : (root who true).toReal =
      1 - (root who false).toReal := by linarith
  have hgap :
      quittingRootQuitPayoff reward tail root who -
          quittingRootSuccessorPayoff reward tail root who =
        (root who false).toReal *
          quittingRootEndpointDifference reward tail root who := by
    rw [quittingRootSuccessorPayoff_eq_endpointMix, hquitProbability]
    unfold quittingRootEndpointDifference
    ring
  rw [hproduct0] at hgap
  exact sub_eq_zero.mp hgap

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

/-! ## Finite player-flag iteration -/

omit [DecidableEq ι] in
/-- Abstract finite-label walk lemma.  If every nongood state has a next
state, then within `card ι` transitions the walk either sees a good state or
repeats a label.  The constructed walk is proof-local; this theorem does not
install a global successor selector. -/
theorem exists_finiteLabelWalk_good_or_repeat
    {State : Type*} (label : State → ι)
    (Good : State → Prop) (Next : State → State → Prop)
    (hstep : ∀ state, Good state ∨ ∃ next, Next state next)
    (initial : State) :
    ∃ walk : ℕ → State,
      walk 0 = initial ∧
      (∀ n, n < Fintype.card ι → ¬Good (walk n) →
        Next (walk n) (walk (n + 1))) ∧
      ((∃ n, n ≤ Fintype.card ι ∧ Good (walk n)) ∨
        (∀ n, n ≤ Fintype.card ι → ¬Good (walk n)) ∧
          ∃ m n, m ≤ Fintype.card ι ∧ n ≤ Fintype.card ι ∧
            m ≠ n ∧ label (walk m) = label (walk n)) := by
  classical
  have hnext (state : State) (hnotGood : ¬Good state) :
      ∃ next, Next state next := by
    rcases hstep state with hgood | hnext
    · exact (hnotGood hgood).elim
    · exact hnext
  let advance : State → State := fun state ↦
    if hgood : Good state then state else Classical.choose (hnext state hgood)
  have hadvance (state : State) (hnotGood : ¬Good state) :
      Next state (advance state) := by
    simp only [advance, dif_neg hnotGood]
    exact Classical.choose_spec (hnext state hnotGood)
  let walk : ℕ → State := fun n ↦ advance^[n] initial
  refine ⟨walk, ?_, ?_, ?_⟩
  · simp [walk]
  · intro n hn hnotGood
    have hnotGood' : ¬Good (advance^[n] initial) := by
      simpa only [walk] using hnotGood
    change Next (advance^[n] initial) (advance^[n + 1] initial)
    rw [Function.iterate_succ_apply']
    exact hadvance (advance^[n] initial) hnotGood'
  · by_cases hgood : ∃ n, n ≤ Fintype.card ι ∧ Good (walk n)
    · exact Or.inl hgood
    · right
      constructor
      · intro n hn hgoodAt
        exact hgood ⟨n, hn, hgoodAt⟩
      let labelAt : Fin (Fintype.card ι + 1) → ι :=
        fun n ↦ label (walk n)
      have hcard : Fintype.card ι <
          Fintype.card (Fin (Fintype.card ι + 1)) := by simp
      obtain ⟨m, n, hmn, hlabel⟩ :=
        Fintype.exists_ne_map_eq_of_card_lt labelAt hcard
      refine ⟨(m : ℕ), (n : ℕ), Nat.le_of_lt_succ m.isLt,
        Nat.le_of_lt_succ n.isLt, ?_, ?_⟩
      · intro heq
        exact hmn (Fin.ext heq)
      · simpa [labelAt] using hlabel

/-- A player-marked negative suffix of one fixed finite chain. -/
structure QuittingNegativeFlagState
    (value : ℕ → Payoff ι) (cutoff : ℕ) (θ : ℝ) where
  owner : ι
  time : ℕ
  time_le_cutoff : time ≤ cutoff
  negative : value time owner ≤ -θ

/-- The current negative flag has a concrete positive-weight good-boundary
mark in its actual owner-deleted suffix packet. -/
def QuittingNegativeFlagState.HasGoodBoundary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (cutoff : ℕ) (θ : ℝ)
    (state : QuittingNegativeFlagState value cutoff θ) : Prop :=
  ∃ mark : QuittingFirstOpponentMark ι (cutoff - state.time),
    0 < quittingFirstOpponentRawWeight roots state.owner state.time
        (cutoff - state.time) mark ∧
      QuittingMarkedFencePacket.IsGoodBoundary θ
        (quittingFirstOpponentOwnerReward reward state.owner)
        (quittingFirstOpponentQuitters state.owner)
        (quittingFirstOpponentValue value state.time) mark

/-- One actual new-negative flag transfer.  It retains the full marked joint
action, advances to exactly its displayed suffix date, and records strict
activity of the new owner at that root. -/
def QuittingNegativeFlagState.IsActualTransfer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (cutoff : ℕ) (θ : ℝ)
    (source target : QuittingNegativeFlagState value cutoff θ) : Prop :=
  ∃ mark : QuittingFirstOpponentMark ι (cutoff - source.time),
    target.time = source.time + mark.1 ∧
    0 < quittingFirstOpponentRawWeight roots source.owner source.time
        (cutoff - source.time) mark ∧
    QuittingMarkedFencePacket.IsNewNegativeOwner θ
      (quittingFirstOpponentOwnerReward reward source.owner)
      (quittingFirstOpponentQuitters source.owner)
      (quittingFirstOpponentValue value source.time) target.owner mark ∧
    0 < (roots target.time target.owner true).toReal

/-- An actual transfer always lands strictly before the fixed terminal
cutoff, even though negative flag states only store the weaker closed bound
needed to form the initial state. -/
theorem QuittingNegativeFlagState.IsActualTransfer.target_time_lt_cutoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (cutoff : ℕ) (θ : ℝ)
    {source target : QuittingNegativeFlagState value cutoff θ}
    (htransfer : source.IsActualTransfer reward roots value cutoff θ target) :
    target.time < cutoff := by
  obtain ⟨mark, htime, _hraw, _hmarked, _hactive⟩ := htransfer
  have hoffset := mark.1.isLt
  omega

/-- Actual transfers never move backward in the fixed chain's calendar. -/
theorem QuittingNegativeFlagState.IsActualTransfer.source_time_le_target_time
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (cutoff : ℕ) (θ : ℝ)
    {source target : QuittingNegativeFlagState value cutoff θ}
    (htransfer : source.IsActualTransfer reward roots value cutoff θ target) :
    source.time ≤ target.time := by
  obtain ⟨mark, htime, _hraw, _hmarked, _hactive⟩ := htransfer
  rw [htime]
  omega

/-- Owner deletion makes every actual transfer change the player flag. -/
theorem QuittingNegativeFlagState.IsActualTransfer.target_owner_ne_source_owner
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (cutoff : ℕ) (θ : ℝ)
    {source target : QuittingNegativeFlagState value cutoff θ}
    (htransfer : source.IsActualTransfer reward roots value cutoff θ target) :
    target.owner ≠ source.owner := by
  obtain ⟨_mark, _htime, _hraw, hmarked, _hactive⟩ := htransfer
  exact (Finset.mem_erase.mp hmarked.2.1).1

/-- At the target of an actual transfer, positive Quit support and exact
root Nash identify the new owner's pure-Quit endpoint with the declared
current value. -/
theorem QuittingNegativeFlagState.IsActualTransfer.quitPayoff_eq_value
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (cutoff : ℕ) (θ : ℝ)
    (hpolicy : ∀ time, time < cutoff →
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time))
    (hnash : ∀ time, time < cutoff →
      IsεQuittingRootNash reward (value (time + 1)) 0 (roots time))
    {source target : QuittingNegativeFlagState value cutoff θ}
    (htransfer : source.IsActualTransfer reward roots value cutoff θ target) :
    quittingRootQuitPayoff reward (value (target.time + 1))
        (roots target.time) target.owner =
      value target.time target.owner := by
  have htime := htransfer.target_time_lt_cutoff reward roots value cutoff θ
  obtain ⟨_mark, _htime, _hraw, _hmarked, hactive⟩ := htransfer
  calc
    quittingRootQuitPayoff reward (value (target.time + 1))
        (roots target.time) target.owner =
      quittingRootSuccessorPayoff reward (value (target.time + 1))
        (roots target.time) target.owner :=
          quittingRootQuitPayoff_eq_successor_of_quitProbability_pos
            reward (value (target.time + 1)) (roots target.time) target.owner
              (hnash target.time htime) hactive
    _ = value target.time target.owner := by
      rw [← congrFun (hpolicy target.time htime) target.owner]

/-- Equivalent fixed-opponents form of the active-transfer equality. -/
theorem QuittingNegativeFlagState.IsActualTransfer.fixedQuitValue_eq_value
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (cutoff : ℕ) (θ : ℝ)
    (hpolicy : ∀ time, time < cutoff →
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time))
    (hnash : ∀ time, time < cutoff →
      IsεQuittingRootNash reward (value (time + 1)) 0 (roots time))
    {source target : QuittingNegativeFlagState value cutoff θ}
    (htransfer : source.IsActualTransfer reward roots value cutoff θ target) :
    quittingFixedOpponentsQuitValue reward roots target.owner target.time =
      value target.time target.owner := by
  rw [← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward roots
    target.owner (value (target.time + 1)) target.time]
  exact htransfer.quitPayoff_eq_value reward roots value cutoff θ hpolicy hnash

/-- Every negative flag on an arbitrary fixed-cutoff exact chain either has
a concrete good boundary or admits one actual active negative transfer on
the same chain. -/
theorem QuittingNegativeFlagState.hasGoodBoundary_or_exists_actualTransfer
    [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (cutoff : ℕ) (θ M : ℝ)
    (hterminal : value cutoff = 0)
    (hpolicy : ∀ time, time < cutoff →
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time))
    (hnash : ∀ time, time < cutoff →
      IsεQuittingRootNash reward (value (time + 1)) 0 (roots time))
    (hθ : 0 < θ) (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (state : QuittingNegativeFlagState value cutoff θ) :
    state.HasGoodBoundary reward roots value cutoff θ ∨
      ∃ next, state.IsActualTransfer reward roots value cutoff θ next := by
  rcases exists_goodBoundary_or_activeNegativeTransfer_of_finiteExactChain
    reward roots value state.owner cutoff state.time θ M
      state.time_le_cutoff hterminal hpolicy hnash hθ hM hreward
        state.negative with hgood | htransfer
  · exact Or.inl hgood
  · right
    obtain ⟨j, mark, hjne, hraw, hmarked, hactive⟩ := htransfer
    have htimeLe : state.time + (mark.1 : ℕ) ≤ cutoff := by
      have hoffset := mark.1.isLt
      omega
    let next : QuittingNegativeFlagState value cutoff θ :=
      { owner := j
        time := state.time + mark.1
        time_le_cutoff := htimeLe
        negative := hmarked.2.2 }
    refine ⟨next, mark, rfl, hraw, hmarked, ?_⟩
    exact hactive

/-- **Finite actual flag iteration.**  Starting from any negative flag on an
arbitrary exact fixed-cutoff chain, there is a walk of actual supported
suffix transfers such that within at most `card ι` transfers either a
concrete good-boundary packet is reached or a player label repeats.

The repeat is only a player-name repeat.  No equality or recurrence of
payoff states, product roots, or charts is asserted. -/
theorem exists_finiteActualNegativeFlagWalk_good_or_repeatedOwner
    [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (cutoff : ℕ) (θ M : ℝ)
    (hterminal : value cutoff = 0)
    (hpolicy : ∀ time, time < cutoff →
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time))
    (hnash : ∀ time, time < cutoff →
      IsεQuittingRootNash reward (value (time + 1)) 0 (roots time))
    (hθ : 0 < θ) (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (initial : QuittingNegativeFlagState value cutoff θ) :
    ∃ walk : ℕ → QuittingNegativeFlagState value cutoff θ,
      walk 0 = initial ∧
      (∀ n, n < Fintype.card ι →
        ¬(walk n).HasGoodBoundary reward roots value cutoff θ →
        (walk n).IsActualTransfer reward roots value cutoff θ
          (walk (n + 1))) ∧
      ((∃ n, n ≤ Fintype.card ι ∧
          (walk n).HasGoodBoundary reward roots value cutoff θ) ∨
        (∀ n, n ≤ Fintype.card ι →
          ¬(walk n).HasGoodBoundary reward roots value cutoff θ) ∧
          ∃ m n, m ≤ Fintype.card ι ∧ n ≤ Fintype.card ι ∧
            m ≠ n ∧ (walk m).owner = (walk n).owner) := by
  apply exists_finiteLabelWalk_good_or_repeat
    (fun state : QuittingNegativeFlagState value cutoff θ ↦ state.owner)
    (fun state ↦ state.HasGoodBoundary reward roots value cutoff θ)
    (fun source target ↦
      source.IsActualTransfer reward roots value cutoff θ target)
  · intro state
    exact state.hasGoodBoundary_or_exists_actualTransfer reward roots value
      cutoff θ M hterminal hpolicy hnash hθ hM hreward

/-- The repeated-owner branch refines into the exact calendar alternatives
needed by the marked construction.  Because actual transfer times are
nondecreasing, an owner repeat is either at the same actual suffix date
(hence at the same supplied value/root node) or occurs at a strictly later
date. -/
theorem exists_finiteActualNegativeFlagWalk_good_or_sameTime_or_strictTimeRepeat
    [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (cutoff : ℕ) (θ M : ℝ)
    (hterminal : value cutoff = 0)
    (hpolicy : ∀ time, time < cutoff →
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time))
    (hnash : ∀ time, time < cutoff →
      IsεQuittingRootNash reward (value (time + 1)) 0 (roots time))
    (hθ : 0 < θ) (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (initial : QuittingNegativeFlagState value cutoff θ) :
    ∃ walk : ℕ → QuittingNegativeFlagState value cutoff θ,
      walk 0 = initial ∧
      (∀ n, n < Fintype.card ι →
        ¬(walk n).HasGoodBoundary reward roots value cutoff θ →
        (walk n).IsActualTransfer reward roots value cutoff θ
          (walk (n + 1))) ∧
      ((∃ n, n ≤ Fintype.card ι ∧
          (walk n).HasGoodBoundary reward roots value cutoff θ) ∨
        (∀ n, n ≤ Fintype.card ι →
          ¬(walk n).HasGoodBoundary reward roots value cutoff θ) ∧
          ((∃ m n, m < n ∧ n ≤ Fintype.card ι ∧
              (walk m).owner = (walk n).owner ∧
              (walk m).time = (walk n).time) ∨
            ∃ m n, m < n ∧ n ≤ Fintype.card ι ∧
              (walk m).owner = (walk n).owner ∧
              (walk m).time < (walk n).time)) := by
  obtain ⟨walk, hinitial, hsteps, hend⟩ :=
    exists_finiteActualNegativeFlagWalk_good_or_repeatedOwner
      reward roots value cutoff θ M hterminal hpolicy hnash hθ hM
        hreward initial
  refine ⟨walk, hinitial, hsteps, ?_⟩
  rcases hend with hgood | ⟨hnogood, hrepeat⟩
  · exact Or.inl hgood
  · right
    refine ⟨hnogood, ?_⟩
    have hadjacent (n : ℕ) (hn : n < Fintype.card ι) :
        (walk n).time ≤ (walk (n + 1)).time := by
      have htransfer := hsteps n hn (hnogood n hn.le)
      exact htransfer.source_time_le_target_time
        reward roots value cutoff θ
    have htimeMonotone : ∀ {m n : ℕ}, m ≤ n →
        n ≤ Fintype.card ι → (walk m).time ≤ (walk n).time := by
      intro m n hmn hn
      induction n generalizing m with
      | zero =>
          have hm : m = 0 := by omega
          subst m
          exact le_rfl
      | succ n ih =>
          by_cases hm : m = n + 1
          · subst m
            exact le_rfl
          · have hmle : m ≤ n := by omega
            exact (ih hmle (by omega)).trans (hadjacent n (by omega))
    obtain ⟨m, n, hm, hn, hmn, howner⟩ := hrepeat
    by_cases horder : m < n
    · have htime := htimeMonotone horder.le hn
      rcases htime.eq_or_lt with heq | hlt
      · exact Or.inl ⟨m, n, horder, hn, howner, heq⟩
      · exact Or.inr ⟨m, n, horder, hn, howner, hlt⟩
    · have hreverse : n < m := by omega
      have htime := htimeMonotone hreverse.le hm
      rcases htime.eq_or_lt with heq | hlt
      · exact Or.inl ⟨n, m, hreverse, hm, howner.symm, heq⟩
      · exact Or.inr ⟨n, m, hreverse, hm, howner.symm, hlt⟩

end GameTheory
