/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Holonomy.AggregateTerminalAnchor
import UniformEquilibrium.Quitting.Boundary.Holonomy.BehavioralTailRepairValue
import UniformEquilibrium.Quitting.Boundary.Repair.CertifiedBoundaryReinsertion
import UniformEquilibrium.Quitting.Debt.Marked.FencePacket
import UniformEquilibrium.Quitting.Debt.Dynamic.FiniteDynamicDebtSemantics

/-!
# Quantitative aggregate terminal anchors

An aggregate exact-`D` minimizer with positive objective has a marked owner
whose initial debt carries at least the average share of that objective.  The
separated terminal-atom extraction may be performed at that same owner.
Consequently the aggregate objective is charged to the resulting marked
packet with an explicit finite-player constant.

This strengthens positive-coordinate extraction without asserting a terminal
replacement.  In particular, the packet inequality does not construct a new
exact Nash--Bellman chain after changing the physical continuation.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

namespace QuittingAggregateCalibratedTerminalAnchor

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## The physical Never tail reads the exact calibrated objective -/

omit [Nonempty ι] in
/-- For any exact zero-boundary chain, attaching the physical Never tail to
the whole finite block reads precisely the player's singleton-capped exact
dynamic debt.  This is the direct semantic bridge from a co-realized boundary
pair to the calibrated objective; it does not change the prefix. -/
theorem fullPrefix_coRealizedGain_elementaryNever_eq_dynamicDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (last : ℕ) (path : QuittingFiniteNashBellmanPath ι (last + 1))
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward (last + 1))
    (who : ι) :
    let roots := quittingFiniteNashBellmanPathRoots (last + 1) path
    let neverRoots := quittingElementaryCapRoots
      (.never : QuittingElementaryTailCap ι)
    (quittingFiniteBoundaryHolonomy reward roots 0 last).coRealizedGain
        (QuittingBoundaryHolonomy.behavioralTailPrescribedBoundary
          reward neverRoots)
        (QuittingBoundaryHolonomy.behavioralTailEnvelopeBoundary
          reward neverRoots) who =
      quittingFiniteNashBellmanPathDynamicDebt
        reward (last + 1) path who 0 := by
  dsimp only
  let roots := quittingFiniteNashBellmanPathRoots (last + 1) path
  let prescribed := fun time ↦
    quittingFiniteNashBellmanPathValue (last + 1) path time who
  let cap := quittingPositiveSingletonDebtCap reward who
  have hterminal : prescribed (last + 1) = 0 := by
    exact congrFun
      (quittingFiniteNashBellmanPathValue_eq_zero_at_cutoff
        reward (last + 1) path hpath) who
  have hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed :=
    isQuittingLivePrescribedValue_finiteNashBellmanPath
      reward (last + 1) path hpath who
  have heval := quittingFiniteTerminalHazardValue_self_eq_prescribed
    reward roots who prescribed hprescribed 0 (last + 1)
  have hbest := prescribed_add_quittingFiniteDynamicDebt_eq_bestResponse
    reward roots who prescribed cap 0 (last + 1)
  simp only [zero_add] at heval hbest
  rw [hterminal] at heval hbest
  simp only [zero_add] at hbest
  unfold QuittingBoundaryHolonomy.coRealizedGain
    QuittingBoundaryHolonomy.boundaryEnvelopeAt
    QuittingBoundaryHolonomy.prescribedAt
    QuittingBoundaryHolonomy.behavioralTailPrescribedBoundary
    QuittingBoundaryHolonomy.behavioralTailEnvelopeBoundary
  rw [quittingRootSequenceTerminalValue_elementaryCap_never]
  rw [quittingRootSequenceBestResponseValue_elementaryCap_never
    reward who (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward)]
  change
    ((quittingFiniteBoundaryHolonomy reward roots 0 last).bestResponse who).eval
        cap -
      ((quittingFiniteBoundaryHolonomy reward roots 0 last).prescribed who).eval 0 =
        quittingFiniteDynamicDebt reward roots who prescribed cap 0 (last + 1)
  rw [quittingFiniteBoundaryHolonomy_bestResponse_eval,
    quittingFiniteBoundaryHolonomy_prescribed_eval]
  linarith

/-- The maximum gain of the full finite prefix against the physical Never
tail is exactly the maximum playerwise exact dynamic debt. -/
theorem fullPrefix_behavioralTailGain_elementaryNever_eq_maxDynamicDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (last : ℕ) (path : QuittingFiniteNashBellmanPath ι (last + 1))
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward (last + 1)) :
    let roots := quittingFiniteNashBellmanPathRoots (last + 1) path
    QuittingBoundaryHolonomy.behavioralTailGain reward
        (quittingFiniteBoundaryHolonomy reward roots 0 last)
        (quittingElementaryCapRoots
          (.never : QuittingElementaryTailCap ι)) =
      quittingFiniteNashBellmanPathMaxDynamicDebt
        reward (last + 1) path := by
  dsimp only
  unfold QuittingBoundaryHolonomy.behavioralTailGain
    QuittingBoundaryHolonomy.maxCoRealizedGain
    QuittingBoundaryHolonomy.finitePlayerMax
    quittingFiniteNashBellmanPathMaxDynamicDebt
  congr 1
  funext who
  rw [fullPrefix_coRealizedGain_elementaryNever_eq_dynamicDebt
    reward last path hpath who]
  exact max_eq_right
    (quittingFiniteNashBellmanPathDynamicDebt_nonneg
      reward (last + 1) path hpath who 0)

/-- Holonomy of the complete canonical aggregate-minimizing prefix at a fixed
positive cutoff.  This definition does not require the optimum to be
positive. -/
def canonicalAggregateFullPrefixHolonomy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (last : ℕ) : QuittingBoundaryHolonomy ι :=
  let path := quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer
    reward (last + 1)
  quittingFiniteBoundaryHolonomy reward
    (quittingFiniteNashBellmanPathRoots (last + 1) path) 0 last

/-- All-tail repair value of the complete canonical aggregate-minimizing
prefix. -/
def canonicalAggregateFullPrefixRepairValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (last : ℕ) : ℝ :=
  QuittingBoundaryHolonomy.behavioralTailRepairValue reward
    (canonicalAggregateFullPrefixHolonomy reward last)

/-- The canonical full-prefix repair value is bounded by the attained
aggregate exact-`D` minimum, with no positivity or marked-anchor premise. -/
theorem canonicalAggregateFullPrefixRepairValue_le_minAggregate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (last : ℕ) :
    canonicalAggregateFullPrefixRepairValue reward last ≤
      quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
        reward (last + 1) := by
  let path := quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer
    reward (last + 1)
  let roots := quittingFiniteNashBellmanPathRoots (last + 1) path
  let neverRoots := quittingElementaryCapRoots
    (.never : QuittingElementaryTailCap ι)
  have hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward (last + 1) :=
    quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer_mem
      reward (last + 1)
  have hinf :
      canonicalAggregateFullPrefixRepairValue reward last ≤
        QuittingBoundaryHolonomy.behavioralTailGain reward
          (quittingFiniteBoundaryHolonomy reward roots 0 last) neverRoots := by
    unfold canonicalAggregateFullPrefixRepairValue
      canonicalAggregateFullPrefixHolonomy
    dsimp only
    apply csInf_le
    · exact QuittingBoundaryHolonomy.bddBelow_range_behavioralTailGain
        reward (quittingFiniteBoundaryHolonomy reward roots 0 last)
    · exact ⟨neverRoots, rfl⟩
  have hnever :
      QuittingBoundaryHolonomy.behavioralTailGain reward
          (quittingFiniteBoundaryHolonomy reward roots 0 last) neverRoots =
        quittingFiniteNashBellmanPathMaxDynamicDebt
          reward (last + 1) path := by
    simpa [neverRoots, roots] using
      (fullPrefix_behavioralTailGain_elementaryNever_eq_maxDynamicDebt
        reward last path hpath)
  rw [hnever] at hinf
  apply hinf.trans
  calc
    quittingFiniteNashBellmanPathMaxDynamicDebt
        reward (last + 1) path ≤
      quittingFiniteNashBellmanPathAggregateDynamicDebt
        reward (last + 1) path :=
      quittingFiniteNashBellmanPathMaxDynamicDebt_le_aggregate
        reward (last + 1) path hpath
    _ = quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
        reward (last + 1) := rfl

omit [Nonempty ι] in
/-- A uniform coordinate bound controls every marked terminal opponent
advantage. -/
theorem terminalOpponentAdvantage_le_two_mul_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (M : ℝ) (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (owner : ι) (action : ι → Bool) :
    quittingTerminalOpponentAdvantage reward owner action ≤ 2 * M := by
  let singleton := reward (quittingSingletonTerminal owner) owner
  let before := quittingRootPayoff reward (fun _ ↦ singleton) action owner
  let after := quittingRootPayoff reward (0 : Payoff ι)
    (Function.update action owner true) owner
  have hsingleton : |singleton| ≤ M :=
    hreward (quittingSingletonTerminal owner) owner
  have hbefore : |before| ≤ M := by
    exact abs_quittingRootPayoff_le reward (fun _ ↦ singleton)
      hreward (fun _ ↦ hsingleton) action owner
  have hafter : |after| ≤ M := by
    exact abs_quittingRootPayoff_le reward (0 : Payoff ι)
      hreward (fun _ ↦ by simpa using hM)
      (Function.update action owner true) owner
  unfold quittingTerminalOpponentAdvantage
  change before - after ≤ 2 * M
  calc
    before - after ≤ |before - after| := le_abs_self _
    _ ≤ |before| + |after| := abs_sub _ _
    _ ≤ M + M := add_le_add hbefore hafter
    _ = 2 * M := by ring

/-- The all-tail repair value of the complete selected prefix is bounded by
its aggregate calibrated objective.  The proof evaluates the infimum at the
physical Never tail and then compares maximum debt with aggregate debt. -/
theorem fullPrefix_behavioralTailRepairValue_le_minAggregate
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward) :
    QuittingBoundaryHolonomy.behavioralTailRepairValue reward
        (quittingFiniteBoundaryHolonomy reward anchor.roots 0 anchor.last) ≤
      quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
        reward (anchor.last + 1) := by
  let neverRoots := quittingElementaryCapRoots
    (.never : QuittingElementaryTailCap ι)
  have hinf :
      QuittingBoundaryHolonomy.behavioralTailRepairValue reward
          (quittingFiniteBoundaryHolonomy reward anchor.roots 0 anchor.last) ≤
        QuittingBoundaryHolonomy.behavioralTailGain reward
          (quittingFiniteBoundaryHolonomy reward anchor.roots 0 anchor.last)
          neverRoots := by
    apply csInf_le
    · exact QuittingBoundaryHolonomy.bddBelow_range_behavioralTailGain
        reward (quittingFiniteBoundaryHolonomy
          reward anchor.roots 0 anchor.last)
    · exact ⟨neverRoots, rfl⟩
  have hnever :
      QuittingBoundaryHolonomy.behavioralTailGain reward
          (quittingFiniteBoundaryHolonomy reward anchor.roots 0 anchor.last)
          neverRoots =
        quittingFiniteNashBellmanPathMaxDynamicDebt
          reward (anchor.last + 1) anchor.path := by
    simpa [neverRoots, roots] using
      (fullPrefix_behavioralTailGain_elementaryNever_eq_maxDynamicDebt
        reward anchor.last anchor.path anchor.path_mem)
  rw [hnever] at hinf
  apply hinf.trans
  calc
    quittingFiniteNashBellmanPathMaxDynamicDebt
        reward (anchor.last + 1) anchor.path ≤
      quittingFiniteNashBellmanPathAggregateDynamicDebt
        reward (anchor.last + 1) anchor.path :=
      quittingFiniteNashBellmanPathMaxDynamicDebt_le_aggregate
        reward (anchor.last + 1) anchor.path anchor.path_mem
    _ = quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
        reward (anchor.last + 1) := by
      rw [anchor.path_is_aggregate_minimizer]
      rfl

/-- A positive aggregate optimum admits a marked aggregate-calibrated anchor
whose owner debt is at least the average playerwise debt.  The division-free
form is stable under later multiplication by packet charges. -/
theorem exists_with_minAggregate_le_card_mul_ownerDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (last : ℕ)
    (hpositive :
      0 < quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
        reward (last + 1)) :
    ∃ anchor : QuittingAggregateCalibratedTerminalAnchor reward,
      anchor.last = last ∧
        quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
          reward (last + 1) ≤
        (Fintype.card ι : ℝ) *
          quittingFiniteNashBellmanPathDynamicDebt
            reward (anchor.last + 1) anchor.path anchor.owner 0 := by
  let selected :=
    quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer
      reward (last + 1)
  have hselected : selected ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward (last + 1) :=
    quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer_mem
      reward (last + 1)
  have haggregate :
      quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
          reward (last + 1) =
        ∑ who, quittingFiniteNashBellmanPathDynamicDebt
          reward (last + 1) selected who 0 := by
    rfl
  obtain ⟨owner, _howner, hownerAverage⟩ :=
    QuittingMarkedFencePacket.exists_sum_le_card_mul
      (Finset.univ : Finset ι) Finset.univ_nonempty
      (fun who ↦ quittingFiniteNashBellmanPathDynamicDebt
        reward (last + 1) selected who 0)
  have hcardPos : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hownerPos : 0 < quittingFiniteNashBellmanPathDynamicDebt
      reward (last + 1) selected owner 0 := by
    rw [← haggregate] at hownerAverage
    nlinarith
  obtain ⟨action, hsurvival0, hsurvival1, hmass0, hmass1,
      hownerFalse, hquitters, hadvantage, hweighted, _, _⟩ :=
    exists_finiteDynamicDebt_separatedTerminalAnchor_quantitative
      reward last selected hselected owner hownerPos
  let anchor : QuittingAggregateCalibratedTerminalAnchor reward := {
    last := last
    path := selected
    path_eq_minimizer := by rfl
    path_mem := hselected
    aggregateDebt_pos := by
      change 0 < ∑ who, quittingFiniteNashBellmanPathDynamicDebt
        reward (last + 1) selected who 0
      rw [← haggregate]
      exact hpositive
    owner := owner
    action := action
    ownerDebt_pos := hownerPos
    preterminalSurvival_pos := hsurvival0
    preterminalSurvival_le_one := hsurvival1
    terminalMass_pos := hmass0
    terminalMass_le_one := hmass1
    owner_continues := hownerFalse
    terminalQuitters_nonempty := hquitters
    terminalAdvantage_pos := hadvantage
    debt_le_weighted_packet := hweighted }
  refine ⟨anchor, rfl, ?_⟩
  rw [haggregate]
  simpa [anchor] using hownerAverage

/-- The quantitatively selected anchor charges the aggregate optimum to its
marked packet and terminal advantage. -/
theorem exists_minAggregate_le_card_mul_actionCard_mul_packetMass_mul_advantage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (last : ℕ)
    (hpositive :
      0 < quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
        reward (last + 1)) :
    ∃ anchor : QuittingAggregateCalibratedTerminalAnchor reward,
      anchor.last = last ∧
        quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
          reward (last + 1) ≤
        (Fintype.card ι : ℝ) *
          (Fintype.card (ι → Bool) : ℝ) * anchor.packetMass *
            quittingTerminalOpponentAdvantage
              reward anchor.owner anchor.action := by
  obtain ⟨anchor, hlast, haverage⟩ :=
    exists_with_minAggregate_le_card_mul_ownerDebt
      reward last hpositive
  refine ⟨anchor, hlast, haverage.trans ?_⟩
  have hcard0 : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hweighted := anchor.debt_le_weighted_packet
  calc
    (Fintype.card ι : ℝ) *
        quittingFiniteNashBellmanPathDynamicDebt
          reward (anchor.last + 1) anchor.path anchor.owner 0 ≤
      (Fintype.card ι : ℝ) *
        ((Fintype.card (ι → Bool) : ℝ) * anchor.packetMass *
          quittingTerminalOpponentAdvantage
            reward anchor.owner anchor.action) :=
      mul_le_mul_of_nonneg_left hweighted hcard0
    _ = (Fintype.card ι : ℝ) *
          (Fintype.card (ι → Bool) : ℝ) * anchor.packetMass *
            quittingTerminalOpponentAdvantage
              reward anchor.owner anchor.action := by ring

/-- After bounding the terminal advantage, a positive aggregate optimum has
an anchor whose packet mass is bounded below in a division-free form. -/
theorem exists_minAggregate_le_two_mul_bound_mul_cards_mul_packetMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (last : ℕ)
    (hpositive :
      0 < quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
        reward (last + 1)) :
    ∃ anchor : QuittingAggregateCalibratedTerminalAnchor reward,
      anchor.last = last ∧
        quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
          reward (last + 1) ≤
        2 * quittingRewardBound reward * (Fintype.card ι : ℝ) *
          (Fintype.card (ι → Bool) : ℝ) * anchor.packetMass := by
  obtain ⟨anchor, hlast, hpacket⟩ :=
    exists_minAggregate_le_card_mul_actionCard_mul_packetMass_mul_advantage
      reward last hpositive
  refine ⟨anchor, hlast, hpacket.trans ?_⟩
  have hscale0 : 0 ≤
      (Fintype.card ι : ℝ) * (Fintype.card (ι → Bool) : ℝ) *
        anchor.packetMass := by
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (le_of_lt anchor.packetMass_pos)
  have hadvantage :=
    quittingTerminalOpponentAdvantage_le_two_mul_rewardBound
      reward anchor.owner anchor.action
  calc
    (Fintype.card ι : ℝ) * (Fintype.card (ι → Bool) : ℝ) *
        anchor.packetMass *
          quittingTerminalOpponentAdvantage reward anchor.owner anchor.action ≤
      (Fintype.card ι : ℝ) * (Fintype.card (ι → Bool) : ℝ) *
        anchor.packetMass * (2 * quittingRewardBound reward) :=
      mul_le_mul_of_nonneg_left hadvantage hscale0
    _ = 2 * quittingRewardBound reward * (Fintype.card ι : ℝ) *
          (Fintype.card (ι → Bool) : ℝ) * anchor.packetMass := by ring

/-- A positive floor for the canonical aggregate-minimizing full prefix
selects, at the same cutoff, a marked aggregate-calibrated anchor whose packet
mass carries that floor at the explicit uniform reward scale. -/
theorem exists_packetCharge_of_pos_le_canonicalFullPrefixRepairValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (M η : ℝ) (last : ℕ)
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hη : 0 < η)
    (hfloor : η ≤ canonicalAggregateFullPrefixRepairValue reward last) :
    ∃ anchor : QuittingAggregateCalibratedTerminalAnchor reward,
      anchor.last = last ∧
        η ≤ 2 * M * (Fintype.card ι : ℝ) *
          (Fintype.card (ι → Bool) : ℝ) * anchor.packetMass := by
  have hrepairLe :=
    canonicalAggregateFullPrefixRepairValue_le_minAggregate reward last
  have hηDebt : η ≤
      quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
        reward (last + 1) := hfloor.trans hrepairLe
  have hpositive :
      0 < quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
        reward (last + 1) := hη.trans_le hηDebt
  obtain ⟨anchor, hlast, hpacket⟩ :=
    exists_minAggregate_le_card_mul_actionCard_mul_packetMass_mul_advantage
      reward last hpositive
  refine ⟨anchor, hlast, ?_⟩
  have hscale0 : 0 ≤
      (Fintype.card ι : ℝ) * (Fintype.card (ι → Bool) : ℝ) *
        anchor.packetMass := by
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (le_of_lt anchor.packetMass_pos)
  have hadvantage := terminalOpponentAdvantage_le_two_mul_bound
    reward M hM hreward anchor.owner anchor.action
  calc
    η ≤ quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
        reward (last + 1) := hηDebt
    _ ≤ (Fintype.card ι : ℝ) * (Fintype.card (ι → Bool) : ℝ) *
          anchor.packetMass *
            quittingTerminalOpponentAdvantage
              reward anchor.owner anchor.action := hpacket
    _ ≤ (Fintype.card ι : ℝ) * (Fintype.card (ι → Bool) : ℝ) *
          anchor.packetMass * (2 * M) :=
      mul_le_mul_of_nonneg_left hadvantage hscale0
    _ = 2 * M * (Fintype.card ι : ℝ) *
          (Fintype.card (ι → Bool) : ℝ) * anchor.packetMass := by ring

/-- A positive aggregate optimum admits one prefix whose all-tail repair
value is below the optimum and whose marked packet carries that optimum at an
explicit scale.  Thus a positive floor for this selected prefix automatically
has a nonvanishing packet charge whenever the aggregate optimum does.  The
statement still supplies no replacement competitor. -/
theorem exists_fullPrefixRepairValue_le_minAggregate_le_packetCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (last : ℕ)
    (hpositive :
      0 < quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
        reward (last + 1)) :
    ∃ anchor : QuittingAggregateCalibratedTerminalAnchor reward,
      QuittingBoundaryHolonomy.behavioralTailRepairValue reward
          (quittingFiniteBoundaryHolonomy reward anchor.roots 0 anchor.last) ≤
        quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
          reward (last + 1) ∧
      quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
          reward (last + 1) ≤
        2 * quittingRewardBound reward * (Fintype.card ι : ℝ) *
          (Fintype.card (ι → Bool) : ℝ) * anchor.packetMass := by
  obtain ⟨anchor, hlast, hcharge⟩ :=
    exists_minAggregate_le_two_mul_bound_mul_cards_mul_packetMass
      reward last hpositive
  refine ⟨anchor, ?_, hcharge⟩
  have hrepair := fullPrefix_behavioralTailRepairValue_le_minAggregate anchor
  simpa [hlast] using hrepair

end QuittingAggregateCalibratedTerminalAnchor

end GameTheory
