/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticConcentratedSingletonConsumer
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDefectStratification
import UniformEquilibrium.Quitting.Debt.Marked.FencePacket

/-!
# Resolving cancellation at a concentrated opponent singleton

Suppose the reset owner strictly gains by joining a recurrent opponent
singleton, while the owner's played-row defect vanishes.  The exact endpoint
average gives a quantitative alternative.  Either the shifted continuation
stays uniformly above the owner's own singleton payoff, or another realized
opponent coalition has a fixed positive Continue-versus-join loss.  Finiteness
freezes that coalition on a frequent set of marked rows.

The latter branch is a literal support-enlargement obstruction: the owner is
strictly harmed by insertion into a nonempty coalition.  It is stronger than
a signed Möbius coefficient because it retains both an actual product-action
atom and the full table-edge payoff difference.  The former branch is the
sharp residual: a high dynamic continuation can cancel the profitable
singleton edge without any negative higher-coalition edge.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The probability-weighted loss from inserting `owner` into the opponent
coalition realized by `action`.  The action is sampled with `owner` forced to
Continue. -/
def quittingPlayedOwnerJoinLossTerm
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι) (action : ι → Bool) : ℝ :=
  ((pmfPi (Function.update root owner (PMF.pure false))) action).toReal *
    max (quittingTerminalOpponentAdvantage reward owner action) 0

@[simp] theorem quittingQuitters_coalitionAction
    (coalition : Finset ι) :
    quittingQuitters (quittingCoalitionAction coalition) = coalition := by
  ext who
  simp [quittingQuitters, quittingCoalitionAction]

/-- On the exact opponent-singleton action, terminal opponent advantage is
the singleton payoff before insertion minus the pair payoff after insertion.
-/
theorem quittingTerminalOpponentAdvantage_coalitionAction_singleton
    (owner other : ι) (hne : other ≠ owner) :
    quittingTerminalOpponentAdvantage reward owner
        (quittingCoalitionAction {other}) =
      quittingSoloReward reward other owner -
        quittingSingletonCollisionReward reward other owner := by
  have howner : quittingCoalitionAction ({other} : Finset ι) owner = false := by
    simp [quittingCoalitionAction, hne.symm]
  have hupdated := quittingQuitters_update_true_of_apply_false
    (quittingCoalitionAction ({other} : Finset ι)) owner
  rw [quittingQuitters_coalitionAction] at hupdated
  unfold quittingTerminalOpponentAdvantage quittingRootPayoff
  rw [quittingQuitters_coalitionAction]
  simp only [Finset.singleton_nonempty, dite_true]
  rw [hupdated]
  simp only [Finset.insert_nonempty, dite_true]
  unfold quittingSoloReward quittingSingletonCollisionReward
  have hpairs : ({owner, other} : Finset ι) = {other, owner} := by
    ext who
    simp [or_comm]
  congr 2
  exact Subtype.ext hpairs

/-- If the owner already Quits in an action, inserting it changes nothing and
the Continue-versus-join table edge is zero. -/
theorem quittingTerminalOpponentAdvantage_eq_zero_of_owner_quits
    (owner : ι) (action : ι → Bool) (howner : action owner = true) :
    quittingTerminalOpponentAdvantage reward owner action = 0 := by
  have hnonempty : (quittingQuitters action).Nonempty :=
    (quittingQuitters_nonempty_iff action).2 ⟨owner, howner⟩
  have hupdate : Function.update action owner true = action := by
    funext who
    by_cases hwho : who = owner
    · subst who
      simp [howner]
    · simp [Function.update_of_ne hwho]
  unfold quittingTerminalOpponentAdvantage quittingRootPayoff
  rw [hupdate]
  simp [hnonempty]

/-- **One-row cancellation extraction.**  A positive exact singleton-joining
edge with mass `rho` cannot disappear from an endpoint average.  If neither
the endpoint positive part nor the dynamic singleton-tail gap spends the
budget, some actual opponent action carries a positive insertion loss.

The conclusion is deliberately multiplication-form: it remains meaningful
without dividing by the finite action count. -/
theorem exists_playedOwnerJoinLossTerm_of_singletonGain_canceled
    (tail : Payoff ι) (root : ι → PMF Bool) (owner other : ι)
    (hne : other ≠ owner) {rho eta epsilon kappa : ℝ}
    (heta : 0 ≤ eta) (hkappa : 0 ≤ kappa)
    (hmass : rho ≤ quittingRootCoalitionMass root {other})
    (hstrict : eta ≤ quittingSingletonCollisionReward reward other owner -
      quittingSoloReward reward other owner)
    (hendpoint : max
      (quittingRootEndpointDifference reward tail root owner) 0 ≤ epsilon)
    (htail : tail owner ≤ quittingSoloReward reward owner owner + kappa)
    (hbudget : epsilon + kappa < rho * eta) :
    ∃ action : ι → Bool,
      action owner = false ∧
      (quittingQuitters action).Nonempty ∧
      0 < quittingTerminalOpponentAdvantage reward owner action ∧
      rho * eta - epsilon - kappa ≤
        (Fintype.card (ι → Bool) : ℝ) *
          quittingPlayedOwnerJoinLossTerm reward root owner action := by
  classical
  let opponentRoot := Function.update root owner (PMF.pure false)
  let advantage : (ι → Bool) → ℝ := fun action =>
    quittingTerminalOpponentAdvantage reward owner action
  let positive : (ι → Bool) → ℝ := fun action =>
    ((pmfPi opponentRoot) action).toReal * max (advantage action) 0
  let negative : (ι → Bool) → ℝ := fun action =>
    ((pmfPi opponentRoot) action).toReal * max (-(advantage action)) 0
  let target := quittingCoalitionAction ({other} : Finset ι)
  have htargetMass : rho ≤ ((pmfPi opponentRoot) target).toReal := by
    have hrouted := quittingRootCoalitionMass_le_pureEndpointRouted
      root ({other} : Finset ι) owner false
    have hroute : quittingPureEndpointRoutedCoalition
        ({other} : Finset ι) owner false = {other} := by
      simp [quittingPureEndpointRoutedCoalition, hne.symm]
    rw [hroute] at hrouted
    rw [← quittingRootCoalitionMass_eq_pmfPi opponentRoot {other}]
    exact hmass.trans (by simpa only [opponentRoot] using hrouted)
  have htargetAdvantage : advantage target =
      quittingSoloReward reward other owner -
        quittingSingletonCollisionReward reward other owner := by
    exact quittingTerminalOpponentAdvantage_coalitionAction_singleton
      owner other hne
  have htargetNegative : rho * eta ≤ negative target := by
    have hmassNonneg : 0 ≤ ((pmfPi opponentRoot) target).toReal :=
      ENNReal.toReal_nonneg
    have hgap : eta ≤ -(advantage target) := by
      rw [htargetAdvantage]
      linarith
    have hmax : eta ≤ max (-(advantage target)) 0 :=
      hgap.trans (le_max_left _ _)
    exact mul_le_mul htargetMass hmax heta hmassNonneg
  have hsurvivalNonneg : 0 ≤ 1 -
      quittingRootAbsorptionMass opponentRoot := by
    unfold quittingRootAbsorptionMass
    linarith [quittingStationaryContinueMass_nonneg opponentRoot]
  have htailGap : quittingSoloReward reward owner owner - tail owner ≥ -kappa := by
    linarith
  have hsurvivalLeOne : 1 - quittingRootAbsorptionMass opponentRoot ≤ 1 := by
    unfold quittingRootAbsorptionMass
    linarith [quittingStationaryContinueMass_le_one opponentRoot]
  have hsurvivalGap :
      -kappa ≤ (1 - quittingRootAbsorptionMass opponentRoot) *
        (quittingSoloReward reward owner owner - tail owner) := by
    calc
      -kappa ≤ (1 - quittingRootAbsorptionMass opponentRoot) * (-kappa) := by
        nlinarith
      _ ≤ (1 - quittingRootAbsorptionMass opponentRoot) *
          (quittingSoloReward reward owner owner - tail owner) :=
        mul_le_mul_of_nonneg_left htailGap hsurvivalNonneg
  have hendpointUpper :
      quittingRootEndpointDifference reward tail root owner ≤ epsilon :=
    (le_max_left _ _).trans hendpoint
  have hexpectLower : - (epsilon + kappa) ≤
      expect (pmfPi opponentRoot) advantage := by
    have hdecomp := quittingRootEndpointDifference_eq_outsiderNever
      reward tail root owner
    change quittingRootEndpointDifference reward tail root owner =
        (1 - quittingRootAbsorptionMass opponentRoot) *
          (quittingSoloReward reward owner owner - tail owner) -
            expect (pmfPi opponentRoot) advantage at hdecomp
    linarith
  have hsplit : expect (pmfPi opponentRoot) advantage =
      (∑ action, positive action) - ∑ action, negative action := by
    rw [expect_eq_sum]
    simp only [positive, negative]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro action _
    have hprob : 0 ≤ ((pmfPi opponentRoot) action).toReal :=
      ENNReal.toReal_nonneg
    by_cases ha : 0 ≤ advantage action
    · rw [max_eq_left ha, max_eq_right (by linarith : -(advantage action) ≤ 0)]
      ring
    · have ha' : advantage action ≤ 0 := le_of_not_ge ha
      rw [max_eq_right ha', max_eq_left (by linarith : 0 ≤ -(advantage action))]
      ring
  have hnegativeSum : negative target ≤ ∑ action, negative action := by
    apply Finset.single_le_sum (s := Finset.univ) (f := negative)
    · intro action _
      exact mul_nonneg ENNReal.toReal_nonneg (le_max_right _ _)
    · exact Finset.mem_univ target
  have hpositiveSum : rho * eta - epsilon - kappa ≤
      ∑ action, positive action := by
    rw [hsplit] at hexpectLower
    linarith [htargetNegative.trans hnegativeSum]
  obtain ⟨action, _haction, havg⟩ :=
    QuittingMarkedFencePacket.exists_sum_le_card_mul
      (Finset.univ : Finset (ι → Bool)) Finset.univ_nonempty positive
  have hlower : rho * eta - epsilon - kappa ≤
      (Fintype.card (ι → Bool) : ℝ) * positive action := by
    exact hpositiveSum.trans (by simpa using havg)
  have htermPos : 0 < positive action := by
    have hbudgetPos : 0 < rho * eta - epsilon - kappa := by linarith
    have hcardNonneg : 0 ≤ (Fintype.card (ι → Bool) : ℝ) := by positivity
    by_contra hnot
    have hnonpos : positive action ≤ 0 := le_of_not_gt hnot
    nlinarith
  have hadvantagePos : 0 < advantage action := by
    have hprobNonneg : 0 ≤ ((pmfPi opponentRoot) action).toReal :=
      ENNReal.toReal_nonneg
    have hmaxPos : 0 < max (advantage action) 0 := by
      by_contra hnot
      have hnonpos : max (advantage action) 0 ≤ 0 := le_of_not_gt hnot
      nlinarith [htermPos]
    exact (lt_max_iff.mp hmaxPos).resolve_right (lt_irrefl 0)
  have hownerFalse : action owner = false := by
    cases hownerAction : action owner with
    | false => rfl
    | true =>
      have hzero : advantage action = 0 :=
        quittingTerminalOpponentAdvantage_eq_zero_of_owner_quits
          owner action hownerAction
      rw [hzero] at hadvantagePos
      exact (lt_irrefl 0 hadvantagePos).elim
  have hnonempty : (quittingQuitters action).Nonempty := by
    by_contra hempty
    have hzero := quittingTerminalOpponentAdvantage_eq_zero_of_quitters_not_nonempty
      reward owner action hempty
    exact (not_lt_of_ge (hzero ▸ le_rfl)) hadvantagePos
  refine ⟨action, hownerFalse, hnonempty, hadvantagePos, ?_⟩
  simpa only [quittingPlayedOwnerJoinLossTerm, opponentRoot, advantage,
    positive] using hlower

/-- **Fixed cancellation label on a concentrated packet.**  If the reset
owner is a strict joiner of the recurrent opponent singleton, then either a
fixed positive fraction of that table gain reappears frequently as a strict
tail escape, or one fixed nonempty opponent coalition frequently carries a
quantitative owner-insertion loss.

The second branch is an actual support-enlargement edge, not a Möbius sign:
the displayed action has positive product-law mass in every certified row and
joining its quitter coalition strictly lowers the owner's terminal reward. -/
theorem QuittingReprojectionConcentratedPacket.frequent_ownerTailEscape_or_fixedJoinLoss
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : ι} {terminal : {S : Finset ι // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner terminal cutoff scale)
    (other : ι) (hne : other ≠ owner)
    (hterminal : terminal.val = {other})
    (hscale : ∀ n, 0 < scale n)
    (hscaleTendsto : Tendsto scale atTop (nhds 0))
    (hstrict : quittingSoloReward reward other owner <
      quittingSingletonCollisionReward reward other owner) :
    let gap := quittingSingletonCollisionReward reward other owner -
      quittingSoloReward reward other owner
    let charge := packet.resolution * gap / 4
    (∃ᶠ rank in atTop,
        quittingSoloReward reward owner owner + charge <
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward
              (profiles (packet.subseq rank)) (packet.mark rank + 1))).1 owner) ∨
      ∃ action : ι → Bool,
        action owner = false ∧
        (quittingQuitters action).Nonempty ∧
        0 < quittingTerminalOpponentAdvantage reward owner action ∧
        ∃ᶠ rank in atTop,
          packet.resolution * gap / 2 ≤
            (Fintype.card (ι → Bool) : ℝ) *
              quittingPlayedOwnerJoinLossTerm reward
                (quittingProfileLiveRoot reward
                  (profiles (packet.subseq rank)) (packet.mark rank))
                owner action := by
  classical
  let gap := quittingSingletonCollisionReward reward other owner -
    quittingSoloReward reward other owner
  let charge := packet.resolution * gap / 4
  let tail : ℕ → Payoff ι := fun rank =>
    (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward
        (profiles (packet.subseq rank)) (packet.mark rank + 1))).1
  let root : ℕ → ι → PMF Bool := fun rank =>
    quittingProfileLiveRoot reward
      (profiles (packet.subseq rank)) (packet.mark rank)
  dsimp only
  have hgap : 0 < gap := by
    dsimp only [gap]
    linarith
  have hcharge : 0 < charge := by
    dsimp only [charge]
    exact div_pos (mul_pos packet.resolution_pos hgap) (by norm_num)
  have hownerNotMem : owner ∉ terminal.val := by
    rw [hterminal]
    simpa using hne.symm
  have hpositivePart : Tendsto (fun rank =>
      max (quittingRootEndpointDifference reward (tail rank)
        (root rank) owner) 0) atTop (nhds 0) := by
    simpa only [tail, root] using
      packet.ownerQuitAdvantage_posPart_tendsto_zero
        hownerNotMem hscale hscaleTendsto
  have hsmall : ∀ᶠ rank in atTop,
      max (quittingRootEndpointDifference reward (tail rank)
        (root rank) owner) 0 ≤ charge := by
    have hlt : ∀ᶠ rank in atTop,
        max (quittingRootEndpointDifference reward (tail rank)
          (root rank) owner) 0 < charge :=
      (tendsto_order.1 hpositivePart).2 charge hcharge
    exact hlt.mono fun _ h => h.le
  have hmass : ∀ rank,
      packet.resolution ≤ quittingRootCoalitionMass (root rank) {other} := by
    intro rank
    have hstage := packet.stageMass rank
    have hlive := quittingLiveMass_le_one reward
      (profiles (packet.subseq rank)) (packet.mark rank)
    have hrootNonneg :=
      MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg
        (root rank) terminal.val
    rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass] at hstage
    have hmassTerminal : packet.resolution ≤
        quittingRootCoalitionMass (root rank) terminal.val := by
      change packet.resolution ≤
        quittingLiveMass reward (profiles (packet.subseq rank))
            (packet.mark rank) *
          quittingRootCoalitionMass (root rank) terminal.val at hstage
      nlinarith
    simpa only [hterminal] using hmassTerminal
  by_cases htailEscape : ∃ᶠ rank in atTop,
      quittingSoloReward reward owner owner + charge < tail rank owner
  · exact Or.inl htailEscape
  · have htailBound : ∀ᶠ rank in atTop,
        tail rank owner ≤ quittingSoloReward reward owner owner + charge := by
      exact (not_frequently.1 htailEscape).mono fun _ hnot => le_of_not_gt hnot
    let good : ℕ → (ι → Bool) → Prop := fun rank action =>
      action owner = false ∧
        (quittingQuitters action).Nonempty ∧
        0 < quittingTerminalOpponentAdvantage reward owner action ∧
        packet.resolution * gap / 2 ≤
          (Fintype.card (ι → Bool) : ℝ) *
            quittingPlayedOwnerJoinLossTerm reward (root rank) owner action
    have hexists : ∀ᶠ rank in atTop, ∃ action, good rank action := by
      filter_upwards [hsmall, htailBound] with rank hrow htailRow
      obtain ⟨action, howner, hnonempty, hadvantage, hterm⟩ :=
        exists_playedOwnerJoinLossTerm_of_singletonGain_canceled
          (reward := reward) (tail rank) (root rank) owner other hne
          (rho := packet.resolution) (eta := gap)
          (epsilon := charge) (kappa := charge)
          hgap.le hcharge.le (hmass rank) (by rfl) hrow htailRow (by
            dsimp only [charge]
            nlinarith [packet.resolution_pos, hgap])
      refine ⟨action, howner, hnonempty, hadvantage, ?_⟩
      dsimp only [charge] at hterm
      calc
        packet.resolution * gap / 2 =
            packet.resolution * gap - packet.resolution * gap / 4 -
              packet.resolution * gap / 4 := by ring
        _ ≤ (Fintype.card (ι → Bool) : ℝ) *
            quittingPlayedOwnerJoinLossTerm reward (root rank) owner action :=
          hterm
    have hfixed : ∃ action, ∃ᶠ rank in atTop, good rank action := by
      by_contra hnot
      have hnot' : ∀ action, ¬ ∃ᶠ rank in atTop, good rank action := by
        simpa using hnot
      have hall : ∀ᶠ rank in atTop, ∀ action, ¬ good rank action := by
        rw [eventually_all]
        intro action
        exact not_frequently.1 (hnot' action)
      obtain ⟨rank, hrank, hallRank⟩ := (hexists.and hall).exists
      obtain ⟨action, haction⟩ := hrank
      exact (hallRank action) haction
    obtain ⟨action, haction⟩ := hfixed
    obtain ⟨_rank, hstatic⟩ := haction.exists
    refine Or.inr ⟨action, hstatic.1, hstatic.2.1, hstatic.2.2.1, ?_⟩
    exact haction.mono fun _ h => h.2.2.2

end GameTheory
