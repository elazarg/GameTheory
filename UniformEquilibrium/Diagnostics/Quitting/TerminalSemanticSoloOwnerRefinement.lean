/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeAtomicOwner
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticEqualityStratum

/-!
# Game-facing refinement of the minimum semantic solo-owner row

The unique-positive-debtor branch of the minimum terminal-semantic stratum
contains a positive-hazard solo-owner row.  This file compares that row with
the genuinely stationary row whose continuation is the owner's singleton
reward vector.

There are only two outcomes.  If the row is still endpoint Nash against the
singleton vector, it is the already classified atomic owner branch: in a
counterexample the owner's singleton payoff is quantitatively negative and
lies strictly below its punishment value.  Otherwise a concrete outsider
blocks stationary closure.  For that outsider the exact affine row lies
strictly above the owner's solo payoff but weakly below the current Continue
endpoint.  Consequently the owner has positive Continue mass and the
outsider's current declared continuation lies strictly above the payoff it
would receive from the owner's solo exit.

This is a finite game-facing alternative.  It does not realize a semantic
carrier point by one behavior profile and does not identify the blocking
outsider with the possibly different outsider whose singleton payoff makes
all-Continue fail.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

omit [Fintype ι] in
/-- If an inactive outsider's singleton strictly dominates its declared tail
but its endpoint inequality is maintained by a genuine solo-owner hazard,
then collision with the owner must be strictly worse for that outsider than
the owner's solo exit. -/
theorem quittingSingletonCollisionReward_lt_soloReward_of_soloEndpoint
    (owner outsider : ι) (hazard : PMF Bool) (tail : Payoff ι)
    (hquit : 0 < (hazard true).toReal)
    (hcontinue : 0 < (hazard false).toReal)
    (hgain : tail outsider <
      quittingSoloReward reward outsider outsider)
    (hendpoint :
      (hazard false).toReal *
            quittingSoloReward reward outsider outsider +
          (hazard true).toReal *
            quittingSingletonCollisionReward reward owner outsider ≤
        (hazard true).toReal *
            quittingSoloReward reward owner outsider +
          (hazard false).toReal * tail outsider) :
    quittingSingletonCollisionReward reward owner outsider <
      quittingSoloReward reward owner outsider := by
  have hweightedGain :
      (hazard false).toReal * tail outsider <
        (hazard false).toReal *
          quittingSoloReward reward outsider outsider :=
    mul_lt_mul_of_pos_left hgain hcontinue
  have hweightedCollision :
      (hazard true).toReal *
          quittingSingletonCollisionReward reward owner outsider <
        (hazard true).toReal *
          quittingSoloReward reward owner outsider := by
    linarith
  exact lt_of_mul_lt_mul_left hweightedCollision hquit.le

/-- **Solo-owner closure refinement.**  At a positive minimum semantic-debt
coordinate, either all-Continue is an exact semantic self-loop, or there is
a unique positive-debt owner and an attractive-singleton outsider.  In the
latter branch, the selected solo row either closes at the owner's singleton
vector, landing in the quantitative isolated-negative branch, or a second
(possibly equal) outsider witnesses the exact affine failure of that closure.
-/
theorem QuittingCounterexampleRegime.minimumTerminalSemantic_soloOwner_refinement
    (regime : QuittingCounterexampleRegime reward)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hmin : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hnash : IsεQuittingRootNash reward pair.1 0 root)
    (first : ι) (hfirst : 0 < quittingTerminalSemanticDebt pair first) :
    (IsεQuittingRootNash reward pair.1 0
          (quittingAllContinueRoot : ι → PMF Bool) ∧
        quittingTerminalSemanticPrefix reward quittingAllContinueRoot pair =
          pair) ∨
      ∃ owner gainWitness,
        0 < quittingTerminalSemanticDebt pair owner ∧
        (∀ player, 0 < quittingTerminalSemanticDebt pair player →
          player = owner) ∧
        gainWitness ≠ owner ∧
        pair.1 gainWitness <
          quittingSoloReward reward gainWitness gainWitness ∧
        0 < (root owner true).toReal ∧
        quittingSoloReward reward owner owner = pair.1 owner ∧
        (∀ player, player ≠ owner → root player = PMF.pure false) ∧
        ((quittingSoloReward reward owner owner ≤ -regime.terminalGap ∧
            quittingSoloReward reward owner owner <
              quittingPunishmentValue reward owner) ∨
          ∃ blocker, blocker ≠ owner ∧
            quittingSoloReward reward owner blocker <
              (root owner false).toReal *
                  quittingSoloReward reward blocker blocker +
                (root owner true).toReal *
                  quittingSingletonCollisionReward reward owner blocker ∧
            (root owner false).toReal *
                  quittingSoloReward reward blocker blocker +
                (root owner true).toReal *
                    quittingSingletonCollisionReward reward owner blocker ≤
              (root owner true).toReal *
                  quittingSoloReward reward owner blocker +
                (root owner false).toReal * pair.1 blocker ∧
            quittingSoloReward reward owner blocker < pair.1 blocker ∧
            0 < (root owner false).toReal ∧
            (blocker ≠ gainWitness ∨
              quittingSingletonCollisionReward reward owner blocker <
                quittingSoloReward reward owner blocker) ∧
            quittingSingletonCollisionReward reward owner gainWitness <
              quittingSoloReward reward owner gainWitness) := by
  rcases quittingTerminalSemantic_minimum_stratum_alternative
      reward pair root hM hreward hpair hmin hnash first hfirst with
    hall | ⟨owner, gainWitness, howner, hunique, hgainNe, hgain,
      hownerQuit, hownerTight, hpure, houtsiderEndpoint⟩
  · exact Or.inl hall
  · refine Or.inr ⟨owner, gainWitness, howner, hunique, hgainNe, ?_,
      hownerQuit, ?_, hpure, ?_⟩
    · simpa [quittingSoloReward, quittingSingletonTerminal] using hgain
    · simpa [quittingSoloReward, quittingSingletonTerminal] using hownerTight
    let hazard : PMF Bool := root owner
    have hroot : root = quittingSoloStationaryRoot owner hazard := by
      exact eq_quittingSoloStationaryRoot_of_others_continue hpure
    have hhazardPositive : 0 < (hazard true).toReal := by
      simpa only [hazard] using hownerQuit
    by_cases hsolo : IsεQuittingRootEndpointNash reward
        (quittingSoloReward reward owner) 0 root
    · have hsolo' : IsεQuittingRootEndpointNash reward
          (quittingSoloReward reward owner) 0
          (quittingSoloStationaryRoot owner hazard) := by
        simpa only [hroot] using hsolo
      exact Or.inl
        ⟨regime.soloReward_le_neg_terminalGap_of_soloEndpointNash
            owner hazard hhazardPositive hsolo',
          regime.soloReward_lt_punishmentValue_of_soloEndpointNash
            owner hazard hhazardPositive hsolo'⟩
    · have hnotInactive : ¬ ∀ blocker, blocker ≠ owner →
          (hazard false).toReal *
                quittingSoloReward reward blocker blocker +
              (hazard true).toReal *
                quittingSingletonCollisionReward reward owner blocker ≤
            quittingSoloReward reward owner blocker := by
        intro hinactive
        apply hsolo
        rw [hroot]
        exact isεQuittingRootEndpointNash_soloStationaryRoot
          reward owner hazard hinactive
      push Not at hnotInactive
      obtain ⟨blocker, hblockerNe, hstrict⟩ := hnotInactive
      have hcurrent := houtsiderEndpoint blocker hblockerNe
      rw [hroot,
        quittingRootQuitPayoff_soloStationaryRoot_other reward hblockerNe,
        quittingRootContinuePayoff_soloStationaryRoot_other reward
          hblockerNe] at hcurrent
      have hmass := quittingSoloHazardMass_add hazard
      have hcontinueNonneg : 0 ≤ (hazard false).toReal :=
        ENNReal.toReal_nonneg
      have hcontinuePositive : 0 < (hazard false).toReal := by
        by_contra hnotPositive
        have hzero : (hazard false).toReal = 0 :=
          le_antisymm (le_of_not_gt hnotPositive) hcontinueNonneg
        have hone : (hazard true).toReal = 1 := by linarith
        simp only [hzero, hone, zero_mul, one_mul, zero_add, add_zero] at hstrict hcurrent
        linarith
      have htailStrict :
          quittingSoloReward reward owner blocker < pair.1 blocker := by
        have hcombined : quittingSoloReward reward owner blocker <
            (hazard true).toReal *
                quittingSoloReward reward owner blocker +
              (hazard false).toReal * pair.1 blocker :=
          hstrict.trans_le hcurrent
        have hidentity :
            (hazard true).toReal *
                  quittingSoloReward reward owner blocker +
                (hazard false).toReal * pair.1 blocker -
              quittingSoloReward reward owner blocker =
            (hazard false).toReal *
              (pair.1 blocker -
                quittingSoloReward reward owner blocker) := by
          calc
            _ = (hazard true).toReal *
                    quittingSoloReward reward owner blocker +
                  (hazard false).toReal * pair.1 blocker -
                ((hazard false).toReal + (hazard true).toReal) *
                  quittingSoloReward reward owner blocker := by
                    rw [hmass]
                    ring
            _ = _ := by ring
        have hproduct : 0 < (hazard false).toReal *
            (pair.1 blocker - quittingSoloReward reward owner blocker) := by
          rw [← hidentity]
          exact sub_pos.mpr hcombined
        rcases (mul_pos_iff.mp hproduct) with hpositive | hnegative
        · exact sub_pos.mp hpositive.2
        · exact False.elim ((not_lt_of_ge hcontinueNonneg) hnegative.1)
      have hseparation : blocker ≠ gainWitness ∨
          quittingSingletonCollisionReward reward owner blocker <
            quittingSoloReward reward owner blocker := by
        by_cases hdistinct : blocker ≠ gainWitness
        · exact Or.inl hdistinct
        · right
          have heq : blocker = gainWitness := not_ne_iff.mp hdistinct
          subst blocker
          exact quittingSingletonCollisionReward_lt_soloReward_of_soloEndpoint
            owner gainWitness hazard pair.1 hhazardPositive
              hcontinuePositive (by
                simpa [quittingSoloReward, quittingSingletonTerminal] using
                  hgain) hcurrent
      have hgainEndpoint := houtsiderEndpoint gainWitness hgainNe
      rw [hroot,
        quittingRootQuitPayoff_soloStationaryRoot_other reward hgainNe,
        quittingRootContinuePayoff_soloStationaryRoot_other reward
          hgainNe] at hgainEndpoint
      have hgainCollision :
          quittingSingletonCollisionReward reward owner gainWitness <
            quittingSoloReward reward owner gainWitness :=
        quittingSingletonCollisionReward_lt_soloReward_of_soloEndpoint
          owner gainWitness hazard pair.1 hhazardPositive hcontinuePositive
            (by
              simpa [quittingSoloReward, quittingSingletonTerminal] using
                hgain) hgainEndpoint
      exact Or.inr ⟨blocker, hblockerNe,
        by simpa only [hazard] using hstrict,
        by simpa only [hazard] using hcurrent,
        htailStrict, by simpa only [hazard] using hcontinuePositive,
        hseparation, hgainCollision⟩

end GameTheory
