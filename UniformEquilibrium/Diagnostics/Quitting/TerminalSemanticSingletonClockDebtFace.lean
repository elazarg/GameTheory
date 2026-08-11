/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDefectTelescope

/-!
# A singleton clock charges complementary semantic debt

At an actual live row, absorption by the singleton `{owner}` is opponent
absorption for every player other than `owner`.  Consequently the singleton
mass, weighted by all complementary shifted-tail debt, is bounded by the
same aggregate opponent-absorption charge used by the stopped defect/excess
telescope.

This is the occupation-level obstruction to Nashifying a diffuse singleton
clock.  Near the positive minimum fiber, a positive singleton clock can have
small all-player Nash defect only if its clock-weighted tails collapse toward
the corresponding debt vertex.  Control of one marked coordinate alone does
not pay the complementary-debt term.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- Total debt outside one displayed coordinate. -/
def quittingTerminalSemanticComplementaryDebt
    (pair : QuittingTerminalSemanticPair iota) (owner : iota) : ℝ :=
  ∑ who ∈ (Finset.univ : Finset iota).erase owner,
    quittingTerminalSemanticDebt pair who

/-- One actual singleton atom charges all shifted-tail debt outside its
owner to the aggregate opponent-absorption account on the same row. -/
theorem quittingStageSingletonMass_mul_tailComplementaryDebt_le_liveMass_mul_charge
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (owner : iota) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingStageCoalitionMass reward profile time
          (quittingSingletonTerminal owner) *
        quittingTerminalSemanticComplementaryDebt
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile (time + 1)))
          owner ≤
      quittingLiveMass reward profile time *
        quittingSpineOpponentAbsorptionDebtCharge reward profile time := by
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (time + 1))
  let root := quittingProfileLiveRoot reward profile time
  have htailCarrier : tail ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward _
  have htailDebt : ∀ who, 0 ≤ quittingTerminalSemanticDebt tail who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward htailCarrier
  have hcoordinate : ∀ who ∈ (Finset.univ : Finset iota).erase owner,
      quittingRootCoalitionMass root {owner} *
          quittingTerminalSemanticDebt tail who ≤
        quittingRootOpponentAbsorptionMass root who *
          quittingTerminalSemanticDebt tail who := by
    intro who hwho
    have hne : owner ≠ who := (Finset.mem_erase.mp hwho).1.symm
    exact mul_le_mul_of_nonneg_right
      (quittingRootCoalitionMass_le_opponentAbsorptionMass_of_other_mem
        root {owner} who owner (by simp) hne)
      (htailDebt who)
  have herase := Finset.sum_le_sum hcoordinate
  have hownerCharge : 0 ≤
      quittingRootOpponentAbsorptionMass root owner *
        quittingTerminalSemanticDebt tail owner :=
    mul_nonneg (quittingRootOpponentAbsorptionMass_nonneg root owner)
      (htailDebt owner)
  have heraseToFull :
      (∑ who ∈ (Finset.univ : Finset iota).erase owner,
          quittingRootOpponentAbsorptionMass root who *
            quittingTerminalSemanticDebt tail who) ≤
        ∑ who, quittingRootOpponentAbsorptionMass root who *
          quittingTerminalSemanticDebt tail who := by
    calc
      _ ≤ (∑ who ∈ (Finset.univ : Finset iota).erase owner,
            quittingRootOpponentAbsorptionMass root who *
              quittingTerminalSemanticDebt tail who) +
          quittingRootOpponentAbsorptionMass root owner *
            quittingTerminalSemanticDebt tail owner :=
        le_add_of_nonneg_right hownerCharge
      _ = _ := Finset.sum_erase_add _ _ (Finset.mem_univ owner)
  have hroot :
      quittingRootCoalitionMass root {owner} *
          quittingTerminalSemanticComplementaryDebt tail owner ≤
        quittingSpineOpponentAbsorptionDebtCharge reward profile time := by
    calc
      quittingRootCoalitionMass root {owner} *
          quittingTerminalSemanticComplementaryDebt tail owner =
        ∑ who ∈ (Finset.univ : Finset iota).erase owner,
          quittingRootCoalitionMass root {owner} *
            quittingTerminalSemanticDebt tail who := by
              rw [quittingTerminalSemanticComplementaryDebt,
                Finset.mul_sum]
      _ ≤ ∑ who ∈ (Finset.univ : Finset iota).erase owner,
          quittingRootOpponentAbsorptionMass root who *
            quittingTerminalSemanticDebt tail who := herase
      _ ≤ ∑ who, quittingRootOpponentAbsorptionMass root who *
          quittingTerminalSemanticDebt tail who := heraseToFull
      _ = quittingSpineOpponentAbsorptionDebtCharge reward profile time := by
        simp [quittingSpineOpponentAbsorptionDebtCharge, tail, root]
  have hlive := mul_le_mul_of_nonneg_left hroot
    (quittingLiveMass_nonneg reward profile time)
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass]
  change quittingLiveMass reward profile time *
      quittingRootCoalitionMass root {owner} *
        quittingTerminalSemanticComplementaryDebt tail owner ≤ _
  simpa only [mul_assoc] using hlive

/-- The singleton-clock complementary-debt occupation is bounded by the
same three stopped residuals as the aggregate charge: endpoint excess,
absorption-weighted tail excess, and total local Nash-defect occupation. -/
theorem sum_stageSingletonMass_mul_tailComplementaryDebt_le_stoppedDefectExcess
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : iota) (reference : ℝ) (cutoff : ℕ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    (∑ time ∈ Finset.range cutoff,
      quittingStageCoalitionMass reward profile time
          (quittingSingletonTerminal owner) *
        quittingTerminalSemanticComplementaryDebt
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile (time + 1)))
          owner) ≤
      quittingLiveMass reward profile cutoff *
          quittingSpineDebtExcess reward profile reference cutoff -
        quittingSpineDebtExcess reward profile reference 0 +
      (∑ time ∈ Finset.range cutoff,
        (quittingLiveMass reward profile time -
            quittingLiveMass reward profile (time + 1)) *
          quittingSpineDebtExcess reward profile reference (time + 1)) +
      ∑ time ∈ Finset.range cutoff,
        quittingLiveMass reward profile time *
          quittingSpineTotalNashDefect reward profile time := by
  have hmarked := Finset.sum_le_sum fun time
      (_htime : time ∈ Finset.range cutoff) =>
    quittingStageSingletonMass_mul_tailComplementaryDebt_le_liveMass_mul_charge
      reward profile time owner hM hreward
  exact hmarked.trans
    (sum_liveMass_mul_spineOpponentAbsorptionDebtCharge_le
      reward profile reference cutoff hM hreward)

/-- If every shifted tail stays within `epsilon` of the reference debt
level, the full singleton-clock complementary-debt occupation costs only one
`epsilon`, plus the all-player local Nash-defect occupation. -/
theorem sum_stageSingletonMass_mul_tailComplementaryDebt_le_epsilon_add_defect
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : iota) (reference epsilon : ℝ) (cutoff : ℕ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hinitial : 0 ≤ quittingSpineDebtExcess reward profile reference 0)
    (hnear : ∀ time ≤ cutoff,
      quittingSpineDebtExcess reward profile reference time ≤ epsilon) :
    (∑ time ∈ Finset.range cutoff,
      quittingStageCoalitionMass reward profile time
          (quittingSingletonTerminal owner) *
        quittingTerminalSemanticComplementaryDebt
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile (time + 1)))
          owner) ≤
      epsilon +
        ∑ time ∈ Finset.range cutoff,
          quittingLiveMass reward profile time *
            quittingSpineTotalNashDefect reward profile time := by
  have hmarked := Finset.sum_le_sum fun time
      (_htime : time ∈ Finset.range cutoff) =>
    quittingStageSingletonMass_mul_tailComplementaryDebt_le_liveMass_mul_charge
      reward profile time owner hM hreward
  exact hmarked.trans
    (sum_liveMass_mul_spineOpponentAbsorptionDebtCharge_le_epsilon_add_defect
      reward profile reference epsilon cutoff hM hreward hinitial hnear)

/-- Quantitative vertex-or-defect alternative on a singleton window.  If
all shifted tails in the window keep at least `faceFloor` debt outside the
singleton owner, then the whole singleton clock must be paid by the
all-player defect occupation (up to the one near-minimality error). -/
theorem faceFloor_mul_sum_stageSingletonMass_le_epsilon_add_defect
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : iota) (reference epsilon faceFloor : ℝ) (cutoff : ℕ)
    {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hinitial : 0 ≤ quittingSpineDebtExcess reward profile reference 0)
    (hnear : ∀ time ≤ cutoff,
      quittingSpineDebtExcess reward profile reference time ≤ epsilon)
    (hface : ∀ time < cutoff, faceFloor ≤
      quittingTerminalSemanticComplementaryDebt
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward profile (time + 1)))
        owner) :
    faceFloor *
        (∑ time ∈ Finset.range cutoff,
          quittingStageCoalitionMass reward profile time
            (quittingSingletonTerminal owner)) ≤
      epsilon +
        ∑ time ∈ Finset.range cutoff,
          quittingLiveMass reward profile time *
            quittingSpineTotalNashDefect reward profile time := by
  have hweighted :
      faceFloor *
          (∑ time ∈ Finset.range cutoff,
            quittingStageCoalitionMass reward profile time
              (quittingSingletonTerminal owner)) ≤
        ∑ time ∈ Finset.range cutoff,
          quittingStageCoalitionMass reward profile time
              (quittingSingletonTerminal owner) *
            quittingTerminalSemanticComplementaryDebt
              (quittingTerminalSemanticPair reward
                (quittingAllContinueProfileSpine reward profile (time + 1)))
              owner := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun time htime => by
      have hmass := quittingStageCoalitionMass_nonneg reward profile time
        (quittingSingletonTerminal owner)
      have hfaceTime := hface time (Finset.mem_range.mp htime)
      nlinarith
  exact hweighted.trans
    (sum_stageSingletonMass_mul_tailComplementaryDebt_le_epsilon_add_defect
      reward profile owner reference epsilon cutoff hM hreward hinitial hnear)

/-- If the finite singleton window has mass at least `clockMass`, the same
alternative has the explicit product `faceFloor * clockMass` on its left. -/
theorem faceFloor_mul_clockMass_le_epsilon_add_defect
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : iota)
    (reference epsilon faceFloor clockMass : ℝ) (cutoff : ℕ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hinitial : 0 ≤ quittingSpineDebtExcess reward profile reference 0)
    (hnear : ∀ time ≤ cutoff,
      quittingSpineDebtExcess reward profile reference time ≤ epsilon)
    (hfaceFloor : 0 ≤ faceFloor)
    (hface : ∀ time < cutoff, faceFloor ≤
      quittingTerminalSemanticComplementaryDebt
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward profile (time + 1)))
        owner)
    (hclock : clockMass ≤
      ∑ time ∈ Finset.range cutoff,
        quittingStageCoalitionMass reward profile time
          (quittingSingletonTerminal owner)) :
    faceFloor * clockMass ≤
      epsilon +
        ∑ time ∈ Finset.range cutoff,
          quittingLiveMass reward profile time *
            quittingSpineTotalNashDefect reward profile time := by
  have hscaled := mul_le_mul_of_nonneg_left hclock hfaceFloor
  exact hscaled.trans
    (faceFloor_mul_sum_stageSingletonMass_le_epsilon_add_defect
      reward profile owner reference epsilon faceFloor cutoff hM hreward
        hinitial hnear hface)

end GameTheory
