/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentTwoOwnerSupport
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentSupportLiftFarkas

/-!
# Exact integration of the compatible two-owner singular chart

When the two directed pair-join effects vanish, the zero Jacobian in the
first radial blow-up is not evidence for a hidden second-order obstruction.
It integrates exactly. A product root supported on the two declared owners
has no triple or higher quitting coalition at all. Each active pure-Quit
payoff is its pinned singleton value, and Bellman elimination makes the
corresponding pure-Continue payoff equal to the same value.

Thus every such root with nonzero survival lies on an exact rational
Nash--Bellman solution manifold for the two active rows. Inactive-owner Nash
signs and continuation floor/upper-box bounds remain separate, explicit
gates. The results below supply one exact edge; they do not construct a
return, a lasso, or a solved cycle.
-/

noncomputable section

namespace GameTheory

open Finset Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A hazard row supported on two declared owners. -/
def quittingTwoOwnerHazard (first second : ι)
    (firstHazard secondHazard : ℝ) : ι → ℝ :=
  quittingTwoOwnerLeadingVariation first second ![firstHazard, secondHazard]

omit [Fintype ι] in
@[simp] theorem quittingTwoOwnerHazard_first
    (first second : ι) (firstHazard secondHazard : ℝ) :
    quittingTwoOwnerHazard first second firstHazard secondHazard first =
      firstHazard := by
  simp [quittingTwoOwnerHazard]

omit [Fintype ι] in
@[simp] theorem quittingTwoOwnerHazard_second
    (first second : ι) (firstHazard secondHazard : ℝ)
    (hne : first ≠ second) :
    quittingTwoOwnerHazard first second firstHazard secondHazard second =
      secondHazard := by
  simp [quittingTwoOwnerHazard, hne]

omit [Fintype ι] in
theorem quittingTwoOwnerHazard_eq_zero_of_ne
    (first second owner : ι) (firstHazard secondHazard : ℝ)
    (hfirst : owner ≠ first) (hsecond : owner ≠ second) :
    quittingTwoOwnerHazard first second firstHazard secondHazard owner = 0 := by
  simp [quittingTwoOwnerHazard, quittingTwoOwnerLeadingVariation,
    hfirst, hsecond]

/-- Forcing `first` to quit against a two-owner row mixes only its singleton
reward and the pair reward with `second`. -/
theorem sigmaValue_twoOwner_first
    (first second : ι) (firstHazard secondHazard : ℝ)
    (hne : first ≠ second) :
    sigmaValue (weightOfReward reward)
        (quittingTwoOwnerHazard first second firstHazard secondHazard) first =
      (1 - secondHazard) *
          reward (quittingSingletonTerminal first) first +
        secondHazard * reward (quittingPairJoinTerminal first second) first := by
  let opponents := Finset.univ.erase first
  let x := quittingTwoOwnerHazard first second firstHazard secondHazard
  let term : Finset ι → ℝ := fun J =>
    (∏ j ∈ J, x j) * (∏ j ∈ opponents \ J, (1 - x j)) *
      weightOfReward reward (insert first J) first
  have hempty : (∅ : Finset ι) ∈ opponents.powerset :=
    Finset.empty_mem_powerset _
  have hsecondMem : ({second} : Finset ι) ∈ opponents.powerset.erase ∅ := by
    simp [opponents, hne.symm]
  have hrest :
      (∑ J ∈ opponents.powerset.erase (∅ : Finset ι), term J) =
        term {second} := by
    apply Finset.sum_eq_single ({second} : Finset ι)
    · intro J hJ hJsecond
      have hsubset : J ⊆ opponents :=
        Finset.mem_powerset.mp (Finset.mem_erase.mp hJ).2
      have hnonempty : J.Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hJ).1
      have hnotsubset : ¬J ⊆ ({second} : Finset ι) := by
        intro hsub
        have hsecondJ : second ∈ J := by
          obtain ⟨owner, howner⟩ := hnonempty
          have heq : owner = second := by simpa using hsub howner
          simpa [heq] using howner
        have hEq : J = {second} :=
          Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hsecondJ)
        exact hJsecond hEq
      obtain ⟨owner, hownerJ, hownerSecond⟩ :=
        Finset.not_subset.mp hnotsubset
      have hownerFirst : owner ≠ first := by
        exact (Finset.mem_erase.mp (hsubset hownerJ)).1
      have hxzero : x owner = 0 :=
        quittingTwoOwnerHazard_eq_zero_of_ne first second owner
          firstHazard secondHazard hownerFirst (by simpa using hownerSecond)
      have hprod : (∏ j ∈ J, x j) = 0 :=
        Finset.prod_eq_zero hownerJ hxzero
      simp [term, hprod]
    · exact fun hnot => (hnot hsecondMem).elim
  have hprodOpponents :
      (∏ owner ∈ opponents, (1 - x owner)) = 1 - secondHazard := by
    have hxsecond : x second = secondHazard := by
      simp [x, hne]
    rw [← hxsecond]
    apply Finset.prod_eq_single second
    · intro owner howner hownerSecond
      have hownerFirst : owner ≠ first := (Finset.mem_erase.mp howner).1
      have hxzero := quittingTwoOwnerHazard_eq_zero_of_ne first second owner
        firstHazard secondHazard hownerFirst hownerSecond
      change x owner = 0 at hxzero
      rw [hxzero]
      ring
    · intro hsecond
      exact (hsecond (by simp [opponents, hne.symm])).elim
  have hprodOutside :
      (∏ owner ∈ opponents \ ({second} : Finset ι), (1 - x owner)) = 1 := by
    apply Finset.prod_eq_one
    intro owner howner
    have hownerFirst : owner ≠ first := by
      exact (Finset.mem_erase.mp (Finset.mem_sdiff.mp howner).1).1
    have hownerSecond : owner ≠ second := by
      simpa using (Finset.mem_sdiff.mp howner).2
    have hxzero := quittingTwoOwnerHazard_eq_zero_of_ne first second owner
      firstHazard secondHazard hownerFirst hownerSecond
    change x owner = 0 at hxzero
    rw [hxzero]
    ring
  unfold sigmaValue
  change (∑ J ∈ opponents.powerset, term J) = _
  rw [← Finset.add_sum_erase opponents.powerset term hempty, hrest]
  change term ∅ + term {second} = _
  simp only [term, Finset.prod_empty, one_mul,
    Finset.prod_singleton]
  rw [Finset.sdiff_empty, hprodOpponents, hprodOutside]
  simp [x,
    quittingTwoOwnerHazard, quittingTwoOwnerLeadingVariation, hne.symm,
    weightOfReward, quittingSingletonTerminal, quittingPairJoinTerminal]

omit [Fintype ι] in
theorem quittingTwoOwnerHazard_swap
    (first second : ι) (firstHazard secondHazard : ℝ)
    (hne : first ≠ second) :
    quittingTwoOwnerHazard second first secondHazard firstHazard =
      quittingTwoOwnerHazard first second firstHazard secondHazard := by
  funext owner
  by_cases hfirst : owner = first
  · subst owner
    rw [quittingTwoOwnerHazard_second second first secondHazard firstHazard
      hne.symm, quittingTwoOwnerHazard_first]
  · by_cases hsecond : owner = second
    · subst owner
      rw [quittingTwoOwnerHazard_first,
        quittingTwoOwnerHazard_second first second firstHazard secondHazard hne]
    · simp [quittingTwoOwnerHazard, quittingTwoOwnerLeadingVariation,
        hfirst, hsecond]

/-- Symmetric active Quit formula for the second owner. -/
theorem sigmaValue_twoOwner_second
    (first second : ι) (firstHazard secondHazard : ℝ)
    (hne : first ≠ second) :
    sigmaValue (weightOfReward reward)
        (quittingTwoOwnerHazard first second firstHazard secondHazard) second =
      (1 - firstHazard) *
          reward (quittingSingletonTerminal second) second +
        firstHazard * reward (quittingPairJoinTerminal second first) second := by
  rw [← quittingTwoOwnerHazard_swap first second firstHazard secondHazard hne]
  exact sigmaValue_twoOwner_first second first secondHazard firstHazard hne.symm

/-- When the first owner continues, the only nonempty absorbing coalition
with nonzero probability is the second owner's singleton. -/
theorem excludedValue_twoOwner_first
    (first second : ι) (firstHazard secondHazard : ℝ)
    (hne : first ≠ second) :
    excludedValue (weightOfReward reward)
        (quittingTwoOwnerHazard first second firstHazard secondHazard) first =
      secondHazard * reward (quittingSingletonTerminal second) first := by
  let opponents := Finset.univ.erase first
  let x := quittingTwoOwnerHazard first second firstHazard secondHazard
  let term : Finset ι → ℝ := fun J =>
    (∏ j ∈ J, x j) * (∏ j ∈ opponents \ J, (1 - x j)) *
      weightOfReward reward J first
  have hsecondMem : ({second} : Finset ι) ∈ opponents.powerset.erase ∅ := by
    simp [opponents, hne.symm]
  have hsum :
      (∑ J ∈ opponents.powerset.erase (∅ : Finset ι), term J) =
        term {second} := by
    apply Finset.sum_eq_single ({second} : Finset ι)
    · intro J hJ hJsecond
      have hsubset : J ⊆ opponents :=
        Finset.mem_powerset.mp (Finset.mem_erase.mp hJ).2
      have hnonempty : J.Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hJ).1
      have hnotsubset : ¬J ⊆ ({second} : Finset ι) := by
        intro hsub
        obtain ⟨owner, howner⟩ := hnonempty
        have heq : owner = second := by simpa using hsub howner
        have hsecondJ : second ∈ J := by simpa [heq] using howner
        exact hJsecond <| Finset.Subset.antisymm hsub
          (Finset.singleton_subset_iff.mpr hsecondJ)
      obtain ⟨owner, hownerJ, hownerSecond⟩ :=
        Finset.not_subset.mp hnotsubset
      have hownerFirst : owner ≠ first :=
        (Finset.mem_erase.mp (hsubset hownerJ)).1
      have hxzero : x owner = 0 :=
        quittingTwoOwnerHazard_eq_zero_of_ne first second owner
          firstHazard secondHazard hownerFirst (by simpa using hownerSecond)
      have hprod : (∏ j ∈ J, x j) = 0 :=
        Finset.prod_eq_zero hownerJ hxzero
      simp [term, hprod]
    · exact fun hnot => (hnot hsecondMem).elim
  have hprodOutside :
      (∏ owner ∈ opponents \ ({second} : Finset ι), (1 - x owner)) = 1 := by
    apply Finset.prod_eq_one
    intro owner howner
    have hownerFirst : owner ≠ first :=
      (Finset.mem_erase.mp (Finset.mem_sdiff.mp howner).1).1
    have hownerSecond : owner ≠ second := by
      simpa using (Finset.mem_sdiff.mp howner).2
    have hxzero := quittingTwoOwnerHazard_eq_zero_of_ne first second owner
      firstHazard secondHazard hownerFirst hownerSecond
    change x owner = 0 at hxzero
    rw [hxzero]
    ring
  unfold excludedValue
  change (∑ J ∈ opponents.powerset.erase (∅ : Finset ι), term J) = _
  rw [hsum]
  simp only [term, Finset.prod_singleton]
  rw [hprodOutside]
  simp [x, hne, weightOfReward, quittingSingletonTerminal]

/-- Symmetric excluded-value formula for the second owner. -/
theorem excludedValue_twoOwner_second
    (first second : ι) (firstHazard secondHazard : ℝ)
    (hne : first ≠ second) :
    excludedValue (weightOfReward reward)
        (quittingTwoOwnerHazard first second firstHazard secondHazard) second =
      firstHazard * reward (quittingSingletonTerminal first) second := by
  rw [← quittingTwoOwnerHazard_swap first second firstHazard secondHazard hne]
  exact excludedValue_twoOwner_first second first secondHazard firstHazard hne.symm

/-- Only the other declared owner contributes to the excluded continue mass. -/
theorem continueMassExcl_twoOwner_first
    (first second : ι) (firstHazard secondHazard : ℝ)
    (hne : first ≠ second) :
    continueMassExcl
        (quittingTwoOwnerHazard first second firstHazard secondHazard) first =
      1 - secondHazard := by
  let opponents := Finset.univ.erase first
  let x := quittingTwoOwnerHazard first second firstHazard secondHazard
  unfold continueMassExcl
  change (∏ owner ∈ opponents, (1 - x owner)) = _
  have hxsecond : x second = secondHazard := by simp [x, hne]
  rw [← hxsecond]
  apply Finset.prod_eq_single second
  · intro owner howner hownerSecond
    have hownerFirst : owner ≠ first := (Finset.mem_erase.mp howner).1
    have hxzero := quittingTwoOwnerHazard_eq_zero_of_ne first second owner
      firstHazard secondHazard hownerFirst hownerSecond
    change x owner = 0 at hxzero
    rw [hxzero]
    ring
  · intro hsecond
    exact (hsecond (by simp [opponents, hne.symm])).elim

theorem continueMassExcl_twoOwner_second
    (first second : ι) (firstHazard secondHazard : ℝ)
    (hne : first ≠ second) :
    continueMassExcl
        (quittingTwoOwnerHazard first second firstHazard secondHazard) second =
      1 - firstHazard := by
  rw [← quittingTwoOwnerHazard_swap first second firstHazard secondHazard hne]
  exact continueMassExcl_twoOwner_first second first secondHazard firstHazard hne.symm

/-- The joint survival factor of a two-owner row. -/
theorem continueMass_twoOwner
    (first second : ι) (firstHazard secondHazard : ℝ)
    (hne : first ≠ second) :
    continueMass
        (quittingTwoOwnerHazard first second firstHazard secondHazard) =
      (1 - firstHazard) * (1 - secondHazard) := by
  unfold continueMass
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ first)]
  change continueMassExcl
      (quittingTwoOwnerHazard first second firstHazard secondHazard) first *
        (1 - quittingTwoOwnerHazard first second firstHazard secondHazard first) = _
  rw [continueMassExcl_twoOwner_first first second firstHazard secondHazard hne]
  simp [quittingTwoOwnerHazard]
  ring

/-- Bellman-eliminated continuation at a root with nonzero joint survival. -/
def quittingTwoOwnerBellmanContinuation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (boundary : Payoff ι) (root : ι → PMF Bool) : Payoff ι :=
  fun who =>
    (boundary who - quittingRootAbsorbingContribution reward root who) /
      quittingStationaryContinueMass root

omit [DecidableEq ι] in
/-- Bellman elimination is exact whenever the root has nonzero joint
survival. -/
theorem boundary_eq_successor_twoOwnerBellmanContinuation
    (boundary : Payoff ι) (root : ι → PMF Bool)
    (hsurvival : quittingStationaryContinueMass root ≠ 0) :
    boundary = quittingRootSuccessorPayoff reward
      (quittingTwoOwnerBellmanContinuation reward boundary root) root := by
  funext who
  rw [quittingRootSuccessorPayoff_apply_eq_affine]
  unfold quittingTwoOwnerBellmanContinuation
  field_simp
  ring

/-- Under a zero directed pair-join effect, the first owner's pure-Quit
endpoint is its pinned boundary for every two-owner hazard pair. -/
theorem quittingRootQuitPayoff_eq_boundary_twoOwner_first
    (boundary : Payoff ι) (root : ι → PMF Bool)
    (first second : ι) (firstHazard secondHazard : ℝ)
    (hne : first ≠ second)
    (hroot : hazardOfRoot root =
      quittingTwoOwnerHazard first second firstHazard secondHazard)
    (hpin : boundary first =
      reward (quittingSingletonTerminal first) first)
    (hjoin : quittingActiveMixingPairJoinEffect reward first second = 0) :
    quittingRootQuitPayoff reward
        (quittingTwoOwnerBellmanContinuation reward boundary root) root first =
      boundary first := by
  rw [quittingRootQuitPayoff_eq_sigmaValue, hroot,
    sigmaValue_twoOwner_first first second firstHazard secondHazard hne]
  unfold quittingActiveMixingPairJoinEffect at hjoin
  have hpair := sub_eq_zero.mp hjoin
  rw [hpair]
  rw [hpin]
  ring

/-- Symmetric pure-Quit endpoint identity for the second owner. -/
theorem quittingRootQuitPayoff_eq_boundary_twoOwner_second
    (boundary : Payoff ι) (root : ι → PMF Bool)
    (first second : ι) (firstHazard secondHazard : ℝ)
    (hne : first ≠ second)
    (hroot : hazardOfRoot root =
      quittingTwoOwnerHazard first second firstHazard secondHazard)
    (hpin : boundary second =
      reward (quittingSingletonTerminal second) second)
    (hjoin : quittingActiveMixingPairJoinEffect reward second first = 0) :
    quittingRootQuitPayoff reward
        (quittingTwoOwnerBellmanContinuation reward boundary root) root second =
      boundary second := by
  rw [quittingRootQuitPayoff_eq_sigmaValue, hroot,
    sigmaValue_twoOwner_second first second firstHazard secondHazard hne]
  unfold quittingActiveMixingPairJoinEffect at hjoin
  have hpair := sub_eq_zero.mp hjoin
  rw [hpair]
  rw [hpin]
  ring

/-- Bellman equality plus a boundary-valued Quit endpoint forces zero gain
whenever Continue has positive probability. -/
theorem gainValue_eq_zero_of_boundary_eq_successor_of_quit_eq_boundary
    (boundary : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hbellman : boundary = quittingRootSuccessorPayoff reward
      (quittingTwoOwnerBellmanContinuation reward boundary root) root)
    (hquit : quittingRootQuitPayoff reward
      (quittingTwoOwnerBellmanContinuation reward boundary root) root who =
        boundary who)
    (hcontinuePos : 0 < (root who false).toReal) :
    gainValue (weightOfReward reward) (hazardOfRoot root) who
      (quittingTwoOwnerBellmanContinuation reward boundary root who) = 0 := by
  let continuation := quittingTwoOwnerBellmanContinuation reward boundary root
  have hmix := quittingRootSuccessorPayoff_eq_endpointMix
    reward continuation root who
  rw [← congrFun hbellman who, hquit] at hmix
  have hprob := quittingRoot_continueProbability_add_quitProbability root who
  have hproduct : (root who false).toReal *
      (quittingRootContinuePayoff reward continuation root who -
        boundary who) = 0 := by
    linear_combination -hmix - boundary who * hprob
  have hcontinue : quittingRootContinuePayoff reward continuation root who =
      boundary who := by
    exact sub_eq_zero.mp <|
      (mul_eq_zero.mp hproduct).resolve_left hcontinuePos.ne'
  rw [← quittingRootEndpointDifference_eq_gainValue]
  unfold quittingRootEndpointDifference
  rw [hquit, hcontinue]
  ring

/-- The compatible two-owner singular chart closes both active rows exactly.
This is the core producer: inactive-owner Nash signs and continuation bounds
are not hypotheses because they are not needed for active closure. -/
theorem twoOwnerBellmanContinuation_activeExact
    (boundary : Payoff ι) (root : ι → PMF Bool)
    (first second : ι) (firstHazard secondHazard : ℝ)
    (hne : first ≠ second)
    (hroot : hazardOfRoot root =
      quittingTwoOwnerHazard first second firstHazard secondHazard)
    (hfirst_lt_one : firstHazard < 1)
    (hsecond_lt_one : secondHazard < 1)
    (hsurvival : quittingStationaryContinueMass root ≠ 0)
    (hpinFirst : boundary first =
      reward (quittingSingletonTerminal first) first)
    (hpinSecond : boundary second =
      reward (quittingSingletonTerminal second) second)
    (hjoinFirst : quittingActiveMixingPairJoinEffect reward first second = 0)
    (hjoinSecond : quittingActiveMixingPairJoinEffect reward second first = 0) :
    boundary = quittingRootSuccessorPayoff reward
        (quittingTwoOwnerBellmanContinuation reward boundary root) root ∧
      gainValue (weightOfReward reward) (hazardOfRoot root) first
          (quittingTwoOwnerBellmanContinuation reward boundary root first) = 0 ∧
      gainValue (weightOfReward reward) (hazardOfRoot root) second
          (quittingTwoOwnerBellmanContinuation reward boundary root second) = 0 := by
  have hbellman := boundary_eq_successor_twoOwnerBellmanContinuation
    (reward := reward) boundary root hsurvival
  have hquitFirst := quittingRootQuitPayoff_eq_boundary_twoOwner_first
    (reward := reward) boundary root first second firstHazard secondHazard hne
      hroot hpinFirst hjoinFirst
  have hquitSecond := quittingRootQuitPayoff_eq_boundary_twoOwner_second
    (reward := reward) boundary root first second firstHazard secondHazard hne
      hroot hpinSecond hjoinSecond
  have htrueFirst : (root first true).toReal = firstHazard := by
    change hazardOfRoot root first = firstHazard
    rw [hroot]
    simp
  have htrueSecond : (root second true).toReal = secondHazard := by
    change hazardOfRoot root second = secondHazard
    rw [hroot]
    simp [hne]
  have hcontinueFirst : 0 < (root first false).toReal := by
    have hprob := quittingRoot_continueProbability_add_quitProbability root first
    linarith
  have hcontinueSecond : 0 < (root second false).toReal := by
    have hprob := quittingRoot_continueProbability_add_quitProbability root second
    linarith
  exact ⟨hbellman,
    gainValue_eq_zero_of_boundary_eq_successor_of_quit_eq_boundary
      boundary root first hbellman hquitFirst hcontinueFirst,
    gainValue_eq_zero_of_boundary_eq_successor_of_quit_eq_boundary
      boundary root second hbellman hquitSecond hcontinueSecond⟩

/-- On the two active coordinates, Bellman elimination reduces to the simple
rational formulas obtained by conditioning on whether the other owner quits. -/
theorem twoOwnerBellmanContinuation_active_formula
    (boundary : Payoff ι) (root : ι → PMF Bool)
    (first second : ι) (firstHazard secondHazard : ℝ)
    (hne : first ≠ second)
    (hroot : hazardOfRoot root =
      quittingTwoOwnerHazard first second firstHazard secondHazard)
    (hfirst_lt_one : firstHazard < 1)
    (hsecond_lt_one : secondHazard < 1)
    (hsurvival : quittingStationaryContinueMass root ≠ 0)
    (hpinFirst : boundary first =
      reward (quittingSingletonTerminal first) first)
    (hpinSecond : boundary second =
      reward (quittingSingletonTerminal second) second)
    (hjoinFirst : quittingActiveMixingPairJoinEffect reward first second = 0)
    (hjoinSecond : quittingActiveMixingPairJoinEffect reward second first = 0) :
    quittingTwoOwnerBellmanContinuation reward boundary root first =
        (boundary first - secondHazard *
          reward (quittingSingletonTerminal second) first) /
          (1 - secondHazard) ∧
      quittingTwoOwnerBellmanContinuation reward boundary root second =
        (boundary second - firstHazard *
          reward (quittingSingletonTerminal first) second) /
          (1 - firstHazard) := by
  rcases twoOwnerBellmanContinuation_activeExact
      (reward := reward) boundary root first second firstHazard secondHazard hne
        hroot hfirst_lt_one hsecond_lt_one hsurvival hpinFirst hpinSecond
        hjoinFirst hjoinSecond with ⟨_, hgainFirst, hgainSecond⟩
  have hsigmaFirst : sigmaValue (weightOfReward reward) (hazardOfRoot root) first =
      boundary first := by
    rw [hroot, sigmaValue_twoOwner_first first second firstHazard secondHazard hne]
    unfold quittingActiveMixingPairJoinEffect at hjoinFirst
    rw [sub_eq_zero.mp hjoinFirst, hpinFirst]
    ring
  have hsigmaSecond : sigmaValue (weightOfReward reward) (hazardOfRoot root) second =
      boundary second := by
    rw [hroot, sigmaValue_twoOwner_second first second firstHazard secondHazard hne]
    unfold quittingActiveMixingPairJoinEffect at hjoinSecond
    rw [sub_eq_zero.mp hjoinSecond, hpinSecond]
    ring
  constructor
  · apply (eq_div_iff (by linarith : 1 - secondHazard ≠ 0)).2
    unfold gainValue gammaValue at hgainFirst
    rw [hsigmaFirst, hroot,
      excludedValue_twoOwner_first first second firstHazard secondHazard hne,
      continueMassExcl_twoOwner_first first second firstHazard secondHazard hne]
      at hgainFirst
    linarith
  · apply (eq_div_iff (by linarith : 1 - firstHazard ≠ 0)).2
    unfold gainValue gammaValue at hgainSecond
    rw [hsigmaSecond, hroot,
      excludedValue_twoOwner_second first second firstHazard secondHazard hne,
      continueMassExcl_twoOwner_second first second firstHazard secondHazard hne]
      at hgainSecond
    linarith

/-- **Exact two-owner singular root.**  Once both directed pair-join effects
vanish, the zero support Jacobian integrates exactly: every two-owner root
with positive joint survival has a Bellman-eliminated continuation on which
both active gains vanish.  Only the inactive owners' gain signs remain as
explicit hypotheses. -/
theorem isNashBellmanRoot_twoOwner_of_pairJoin_zero
    (boundary : Payoff ι) (root : ι → PMF Bool)
    (first second : ι) (firstHazard secondHazard : ℝ)
    (hne : first ≠ second)
    (hroot : hazardOfRoot root =
      quittingTwoOwnerHazard first second firstHazard secondHazard)
    (hfirst_lt_one : firstHazard < 1)
    (hsecond_lt_one : secondHazard < 1)
    (hsurvival : quittingStationaryContinueMass root ≠ 0)
    (hpinFirst : boundary first =
      reward (quittingSingletonTerminal first) first)
    (hpinSecond : boundary second =
      reward (quittingSingletonTerminal second) second)
    (hjoinFirst : quittingActiveMixingPairJoinEffect reward first second = 0)
    (hjoinSecond : quittingActiveMixingPairJoinEffect reward second first = 0)
    (houtside : ∀ who, who ≠ first → who ≠ second →
      gainValue (weightOfReward reward) (hazardOfRoot root) who
        (quittingTwoOwnerBellmanContinuation reward boundary root who) ≤ 0) :
    boundary = quittingRootSuccessorPayoff reward
        (quittingTwoOwnerBellmanContinuation reward boundary root) root ∧
      IsεQuittingRootEndpointNash reward
        (quittingTwoOwnerBellmanContinuation reward boundary root) 0 root := by
  have hbellman := boundary_eq_successor_twoOwnerBellmanContinuation
    (reward := reward) boundary root hsurvival
  have hquitFirst := quittingRootQuitPayoff_eq_boundary_twoOwner_first
    (reward := reward) boundary root first second firstHazard secondHazard hne
      hroot hpinFirst hjoinFirst
  have hquitSecond := quittingRootQuitPayoff_eq_boundary_twoOwner_second
    (reward := reward) boundary root first second firstHazard secondHazard hne
      hroot hpinSecond hjoinSecond
  have htrueFirst : (root first true).toReal = firstHazard := by
    change hazardOfRoot root first = firstHazard
    rw [hroot]
    simp
  have htrueSecond : (root second true).toReal = secondHazard := by
    change hazardOfRoot root second = secondHazard
    rw [hroot]
    simp [hne]
  have hcontinueFirst : 0 < (root first false).toReal := by
    have hprob := quittingRoot_continueProbability_add_quitProbability root first
    linarith
  have hcontinueSecond : 0 < (root second false).toReal := by
    have hprob := quittingRoot_continueProbability_add_quitProbability root second
    linarith
  have hgainFirst : gainValue (weightOfReward reward) (hazardOfRoot root) first
      (quittingTwoOwnerBellmanContinuation reward boundary root first) = 0 :=
    gainValue_eq_zero_of_boundary_eq_successor_of_quit_eq_boundary
      boundary root first hbellman hquitFirst hcontinueFirst
  have hgainSecond : gainValue (weightOfReward reward) (hazardOfRoot root) second
      (quittingTwoOwnerBellmanContinuation reward boundary root second) = 0 :=
    gainValue_eq_zero_of_boundary_eq_successor_of_quit_eq_boundary
      boundary root second hbellman hquitSecond hcontinueSecond
  refine ⟨hbellman, ?_⟩
  rw [← isExactRowComplementary_hazardOfRoot_iff reward
    (quittingTwoOwnerBellmanContinuation reward boundary root) root]
  intro who
  by_cases hwhoFirst : who = first
  · subst who
    exact ⟨fun _ => hgainFirst.ge, fun _ => hgainFirst.le⟩
  · by_cases hwhoSecond : who = second
    · subst who
      exact ⟨fun _ => hgainSecond.ge, fun _ => hgainSecond.le⟩
    · have hzero : hazardOfRoot root who = 0 := by
        rw [hroot]
        exact quittingTwoOwnerHazard_eq_zero_of_ne first second who
          firstHazard secondHazard hwhoFirst hwhoSecond
      exact ⟨fun hpositive => by simp [hzero] at hpositive,
        fun _ => houtside who hwhoFirst hwhoSecond⟩

/-- The exact two-owner continuation satisfies the frozen-root lift system
when the remaining outsider, floor, and upper-box gates are supplied. -/
theorem isQuittingFrozenRootContinuationLift_twoOwner_of_pairJoin_zero
    (boundary floor : Payoff ι) (upper : ℝ) (root : ι → PMF Bool)
    (first second : ι) (firstHazard secondHazard : ℝ)
    (hne : first ≠ second)
    (hroot : hazardOfRoot root =
      quittingTwoOwnerHazard first second firstHazard secondHazard)
    (hfirst_lt_one : firstHazard < 1)
    (hsecond_lt_one : secondHazard < 1)
    (hsurvival : quittingStationaryContinueMass root ≠ 0)
    (hpinFirst : boundary first =
      reward (quittingSingletonTerminal first) first)
    (hpinSecond : boundary second =
      reward (quittingSingletonTerminal second) second)
    (hjoinFirst : quittingActiveMixingPairJoinEffect reward first second = 0)
    (hjoinSecond : quittingActiveMixingPairJoinEffect reward second first = 0)
    (houtside : ∀ who, who ≠ first → who ≠ second →
      gainValue (weightOfReward reward) (hazardOfRoot root) who
        (quittingTwoOwnerBellmanContinuation reward boundary root who) ≤ 0)
    (hfloor : ∀ who, floor who ≤
      quittingTwoOwnerBellmanContinuation reward boundary root who)
    (hupper : ∀ who,
      quittingTwoOwnerBellmanContinuation reward boundary root who ≤ upper) :
    IsQuittingFrozenRootContinuationLift reward boundary floor upper root
      {first, second}
      (quittingTwoOwnerBellmanContinuation reward boundary root) := by
  rcases twoOwnerBellmanContinuation_activeExact
      (reward := reward) boundary root first second firstHazard secondHazard hne
        hroot hfirst_lt_one hsecond_lt_one hsurvival hpinFirst hpinSecond
        hjoinFirst hjoinSecond with ⟨hbellman, hgainFirst, hgainSecond⟩
  refine ⟨hbellman, ?_, ?_, hfloor, hupper⟩
  · intro who hwho
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwho
    rcases hwho with rfl | rfl
    · rw [← quittingRootEndpointDifference_eq_mobiusCoordinateDerivative,
        quittingRootEndpointDifference_eq_gainValue]
      exact hgainFirst
    · rw [← quittingRootEndpointDifference_eq_mobiusCoordinateDerivative,
        quittingRootEndpointDifference_eq_gainValue]
      exact hgainSecond
  · intro who hwho
    have hwhoFirst : who ≠ first := by
      intro heq
      subst who
      exact hwho (by simp)
    have hwhoSecond : who ≠ second := by
      intro heq
      subst who
      exact hwho (by simp)
    rw [← quittingRootEndpointDifference_eq_mobiusCoordinateDerivative,
      quittingRootEndpointDifference_eq_gainValue]
    exact houtside who hwhoFirst hwhoSecond

/-- With strictly positive hazards on both declared owners, the exact lift is
one genuine Nash--Bellman edge. The explicit floor/box assumptions certify
admissibility of its continuation, but this theorem does not produce a
return edge or a cycle. -/
theorem isQuittingNashBellmanEdge_twoOwner_of_pairJoin_zero
    (boundary floor : Payoff ι) (upper : ℝ) (root : ι → PMF Bool)
    (first second : ι) (firstHazard secondHazard : ℝ)
    (hne : first ≠ second)
    (hroot : hazardOfRoot root =
      quittingTwoOwnerHazard first second firstHazard secondHazard)
    (hfirst_pos : 0 < firstHazard) (hfirst_lt_one : firstHazard < 1)
    (hsecond_pos : 0 < secondHazard) (hsecond_lt_one : secondHazard < 1)
    (hsurvival : quittingStationaryContinueMass root ≠ 0)
    (hpinFirst : boundary first =
      reward (quittingSingletonTerminal first) first)
    (hpinSecond : boundary second =
      reward (quittingSingletonTerminal second) second)
    (hjoinFirst : quittingActiveMixingPairJoinEffect reward first second = 0)
    (hjoinSecond : quittingActiveMixingPairJoinEffect reward second first = 0)
    (houtside : ∀ who, who ≠ first → who ≠ second →
      gainValue (weightOfReward reward) (hazardOfRoot root) who
        (quittingTwoOwnerBellmanContinuation reward boundary root who) ≤ 0)
    (hfloor : ∀ who, floor who ≤
      quittingTwoOwnerBellmanContinuation reward boundary root who)
    (hupper : ∀ who,
      quittingTwoOwnerBellmanContinuation reward boundary root who ≤ upper)
    (tailRoot : QuittingRootSimplex ι) :
    IsQuittingNashBellmanEdge reward
      (boundary, quittingFrozenRootLiftSimplex root)
      (quittingTwoOwnerBellmanContinuation reward boundary root, tailRoot) := by
  have hlift :=
    isQuittingFrozenRootContinuationLift_twoOwner_of_pairJoin_zero
      (reward := reward) boundary floor upper root first second
        firstHazard secondHazard hne hroot hfirst_lt_one hsecond_lt_one
        hsurvival hpinFirst hpinSecond hjoinFirst hjoinSecond houtside
        hfloor hupper
  apply isQuittingNashBellmanEdge_of_frozenRootContinuationLift
    boundary floor upper root {first, second}
      (quittingTwoOwnerBellmanContinuation reward boundary root) hlift
  · constructor
    · intro who hwho
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwho
      rcases hwho with rfl | rfl
      · rw [hroot]
        simp [hfirst_pos, hfirst_lt_one]
      · rw [hroot]
        simp [hne, hsecond_pos, hsecond_lt_one]
    · intro who hwho
      rw [hroot]
      apply quittingTwoOwnerHazard_eq_zero_of_ne first second who
        firstHazard secondHazard
      · intro heq
        subst who
        exact hwho (by simp)
      · intro heq
        subst who
        exact hwho (by simp)

end GameTheory
