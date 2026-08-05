import GameTheory.Concepts.Stochastic.QuittingPositiveDynamicDebtProvenance

/-!
# Separating the preterminal clock from the final terminal atom

The residual-depth-one packet controls a product of two probabilities: the
opponent survival product strictly before the last live root and the mass of
one complete opponent action at that last root.  Since both factors lie in
`[0,1]`, the same packet estimate lower-bounds each factor separately.  This
is the corrected finite-chain datum; it does not fold the final root into the
preterminal opponent clock.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Positive initial exact debt selects a terminal full action for which the
preterminal survival and final action mass are separately nonvanishing at the
same linear scale. -/
theorem exists_finiteDynamicDebt_separatedTerminalAnchor_quantitative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (last : ℕ) (path : QuittingFiniteNashBellmanPath ι (last + 1))
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward (last + 1))
    (owner : ι)
    (hpositive : 0 < quittingFiniteNashBellmanPathDynamicDebt
      reward (last + 1) path owner 0) :
    ∃ action : ι → Bool,
      let survival := quittingOpponentSurvivalWeight
        (quittingFiniteNashBellmanPathRoots (last + 1) path) owner 0 last
      let mass := ((pmfPi (Function.update
        (quittingFiniteNashBellmanPathRoots (last + 1) path last)
          owner (PMF.pure false))) action).toReal
      let advantage := quittingTerminalOpponentAdvantage reward owner action
      0 < survival ∧ survival ≤ 1 ∧
      0 < mass ∧ mass ≤ 1 ∧
      action owner = false ∧
      (quittingQuitters action).Nonempty ∧
      0 < advantage ∧
      quittingFiniteNashBellmanPathDynamicDebt
          reward (last + 1) path owner 0 ≤
        (Fintype.card (ι → Bool) : ℝ) * (survival * mass) * advantage ∧
      quittingFiniteNashBellmanPathDynamicDebt
          reward (last + 1) path owner 0 ≤
        2 * quittingRewardBound reward *
          (Fintype.card (ι → Bool) : ℝ) * survival ∧
      quittingFiniteNashBellmanPathDynamicDebt
          reward (last + 1) path owner 0 ≤
        2 * quittingRewardBound reward *
          (Fintype.card (ι → Bool) : ℝ) * mass := by
  obtain ⟨action, hproduct, hadvantage, hweighted, hraw⟩ :=
    exists_finiteDynamicDebt_lastAtom_quantitative
      reward last path hpath owner hpositive
  let roots := quittingFiniteNashBellmanPathRoots (last + 1) path
  let survival := quittingOpponentSurvivalWeight roots owner 0 last
  let mass := ((pmfPi (Function.update (roots last)
    owner (PMF.pure false))) action).toReal
  have hsurvival0 : 0 < survival :=
    pos_of_mul_pos_left hproduct ENNReal.toReal_nonneg
  have hmass0 : 0 < mass :=
    pos_of_mul_pos_right hproduct
      (quittingOpponentSurvivalWeight_nonneg roots owner 0 last)
  have hsurvival1 : survival ≤ 1 :=
    quittingOpponentSurvivalWeight_le_one roots owner 0 last
  have hmass1 : mass ≤ 1 := by
    exact ENNReal.toReal_mono ENNReal.one_ne_top
      (PMF.coe_le_one
        (pmfPi (Function.update (roots last) owner (PMF.pure false))) action)
  have hsupport : action ∈
      (pmfPi (Function.update (roots last)
        owner (PMF.pure false))).support := by
    rw [PMF.mem_support_iff]
    intro hzero
    have : mass = 0 := by simp [mass, hzero]
    linarith
  have hownerFalse : action owner = false :=
    action_eq_false_of_mem_support_pmfPi_update_pure_false
      (roots last) owner action hsupport
  have hquitters : (quittingQuitters action).Nonempty := by
    by_contra hnot
    have hempty : quittingQuitters action = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnot
    have hadvantageZero :
        quittingTerminalOpponentAdvantage reward owner action = 0 := by
      unfold quittingTerminalOpponentAdvantage quittingRootPayoff
      rw [quittingQuitters_update_true_of_apply_false action owner]
      simp [hempty, quittingSingletonTerminal]
    linarith
  have hconstant0 :
      0 ≤ 2 * quittingRewardBound reward *
        (Fintype.card (ι → Bool) : ℝ) := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (quittingRewardBound_nonneg reward))
      (Nat.cast_nonneg _)
  have hproductLeSurvival : survival * mass ≤ survival :=
    mul_le_of_le_one_right (le_of_lt hsurvival0) hmass1
  have hproductLeMass : survival * mass ≤ mass :=
    mul_le_of_le_one_left (le_of_lt hmass0) hsurvival1
  refine ⟨action, hsurvival0, hsurvival1, hmass0, hmass1,
    hownerFalse, hquitters, hadvantage, hweighted, ?_, ?_⟩
  · exact hraw.trans (mul_le_mul_of_nonneg_left
      hproductLeSurvival hconstant0)
  · exact hraw.trans (mul_le_mul_of_nonneg_left
      hproductLeMass hconstant0)

end GameTheory
