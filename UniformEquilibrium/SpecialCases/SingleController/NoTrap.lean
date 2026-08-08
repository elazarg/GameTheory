/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.SpecialCases.SingleController.Basic

/-!
# No-trap extraction for the Vrieze single-controller LP

This file closes the game-specific policy-improvement part of the
single-controller residual.

For a strongly complementary Vrieze primal--dual pair, let `R` be the states
with positive total dual occupation mass.  If a state could not reach `R`
through any pure controller-action support edge, the set of all such states
would be closed under every controller action.  Strong complementarity makes
every primal bias row on that zero-occupation set strictly slack.  Finiteness
therefore supplies one common positive slack margin.  Raising the primal gain
by half that margin on the closed set preserves every gain and bias row while
strictly improving the objective, contradicting primal--dual optimality.

The conclusion is support-graph reachability to `R`.  It does not yet turn a
completed policy into a mean-ergodic transience/projection statement; that is
the next, genuinely probabilistic, step.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability

variable {G : StochasticGame Bool} [Finite G.State]
  [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)]

/-- A strongly complementary Vrieze pair has no controller-support trap
outside its positive dual-occupation support. -/
theorem all_canReach_vriezeOccupationSupport_of_strongComplementary
    {controller : Bool} (hSC : G.IsSingleController controller)
    {q : VriezeCol G controller → ℝ}
    {w : VriezeRow G controller → ℝ}
    (hstrong : Math.LinearProgramming.IsStrongComplementaryPair
      (G.vriezeA controller) (G.vriezeB controller)
        (G.vriezeC controller) q w) :
    ∀ source : G.State,
      FiniteReachability.CanReachSet (G.controllerSucc controller)
        (G.vriezeOccupationSupport controller
          (G.vriezeDualZ controller w)) source := by
  classical
  let R : G.State → Prop :=
    G.vriezeOccupationSupport controller (G.vriezeDualZ controller w)
  let Succ : G.State → G.State → Prop := G.controllerSucc controller
  let bad : G.State → Prop := fun state =>
    ¬ FiniteReachability.CanReachSet Succ R state
  by_contra hall
  push Not at hall
  obtain ⟨badState, hbadState⟩ := hall
  change bad badState at hbadState
  have hbad_not_R : ∀ {state : G.State}, bad state → ¬ R state := by
    intro state hbad hR
    exact hbad ⟨state, hR, Relation.ReflTransGen.refl⟩
  have hbad_closed : ∀ {source destination : G.State},
      bad source → Succ source destination → bad destination := by
    intro source destination hsource hstep
    exact (FiniteReachability.trap_closed_of_not_canReachSet
      Succ R (hbad_not_R hsource) hsource hstep).2
  have hkernel_pure : ∀ (source : G.State) (action : G.Act controller),
      G.controllerKernel controller (fun _ => PMF.pure action) source =
        G.transition source
          (G.jointOfControllerAct controller action) := by
    intro source action
    rw [G.controllerKernel_eq_bind hSC
      (fun _ => PMF.pure action) source
      (G.jointOfControllerAct controller action), PMF.pure_bind]
    congr 1
    have hupdate := Function.update_eq_self controller
      (G.jointOfControllerAct controller action)
    rwa [G.jointOfControllerAct_apply_self] at hupdate
  have hbad_of_transProb_pos : ∀ {source destination : G.State}
      (action : G.Act controller), bad source →
      0 < G.transProb controller source action destination →
      bad destination := by
    intro source destination action hsource hpositive
    apply hbad_closed hsource
    refine ⟨action, ?_⟩
    rw [PMF.mem_support_iff, hkernel_pure source action]
    intro hzero
    simp [transProb, hzero] at hpositive
  let indicator : G.State → ℝ := fun state => if bad state then 1 else 0
  have hindicator_nonneg : ∀ state, 0 ≤ indicator state := by
    intro state
    simp only [indicator]
    split <;> norm_num
  have htransProb_nonneg : ∀ source (action : G.Act controller) destination,
      0 ≤ G.transProb controller source action destination := by
    intro source action destination
    exact ENNReal.toReal_nonneg
  have hindicator_expect_bad : ∀ source (action : G.Act controller),
      bad source →
      (∑ destination, G.transProb controller source action destination *
        indicator destination) = 1 := by
    intro source action hsource
    calc
      (∑ destination, G.transProb controller source action destination *
          indicator destination) =
          ∑ destination, G.transProb controller source action destination := by
        apply Finset.sum_congr rfl
        intro destination _
        by_cases hzero :
            G.transProb controller source action destination = 0
        · simp [hzero]
        · have hpositive :
              0 < G.transProb controller source action destination :=
            lt_of_le_of_ne
              (htransProb_nonneg source action destination)
              (Ne.symm hzero)
          have hdestination :=
            hbad_of_transProb_pos action hsource hpositive
          simp [indicator, hdestination]
      _ = 1 := by
        simpa [transProb] using
          pmf_toReal_sum_one
            (G.transition source
              (G.jointOfControllerAct controller action))
  have hindicator_expect_nonneg : ∀ source (action : G.Act controller),
      0 ≤ ∑ destination,
        G.transProb controller source action destination *
          indicator destination := by
    intro source action
    exact Finset.sum_nonneg fun destination _ =>
      mul_nonneg (htransProb_nonneg source action destination)
        (hindicator_nonneg destination)
  let biasSlack : G.State × G.Act controller → ℝ := fun pair =>
    Math.LinearProgramming.minPrimalSlack
      (G.vriezeA controller) (G.vriezeB controller) q
      (Sum.inr (Sum.inl pair))
  let guardedSlack : G.State × G.Act controller → ℝ := fun pair =>
    if bad pair.1 then biasSlack pair else 1
  let witnessPair : G.State × G.Act controller :=
    (badState, Classical.choice (inferInstance : Nonempty (G.Act controller)))
  have hpairs_nonempty :
      (Finset.univ : Finset (G.State × G.Act controller)).Nonempty :=
    ⟨witnessPair, Finset.mem_univ witnessPair⟩
  have hdualZ_zero_of_bad : ∀ (state : G.State), bad state →
      ∀ action : G.Act controller,
        G.vriezeDualZ controller w state action = 0 := by
    intro state hstate action
    have hmass_nonpos :
        (∑ candidate, G.vriezeDualZ controller w state candidate) ≤ 0 :=
      le_of_not_gt (hbad_not_R hstate)
    have hnonneg : ∀ candidate : G.Act controller,
        0 ≤ G.vriezeDualZ controller w state candidate := fun candidate =>
      hstrong.2.1.1 (Sum.inr (Sum.inl (state, candidate)))
    apply le_antisymm
    · exact (Finset.single_le_sum
        (fun candidate _ => hnonneg candidate)
        (Finset.mem_univ action)).trans hmass_nonpos
    · exact hnonneg action
  have hguardedSlack_pos : ∀ pair : G.State × G.Act controller,
      0 < guardedSlack pair := by
    intro pair
    by_cases hpair : bad pair.1
    · dsimp only [guardedSlack]
      rw [if_pos hpair]
      exact
        (hstrong.minPrimalSlack_pos_iff_dual_eq_zero
          (Sum.inr (Sum.inl pair))).2
          (hdualZ_zero_of_bad pair.1 hpair pair.2)
    · simp [guardedSlack, hpair]
  let margin : ℝ :=
    Finset.univ.inf' hpairs_nonempty guardedSlack
  have hmargin_pos : 0 < margin := by
    exact (Finset.lt_inf'_iff hpairs_nonempty).2 fun pair _ =>
      hguardedSlack_pos pair
  let epsilon : ℝ := margin / 2
  have hepsilon_pos : 0 < epsilon := by
    dsimp only [epsilon]
    linarith
  have hepsilon_le_slack : ∀ (state : G.State), bad state →
      ∀ action : G.Act controller,
        epsilon ≤ biasSlack (state, action) := by
    intro state hstate action
    have hmargin_le : margin ≤ guardedSlack (state, action) :=
      Finset.inf'_le guardedSlack (Finset.mem_univ (state, action))
    have hepsilon_le_margin : epsilon ≤ margin := by
      dsimp only [epsilon]
      linarith
    calc
      epsilon ≤ margin := hepsilon_le_margin
      _ ≤ guardedSlack (state, action) := hmargin_le
      _ = biasSlack (state, action) := by
        dsimp only [guardedSlack]
        rw [if_pos hstate]
  let decodedX : G.State → PMF (G.Act (!controller)) :=
    G.vriezeDecodeX controller q
  let decodedG : G.State → ℝ := G.vriezeDecodeG controller q
  let decodedV : G.State → ℝ := G.vriezeDecodeV controller q
  have hdecodeXVal_isProb : ∀ state : G.State,
      (∀ action, 0 ≤ G.vriezeDecodeXVal controller q state action) ∧
        (∑ action, G.vriezeDecodeXVal controller q state action) = 1 := by
    intro state
    refine ⟨fun action => hstrong.1.1 (Sum.inl (state, action)), ?_⟩
    have hpos := hstrong.1.2
      (Sum.inr (Sum.inr (Sum.inl state)))
    have hneg := hstrong.1.2
      (Sum.inr (Sum.inr (Sum.inr state)))
    rw [(G.rowEval_vriezeA_simplex controller q state).1] at hpos
    rw [(G.rowEval_vriezeA_simplex controller q state).2] at hneg
    simp only [vriezeB] at hpos hneg
    linarith
  have hdecodedX_toReal : ∀ (state : G.State)
      (action : G.Act (!controller)),
      ((decodedX state) action).toReal =
        G.vriezeDecodeXVal controller q state action := by
    intro state action
    dsimp only [decodedX]
    exact G.vriezeDecodeX_apply_toReal controller q state
      (hdecodeXVal_isProb state).1 (hdecodeXVal_isProb state).2 action
  let improvedG : G.State → ℝ := fun state =>
    decodedG state + epsilon * indicator state
  have hgain_improved : ∀ (state : G.State) (action : G.Act controller),
      improvedG state ≤
        ∑ destination,
          G.transProb controller state action destination *
            improvedG destination := by
    intro state action
    have hrow := hstrong.1.2 (Sum.inl (state, action))
    rw [G.rowEval_vriezeA_gain] at hrow
    simp only [vriezeB] at hrow
    have hexpand :
        (∑ destination,
          G.transProb controller state action destination *
            improvedG destination) =
          (∑ destination,
            G.transProb controller state action destination *
              decodedG destination) +
            epsilon *
              (∑ destination,
                G.transProb controller state action destination *
                  indicator destination) := by
      dsimp only [improvedG]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro destination _
      ring
    rw [hexpand]
    dsimp only [improvedG]
    by_cases hstate : bad state
    · rw [hindicator_expect_bad state action hstate]
      have hindicator_state : indicator state = 1 := by
        dsimp only [indicator]
        rw [if_pos hstate]
      rw [hindicator_state]
      linarith
    · have hnonneg := hindicator_expect_nonneg state action
      have hindicator_state : indicator state = 0 := by
        dsimp only [indicator]
        rw [if_neg hstate]
      rw [hindicator_state]
      linarith [mul_nonneg hepsilon_pos.le hnonneg]
  have hbias_improved : ∀ (state : G.State) (action : G.Act controller),
      improvedG state + decodedV state ≤
        (∑ opponentAction,
          ((decodedX state) opponentAction).toReal *
            G.rewardVal controller state opponentAction action) +
          ∑ destination,
            G.transProb controller state action destination *
              decodedV destination := by
    intro state action
    have hslack_nonneg := hstrong.1.2
      (Sum.inr (Sum.inl (state, action)))
    simp only [vriezeB] at hslack_nonneg
    have hbiasSlack_nonneg : 0 ≤ biasSlack (state, action) := by
      dsimp only [biasSlack, Math.LinearProgramming.minPrimalSlack]
      simpa only [vriezeB, sub_zero] using hslack_nonneg
    have hslack_eq : biasSlack (state, action) =
        (∑ opponentAction,
          ((decodedX state) opponentAction).toReal *
            G.rewardVal controller state opponentAction action) +
          (∑ destination,
            G.transProb controller state action destination *
              decodedV destination) - decodedG state - decodedV state := by
      dsimp only [biasSlack]
      rw [Math.LinearProgramming.minPrimalSlack,
        G.rowEval_vriezeA_bias]
      simp only [vriezeB, sub_zero, hdecodedX_toReal]
      rfl
    have hincrement_le : epsilon * indicator state ≤
        biasSlack (state, action) := by
      by_cases hstate : bad state
      · simp only [indicator, if_pos hstate, mul_one]
        exact hepsilon_le_slack state hstate action
      · simp only [indicator, if_neg hstate, mul_zero]
        exact hbiasSlack_nonneg
    dsimp only [improvedG]
    rw [hslack_eq] at hincrement_le
    linarith
  let improvedPoint : VriezeCol G controller → ℝ :=
    G.vriezeEncode controller decodedX improvedG decodedV
  have himproved_feasible :
      Math.LinearProgramming.MinPrimalFeasible
        (G.vriezeA controller) (G.vriezeB controller) improvedPoint := by
    refine ⟨?_, ?_⟩
    · rintro (⟨state, action⟩ | state | state | state | state) <;>
        simp [improvedPoint, vriezeEncode, ENNReal.toReal_nonneg]
    · rintro (⟨state, action⟩ | ⟨state, action⟩ | state | state)
      · dsimp only [improvedPoint]
        rw [G.rowEval_vriezeA_vriezeEncode_gain]
        change (0 : ℝ) ≤ _
        linarith [hgain_improved state action]
      · dsimp only [improvedPoint]
        rw [G.rowEval_vriezeA_vriezeEncode_bias]
        change (0 : ℝ) ≤ _
        linarith [hbias_improved state action]
      · change (1 : ℝ) ≤ Math.LinearProgramming.rowEval
          (G.vriezeA controller) improvedPoint
            (Sum.inr (Sum.inr (Sum.inl state)))
        rw [(G.rowEval_vriezeA_simplex controller improvedPoint state).1]
        dsimp only [improvedPoint]
        simp only [G.vriezeDecodeXVal_vriezeEncode]
        exact le_of_eq (pmf_toReal_sum_one (decodedX state)).symm
      · change (-1 : ℝ) ≤ Math.LinearProgramming.rowEval
          (G.vriezeA controller) improvedPoint
            (Sum.inr (Sum.inr (Sum.inr state)))
        rw [(G.rowEval_vriezeA_simplex controller improvedPoint state).2]
        dsimp only [improvedPoint]
        simp only [G.vriezeDecodeXVal_vriezeEncode]
        rw [pmf_toReal_sum_one (decodedX state)]
  have hsum_indicator_pos :
      0 < ∑ state, epsilon * indicator state := by
    apply Finset.sum_pos'
    · intro state _
      exact mul_nonneg hepsilon_pos.le (hindicator_nonneg state)
    · refine ⟨badState, Finset.mem_univ badState, ?_⟩
      have hindicator_badState : indicator badState = 1 := by
        dsimp only [indicator]
        rw [if_pos hbadState]
      rw [hindicator_badState, mul_one]
      exact hepsilon_pos
  have hsum_gain_lt :
      (∑ state, decodedG state) < ∑ state, improvedG state := by
    have hexpand :
        (∑ state, improvedG state) =
          (∑ state, decodedG state) +
            ∑ state, epsilon * indicator state := by
      dsimp only [improvedG]
      exact Finset.sum_add_distrib
    rw [hexpand]
    linarith
  have himproved_value_lt :
      Math.LinearProgramming.minPrimalValue (G.vriezeC controller)
          improvedPoint <
        Math.LinearProgramming.minPrimalValue (G.vriezeC controller) q := by
    rw [G.minPrimalValue_vriezeC_eq,
      G.minPrimalValue_vriezeC_eq]
    simp only [improvedPoint, G.vriezeDecodeG_vriezeEncode]
    exact neg_lt_neg hsum_gain_lt
  have hoptimal :
      Math.LinearProgramming.minPrimalValue (G.vriezeC controller) q ≤
        Math.LinearProgramming.minPrimalValue (G.vriezeC controller)
          improvedPoint := by
    calc
      Math.LinearProgramming.minPrimalValue (G.vriezeC controller) q =
          Math.LinearProgramming.maxDualValue (G.vriezeB controller) w :=
        hstrong.2.2.1
      _ ≤ Math.LinearProgramming.minPrimalValue (G.vriezeC controller)
          improvedPoint :=
        Math.LinearProgramming.min_weak_duality
          himproved_feasible hstrong.2.1
  exact (not_lt_of_ge hoptimal) himproved_value_lt

/-- Primal optimality therefore supplies a strongly complementary pair whose
positive occupation support is reachable from every state. -/
theorem exists_vriezeStrongComplementaryPair_noTrap
    [Nonempty G.State] {controller : Bool}
    (hSC : G.IsSingleController controller)
    {x : G.State → PMF (G.Act (!controller))} {g v : G.State → ℝ}
    (hopt : G.IsVriezePrimalOptimal controller x g v) :
    ∃ (q : VriezeCol G controller → ℝ)
        (w : VriezeRow G controller → ℝ),
      Math.LinearProgramming.IsStrongComplementaryPair
          (G.vriezeA controller) (G.vriezeB controller)
            (G.vriezeC controller) q w ∧
        ∀ source : G.State,
          FiniteReachability.CanReachSet (G.controllerSucc controller)
            (G.vriezeOccupationSupport controller
              (G.vriezeDualZ controller w)) source := by
  obtain ⟨q, w, hstrong⟩ :=
    G.exists_vriezeStrongComplementaryPair_of_vriezePrimalOptimal hSC hopt
  exact ⟨q, w, hstrong,
    G.all_canReach_vriezeOccupationSupport_of_strongComplementary
      hSC hstrong⟩

end StochasticGame
end GameTheory
