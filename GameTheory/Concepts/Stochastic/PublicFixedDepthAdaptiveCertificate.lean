/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.FixedDepthAdaptivePotentialSplice

/-!
# Adaptive certificates after a finite public selection prefix

This file removes the numerical packaging from the fixed-depth splice.
Given child certificates at half the requested error, exact preservation of
the parent target by a deviation-safe selector, and exact terminal entry,
finiteness supplies uniform payoff and child-potential bounds.  An
Archimedean accounting horizon absorbs the finite selection cost.

The resulting theorem returns the existing adaptive-potential certificate
interface at the parent state and target.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability

variable {ι Child : Type} {G : StochasticGame ι}

/-- A finite sum of absolute stage payoffs is a uniform nonnegative payoff
bound. -/
def finiteStagePayoffBound
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)] :
    ℝ := by
  classical
  letI : Fintype G.State := Fintype.ofFinite G.State
  letI : Fintype G.JointAct := Fintype.ofFinite G.JointAct
  exact
    Finset.univ.sum fun state : G.State =>
      Finset.univ.sum fun action : G.JointAct =>
        Finset.univ.sum fun who : ι =>
          |G.stagePayoff state action who|

theorem finiteStagePayoffBound_nonneg
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)] :
    0 ≤ G.finiteStagePayoffBound := by
  classical
  unfold finiteStagePayoffBound
  positivity

theorem abs_stagePayoff_le_finiteStagePayoffBound
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    (state : G.State) (action : G.JointAct) (who : ι) :
    |G.stagePayoff state action who| ≤
      G.finiteStagePayoffBound := by
  classical
  letI : Fintype G.State := Fintype.ofFinite G.State
  letI : Fintype G.JointAct := Fintype.ofFinite G.JointAct
  unfold finiteStagePayoffBound
  calc
    |G.stagePayoff state action who| ≤
        ∑ candidate : ι, |G.stagePayoff state action candidate| := by
      apply Finset.single_le_sum
        (s := Finset.univ)
        (f := fun candidate : ι =>
          |G.stagePayoff state action candidate|)
      · intro candidate _
        exact abs_nonneg _
      · exact Finset.mem_univ who
    _ ≤
        ∑ candidate : G.JointAct,
          ∑ player : ι, |G.stagePayoff state candidate player| := by
      apply Finset.single_le_sum
        (s := Finset.univ)
        (f := fun candidate : G.JointAct =>
          ∑ player : ι, |G.stagePayoff state candidate player|)
      · intro candidate _
        exact Finset.sum_nonneg fun player _ =>
          abs_nonneg (G.stagePayoff state candidate player)
      · exact Finset.mem_univ action
    _ ≤
        ∑ candidate : G.State,
          ∑ joint : G.JointAct,
            ∑ player : ι, |G.stagePayoff candidate joint player| := by
      apply Finset.single_le_sum
        (s := Finset.univ)
        (f := fun candidate : G.State =>
          ∑ joint : G.JointAct,
            ∑ player : ι, |G.stagePayoff candidate joint player|)
      · intro candidate _
        exact Finset.sum_nonneg fun joint _ =>
          Finset.sum_nonneg fun player _ =>
            abs_nonneg (G.stagePayoff candidate joint player)
      · exact Finset.mem_univ state

namespace FiniteChildAdaptivePotentialFamily

variable [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ who, Finite (G.Act who)] [Fintype Child]
  {entry : Child → G.State} {target : Child → Payoff ι}
  {error : ℝ}

/-- A finite sum of all three child initial potential magnitudes is a common
terminal-target bound for the splice. -/
def terminalPotentialBound
    (family :
      G.FiniteChildAdaptivePotentialFamily entry target error) :
    ℝ :=
  Finset.univ.sum fun child : Child =>
    Finset.univ.sum fun who : ι =>
      (|family.lowerTerminalTarget child who| +
        |family.upperTerminalTarget child who|) +
        |family.deviationTerminalTarget child who|

theorem terminalPotentialBound_nonneg
    (family :
      G.FiniteChildAdaptivePotentialFamily entry target error) :
    0 ≤ family.terminalPotentialBound := by
  unfold terminalPotentialBound
  positivity

private theorem component_le_terminalPotentialBound
    (family :
      G.FiniteChildAdaptivePotentialFamily entry target error)
    (component : Child → ι → ℝ)
    (hcomponent : ∀ child who,
      |component child who| ≤
        (|family.lowerTerminalTarget child who| +
          |family.upperTerminalTarget child who|) +
          |family.deviationTerminalTarget child who|)
    (child : Child) (who : ι) :
    |component child who| ≤ family.terminalPotentialBound := by
  calc
    |component child who| ≤
        (|family.lowerTerminalTarget child who| +
          |family.upperTerminalTarget child who|) +
          |family.deviationTerminalTarget child who| :=
      hcomponent child who
    _ ≤
        ∑ player : ι,
          ((|family.lowerTerminalTarget child player| +
            |family.upperTerminalTarget child player|) +
            |family.deviationTerminalTarget child player|) := by
      apply Finset.single_le_sum
        (s := Finset.univ)
        (f := fun player : ι =>
          (|family.lowerTerminalTarget child player| +
            |family.upperTerminalTarget child player|) +
            |family.deviationTerminalTarget child player|)
      · intro player _
        positivity
      · exact Finset.mem_univ who
    _ ≤ family.terminalPotentialBound := by
      unfold terminalPotentialBound
      apply Finset.single_le_sum
        (s := Finset.univ)
        (f := fun candidate : Child =>
          ∑ player : ι,
            ((|family.lowerTerminalTarget candidate player| +
              |family.upperTerminalTarget candidate player|) +
              |family.deviationTerminalTarget candidate player|))
      · intro candidate _
        exact Finset.sum_nonneg fun player _ => by positivity
      · exact Finset.mem_univ child

theorem abs_lowerTerminalTarget_le_terminalPotentialBound
    (family :
      G.FiniteChildAdaptivePotentialFamily entry target error)
    (child : Child) (who : ι) :
    |family.lowerTerminalTarget child who| ≤
      family.terminalPotentialBound := by
  apply family.component_le_terminalPotentialBound
  intro candidate player
  linarith [abs_nonneg (family.upperTerminalTarget candidate player),
    abs_nonneg (family.deviationTerminalTarget candidate player)]

theorem abs_upperTerminalTarget_le_terminalPotentialBound
    (family :
      G.FiniteChildAdaptivePotentialFamily entry target error)
    (child : Child) (who : ι) :
    |family.upperTerminalTarget child who| ≤
      family.terminalPotentialBound := by
  apply family.component_le_terminalPotentialBound
  intro candidate player
  linarith [abs_nonneg (family.lowerTerminalTarget candidate player),
    abs_nonneg (family.deviationTerminalTarget candidate player)]

theorem abs_deviationTerminalTarget_le_terminalPotentialBound
    (family :
      G.FiniteChildAdaptivePotentialFamily entry target error)
    (child : Child) (who : ι) :
    |family.deviationTerminalTarget child who| ≤
      family.terminalPotentialBound := by
  apply family.component_le_terminalPotentialBound
  intro candidate player
  linarith [abs_nonneg (family.lowerTerminalTarget candidate player),
    abs_nonneg (family.upperTerminalTarget candidate player)]

end FiniteChildAdaptivePotentialFamily

namespace FixedDepthAdaptivePotentialSplice

section FiniteChildFamily

variable [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ who, Finite (G.Act who)] [Fintype Child]
  {entry : Child → G.State} {target : Child → Payoff ι}
  {selector : DeviationSafePublicCoinSelector G Child}
  {selection : G.BehaviorProfile} {initial : G.State} {fuel : ℕ}

/-- Exact preservation of nominal child targets controls the expected
actual lower child initial potentials by the child certificate error. -/
theorem lower_parent_bound_of_exact_target
    {childError : ℝ}
    (family :
      G.FiniteChildAdaptivePotentialFamily entry target childError)
    (parentTarget : Payoff ι)
    (hexact : ∀ who,
      expect (selector.process.value initial)
        (fun child => target child who) = parentTarget who)
    (who : ι) :
    |expect (selector.process.value initial)
          (fun child => family.lowerTerminalTarget child who) -
        parentTarget who| ≤ childError := by
  rw [← hexact who, ← expect_sub]
  exact abs_expect_le_of_abs_le _ _ fun child =>
    (family.system child).lower_initial who

/-- The corresponding upper parent-target bound. -/
theorem upper_parent_bound_of_exact_target
    {childError : ℝ}
    (family :
      G.FiniteChildAdaptivePotentialFamily entry target childError)
    (parentTarget : Payoff ι)
    (hexact : ∀ who,
      expect (selector.process.value initial)
        (fun child => target child who) = parentTarget who)
    (who : ι) :
    |expect (selector.process.value initial)
          (fun child => family.upperTerminalTarget child who) -
        parentTarget who| ≤ childError := by
  rw [← hexact who, ← expect_sub]
  exact abs_expect_le_of_abs_le _ _ fun child =>
    (family.system child).upper_initial who

/-- The corresponding unilateral-deviation parent-target bound. -/
theorem deviation_parent_bound_of_exact_target
    {childError : ℝ}
    (family :
      G.FiniteChildAdaptivePotentialFamily entry target childError)
    (parentTarget : Payoff ι)
    (hexact : ∀ who,
      expect (selector.process.value initial)
        (fun child => target child who) = parentTarget who)
    (who : ι) :
    |expect (selector.process.value initial)
          (fun child => family.deviationTerminalTarget child who) -
        parentTarget who| ≤ childError := by
  rw [← hexact who, ← expect_sub]
  exact abs_expect_le_of_abs_le _ _ fun child =>
    (family.system child).deviation_initial who

end FiniteChildFamily

section FiniteChildren

variable [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ who, Finite (G.Act who)] [Finite Child]
  {entry : Child → G.State} {target : Child → Payoff ι}
  {selector : DeviationSafePublicCoinSelector G Child}
  {selection : G.BehaviorProfile} {initial : G.State} {fuel : ℕ}

/-- Child adaptive certificates at half the requested positive error,
together with exact public selection data, compile to a parent adaptive
certificate at the full requested error. -/
theorem isAdaptivePotentialCertificateAt_of_fixedDepthSelector
    (selection : G.BehaviorProfile)
    (parentTarget : Payoff ι) (error : ℝ) (herror : 0 < error)
    (hfuel : selector.process.rank initial ≤ fuel)
    (hentry : ∀ state, selector.process.terminal state →
      state = entry (selector.process.observe state))
    (hexact : ∀ who,
      expect (selector.process.value initial)
        (fun child => target child who) = parentTarget who)
    (childCertificates : ∀ child,
      G.IsAdaptivePotentialCertificateAt
        (entry child) (target child) (error / 2)) :
    G.IsAdaptivePotentialCertificateAt initial parentTarget error := by
  letI : Fintype Child := Fintype.ofFinite Child
  let family :
      G.FiniteChildAdaptivePotentialFamily entry target (error / 2) :=
    FiniteChildAdaptivePotentialFamily.ofCertificates childCertificates
  let splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel := {
    fuel_covers_rank := hfuel
    terminal_entry := hentry
  }
  let payoffBound := G.finiteStagePayoffBound
  let targetBound := family.terminalPotentialBound
  let prefixCost : ℝ :=
    (fuel : ℝ) * (payoffBound + targetBound)
  obtain ⟨rawHorizon, hrawHorizon⟩ :=
    exists_nat_gt (2 * prefixCost / error)
  let accountingHorizon : ℕ :=
    max 1 (max fuel rawHorizon)
  have haccountingPos : 0 < accountingHorizon := by
    exact lt_of_lt_of_le Nat.zero_lt_one
      (Nat.le_max_left 1 (max fuel rawHorizon))
  have hfuelAccounting : fuel ≤ accountingHorizon := by
    exact le_trans (Nat.le_max_left fuel rawHorizon)
      (Nat.le_max_right 1 (max fuel rawHorizon))
  have hrawAccounting :
      (rawHorizon : ℝ) ≤ accountingHorizon := by
    exact_mod_cast
      le_trans (Nat.le_max_right fuel rawHorizon)
        (Nat.le_max_right 1 (max fuel rawHorizon))
  have hprefixCost :
      prefixCost ≤ (accountingHorizon : ℝ) * (error / 2) := by
    have hscaled :
        2 * prefixCost < (rawHorizon : ℝ) * error := by
      exact (div_lt_iff₀ herror).mp hrawHorizon
    have hscaledAccounting :
        (rawHorizon : ℝ) * error ≤
          (accountingHorizon : ℝ) * error :=
      mul_le_mul_of_nonneg_right hrawAccounting herror.le
    linarith
  have bounds :
      splice.Bounds parentTarget error (error / 2)
        payoffBound targetBound accountingHorizon := {
    lower_parent := fun who =>
      (lower_parent_bound_of_exact_target
        (selector := selector) family parentTarget hexact who).trans
          (by linarith)
    upper_parent := fun who =>
      (upper_parent_bound_of_exact_target
        (selector := selector) family parentTarget hexact who).trans
          (by linarith)
    deviation_parent := fun who =>
      (deviation_parent_bound_of_exact_target
        (selector := selector) family parentTarget hexact who).trans
          (by linarith)
    payoff_bound := G.abs_stagePayoff_le_finiteStagePayoffBound
    lower_target_bound :=
      family.abs_lowerTerminalTarget_le_terminalPotentialBound
    upper_target_bound :=
      family.abs_upperTerminalTarget_le_terminalPotentialBound
    deviation_target_bound :=
      family.abs_deviationTerminalTarget_le_terminalPotentialBound
    payoffBound_nonneg := G.finiteStagePayoffBound_nonneg
    targetBound_nonneg := family.terminalPotentialBound_nonneg
    childError_nonneg := by linarith
    prefixError_nonneg := by linarith
    error_budget := by linarith
    accountingHorizon_pos := haccountingPos
    fuel_le_accountingHorizon := hfuelAccounting
    prefix_cost := by
      change prefixCost ≤
        (accountingHorizon : ℝ) * (error / 2)
      exact hprefixCost
  }
  exact
    (splice.toAdaptivePotentialSystemAt bounds).toIsAdaptivePotentialCertificateAt

/-- If child certificates are available at every positive accuracy, the
half-error premise of the fixed-depth constructor is automatic. -/
theorem isAdaptivePotentialCertificateAt_of_fixedDepthSelector_allErrors
    (selection : G.BehaviorProfile)
    (parentTarget : Payoff ι) (error : ℝ) (herror : 0 < error)
    (hfuel : selector.process.rank initial ≤ fuel)
    (hentry : ∀ state, selector.process.terminal state →
      state = entry (selector.process.observe state))
    (hexact : ∀ who,
      expect (selector.process.value initial)
        (fun child => target child who) = parentTarget who)
    (childCertificates : ∀ child childError, 0 < childError →
      G.IsAdaptivePotentialCertificateAt
        (entry child) (target child) childError) :
    G.IsAdaptivePotentialCertificateAt initial parentTarget error := by
  apply isAdaptivePotentialCertificateAt_of_fixedDepthSelector
    selection parentTarget error herror hfuel hentry hexact
  intro child
  exact childCertificates child (error / 2) (by linarith)

end FiniteChildren

end FixedDepthAdaptivePotentialSplice

end StochasticGame
end GameTheory
