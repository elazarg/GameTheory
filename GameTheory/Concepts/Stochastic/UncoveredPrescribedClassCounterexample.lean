/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.ExplicitDomainGainBiasVerifier

/-!
# The two-node uncovered prescribed-class counterexample

This module formalizes the minimal two-node counterexample.  Player
one cannot leave the entry node while player two follows the prescription;
player two can deviate once and enter a second prescribed-absorbing node.
Player one's prescribed payoff is zero at the entry and one at the escaped
node, while the proposed target is zero everywhere.

The game API has state-independent action types, so player two's Boolean
action remains syntactically available at the escaped node; both choices have
the same absorbing transition and zero payoff there.  This is behaviorally the
state-dependent singleton action set of the underlying counterexample.

The support-pruned target, owner-occupation, and nonnegative prescribed
delivery checks all pass.  Nevertheless exact prescribed target delivery and
the prescribed Poisson equation fail when play is restarted at the escaped
node, which lies outside player one's arena.

The current `IsReachableCredibilityCriterion` deliberately supports its
prescribed stationary occupations only on `R.prescribed`.  Here that set is
the singleton entry node.  To match the counterexample's broader nonnegative
test as closely as the present APIs permit, this file additionally proves
the *global* `IsPrescribedDelivery` predicate and exhibits the positive
escaped stationary occupation explicitly.  No converse or general
fifth-obstruction API is introduced.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability Math.PMFProduct

namespace Q96UncoveredClass

abbrev Player := Bool
abbrev State := Bool

/-- Player one (`false`) has one action; player two (`true`) has the move that
can enter the escaped node. -/
def Act : Player → Type
  | false => Unit
  | true => Bool

instance : ∀ who : Player, Fintype (Act who)
  | false => inferInstanceAs (Fintype Unit)
  | true => inferInstanceAs (Fintype Bool)

instance : ∀ who : Player, DecidableEq (Act who)
  | false => inferInstanceAs (DecidableEq Unit)
  | true => inferInstanceAs (DecidableEq Bool)

instance : ∀ who : Player, Nonempty (Act who)
  | false => inferInstanceAs (Nonempty Unit)
  | true => inferInstanceAs (Nonempty Bool)

/-- The next node: the escaped node is absorbing; at the entry, player two's
Boolean action selects whether to escape. -/
def transition (state : State) (action : ∀ who, Act who) : PMF State :=
  if state then PMF.pure true else PMF.pure (action true)

/-- Only player one is paid, and only at the escaped node. -/
def stagePayoff (state : State) (_action : ∀ who, Act who)
    (who : Player) : ℝ :=
  if who then 0 else if state then 1 else 0

/-- The two-player/two-node stochastic game underlying the counterexample. -/
abbrev game : StochasticGame Player where
  State := State
  Act := Act
  stagePayoff := stagePayoff
  transition := transition
  discount := 0
  discount_nonneg := le_rfl
  discount_lt_one := by norm_num

instance : Finite game.State := inferInstanceAs (Finite Bool)

instance : ∀ who : Player, Finite (game.Act who) := fun who =>
  inferInstanceAs (Finite (Act who))

instance : ∀ who : Player, Fintype (game.Act who) := fun who =>
  inferInstanceAs (Fintype (Act who))

instance : ∀ who : Player, Nonempty (game.Act who) := fun who =>
  inferInstanceAs (Nonempty (Act who))

/-- The joint action with player two's component equal to `move`. -/
def jointAction (move : Bool) : game.JointAct
  | false => ()
  | true => move

/-- The prescription is player one's unique action and player two's `false`
action at both nodes. -/
def prescribedPlay (_z : State) : ∀ who, PMF (game.Act who)
  | false => PMF.pure ()
  | true => PMF.pure false

/-- Configurations are exactly the two public game states. -/
abbrev architecture : game.FiniteResponseArchitecture false where
  Config := State
  start := false
  publicState := id
  play := prescribedPlay
  step := fun _z _act state' => state'
  start_publicState := rfl
  step_publicState := fun _ _ _ => rfl

/-- The proposed target is zero for both players at both nodes. -/
def target : architecture.Config → Payoff Player := fun _ _ => 0

theorem actionDist_playerOne (z : State) (act : game.Act false) :
    architecture.actionDist false z (PMF.pure act) =
      PMF.pure (jointAction false) := by
  cases act
  unfold FiniteResponseArchitecture.actionDist
  change pmfPi (Function.update (prescribedPlay z) false (PMF.pure ())) = _
  rw [show Function.update (prescribedPlay z) false (PMF.pure ()) =
      fun who => PMF.pure (jointAction false who) by
    funext who
    cases who <;> rfl]
  exact pmfPi_pure (jointAction false)

theorem actionDist_playerTwo (z : State) (act : game.Act true) :
    architecture.actionDist true z (PMF.pure act) =
      PMF.pure (jointAction act) := by
  unfold FiniteResponseArchitecture.actionDist
  change pmfPi (Function.update (prescribedPlay z) true (PMF.pure act)) = _
  rw [show Function.update (prescribedPlay z) true (PMF.pure act) =
      fun who => PMF.pure (jointAction act who) by
    funext who
    cases who <;> rfl]
  exact pmfPi_pure (jointAction act)

theorem prescribedActionDist_eq (z : State) :
    architecture.prescribedActionDist z = PMF.pure (jointAction false) := by
  rw [architecture.prescribedActionDist_eq true z]
  exact actionDist_playerTwo z false

/-- Player one's only unilateral row leaves either node fixed. -/
theorem nextConfigDist_playerOne_eq (z : State) (act : game.Act false) :
    architecture.nextConfigDist false z (PMF.pure act) = PMF.pure z := by
  unfold FiniteResponseArchitecture.nextConfigDist
  rw [actionDist_playerOne]
  cases z <;> simp [game, transition, architecture, jointAction]

/-- At the entry, player two selects the next node; the escaped node remains
absorbing. -/
theorem nextConfigDist_playerTwo_eq (z : State) (act : game.Act true) :
    architecture.nextConfigDist true z (PMF.pure act) =
      PMF.pure (if z then true else act) := by
  unfold FiniteResponseArchitecture.nextConfigDist
  rw [actionDist_playerTwo]
  cases z <;> simp [game, transition, architecture, jointAction]

/-- Both nodes are absorbing under prescribed play. -/
theorem prescribedConfigDist_eq (z : State) :
    architecture.prescribedConfigDist z = PMF.pure z := by
  unfold FiniteResponseArchitecture.prescribedConfigDist
  rw [prescribedActionDist_eq]
  cases z <;> simp [game, transition, architecture, jointAction]

theorem stagePayoffAt_playerOne_eq (z : State) (act : game.Act false) :
    architecture.stagePayoffAt false z (PMF.pure act) =
      if z then 1 else 0 := by
  unfold FiniteResponseArchitecture.stagePayoffAt
  rw [actionDist_playerOne, expect_pure]
  simp [stagePayoff]

theorem stagePayoffAt_playerTwo_eq (z : State) (act : game.Act true) :
    architecture.stagePayoffAt true z (PMF.pure act) = 0 := by
  unfold FiniteResponseArchitecture.stagePayoffAt
  rw [actionDist_playerTwo, expect_pure]
  simp [stagePayoff]

theorem prescribedStagePayoff_playerOne_eq (z : State) :
    architecture.prescribedStagePayoff z false = if z then 1 else 0 := by
  unfold FiniteResponseArchitecture.prescribedStagePayoff
  rw [prescribedActionDist_eq, expect_pure]
  simp [stagePayoff]

theorem prescribedStagePayoff_playerTwo_eq (z : State) :
    architecture.prescribedStagePayoff z true = 0 := by
  unfold FiniteResponseArchitecture.prescribedStagePayoff
  rw [prescribedActionDist_eq, expect_pure]
  simp [stagePayoff]

theorem pure_toReal_eq_indicator (z y : State) :
    ((PMF.pure z) y).toReal = if y = z then 1 else 0 := by
  by_cases h : y = z
  · subst y
    simp
  · rw [PMF.pure_apply, if_neg]
    · simp [h]
    · exact fun hzy => h hzy

/-- The declared support-closed domains: prescribed reachability and player
one's arena contain only the entry; player two's arena contains both nodes. -/
def region : architecture.ClosedResponseRegion where
  unilateral who z := if who then True else z = false
  prescribed z := z = false
  start_unilateral := by intro who; cases who <;> simp [architecture]
  start_prescribed := rfl
  prescribed_unilateral := by
    intro who z hz
    cases who <;> simp [hz]
  unilateral_closed := by
    intro who z hz act y hy
    cases who with
    | false =>
        rw [nextConfigDist_playerOne_eq] at hy
        have hyz : y = z := (PMF.mem_support_pure_iff z y).mp hy
        simpa [hyz] using hz
    | true => simp
  prescribed_closed := by
    intro z hz y hy
    rw [prescribedConfigDist_eq] at hy
    have hyz : y = z := (PMF.mem_support_pure_iff z y).mp hy
    exact hyz.trans hz

@[simp] theorem region_prescribed_iff (z : State) :
    region.prescribed z ↔ z = false := by
  change (z = false ↔ z = false)
  exact Iff.rfl

@[simp] theorem region_unilateral_playerOne_iff (z : State) :
    region.unilateral false z ↔ z = false := by
  change (z = false ↔ z = false)
  exact Iff.rfl

@[simp] theorem region_unilateral_playerTwo (z : State) :
    region.unilateral true z := by
  simp [region]

/-- Canonical prescribed reachability is exactly the singleton entry. -/
theorem prescribedReachable_iff (z : State) :
    architecture.PrescribedReachable z ↔ z = false := by
  constructor
  · intro hz
    induction hz with
    | refl => rfl
    | tail hxy hy ih =>
        rw [FiniteResponseArchitecture.PrescribedSupportStep,
          prescribedConfigDist_eq] at hy
        exact ((PMF.mem_support_pure_iff _ _).mp hy).trans ih
  · intro hz
    subst z
    exact Relation.ReflTransGen.refl

/-- Player one's canonical unilateral reachability is exactly the singleton
entry. -/
theorem unilateralReachable_playerOne_iff (z : State) :
    architecture.UnilateralReachable false z ↔ z = false := by
  constructor
  · intro hz
    induction hz with
    | refl => rfl
    | tail hxy hy ih =>
        obtain ⟨act, hact⟩ := hy
        rw [nextConfigDist_playerOne_eq] at hact
        exact ((PMF.mem_support_pure_iff _ _).mp hact).trans ih
  · intro hz
    subst z
    exact Relation.ReflTransGen.refl

/-- Player two can reach both nodes. -/
theorem unilateralReachable_playerTwo (z : State) :
    architecture.UnilateralReachable true z := by
  cases z with
  | false => exact Relation.ReflTransGen.refl
  | true =>
      apply Relation.ReflTransGen.tail Relation.ReflTransGen.refl
      refine ⟨true, ?_⟩
      rw [nextConfigDist_playerTwo_eq]
      exact PMF.mem_support_pure_iff _ _ |>.mpr rfl

/-- (T0) actually holds globally, hence in particular on the prescribed
domain. -/
theorem isPrescribedTargetHarmonic :
    architecture.IsPrescribedTargetHarmonic target := by
  intro who z
  simp [target]

/-- (Ti) actually holds globally because the proposed target is constant. -/
theorem isUnilateralTargetSuperharmonic :
    architecture.IsUnilateralTargetSuperharmonic target := by
  intro who z act
  simp [target]

/-- The owner-specific neutral-occupation check (N) holds.  Player one's
relevant positive mass can occur only at the zero-payoff entry, while player
two's payoff is zero everywhere. -/
theorem isNeutralOccupationNonpositiveOn :
    architecture.IsNeutralOccupationNonpositiveOn region target := by
  intro who μ
  cases who with
  | false =>
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro p hp
      by_cases hm : 0 < μ.mass p
      · have hrel := μ.relevant_support p hm
        have hstate : p.1 = false := by simpa [region] using hrel
        rw [hstate, stagePayoffAt_playerOne_eq]
        simp [target]
      · have hnonneg := μ.mass_nonneg p
        have hmass : μ.mass p = 0 := le_antisymm (not_lt.mp hm) hnonneg
        simp [hmass]
  | true =>
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro p hp
      rw [stagePayoffAt_playerTwo_eq]
      simp [target]

/-- The nonnegative prescribed stationary-delivery test (P) holds even on
the ambient two-node configuration set. -/
theorem isPrescribedDelivery : architecture.IsPrescribedDelivery target := by
  intro who ν
  cases who with
  | false =>
      exact Finset.sum_nonneg fun z _ =>
        mul_nonneg (ν.mass_nonneg z) (by
          rw [prescribedStagePayoff_playerOne_eq]
          cases z <;> simp [target])
  | true =>
      exact le_of_eq (Finset.sum_eq_zero (fun z _ => by
        rw [prescribedStagePayoff_playerTwo_eq]
        simp [target])).symm

/-- The closest four-field bundle in the current support-pruned API passes.
Its prescribed stationary field is restricted to `region.prescribed = {e}`;
the preceding theorem separately verifies the stronger ambient (P) check. -/
theorem isReachableCredibilityCriterion :
    architecture.IsReachableCredibilityCriterion region target where
  targetHarmonic := fun who z _ => isPrescribedTargetHarmonic who z
  targetSuperharmonic := fun who z _ act =>
    isUnilateralTargetSuperharmonic who z act
  neutralOccupation := isNeutralOccupationNonpositiveOn
  prescribedDelivery := by
    intro who ν
    let ν' : architecture.PrescribedStationary :=
      { mass := ν.mass
        mass_nonneg := ν.mass_nonneg
        balance := ν.balance
        total := ν.total }
    exact isPrescribedDelivery who ν'

/-- The four target/occupation-side checks in the closest current domain
split: global (T0), global (hence owner-local) (Ti), owner-local (N), and
global nonnegative (P). -/
theorem target_occupation_checks_hold :
    architecture.IsPrescribedTargetHarmonic target ∧
      architecture.IsUnilateralTargetSuperharmonic target ∧
      architecture.IsNeutralOccupationNonpositiveOn region target ∧
      architecture.IsPrescribedDelivery target :=
  ⟨isPrescribedTargetHarmonic, isUnilateralTargetSuperharmonic,
    isNeutralOccupationNonpositiveOn, isPrescribedDelivery⟩

/-- Point mass on the escaped prescribed-absorbing node. -/
def escapedMass (z : State) : ℝ := if z then 1 else 0

/-- The escaped node is a prescribed stationary class. -/
def escapedStationary : architecture.PrescribedStationary where
  mass := escapedMass
  mass_nonneg := by intro z; cases z <;> simp [escapedMass]
  balance := by
    intro y
    apply Finset.sum_eq_zero
    intro z hz
    rw [prescribedConfigDist_eq, pure_toReal_eq_indicator]
    simp
  total := by
    rw [Fintype.sum_bool]
    norm_num [escapedMass]

/-- The stationary prescribed surplus at the uncovered class is strictly
positive for player one. -/
theorem escapedStationary_surplus_playerOne :
    (∑ z : State, escapedStationary.mass z *
      (architecture.prescribedStagePayoff z false - target z false)) = 1 := by
  rw [Fintype.sum_bool]
  norm_num [escapedStationary, escapedMass,
    prescribedStagePayoff_playerOne_eq, target]

/-- The escaped recurrent node is outside player one's arena but inside player
two's arena. -/
theorem escaped_domain_split :
    ¬ region.unilateral false true ∧ region.unilateral true true := by
  simp [region]

/-- From the escaped node, player one's expected payoff is one at every stage,
under any behavior profile. -/
theorem expectedStagePayoff_escaped_playerOne
    (σ : game.BehaviorProfile) (t : ℕ) :
    game.expectedStagePayoff σ true t false = 1 := by
  induction t generalizing σ with
  | zero =>
      rw [game.expectedStagePayoff_zero]
      unfold StochasticGame.stageEUAt
      simp [stagePayoff, StochasticGame.emptyHist]
  | succ t ih =>
      rw [game.expectedStagePayoff_succ_shift]
      simp [transition, ih]

/-- The escaped prescribed-play average is exactly one at every positive
horizon, so its cumulative target error is linear rather than sublinear. -/
theorem finiteAveragePayoff_escaped_playerOne
    (σ : game.BehaviorProfile) {T : ℕ} (hT : 0 < T) :
    game.finiteAveragePayoff true T σ false = 1 := by
  rw [game.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  simp_rw [expectedStagePayoff_escaped_playerOne]
  simp [Nat.ne_of_gt hT]

/-- Restarting prescribed play at the escaped node already misses the proposed
target by one at horizon one. -/
theorem finiteAveragePayoff_escaped_one_playerOne :
    game.finiteAveragePayoff true 1
      (architecture.rebase true).phaseProfile.behaviorProfile false = 1 := by
  exact finiteAveragePayoff_escaped_playerOne _ (by norm_num)

/-- At every positive horizon, prescribed play restarted at the escaped node
misses the proposed target by exactly one in average payoff. -/
theorem prescribed_target_gap_escaped_playerOne {T : ℕ} (hT : 0 < T) :
    game.finiteAveragePayoff true T
          (architecture.rebase true).phaseProfile.behaviorProfile false -
        target true false = 1 := by
  rw [finiteAveragePayoff_escaped_playerOne _ hT]
  simp [target]

theorem exact_target_delivery_fails_at_escaped :
    game.finiteAveragePayoff true 1
        (architecture.rebase true).phaseProfile.behaviorProfile false ≠
      target true false := by
  rw [finiteAveragePayoff_escaped_one_playerOne]
  simp [target]

/-- No prescribed Poisson bias can solve the target-delivery equation at the
escaped self-loop. -/
theorem no_prescribedPoissonBias_at_escaped :
    ¬ ∃ bias : State → ℝ,
      target true false + bias true =
        architecture.prescribedStagePayoff true false +
          expect (architecture.prescribedConfigDist true) bias := by
  intro h
  obtain ⟨bias, hbias⟩ := h
  rw [prescribedStagePayoff_playerOne_eq, prescribedConfigDist_eq,
    expect_pure] at hbias
  simp [target] at hbias

/-- Consequently no bias solves the prescribed Poisson equation on the whole
two-node ambient domain. -/
theorem no_global_prescribedPoissonBias :
    ¬ ∃ bias : State → ℝ, ∀ z : State,
      target z false + bias z =
        architecture.prescribedStagePayoff z false +
          expect (architecture.prescribedConfigDist z) bias := by
  intro h
  obtain ⟨bias, hbias⟩ := h
  exact no_prescribedPoissonBias_at_escaped ⟨bias, hbias true⟩

end Q96UncoveredClass
end StochasticGame
end GameTheory
