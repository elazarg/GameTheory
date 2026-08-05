/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.PlayerNeutralAnalyticCirculationTerminalSemantics

/-!
# The exact target transported by a player-neutral positive class

The operational kernel stored by a player-neutral analytic-circulation
terminal mixes endpoint baseline transitions with continuation-neutral
deviations of one fixed player.  Every such column preserves that player's
endpoint continuation value.  Consequently the induced kernel is harmonic
in the owner's coordinate, and that scalar coordinate is constant on the
stored positive communicating class.

There is no corresponding per-column whole-vector theorem.  The two-state
analytic Bellman germ at the end of this file has an owner-neutral pure
deviation which swaps the states.  It preserves the owner's (zero) endpoint
value but changes another player's endpoint value from zero to one.  This is
a no-go for upgrading one neutral Bellman/Fink column to a vector-preserving
column.  It does not assert that the terminal positive class constructed
above fails whole-vector harmonicity.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math Math.Probability

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

namespace AnalyticBellmanGerm

/-- Restricting a balanced operational kernel to its positive source support
does not destroy a scalar value preserved by every original transition. -/
private theorem expect_occupationActiveKernel_eq_of_preserved
    {S I : Type*} [Fintype S] [Fintype I] [DecidableEq S]
    (kernel : I → PMF S) (source : I → S)
    (mass : I → ℝ) (mass_nonneg : ∀ index, 0 ≤ mass index)
    (balance :
      ∀ destination,
        ∑ index, mass index *
          ((kernel index destination).toReal -
            if destination = source index then 1 else 0) = 0)
    (value : S → ℝ)
    (preserved :
      ∀ index,
        expect (kernel index) value = value (source index))
    (state : occupationActiveStates source mass) :
    expect
        (occupationActiveKernel
          kernel source mass mass_nonneg balance state)
        (fun destination => value destination.1) =
      value state.1 := by
  let operational : PMF S :=
    occupationOperationalKernel
      kernel source mass mass_nonneg
      (occupationActiveState_sourceMass_pos source mass state)
  have hrestricted :
      expect
          (occupationActiveKernel
            kernel source mass mass_nonneg balance state)
          (fun destination => value destination.1) =
        expect operational value := by
    rw [expect_eq_sum, expect_eq_sum]
    simp_rw [occupationActiveKernel_toReal]
    rw [← Finset.sum_subtype
      (occupationActiveStates source mass)
      (fun _ => Iff.rfl)
      (fun destination =>
        (operational destination).toReal * value destination)]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro destination _ hdestination
    rw [show operational destination = 0 by
      exact occupationOperationalKernel_eq_zero_of_not_active
        kernel source mass_nonneg balance
          (occupationActiveState_sourceMass_pos source mass state)
          hdestination]
    simp
  rw [hrestricted]
  change
    expect
        ((occupationPolicyPMF source mass mass_nonneg
          (occupationActiveState_sourceMass_pos source mass state)).bind
            fun index => kernel index.1)
        value =
      value state.1
  rw [expect_bind]
  have hfiber :
      (fun index : occupationSourceFiber source state.1 =>
          expect (kernel index.1) value) =
        fun _ => value state.1 := by
    funext index
    rw [preserved index.1,
      occupationSourceFiber_source_eq source index]
  rw [hfiber, expect_const]

omit [DecidableEq G.State] in
/-- Every original column of the player-neutral occupation family preserves
the selected owner's endpoint continuation value. -/
theorem playerNeutralOccupationKernel_endpointValue_owner_preserved
    (germ : G.AnalyticBellmanGerm) (who : ι)
    (index : germ.PlayerNeutralOccupationIndex who) :
    expect
        (germ.playerNeutralOccupationKernel who index)
        (fun state => germ.endpointValue state who) =
      germ.endpointValue
        (germ.playerNeutralOccupationSource who index) who := by
  rcases index with source | response
  · have hzero :=
      congrFun
        (congrFun
          germ.finkContinuationResidualVector_endpointValue_eq_zero
          source) who
    dsimp only [playerNeutralOccupationKernel,
      playerNeutralOccupationSource]
    rw [G.expect_finkStateKernel_eq]
    exact sub_eq_zero.mp
      (by
        simpa [finkContinuationResidualVector,
          finkContinuationResidual, finkContinuationEU] using hzero)
  · have hbaseline :=
      congrFun
        (congrFun
          germ.finkContinuationResidualVector_endpointValue_eq_zero
          response.source) who
    have hbaseline' :
        expect
            (G.finkStateKernel germ.endpointFinkPoint response.source)
            (fun state => germ.endpointValue state who) =
          germ.endpointValue response.source who := by
      rw [G.expect_finkStateKernel_eq]
      exact sub_eq_zero.mp
        (by
          simpa [finkContinuationResidualVector,
            finkContinuationResidual, finkContinuationEU] using hbaseline)
    have hneutral := response.2
    rw [G.finkContinuationGain_eq_expect_stateKernels] at hneutral
    dsimp only [playerNeutralOccupationKernel,
      playerNeutralOccupationSource, ContinuationNeutralAction.kernel]
    calc
      expect
          (G.finkPureDeviationStateKernel germ.endpointFinkPoint
            response.source who response.1.2)
          (fun state => germ.endpointValue state who) =
          expect
            (G.finkStateKernel germ.endpointFinkPoint response.source)
            (fun state => germ.endpointValue state who) := by
        exact sub_eq_zero.mp
          (by
            simpa only [ContinuationNeutralAction.source] using hneutral)
      _ = germ.endpointValue response.source who := hbaseline'

variable
    {germ : G.AnalyticBellmanGerm}
    {B : G.State → Payoff ι} {who : ι}
    {initial :
      FiniteDeflationState
        (germ.PlayerNeutralOccupationIndex who)}
    {terminalAnchor : G.State}

namespace PlayerNeutralAnalyticCirculationTerminalData

/-- The owner's endpoint coordinate is harmonic for the actual operational
kernel induced by the terminal circulation, on every active state. -/
theorem endpointValue_owner_harmonic
    (data :
      PlayerNeutralAnalyticCirculationTerminalData
        germ B who initial terminalAnchor)
    (state :
      occupationActiveStates
        data.activeSource
        data.positiveClass.mass) :
    germ.endpointValue state.1 who =
      expect
        (WholeTargetBoundary.legalKernel data state)
        (fun destination => germ.endpointValue destination.1 who) := by
  symm
  exact expect_occupationActiveKernel_eq_of_preserved
    data.activeKernel
    data.activeSource
    data.positiveClass.mass
    data.positiveClass.mass_nonneg
    (actualOccupationBalance_explicit
      data.activeKernel
      data.activeSource
      data.positiveClass.mass
      data.positiveClass.balance)
    (fun state => germ.endpointValue state who)
    (fun index => by
      simpa only [activeKernel, activeSource] using
        germ.playerNeutralOccupationKernel_endpointValue_owner_preserved
          who index.1)
    state

/-- Hence the owner's endpoint coordinate is constant throughout the stored
positive communicating class. -/
theorem endpointValue_owner_eq_representative
    (data :
      PlayerNeutralAnalyticCirculationTerminalData
        germ B who initial terminalAnchor)
    {state :
      occupationActiveStates
        data.activeSource
        data.positiveClass.mass}
    (state_mem : state ∈ data.positiveClass.closedClass.states) :
    germ.endpointValue state.1 who =
      germ.endpointValue data.positiveClass.representative.1 who := by
  have hconstant :=
    data.positiveClass.closedClass.harmonic_eq_on_class
      (fun active => germ.endpointValue active.1 who)
      (fun active _ => data.endpointValue_owner_harmonic active)
      state_mem
      (by
        simpa only [data.positiveClass.closedClass_entry] using
          data.positiveClass.closedClass.entry_mem)
  exact hconstant

end PlayerNeutralAnalyticCirculationTerminalData

end AnalyticBellmanGerm

namespace PlayerNeutralWholeVectorCounterexample

abbrev Player := Bool
abbrev State := Bool

def Act : Player → Type
  | false => Bool
  | true => Unit

instance (player : Player) : Fintype (Act player) := by
  cases player with
  | false =>
      change Fintype Bool
      infer_instance
  | true =>
      change Fintype Unit
      infer_instance

instance (player : Player) : DecidableEq (Act player) := by
  cases player with
  | false =>
      change DecidableEq Bool
      infer_instance
  | true =>
      change DecidableEq Unit
      infer_instance

def ownerAction (action : ∀ player, Act player) : Bool :=
  action false

abbrev game : StochasticGame Player where
  State := State
  Act := Act
  stagePayoff state _ player :=
    if player then if state then 1 else 0 else 0
  transition state action :=
    if ownerAction action then PMF.pure (!state) else PMF.pure state
  discount := 0
  discount_nonneg := le_rfl
  discount_lt_one := zero_lt_one

instance (player : Player) : Fintype (game.Act player) := by
  change Fintype (Act player)
  infer_instance

instance (player : Player) : DecidableEq (game.Act player) := by
  change DecidableEq (Act player)
  infer_instance

def prescribedAction : game.JointAct :=
  fun player =>
    match player with
    | false => false
    | true => ()

def profile : game.StationaryMixedProfile :=
  fun _ player => PMF.pure (prescribedAction player)

def value (state : State) (player : Player) : ℝ :=
  if player then if state then 1 else 0 else 0

instance : Fintype game.State := by
  change Fintype Bool
  infer_instance

instance : DecidableEq game.State := by
  change DecidableEq Bool
  infer_instance

private theorem pmfPi_profile (state : State) :
    Math.PMFProduct.pmfPi (profile state) =
      PMF.pure prescribedAction := by
  change
    Math.PMFProduct.pmfPi
        (fun player : Player => PMF.pure (prescribedAction player)) =
      PMF.pure prescribedAction
  exact Math.PMFProduct.pmfPi_pure prescribedAction

private theorem pmfPi_profile_update_pure
    (state : State) (player : Player) (action : game.Act player) :
    Math.PMFProduct.pmfPi
        (Function.update (profile state) player (PMF.pure action)) =
      PMF.pure (Function.update prescribedAction player action) := by
  have hfamily :
      Function.update (profile state) player (PMF.pure action) =
        fun other =>
          PMF.pure (Function.update prescribedAction player action other) := by
    funext other
    by_cases hother : other = player
    · subst hother
      simp [Function.update]
    · simp [profile, prescribedAction, Function.update, hother]
  rw [hfamily]
  exact Math.PMFProduct.pmfPi_pure _

private theorem pureDeviationAuxEU_eq
    (β : ℝ) (state : State) (player : Player)
    (action : game.Act player) :
    game.discountedAuxEU β value state
        (Function.update (profile state) player (PMF.pure action)) player =
      game.discountedAuxEU β value state (profile state) player := by
  rw [game.discountedAuxEU_eq, game.discountedAuxEU_eq,
    pmfPi_profile_update_pure, pmfPi_profile]
  simp only [expect_pure]
  cases state <;> cases player <;> cases action <;>
    simp [value, ownerAction, prescribedAction, Function.update]

/-- The fixed pure profile and value solve Fink's discounted Bellman system
for every discount factor. -/
theorem equilibrium (β : ℝ) :
    game.IsDiscountedStationaryBellmanEq β profile value := by
  constructor
  · intro state player deviation
    rw [game.discountedAuxEU_update_eq_expect_pure]
    calc
      expect deviation
          (fun action =>
            game.discountedAuxEU β value state
              (Function.update (profile state) player
                (PMF.pure action)) player) =
          expect deviation
            (fun _ =>
              game.discountedAuxEU β value state
                (profile state) player) := by
            congr 1
            funext action
            exact pureDeviationAuxEU_eq β state player action
      _ ≤ game.discountedAuxEU β value state
          (profile state) player :=
        le_of_eq (expect_const _ _)
  · intro state player
    rw [game.discountedAuxEU_eq]
    rw [pmfPi_profile]
    simp only [expect_pure]
    cases state <;> cases player <;>
      simp [value, ownerAction, prescribedAction]

def assignment (t : ℝ) : BellmanVar game → ℝ :=
  game.bellmanAssignment profile value (1 - t)

/-- A genuine analytic Bellman germ realizing the counterexample. -/
def germ : game.AnalyticBellmanGerm where
  ramification := 1
  radius := 1
  assignment := assignment
  ramification_pos := Nat.zero_lt_succ 0
  radius_pos := zero_lt_one
  analytic_assignment := by
    rw [analyticAt_pi_iff]
    intro coordinate
    cases coordinate with
    | mix state player action =>
        exact analyticAt_const
    | val state player =>
        exact analyticAt_const
    | disc =>
        exact
          analyticAt_const.sub
            (analyticAt_const.sub
              (analyticAt_id : AnalyticAt ℝ (fun t : ℝ => t) 0))
  solution := by
    intro t _
    exact game.isPolynomialBellmanSolution_bellmanAssignment
      (equilibrium (1 - t))
  discountCoordinate := by
    intro t _
    simp [assignment, StochasticGame.bellmanAssignment]

@[simp]
theorem germ_endpointValue (state : State) (player : Player) :
    germ.endpointValue state player = value state player :=
  rfl

@[simp]
theorem germ_endpointProfile :
    germ.endpointProfile = profile := by
  unfold AnalyticBellmanGerm.endpointProfile
  exact game.bellmanDecodeProfile_bellmanAssignment _

theorem finkStateKernel_germ (state : State) :
    game.finkStateKernel germ.endpointFinkPoint state =
      PMF.pure state := by
  unfold StochasticGame.finkStateKernel
  rw [germ.finkProfile_endpointFinkPoint,
    germ_endpointProfile, pmfPi_profile]
  simp [game, ownerAction, prescribedAction]

theorem finkPureDeviationStateKernel_switch :
    game.finkPureDeviationStateKernel
        germ.endpointFinkPoint false false true =
      PMF.pure true := by
  unfold StochasticGame.finkPureDeviationStateKernel
  rw [germ.finkProfile_endpointFinkPoint, germ_endpointProfile,
    pmfPi_profile_update_pure]
  simp [game, ownerAction]

def switchAtFalse :
    germ.ContinuationNeutralAction false :=
  ⟨(false, true), by
    rw [game.finkContinuationGain_eq_expect_stateKernels]
    rw [finkPureDeviationStateKernel_switch,
      finkStateKernel_germ]
    norm_num [value]
  ⟩

/-- The actual endpoint deviation preserves its owner's coordinate. -/
theorem switch_owner_neutral :
    game.finkContinuationGain germ.endpointValue
      germ.endpointFinkPoint false false true = 0 :=
  switchAtFalse.2

/-- The same actual endpoint deviation changes the other player's
continuation target. -/
theorem switch_other_player_not_neutral :
    expect switchAtFalse.kernel
        (fun state : State => germ.endpointValue state true) ≠
      germ.endpointValue switchAtFalse.source true := by
  rw [show switchAtFalse.kernel =
      PMF.pure (true : game.State) by
    exact finkPureDeviationStateKernel_switch]
  rw [expect_pure]
  norm_num [
    AnalyticBellmanGerm.ContinuationNeutralAction.kernel,
    AnalyticBellmanGerm.ContinuationNeutralAction.source,
    switchAtFalse, value]

/-- For one genuine analytic Bellman/Fink column, owner-coordinate
continuation neutrality does not imply preservation of the whole endpoint
payoff vector.  This theorem makes no claim about a terminal positive
communicating class. -/
theorem owner_neutral_not_wholeVector :
    game.finkContinuationGain germ.endpointValue
        germ.endpointFinkPoint false false true = 0 ∧
      (fun player =>
        expect switchAtFalse.kernel
          (fun state => germ.endpointValue state player)) ≠
        germ.endpointValue switchAtFalse.source := by
  refine ⟨switch_owner_neutral, ?_⟩
  intro hwhole
  exact switch_other_player_not_neutral
    (congrFun hwhole true)

end PlayerNeutralWholeVectorCounterexample

end StochasticGame
end GameTheory
