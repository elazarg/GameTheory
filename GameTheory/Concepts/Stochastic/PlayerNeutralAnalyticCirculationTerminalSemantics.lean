/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.PlayerNeutralAnalyticDeflationTerminal
import GameTheory.Concepts.Stochastic.PublicRecurrentClassChild

/-!
# Semantic boundary of the analytic-circulation terminal branch

The positive class stored by
`PlayerNeutralAnalyticCirculationTerminalData` contains more operational
information than an unrelated globally positive action.  Its positive
aggregate charge forces an actually occupied continuation-neutral deviation
whose source lies in that same class.  Thus the class representative reaches
the source of a concrete endpoint public constraint response under the
induced operational kernel.

This is still not a public recursive child carrying an application's whole
target.  The final two-node construction keeps the terminal branch's genuine
reachable closed class but chooses a whole target that separates the only
strictly lower node from its parent.  No `PublicRecurrentClassChild` can then
exist.  Consequently class-local operationality does not manufacture
whole-target transport (and hence cannot by itself provide a credible parent
resume).
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math Math.Probability

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

namespace AnalyticBellmanGerm

variable
    {germ : G.AnalyticBellmanGerm}
    {B : G.State → Payoff ι} {who : ι}
    {initial :
      FiniteDeflationState
        (germ.PlayerNeutralOccupationIndex who)}
    {terminalAnchor : G.State}

namespace PlayerNeutralAnalyticCirculationTerminalData

def activeKernel
    (data :
      PlayerNeutralAnalyticCirculationTerminalData
        germ B who initial terminalAnchor) :
    data.terminal.ActiveIndex → PMF G.State :=
  fun index => germ.playerNeutralOccupationKernel who index.1

def activeSource
    (data :
      PlayerNeutralAnalyticCirculationTerminalData
        germ B who initial terminalAnchor) :
    data.terminal.ActiveIndex → G.State :=
  fun index => germ.playerNeutralOccupationSource who index.1

def activeCharge
    (data :
      PlayerNeutralAnalyticCirculationTerminalData
        germ B who initial terminalAnchor) :
    data.terminal.ActiveIndex → ℝ :=
  fun index => germ.playerNeutralOccupationCharge B who index.1

/-- A class-local positive response extracted from the positive aggregate
charge of the selected communicating class.

Unlike the response field of the terminal package, this response is tied to
the selected class by `source_mem`, and `reachable` is legal reachability
under that class's induced operational kernel. -/
structure ClassLocalPublicResponse
    (data :
      PlayerNeutralAnalyticCirculationTerminalData
        germ B who initial terminalAnchor) where
  response : germ.ContinuationNeutralAction who
  responseIndex : data.terminal.ActiveIndex
  responseIndex_eq : responseIndex.1 = Sum.inr response
  sourceState :
    occupationActiveStates
      data.activeSource
      data.positiveClass.mass
  source_eq : sourceState.1 = response.source
  source_mem : sourceState ∈ data.positiveClass.closedClass.states
  occupied_pos :
    0 <
      data.positiveClass.mass responseIndex
  charge_pos :
    0 < germ.neutralActionCharge B who response
  reachable :
    PMFReachable
      (occupationActiveKernel
        data.activeKernel
        data.activeSource
        data.positiveClass.mass
        data.positiveClass.mass_nonneg
        (actualOccupationBalance_explicit
          data.activeKernel
          data.activeSource
          data.positiveClass.mass
          data.positiveClass.balance))
      data.positiveClass.representative sourceState
  publicResponse :
    G.FinkPublicConstraintResponse
      germ.endpointFinkPoint B response.source who response.1.2

/-- Positive aggregate charge of the stored class forces a positively
occupied transition with source in that class. -/
private theorem exists_positive_index_in_class
    (data :
      PlayerNeutralAnalyticCirculationTerminalData
        germ B who initial terminalAnchor) :
    ∃ (state :
        occupationActiveStates
          data.activeSource
          data.positiveClass.mass)
      (index : data.terminal.ActiveIndex),
      state ∈ data.positiveClass.closedClass.states ∧
        data.activeSource index = state.1 ∧
        0 <
          data.positiveClass.mass index *
            data.activeCharge index := by
  have hstate :
      ∃ state ∈ data.positiveClass.closedClass.states,
        0 <
          occupationSourceCharge
            data.activeSource
            data.activeCharge
            data.positiveClass.mass state.1 := by
    by_contra hnone
    push Not at hnone
    have hnonpos :
        occupationCommunicationClassOriginalCharge
            data.activeKernel
            data.activeSource
            data.activeCharge
            data.positiveClass.mass
            data.positiveClass.mass_nonneg
            data.positiveClass.balance
            data.positiveClass.representative ≤
          0 := by
      apply Finset.sum_nonpos
      intro state hmem
      apply hnone state
      rw [data.positiveClass.closedClass.states_eq_communicationClass,
        data.positiveClass.closedClass_entry]
      exact hmem
    exact
      (not_lt_of_ge hnonpos)
        data.positiveClass.original_class_charge_pos
  obtain ⟨state, hstate_mem, hsource_pos⟩ := hstate
  have hindex :
      ∃ index ∈
          Finset.univ.filter
            (fun index =>
              data.activeSource index = state.1),
        0 <
          data.positiveClass.mass index *
            data.activeCharge index := by
    by_contra hnone
    push Not at hnone
    have hnonpos :
        occupationSourceCharge
            data.activeSource
            data.activeCharge
            data.positiveClass.mass state.1 ≤
          0 := by
      apply Finset.sum_nonpos
      intro index hmem
      exact hnone index hmem
    exact (not_lt_of_ge hnonpos) hsource_pos
  obtain ⟨index, hindex_mem, hindex_pos⟩ := hindex
  exact
    ⟨state, index, hstate_mem,
      (Finset.mem_filter.mp hindex_mem).2, hindex_pos⟩

/-- Existence form of the strongest class-local semantic consequence of the
terminal analytic-circulation data. -/
theorem exists_classLocalPublicResponse
    (data :
      PlayerNeutralAnalyticCirculationTerminalData
        germ B who initial terminalAnchor) :
    Nonempty (ClassLocalPublicResponse data) := by
  obtain ⟨state, index, hstate_mem, hsource, hpositive⟩ :=
    exists_positive_index_in_class data
  rcases hindex : index.1 with source | response
  · simp [activeCharge, hindex, playerNeutralOccupationCharge]
      at hpositive
  · have hpositive' :
        0 <
          data.positiveClass.mass index *
            germ.neutralActionCharge B who response := by
      simpa [activeCharge, hindex, playerNeutralOccupationCharge]
        using hpositive
    have hcharge :
        0 < germ.neutralActionCharge B who response :=
      pos_of_mul_pos_right hpositive'
        (data.positiveClass.mass_nonneg index)
    have hmass :
        0 < data.positiveClass.mass index :=
      pos_of_mul_pos_left hpositive' hcharge.le
    refine ⟨{
      response := response
      responseIndex := index
      responseIndex_eq := hindex
      sourceState := state
      source_eq := ?_
      source_mem := hstate_mem
      occupied_pos := hmass
      charge_pos := hcharge
      reachable := data.positiveClass.reachable_from_representative hstate_mem
      publicResponse :=
        response.publicConstraintResponse B hcharge
    }⟩
    simpa [activeSource, hindex, playerNeutralOccupationSource]
      using hsource.symm

/-- Strongest class-local semantic consequence of the terminal
analytic-circulation data: an internally reachable, positively occupied,
owner-preserving actual deviation with a concrete endpoint public response. -/
def classLocalPublicResponse
    (data :
      PlayerNeutralAnalyticCirculationTerminalData
        germ B who initial terminalAnchor) :
    ClassLocalPublicResponse data :=
  Classical.choice data.exists_classLocalPublicResponse

/-- The class-local response preserves the endpoint continuation target in
the selected owner's coordinate.  No claim is made for the other players'
coordinates. -/
theorem classLocalPublicResponse_owner_target_neutral
    (data :
      PlayerNeutralAnalyticCirculationTerminalData
        germ B who initial terminalAnchor) :
    G.finkContinuationGain germ.endpointValue
        germ.endpointFinkPoint
        data.classLocalPublicResponse.response.source who
        data.classLocalPublicResponse.response.1.2 =
      0 :=
  data.classLocalPublicResponse.response.2

namespace WholeTargetBoundary

abbrev ActiveState
    (data :
      PlayerNeutralAnalyticCirculationTerminalData
        germ B who initial terminalAnchor) :=
  occupationActiveStates
    data.activeSource
    data.positiveClass.mass

def legalKernel
    (data :
      PlayerNeutralAnalyticCirculationTerminalData
        germ B who initial terminalAnchor) :
    ActiveState data → PMF (ActiveState data) :=
  occupationActiveKernel
    data.activeKernel
    data.activeSource
    data.positiveClass.mass
    data.positiveClass.mass_nonneg
    (actualOccupationBalance_explicit
      data.activeKernel
      data.activeSource
      data.positiveClass.mass
      data.positiveClass.balance)

def nodeEntry
    (data :
      PlayerNeutralAnalyticCirculationTerminalData
        germ B who initial terminalAnchor) (_ : Bool) :
    ActiveState data :=
  data.positiveClass.representative

def nodeTarget (node : Bool) (_ : Unit) : ℝ :=
  if node then 1 else 0

def rankLt (child parent : Bool) : Prop :=
  child = true ∧ parent = false

/-- The terminal branch genuinely supplies a legal recurrent core at its
internal representative. -/
def internalLegalCore
    (data :
      PlayerNeutralAnalyticCirculationTerminalData
        germ B who initial terminalAnchor) :
    ReachableClosedClass
      (legalKernel data) (nodeEntry data false) :=
  data.positiveClass.closedClass

/-- Exact two-node whole-target obstruction.

Both nodes use the terminal branch's genuine legal internal entry and the
only strict lower rank is `true < false`.  Giving that lower node a
different (one-coordinate, hence whole-vector) target makes a recurrent
child impossible.  Thus no target-preserving child can be derived from the
terminal data uniformly over an application's node target. -/
theorem no_wholeTargetCompatible_strictChild
    (data :
      PlayerNeutralAnalyticCirculationTerminalData
        germ B who initial terminalAnchor) :
    PublicRecurrentClassChild
        (legalKernel data)
        (nodeEntry data)
        nodeTarget
        (fun node : Bool => node)
        rankLt
        (fun _ : Bool => True)
        false →
      False := by
  intro childData
  have hchild : childData.child = true :=
    childData.rank_decreases.1
  have htarget :=
    congrFun childData.target_preserved ()
  simp only [nodeTarget, Bool.false_eq_true, ↓reduceIte] at htarget
  rw [hchild] at htarget
  simp at htarget

end WholeTargetBoundary

end PlayerNeutralAnalyticCirculationTerminalData
end AnalyticBellmanGerm

end StochasticGame
end GameTheory
