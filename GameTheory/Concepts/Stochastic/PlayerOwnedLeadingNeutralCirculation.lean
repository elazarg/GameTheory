/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.AnalyticPlayerNeutralOccupationAlternative
import GameTheory.Concepts.Stochastic.PlayerNeutralAnalyticDeflationTerminal
import GameTheory.Concepts.Stochastic.PlayerOwnedCirculationLeadingNeutrality

/-!
# Equal-order player-owned leading circulation

When the first nonzero mass coefficient of a full player-owned analytic
charged circulation occurs exactly at its pole-clearing order, that
coefficient retains unit endpoint charge.  Endpoint-value balance forces
every pure action carrying positive leading mass to be continuation-neutral.
Nonnegativity then forces every endpoint-strict action to carry zero mass.

Consequently the leading coefficient restricts to the existing
player-neutral operational family and gives an actual normalized positive
charged circulation there.  This is the static endpoint object consumed by
the player-neutral occupation, recurrent-class, and potential-jet hierarchy.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm

open Math Math.Probability
open Math.Probability.AnalyticPositiveChargedCirculation

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

/-- Forget the proof of endpoint continuation neutrality and regard a
player-neutral operational index as a full player-owned index. -/
def playerNeutralToOwnerOccupationIndex
    {germ : G.AnalyticBellmanGerm} (who : ι) :
    germ.PlayerNeutralOccupationIndex who → OwnerOccupationIndex G who
  | .inl source => .inl source
  | .inr response => .inr response.1

/-- The full player-owned moving column restricted along the neutral
embedding is the moving player-neutral column. -/
theorem rawOwnerAnalyticOccupationColumn_playerNeutralToOwner
    (germ : G.AnalyticBellmanGerm) (who : ι)
    (t : ℝ) (index : germ.PlayerNeutralOccupationIndex who) :
    germ.rawOwnerAnalyticOccupationColumn who t
        (playerNeutralToOwnerOccupationIndex who index) =
      germ.rawPlayerNeutralOccupationColumn who t index := by
  cases index <;> rfl

omit [DecidableEq G.State] in
/-- The full player-owned moving charge restricted along the neutral
embedding is the moving player-neutral charge. -/
theorem rawPlayerOwnedOccupationCharge_playerNeutralToOwner
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (t : ℝ) (index : germ.PlayerNeutralOccupationIndex who) :
    germ.rawPlayerOwnedOccupationCharge B who t
        (playerNeutralToOwnerOccupationIndex who index) =
      germ.rawPlayerNeutralOccupationCharge B who t index := by
  cases index <;> rfl

namespace PlayerOwnedLeadingNeutralCirculation

local instance playerNeutralOccupationIndexDecidableEq
    (germ : G.AnalyticBellmanGerm) (who : ι) :
    DecidableEq (germ.PlayerNeutralOccupationIndex who) :=
  Classical.decEq _

/-- An endpoint-strict pure action has zero leading mass. -/
theorem action_mass_eq_zero_of_not_neutral
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    {C : AnalyticPositiveChargedCirculation
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who)}
    (jet : C.LeadingMassJet)
    (source : G.State) (action : G.Act who)
    (strict :
      G.finkContinuationGain germ.endpointValue
        germ.endpointFinkPoint source who action ≠ 0) :
    jet.factor 0 (.inr (source, action)) = 0 := by
  apply le_antisymm
  · apply le_of_not_gt
    intro positive
    exact strict
      (AnalyticPositiveChargedCirculation.LeadingMassJet.action_neutral_of_pos
        germ B who jet source action positive)
  · exact jet.leading_nonnegative _

/-- Restrict the endpoint leading mass to the operational family of
prescribed rows and continuation-neutral actions. -/
def mass
    {germ : G.AnalyticBellmanGerm}
    {B : G.State → Payoff ι} {who : ι}
    {C : AnalyticPositiveChargedCirculation
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who)}
    (jet : C.LeadingMassJet) :
    germ.PlayerNeutralOccupationIndex who → ℝ :=
  fun index =>
    jet.factor 0 (playerNeutralToOwnerOccupationIndex who index)

theorem mass_nonnegative
    {germ : G.AnalyticBellmanGerm}
    {B : G.State → Payoff ι} {who : ι}
    {C : AnalyticPositiveChargedCirculation
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who)}
    (jet : C.LeadingMassJet)
    (index : germ.PlayerNeutralOccupationIndex who) :
    0 ≤ mass jet index :=
  jet.leading_nonnegative _

private theorem sum_owner_actions_eq_sum_neutral_actions
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    {C : AnalyticPositiveChargedCirculation
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who)}
    (jet : C.LeadingMassJet)
    (term : G.State × G.Act who → ℝ) :
    (∑ response : G.State × G.Act who,
        jet.factor 0 (.inr response) * term response) =
      ∑ response : germ.ContinuationNeutralAction who,
        jet.factor 0 (.inr response.1) * term response.1 := by
  classical
  unfold ContinuationNeutralAction
  rw [← Finset.sum_subtype
    (Finset.univ.filter fun response =>
      G.finkContinuationGain germ.endpointValue
        germ.endpointFinkPoint response.1 who response.2 = 0)
    (fun response => by simp)
    (fun response =>
      jet.factor 0 (.inr response) * term response)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro response _
  by_cases neutral :
      G.finkContinuationGain germ.endpointValue
        germ.endpointFinkPoint response.1 who response.2 = 0
  · simp [neutral]
  · have mass_zero :=
      action_mass_eq_zero_of_not_neutral
        germ B who jet response.1 response.2 neutral
    simp [neutral, mass_zero]

/-- The endpoint leading mass, restricted to neutral actions, balances the
static actual player-neutral occupation columns. -/
theorem mass_balance
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    {C : AnalyticPositiveChargedCirculation
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who)}
    (jet : C.LeadingMassJet)
    (destination : G.State) :
    ∑ index,
        mass jet index *
          actualOccupationColumn
            (germ.playerNeutralOccupationKernel who)
            (germ.playerNeutralOccupationSource who)
            index destination = 0 := by
  classical
  have endpoint_balance := jet.endpoint_balance destination
  rw [Fintype.sum_sum_type] at endpoint_balance
  rw [Fintype.sum_sum_type]
  have action_sum :=
    sum_owner_actions_eq_sum_neutral_actions
      germ B who jet
      (fun response =>
        germ.rawOwnerAnalyticOccupationColumn
          who 0 (.inr response) destination)
  rw [action_sum] at endpoint_balance
  have column_eq
      (index : germ.PlayerNeutralOccupationIndex who) :
      germ.rawOwnerAnalyticOccupationColumn who 0
          (playerNeutralToOwnerOccupationIndex who index) destination =
        actualOccupationColumn
          (germ.playerNeutralOccupationKernel who)
          (germ.playerNeutralOccupationSource who)
          index destination := by
    rw [rawOwnerAnalyticOccupationColumn_playerNeutralToOwner]
    exact congrFun
      (congrFun (germ.rawPlayerNeutralOccupationColumn_zero who) index)
      destination
  have baseline_sum_eq :
      (∑ source : G.State,
          jet.factor 0 (.inl source) *
            germ.rawOwnerAnalyticOccupationColumn
              who 0 (.inl source) destination) =
        ∑ source : G.State,
          jet.factor 0 (.inl source) *
            actualOccupationColumn
              (germ.playerNeutralOccupationKernel who)
              (germ.playerNeutralOccupationSource who)
              (.inl source) destination := by
    apply Finset.sum_congr rfl
    intro source _
    exact congrArg
      (fun value => jet.factor 0 (.inl source) * value)
      (by
        simpa only [playerNeutralToOwnerOccupationIndex] using
          column_eq (.inl source))
  have neutral_sum_eq :
      (∑ response : germ.ContinuationNeutralAction who,
          jet.factor 0 (.inr response.1) *
            germ.rawOwnerAnalyticOccupationColumn
              who 0 (.inr response.1) destination) =
        ∑ response : germ.ContinuationNeutralAction who,
          jet.factor 0 (.inr response.1) *
            actualOccupationColumn
              (germ.playerNeutralOccupationKernel who)
              (germ.playerNeutralOccupationSource who)
              (.inr response) destination := by
    apply Finset.sum_congr rfl
    intro response _
    exact congrArg
      (fun value => jet.factor 0 (.inr response.1) * value)
      (by
        simpa only [playerNeutralToOwnerOccupationIndex] using
          column_eq (.inr response))
  rw [baseline_sum_eq, neutral_sum_eq] at endpoint_balance
  simpa only [mass, playerNeutralToOwnerOccupationIndex] using
    endpoint_balance

/-- At equal leading and clearing orders, the restricted endpoint leading
mass has unit static player-neutral charge. -/
theorem mass_charge_eq_one
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    {C : AnalyticPositiveChargedCirculation
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who)}
    (jet : C.LeadingMassJet)
    (horder : jet.order = C.poleOrder) :
    ∑ index,
        mass jet index *
          germ.playerNeutralOccupationCharge B who index = 1 := by
  classical
  have endpoint_charge := jet.endpoint_weightedCharge_eq_one horder
  rw [Fintype.sum_sum_type] at endpoint_charge
  rw [Fintype.sum_sum_type]
  have action_sum :=
    sum_owner_actions_eq_sum_neutral_actions
      germ B who jet
      (fun response =>
        germ.rawPlayerOwnedOccupationCharge
          B who 0 (.inr response))
  rw [action_sum] at endpoint_charge
  have charge_eq
      (index : germ.PlayerNeutralOccupationIndex who) :
      germ.rawPlayerOwnedOccupationCharge B who 0
          (playerNeutralToOwnerOccupationIndex who index) =
        germ.playerNeutralOccupationCharge B who index := by
    rw [rawPlayerOwnedOccupationCharge_playerNeutralToOwner]
    exact congrFun
      (germ.rawPlayerNeutralOccupationCharge_zero B who) index
  have baseline_sum_eq :
      (∑ source : G.State,
          jet.factor 0 (.inl source) *
            germ.rawPlayerOwnedOccupationCharge
              B who 0 (.inl source)) =
        ∑ source : G.State,
          jet.factor 0 (.inl source) *
            germ.playerNeutralOccupationCharge
              B who (.inl source) := by
    apply Finset.sum_congr rfl
    intro source _
    exact congrArg
      (fun value => jet.factor 0 (.inl source) * value)
      (by
        simpa only [playerNeutralToOwnerOccupationIndex] using
          charge_eq (.inl source))
  have neutral_sum_eq :
      (∑ response : germ.ContinuationNeutralAction who,
          jet.factor 0 (.inr response.1) *
            germ.rawPlayerOwnedOccupationCharge
              B who 0 (.inr response.1)) =
        ∑ response : germ.ContinuationNeutralAction who,
          jet.factor 0 (.inr response.1) *
            germ.playerNeutralOccupationCharge
              B who (.inr response) := by
    apply Finset.sum_congr rfl
    intro response _
    exact congrArg
      (fun value => jet.factor 0 (.inr response.1) * value)
      (by
        simpa only [playerNeutralToOwnerOccupationIndex] using
          charge_eq (.inr response))
  rw [baseline_sum_eq, neutral_sum_eq] at endpoint_charge
  simpa only [mass, playerNeutralToOwnerOccupationIndex] using
    endpoint_charge

/-- **Equal-order bridge.**  A full player-owned analytic charged
circulation whose leading mass occurs at the pole-clearing order yields the
existing normalized positive charged circulation on the static
player-neutral actual occupation family. -/
theorem hasNormalizedPositiveChargedCirculation_playerNeutral
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    {C : AnalyticPositiveChargedCirculation
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who)}
    (jet : C.LeadingMassJet)
    (horder : jet.order = C.poleOrder) :
    HasNormalizedPositiveChargedCirculation
      (actualOccupationColumn
        (germ.playerNeutralOccupationKernel who)
        (germ.playerNeutralOccupationSource who))
      (germ.playerNeutralOccupationCharge B who) := by
  exact ⟨
    mass jet,
    mass_nonnegative jet,
    mass_balance germ B who jet,
    mass_charge_eq_one germ B who jet horder⟩

/-- The active subtype of the full player-neutral deflation node is
canonically equivalent to its ambient player-neutral occupation type. -/
def fullDeflationActiveEquiv
    (germ : G.AnalyticBellmanGerm) (who : ι) :
    (PlayerNeutralStrictLeadingDrift.fullDeflationState
      (germ := germ) (who := who)).ActiveIndex ≃
        germ.PlayerNeutralOccupationIndex who :=
  Equiv.ofBijective Subtype.val
    ⟨Subtype.val_injective, fun index =>
      ⟨⟨index, Finset.mem_univ index⟩, rfl⟩⟩

/-- The equal-order circulation, reindexed onto the active subtype of the
full player-neutral deflation node. -/
theorem fullDeflationState_hasEndpointCirculation
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    {C : AnalyticPositiveChargedCirculation
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who)}
    (jet : C.LeadingMassJet)
    (horder : jet.order = C.poleOrder) :
    HasNormalizedPositiveChargedCirculation
      (activeOccupationColumn
        (PlayerNeutralStrictLeadingDrift.fullDeflationState
          (germ := germ) (who := who))
        (germ.rawPlayerNeutralOccupationColumn who) 0)
      (activeOccupationCharge
        (PlayerNeutralStrictLeadingDrift.fullDeflationState
          (germ := germ) (who := who))
        (germ.rawPlayerNeutralOccupationCharge B who) 0) := by
  have static :=
    hasNormalizedPositiveChargedCirculation_playerNeutral
      germ B who jet horder
  have reindexed :=
    static.reindex
      (actualOccupationColumn
        (germ.playerNeutralOccupationKernel who)
        (germ.playerNeutralOccupationSource who))
      (germ.playerNeutralOccupationCharge B who)
      (fullDeflationActiveEquiv germ who)
  change
    HasNormalizedPositiveChargedCirculation
      (fun index :
          (PlayerNeutralStrictLeadingDrift.fullDeflationState
            (germ := germ) (who := who)).ActiveIndex =>
        germ.rawPlayerNeutralOccupationColumn who 0 index.1)
      (fun index :
          (PlayerNeutralStrictLeadingDrift.fullDeflationState
            (germ := germ) (who := who)).ActiveIndex =>
        germ.rawPlayerNeutralOccupationCharge B who 0 index.1)
  rw [germ.rawPlayerNeutralOccupationColumn_zero who,
    germ.rawPlayerNeutralOccupationCharge_zero B who]
  exact reindexed

/-- Run the existing finite player-neutral analytic deflation from the full
operational family.  The anchor remains explicit: this theorem supplies the
analytic terminal data, not a legal entry state or a target-preserving
recurrent child. -/
theorem exists_playerNeutralAnalyticDeflationTerminalData
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    {C : AnalyticPositiveChargedCirculation
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who)}
    (jet : C.LeadingMassJet)
    (horder : jet.order = C.poleOrder)
    (terminalAnchor : G.State) :
    Nonempty
      (PlayerNeutralAnalyticDeflationTerminalData
        germ B who
        (PlayerNeutralStrictLeadingDrift.fullDeflationState
          (germ := germ) (who := who))
        terminalAnchor) :=
  germ.exists_playerNeutralAnalyticDeflationTerminalData
    B who
    (PlayerNeutralStrictLeadingDrift.fullDeflationState
      (germ := germ) (who := who))
    (fullDeflationState_hasEndpointCirculation
      germ B who jet horder)
    terminalAnchor

end PlayerOwnedLeadingNeutralCirculation

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
