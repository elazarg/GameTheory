/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

/-
# Behavioral Nash at proper continuation roots

Finite-player simultaneous play and single-mover play with arbitrary players
specialize the same continuation-Nash predicate. Both use canonical randomized
histories. A certified bound supplies evaluation fuel, and larger certified
bounds give the same laws. Transfer is inherited from `IsContinuationNash`.
-/

import GameTheory.Protocol.SingleMover
import GameTheory.Protocol.Continuation

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

universe uι us ua up uq uk

variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
  (M : InformationModel.{uι, us, ua, up, uq, uk} E)

/-- Behavioral strategies evaluated from a retained history. Simultaneous
decisions use the same independent product as the canonical behavioral runner. -/
@[reducible] def toBehavioralContinuationGameForm [Fintype ι]
    (fuel : ℕ) (history : E.History) : GameForm ι where
  sig := M.behavioralSignature
  play profile := M.runBehavioralFrom profile fuel history

/-- Behavioral SPE is canonical Nash in every information-set-closed subgame.
The bound covers every legal history, including deviations and off-path roots. -/
abbrev IsBehavioralSubgamePerfect [Fintype ι] [DecidableEq ι] {bound : ℕ}
    (_bounded : E.BoundedHorizon bound) (profile : Profile M.behavioralSignature)
    (utility : E.History → ι → ℝ) : Prop :=
  M.IsContinuationNash (fun history policies => M.runBehavioralFrom policies bound history)
    profile utility

theorem isBehavioralSubgamePerfect_iff [Fintype ι] [DecidableEq ι]
    {bound : ℕ} (bounded : E.BoundedHorizon bound)
    (profile : Profile M.behavioralSignature) (utility : E.History → ι → ℝ) :
    M.IsBehavioralSubgamePerfect bounded profile utility ↔
      ∀ history, M.IsSubgameRoot history → ∀ who (alternative : M.BehavioralPolicy who),
        ∃ hbase : UtilityIntegrable utility who
            (M.runBehavioralFrom profile bound history),
          ∃ hdev : UtilityIntegrable utility who
              (M.runBehavioralFrom (Profile.update profile who alternative)
                bound history),
            expectedUtility utility who
                (M.runBehavioralFrom (Profile.update profile who alternative)
                  bound history) hdev ≤
              expectedUtility utility who
                (M.runBehavioralFrom profile bound history) hbase :=
  M.isContinuationNash_iff _ _ _

/-- Evaluation fuel is not a semantic deadline. -/
theorem isBehavioralSubgamePerfect_bound_iff [Fintype ι] [DecidableEq ι]
    {first second : ℕ} (firstBound : E.BoundedHorizon first)
    (secondBound : E.BoundedHorizon second)
    (profile : Profile M.behavioralSignature) (utility : E.History → ι → ℝ) :
    M.IsBehavioralSubgamePerfect firstBound profile utility ↔
      M.IsBehavioralSubgamePerfect secondBound profile utility := by
  apply M.isContinuationNash_congr
  intro history _ policies
  exact (E.runRandomizedFor_eq_of_bound firstBound _ history
    (max first second) (Nat.le_max_left _ _)).symm.trans
    (E.runRandomizedFor_eq_of_bound secondBound _ history
      (max first second) (Nat.le_max_right _ _))

/-- A point-mass behavioral SPE defeats every pure replacement. -/
theorem isSubgamePerfect_of_behavioral [Fintype ι] [DecidableEq ι]
    {bound : ℕ} (bounded : E.BoundedHorizon bound)
    (certificate : E.WellFoundedPlay) (profile : Profile M.strategicSignature)
    (utility : E.History → ι → ℝ)
    (perfect : M.IsBehavioralSubgamePerfect bounded
      (Profile.map (target := M.behavioralSignature)
        (fun who (policy : M.Policy who) => policy.toBehavioral) profile) utility) :
    M.IsSubgamePerfect certificate profile utility := by
  rw [M.isSubgamePerfect_iff_isNash_continuation certificate bounded]
  intro history proper
  apply GameForm.isNash_of_honest_law
    (source := M.toContinuationGameForm bound history)
    (target := M.toBehavioralContinuationGameForm bound history)
    (sourceObserve := id) (targetObserve := id)
    (fun who (policy : M.Policy who) => policy.toBehavioral)
  · intro pureProfile
    simp only [PMF.map_id]
    exact M.runBehavioralFrom_toBehavioral pureProfile bound history
  · exact perfect history proper

section SingleMover

variable [DecidableEq ι]
  (single : ∀ (state : E.State) {first second : ι},
    E.active state first → E.active state second → first = second)

/-- The same behavioral continuation form without an ambient finite-player
assumption, when at most one player moves. -/
@[reducible] def toSingleMoverBehavioralContinuationGameForm
    (fuel : ℕ) (history : E.History) : GameForm ι where
  sig := M.behavioralSignature
  play profile := M.runSingleMoverBehavioralFrom single profile fuel history

/-- The single-mover specialization of canonical continuation Nash. -/
abbrev IsSingleMoverBehavioralSubgamePerfect {bound : ℕ}
    (_bounded : E.BoundedHorizon bound) (profile : Profile M.behavioralSignature)
    (utility : E.History → ι → ℝ) : Prop :=
  M.IsContinuationNash
    (fun history policies => M.runSingleMoverBehavioralFrom single policies bound history)
    profile utility

theorem isSingleMoverBehavioralSubgamePerfect_iff {bound : ℕ}
    (bounded : E.BoundedHorizon bound) (profile : Profile M.behavioralSignature)
    (utility : E.History → ι → ℝ) :
    M.IsSingleMoverBehavioralSubgamePerfect single bounded profile utility ↔
      ∀ history, M.IsSubgameRoot history → ∀ who (alternative : M.BehavioralPolicy who),
        ∃ hbase : UtilityIntegrable utility who
            (M.runSingleMoverBehavioralFrom single profile bound history),
          ∃ hdev : UtilityIntegrable utility who
              (M.runSingleMoverBehavioralFrom single
                (Profile.update profile who alternative) bound history),
            expectedUtility utility who
                (M.runSingleMoverBehavioralFrom single
                  (Profile.update profile who alternative) bound history) hdev ≤
              expectedUtility utility who
                (M.runSingleMoverBehavioralFrom single profile bound history) hbase :=
  M.isContinuationNash_iff _ _ _

/-- Single-mover behavioral SPE is also independent of the certified bound. -/
theorem isSingleMoverBehavioralSubgamePerfect_bound_iff {first second : ℕ}
    (firstBound : E.BoundedHorizon first) (secondBound : E.BoundedHorizon second)
    (profile : Profile M.behavioralSignature) (utility : E.History → ι → ℝ) :
    M.IsSingleMoverBehavioralSubgamePerfect single firstBound profile utility ↔
      M.IsSingleMoverBehavioralSubgamePerfect single secondBound profile utility := by
  apply M.isContinuationNash_congr
  intro history _ policies
  exact (E.runRandomizedFor_eq_of_bound firstBound _ history
    (max first second) (Nat.le_max_left _ _)).symm.trans
    (E.runRandomizedFor_eq_of_bound secondBound _ history
      (max first second) (Nat.le_max_right _ _))

/-- The two constructions agree whenever both apply. -/
theorem toSingleMoverBehavioralContinuationGameForm_eq [Fintype ι]
    (fuel : ℕ) (history : E.History) :
    M.toSingleMoverBehavioralContinuationGameForm single fuel history =
      M.toBehavioralContinuationGameForm fuel history := by
  simp only [toSingleMoverBehavioralContinuationGameForm, toBehavioralContinuationGameForm,
    M.runSingleMoverBehavioralFrom_eq_runBehavioralFrom]

theorem isSingleMoverBehavioralSubgamePerfect_iff_behavioral [Fintype ι]
    {bound : ℕ} (bounded : E.BoundedHorizon bound)
    (profile : Profile M.behavioralSignature) (utility : E.History → ι → ℝ) :
    M.IsSingleMoverBehavioralSubgamePerfect single bounded profile utility ↔
      M.IsBehavioralSubgamePerfect bounded profile utility := by
  apply M.isContinuationNash_congr
  exact fun history _ policies =>
    M.runSingleMoverBehavioralFrom_eq_runBehavioralFrom single policies bound history

/-- The pure implication does not require finitely many possible players. -/
theorem isSubgamePerfect_of_singleMoverBehavioral {bound : ℕ}
    (bounded : E.BoundedHorizon bound) (certificate : E.WellFoundedPlay)
    (profile : Profile M.strategicSignature) (utility : E.History → ι → ℝ)
    (perfect : M.IsSingleMoverBehavioralSubgamePerfect single bounded
      (Profile.map (target := M.behavioralSignature)
        (fun who (policy : M.Policy who) => policy.toBehavioral) profile) utility) :
    M.IsSubgamePerfect certificate profile utility := by
  rw [M.isSubgamePerfect_iff_isNash_continuation certificate bounded]
  intro history proper
  apply GameForm.isNash_of_honest_law
    (source := M.toContinuationGameForm bound history)
    (target := M.toSingleMoverBehavioralContinuationGameForm single bound history)
    (sourceObserve := id) (targetObserve := id)
    (fun who (policy : M.Policy who) => policy.toBehavioral)
  · intro pureProfile
    simp only [PMF.map_id]
    exact M.runSingleMoverBehavioralFrom_toBehavioral single pureProfile bound history
  · exact perfect history proper

end SingleMover

end GameTheory.Protocol.InformationModel
