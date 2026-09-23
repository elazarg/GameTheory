/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

/-
# Continuation games and subgame-perfect transfer

The game at a history uses the existing information-local policy carrier and
history runner. A certified horizon makes its expected utility agree with
well-founded continuation value. Thus pure subgame perfection is ordinary
Nash in each proper continuation game.

Transfer fixes one playerwise compiler. Each proper target root must match a
proper source root before a deviation is selected. Initial outcome laws alone
do not supply that coverage. No new equilibrium predicate or evaluator is used.
-/

import GameTheory.Protocol.Strategic
import GameTheory.Protocol.SubgamePerfect
import GameTheory.Core.MixtureSimulation

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability

universe uι us ua up uq uk us' ua' up' uq' uk' uv uσ uω uσ' uω'

variable {ι : Type uι}

namespace InformationModel

variable {E : ExecutionProtocol.{uι, us, ua} ι}
  (M : InformationModel.{uι, us, ua, up, uq, uk} E)

/-- Canonical Nash in each proper continuation of a fixed strategy signature.
The supplied play law determines the strategy interpretation. Pure, behavioral,
and single-mover behavioral play specialize this same root quantification. -/
abbrev IsContinuationNash [DecidableEq ι] {sig : GameSignature.{uι, uσ, uω} ι}
    (play : E.History → Profile sig → FinDist sig.Outcome)
    (profile : Profile sig) (utility : sig.Outcome → ι → ℝ) : Prop :=
  ∀ history, M.IsSubgameRoot history →
    IsNash { sig := sig, play := play history } (euPreference utility) profile

theorem isContinuationNash_iff [DecidableEq ι]
    {sig : GameSignature.{uι, uσ, uω} ι}
    (play : E.History → Profile sig → FinDist sig.Outcome)
    (profile : Profile sig) (utility : sig.Outcome → ι → ℝ) :
    M.IsContinuationNash play profile utility ↔
      ∀ history, M.IsSubgameRoot history → ∀ who replacement,
        (play history (Profile.update profile who replacement)).expect (utility · who) ≤
          (play history profile).expect (utility · who) := by
  simp only [IsContinuationNash, isNash_iff]
  rfl

/-- Continuation Nash depends only on the supplied laws at proper roots. -/
theorem isContinuationNash_congr [DecidableEq ι]
    {sig : GameSignature.{uι, uσ, uω} ι}
    {first second : E.History → Profile sig → FinDist sig.Outcome}
    (same : ∀ history, M.IsSubgameRoot history → ∀ profile,
      first history profile = second history profile)
    (profile : Profile sig) (utility : sig.Outcome → ι → ℝ) :
    M.IsContinuationNash first profile utility ↔
      M.IsContinuationNash second profile utility := by
  simp only [isContinuationNash_iff]
  constructor <;> intro optimal history proper who replacement
  · simpa only [← same history proper] using optimal history proper who replacement
  · simpa only [same history proper] using optimal history proper who replacement

section Transfer

variable {T : ExecutionProtocol.{uι, us', ua'} ι}
  (N : InformationModel.{uι, us', ua', up', uq', uk'} T)
  [DecidableEq ι]
  {sourceSig : GameSignature.{uι, uσ, uω} ι}
  {targetSig : GameSignature.{uι, uσ', uω'} ι}
  {sourcePlay : E.History → Profile sourceSig → FinDist sourceSig.Outcome}
  {targetPlay : T.History → Profile targetSig → FinDist targetSig.Outcome}

/-- Match each proper target root before selecting the deviator. The strategic
calculation is Core's profile-local mixture transfer at that pair of roots. -/
theorem isContinuationNash_of_laws
    (compile : ∀ who, sourceSig.Strategy who → targetSig.Strategy who)
    {Observation : Type uv} (sourceObserve : sourceSig.Outcome → Observation)
    (targetObserve : targetSig.Outcome → Observation) (profile : Profile sourceSig)
    (coverage : ∀ targetRoot, N.IsSubgameRoot targetRoot →
      ∃ sourceRoot, M.IsSubgameRoot sourceRoot ∧
        (targetPlay targetRoot (Profile.map compile profile)).map targetObserve =
          (sourcePlay sourceRoot profile).map sourceObserve ∧
        ∀ who alternative, ∃ mixture : FinDist (sourceSig.Strategy who),
          (targetPlay targetRoot
            (Profile.update (Profile.map compile profile) who alternative)).map targetObserve =
          mixture.bind fun replacement =>
            (sourcePlay sourceRoot (Profile.update profile who replacement)).map sourceObserve)
    (utility : Observation → ι → ℝ)
    (perfect : M.IsContinuationNash sourcePlay profile
      (fun outcome who => utility (sourceObserve outcome) who)) :
    N.IsContinuationNash targetPlay (Profile.map compile profile)
      (fun outcome who => utility (targetObserve outcome) who) := by
  intro targetRoot proper
  obtain ⟨sourceRoot, sourceProper, honest, deviations⟩ := coverage targetRoot proper
  have sourceNash := perfect sourceRoot sourceProper
  rw [isNash_iff_isεNash_zero] at sourceNash
  have bounds := GameForm.considered_deviations_of_isεNash_of_mixtures
    (source := { sig := sourceSig, play := sourcePlay sourceRoot })
    (target := { sig := targetSig, play := targetPlay targetRoot })
    profile (Profile.map compile profile) (fun _ _ => True) honest
    (fun who replacement _ => deviations who replacement) utility 0 sourceNash
  rw [isNash_iff]
  exact fun who replacement => by
    simpa only [euPreference, expectedUtility, add_zero] using bounds who replacement trivial

/-- Reflection covers proper source roots and only uses honest compiled laws.
It imposes no coverage premise on arbitrary target deviations. -/
theorem isContinuationNash_of_compiled_laws
    (compile : ∀ who, sourceSig.Strategy who → targetSig.Strategy who)
    {Observation : Type uv} (sourceObserve : sourceSig.Outcome → Observation)
    (targetObserve : targetSig.Outcome → Observation)
    (coverage : ∀ sourceRoot, M.IsSubgameRoot sourceRoot →
      ∃ targetRoot, N.IsSubgameRoot targetRoot ∧
        ∀ profile : Profile sourceSig,
          (targetPlay targetRoot (Profile.map compile profile)).map targetObserve =
            (sourcePlay sourceRoot profile).map sourceObserve)
    (profile : Profile sourceSig) (utility : Observation → ι → ℝ)
    (perfect : N.IsContinuationNash targetPlay (Profile.map compile profile)
      (fun outcome who => utility (targetObserve outcome) who)) :
    M.IsContinuationNash sourcePlay profile
      (fun outcome who => utility (sourceObserve outcome) who) := by
  intro sourceRoot proper
  obtain ⟨targetRoot, targetProper, laws⟩ := coverage sourceRoot proper
  exact GameForm.isNash_of_honest_law
    (source := { sig := sourceSig, play := sourcePlay sourceRoot })
    (target := { sig := targetSig, play := targetPlay targetRoot })
    (sourceObserve := sourceObserve) (targetObserve := targetObserve)
    compile laws utility profile (perfect targetRoot targetProper)

end Transfer

/-- Ordinary strategic form at a retained history. Strategies are whole
information-local policies; the prefix is supplied and is never replayed. -/
@[reducible] def toContinuationGameForm (fuel : ℕ) (history : E.History) : GameForm ι where
  sig := M.strategicSignature
  play profile := M.runFrom profile fuel history

theorem historyBackwardValue_eq_expect_runFrom_of_bound
    (certificate : E.WellFoundedPlay) {bound : ℕ} (bounded : E.BoundedHorizon bound)
    (profile : Profile M.strategicSignature) (payoff : E.History → ℝ) (history : E.History) :
    E.historyBackwardValue certificate (M.historyChooser profile) payoff history =
      (M.runFrom profile bound history).expect payoff :=
  E.historyBackwardValue_eq_expect_runHistoryFor
    (E.stopsHistoryWithin_of_bound bounded _ _)

theorem isSubgamePerfect_iff_isNash_continuation [DecidableEq ι]
    (certificate : E.WellFoundedPlay) {bound : ℕ} (bounded : E.BoundedHorizon bound)
    (profile : Profile M.strategicSignature) (utility : E.History → ι → ℝ) :
    M.IsSubgamePerfect certificate profile utility ↔
      ∀ history, M.IsSubgameRoot history →
        IsNash (M.toContinuationGameForm bound history) (euPreference utility) profile := by
  constructor
  · intro perfect history proper
    rw [isNash_iff]
    intro who alternative
    show (M.runFrom (Profile.update profile who alternative) bound history).expect
        (utility · who) ≤ (M.runFrom profile bound history).expect (utility · who)
    rw [← M.historyBackwardValue_eq_expect_runFrom_of_bound certificate bounded,
      ← M.historyBackwardValue_eq_expect_runFrom_of_bound certificate bounded]
    exact perfect history proper who alternative
  · intro optimal history proper who alternative
    rw [M.historyBackwardValue_eq_expect_runFrom_of_bound certificate bounded,
      M.historyBackwardValue_eq_expect_runFrom_of_bound certificate bounded]
    have bound := optimal history proper
    rw [isNash_iff] at bound
    exact bound who alternative

variable {T : ExecutionProtocol.{uι, us', ua'} ι}
  (N : InformationModel.{uι, us', ua', up', uq', uk'} T)

/-- Exact continuation laws and unilateral mixture coverage preserve pure
SPE. The matching source root is chosen once per proper target root, before
the deviator or replacement. Every target root is covered, including roots
outside the prescribed profile's support. No finiteness of players or action
carriers, nor an equilibrium-existence premise, is required. -/
theorem isSubgamePerfect_of_continuation_laws [DecidableEq ι]
    (sourceTerminates : E.WellFoundedPlay) (targetTerminates : T.WellFoundedPlay)
    {sourceBound targetBound : ℕ} (sourceBounded : E.BoundedHorizon sourceBound)
    (targetBounded : T.BoundedHorizon targetBound)
    (compile : ∀ who, M.Policy who → N.Policy who)
    {Observation : Type uv} (sourceObserve : E.History → Observation)
    (targetObserve : T.History → Observation) (profile : Profile M.strategicSignature)
    (coverage : ∀ targetRoot, N.IsSubgameRoot targetRoot →
      ∃ sourceRoot, M.IsSubgameRoot sourceRoot ∧
        (N.runFrom (Profile.map (target := N.strategicSignature) compile profile)
          targetBound targetRoot).map targetObserve =
          (M.runFrom profile sourceBound sourceRoot).map sourceObserve ∧
        ∀ who (alternative : N.Policy who), ∃ mixture : FinDist (M.Policy who),
          (N.runFrom (Profile.update
            (Profile.map (target := N.strategicSignature) compile profile) who alternative)
            targetBound targetRoot).map targetObserve =
          mixture.bind fun replacement =>
            (M.runFrom (Profile.update profile who replacement) sourceBound sourceRoot).map
              sourceObserve)
    (utility : Observation → ι → ℝ)
    (perfect : M.IsSubgamePerfect sourceTerminates profile
      (fun history who => utility (sourceObserve history) who)) :
    N.IsSubgamePerfect targetTerminates (Profile.map compile profile)
      (fun history who => utility (targetObserve history) who) := by
  apply (N.isSubgamePerfect_iff_isNash_continuation targetTerminates targetBounded
    (Profile.map (target := N.strategicSignature) compile profile)
    (fun history who => utility (targetObserve history) who)).mpr
  exact M.isContinuationNash_of_laws N
    (sourceSig := M.strategicSignature) (targetSig := N.strategicSignature)
    (sourcePlay := fun history policies => M.runFrom policies sourceBound history)
    (targetPlay := fun history policies => N.runFrom policies targetBound history)
    compile sourceObserve targetObserve profile coverage utility
    ((M.isSubgamePerfect_iff_isNash_continuation sourceTerminates sourceBounded
      profile (fun history who => utility (sourceObserve history) who)).mp perfect)

/-- Reflection needs coverage of proper source roots. At a matching proper
target root, honest laws for all source profiles also realize every compiled
source replacement. No simulation of arbitrary target deviations is needed
for this direction. -/
theorem isSubgamePerfect_of_compiled_of_continuation_laws [DecidableEq ι]
    (sourceTerminates : E.WellFoundedPlay) (targetTerminates : T.WellFoundedPlay)
    {sourceBound targetBound : ℕ} (sourceBounded : E.BoundedHorizon sourceBound)
    (targetBounded : T.BoundedHorizon targetBound)
    (compile : ∀ who, M.Policy who → N.Policy who)
    {Observation : Type uv} (sourceObserve : E.History → Observation)
    (targetObserve : T.History → Observation)
    (coverage : ∀ sourceRoot, M.IsSubgameRoot sourceRoot →
      ∃ targetRoot, N.IsSubgameRoot targetRoot ∧
        ∀ profile : Profile M.strategicSignature,
          (N.runFrom (Profile.map (target := N.strategicSignature) compile profile)
            targetBound targetRoot).map targetObserve =
          (M.runFrom profile sourceBound sourceRoot).map sourceObserve)
    (profile : Profile M.strategicSignature) (utility : Observation → ι → ℝ)
    (perfect : N.IsSubgamePerfect targetTerminates (Profile.map compile profile)
      (fun history who => utility (targetObserve history) who)) :
    M.IsSubgamePerfect sourceTerminates profile
      (fun history who => utility (sourceObserve history) who) := by
  apply (M.isSubgamePerfect_iff_isNash_continuation sourceTerminates sourceBounded
    profile (fun history who => utility (sourceObserve history) who)).mpr
  intro sourceRoot proper
  obtain ⟨targetRoot, targetProper, laws⟩ := coverage sourceRoot proper
  have targetEquiv := N.isSubgamePerfect_iff_isNash_continuation
    targetTerminates targetBounded (Profile.map (target := N.strategicSignature) compile profile)
    (fun history who => utility (targetObserve history) who)
  have targetOptimal := targetEquiv.mp perfect
  have targetNash := targetOptimal targetRoot targetProper
  exact GameForm.isNash_of_honest_law
    (source := M.toContinuationGameForm sourceBound sourceRoot)
    (target := N.toContinuationGameForm targetBound targetRoot)
    (sourceObserve := sourceObserve) (targetObserve := targetObserve)
    compile laws utility profile targetNash

end InformationModel
end GameTheory.Protocol
