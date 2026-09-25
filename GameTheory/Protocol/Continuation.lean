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
    (play : E.History → Profile sig → PMF sig.Outcome)
    (profile : Profile sig) (utility : sig.Outcome → ι → ℝ) : Prop :=
  ∀ history, M.IsSubgameRoot history →
    IsNash { sig := sig, play := play history } (euPreference utility) profile

theorem isContinuationNash_iff [DecidableEq ι]
    {sig : GameSignature.{uι, uσ, uω} ι}
    (play : E.History → Profile sig → PMF sig.Outcome)
    (profile : Profile sig) (utility : sig.Outcome → ι → ℝ) :
    M.IsContinuationNash play profile utility ↔
      ∀ history, M.IsSubgameRoot history → ∀ who replacement,
        ∃ hbase : UtilityIntegrable utility who (play history profile),
          ∃ hdev : UtilityIntegrable utility who
              (play history (Profile.update profile who replacement)),
            expectedUtility utility who
                (play history (Profile.update profile who replacement)) hdev ≤
              expectedUtility utility who (play history profile) hbase := by
  simp only [IsContinuationNash, isNash_iff]
  rfl

/-- Continuation Nash depends only on the supplied laws at proper roots. -/
theorem isContinuationNash_congr [DecidableEq ι]
    {sig : GameSignature.{uι, uσ, uω} ι}
    {first second : E.History → Profile sig → PMF sig.Outcome}
    (same : ∀ history, M.IsSubgameRoot history → ∀ profile,
      first history profile = second history profile)
    (profile : Profile sig) (utility : sig.Outcome → ι → ℝ) :
    M.IsContinuationNash first profile utility ↔
      M.IsContinuationNash second profile utility := by
  simp only [IsContinuationNash]
  constructor <;> intro optimal history proper
  · have h := optimal history proper
    rw [isNash_iff] at h ⊢
    intro who replacement
    simpa only [euPreference_apply, ← same history proper] using h who replacement
  · have h := optimal history proper
    rw [isNash_iff] at h ⊢
    intro who replacement
    simpa only [euPreference_apply, same history proper] using h who replacement

section Transfer

variable {T : ExecutionProtocol.{uι, us', ua'} ι}
  (N : InformationModel.{uι, us', ua', up', uq', uk'} T)
  [DecidableEq ι]
  {sourceSig : GameSignature.{uι, uσ, uω} ι}
  {targetSig : GameSignature.{uι, uσ', uω'} ι}
  {sourcePlay : E.History → Profile sourceSig → PMF sourceSig.Outcome}
  {targetPlay : T.History → Profile targetSig → PMF targetSig.Outcome}

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
        ∀ who alternative, ∃ mixture : PMF (sourceSig.Strategy who),
          (targetPlay targetRoot
            (Profile.update (Profile.map compile profile) who alternative)).map targetObserve =
          mixture.bind fun replacement =>
            (sourcePlay sourceRoot (Profile.update profile who replacement)).map sourceObserve)
    (utility : Observation → ι → ℝ)
    (hdev : ∀ targetRoot, N.IsSubgameRoot targetRoot →
      ∀ who alternative, UtilityIntegrable
        (fun outcome player => utility (targetObserve outcome) player) who
        (targetPlay targetRoot
          (Profile.update (Profile.map compile profile) who alternative)))
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
    (fun who replacement _ => deviations who replacement) utility 0
    (fun who replacement _ => hdev targetRoot proper who replacement) sourceNash
  rw [isNash_iff]
  exact fun who replacement => by
    obtain ⟨hbase, halt, hle⟩ := bounds who replacement trivial
    exact ⟨hbase, halt, by simpa only [add_zero] using hle⟩

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
    (profile : Profile M.strategicSignature) (payoff : E.History → ℝ)
    (history : E.History)
    (hback : PayoffIntegrable
      (E.historyBackwardLaw certificate (M.historyChooser profile) history) payoff)
    (hrun : PayoffIntegrable (M.runFrom profile bound history) payoff) :
    E.historyBackwardValue certificate (M.historyChooser profile) payoff history hback =
      expect (M.runFrom profile bound history) payoff hrun :=
  E.historyBackwardValue_eq_expect_runHistoryFor
    (E.stopsHistoryWithin_of_bound bounded _ _) hback hrun

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
    obtain ⟨hbackDev, hbackBase, hle⟩ := perfect history proper who alternative
    have hdevLaw := E.historyBackwardLaw_eq_runHistoryFor
      (certificate := certificate)
      (E.stopsHistoryWithin_of_bound bounded
        (M.historyChooser (Profile.update profile who alternative)) history)
    have hbaseLaw := E.historyBackwardLaw_eq_runHistoryFor
      (certificate := certificate)
      (E.stopsHistoryWithin_of_bound bounded (M.historyChooser profile) history)
    have hrunDev : UtilityIntegrable utility who
        (M.runFrom (Profile.update profile who alternative) bound history) := by
      simp only [InformationModel.runFrom]
      rw [← hdevLaw]
      exact hbackDev
    have hrunBase : UtilityIntegrable utility who
        (M.runFrom profile bound history) := by
      simp only [InformationModel.runFrom]
      rw [← hbaseLaw]
      exact hbackBase
    refine ⟨hrunBase, hrunDev, ?_⟩
    simp only [toContinuationGameForm, expectedUtility]
    rw [← M.historyBackwardValue_eq_expect_runFrom_of_bound
      certificate bounded _ _ history hbackDev hrunDev,
      ← M.historyBackwardValue_eq_expect_runFrom_of_bound
        certificate bounded _ _ history hbackBase hrunBase]
    exact hle
  · intro optimal history proper who alternative
    have bound := optimal history proper
    rw [isNash_iff] at bound
    obtain ⟨hrunBase, hrunDev, hle⟩ := bound who alternative
    have hdevLaw := E.historyBackwardLaw_eq_runHistoryFor
      (certificate := certificate)
      (E.stopsHistoryWithin_of_bound bounded
        (M.historyChooser (Profile.update profile who alternative)) history)
    have hbaseLaw := E.historyBackwardLaw_eq_runHistoryFor
      (certificate := certificate)
      (E.stopsHistoryWithin_of_bound bounded (M.historyChooser profile) history)
    have hbackDev : PayoffIntegrable
        (E.historyBackwardLaw certificate
          (M.historyChooser (Profile.update profile who alternative)) history)
        (fun outcome => utility outcome who) := by
      rw [hdevLaw]
      simp only [InformationModel.runFrom] at hrunDev
      exact hrunDev
    have hbackBase : PayoffIntegrable
        (E.historyBackwardLaw certificate (M.historyChooser profile) history)
        (fun outcome => utility outcome who) := by
      rw [hbaseLaw]
      simp only [InformationModel.runFrom] at hrunBase
      exact hrunBase
    refine ⟨hbackDev, hbackBase, ?_⟩
    simp only [toContinuationGameForm, expectedUtility] at hle
    rw [M.historyBackwardValue_eq_expect_runFrom_of_bound
      certificate bounded _ _ history hbackDev hrunDev,
      M.historyBackwardValue_eq_expect_runFrom_of_bound
        certificate bounded _ _ history hbackBase hrunBase]
    exact hle

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
        ∀ who (alternative : N.Policy who), ∃ mixture : PMF (M.Policy who),
          (N.runFrom (Profile.update
            (Profile.map (target := N.strategicSignature) compile profile) who alternative)
            targetBound targetRoot).map targetObserve =
          mixture.bind fun replacement =>
            (M.runFrom (Profile.update profile who replacement) sourceBound sourceRoot).map
              sourceObserve)
    (utility : Observation → ι → ℝ)
    (hdev : ∀ targetRoot, N.IsSubgameRoot targetRoot →
      ∀ who (alternative : N.Policy who), UtilityIntegrable
        (fun history player => utility (targetObserve history) player) who
        (N.runFrom (Profile.update
          (Profile.map (target := N.strategicSignature) compile profile)
          who alternative) targetBound targetRoot))
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
    compile sourceObserve targetObserve profile coverage utility hdev
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
