/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.NormalCore
import UniformEquilibrium.Quitting.Stationary.Root
import UniformEquilibrium.Quitting.Punishment.ZeroSoloDisjunct

/-!
# Audited source interfaces for the quitting-game LCP gate

This file does not hide literature theorems in a broad existence axiom.  It
states narrow interfaces matching the audited conclusions.

* Solan--Solan's ordinary branches conclude **stationary undiscounted**
  approximate equilibria.  The Q side concludes a separate caller-supplied
  sunspot/public-correlation predicate.
* AGKRS Theorem 5.4 concludes a caller-supplied **continuous absorption-path
  equilibrium** predicate.  It is not identified here with an ordinary
  strategy profile, an approximate Nash equilibrium, or a uniform payoff.

The interfaces are stated after the exact playerwise translation and positive
rescaling adapters used in the papers.  Their matrix arguments are the proved
objects from `Normalization.lean` and `NormalCore.lean`.  A downstream import
may instantiate an interface only after separately auditing the corresponding
strategic semantics.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open StochasticGame Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Ordinary undiscounted approximate equilibria for the repository terminal
payoff functional. -/
def HasOrdinaryApproximateEquilibria
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε profile

/-- The stronger conclusion actually delivered by the ordinary
Solan--Solan branches: the witnesses are stationary. -/
def HasOrdinaryStationaryApproximateEquilibria
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ root : ι → PMF Bool,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε
        (quittingStationaryProfile reward root)

/-- A profile has a player who quits surely at the first stage. -/
def QuitsSurelyAtFirstStage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) : Prop :=
  ∃ owner : ι,
    profile owner 0 ((quittingGame reward).emptyHist none) = PMF.pure true

/-- The literature's simple instant branch, kept in the ordinary strategy
model.  No continuous or public-correlation witness satisfies this predicate
merely by being such a witness. -/
def HasOrdinaryInstantApproximateEquilibria
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) ε profile ∧
        QuitsSurelyAtFirstStage reward profile

/-- Stationary ordinary witnesses are ordinary witnesses. -/
theorem hasOrdinaryApproximateEquilibria_of_stationary
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hstationary : HasOrdinaryStationaryApproximateEquilibria reward) :
    HasOrdinaryApproximateEquilibria reward := by
  intro ε hε
  obtain ⟨root, hnash⟩ := hstationary ε hε
  exact ⟨quittingStationaryProfile reward root, hnash⟩

/-- Instant ordinary witnesses are ordinary witnesses after forgetting the
first-stage support condition. -/
theorem hasOrdinaryApproximateEquilibria_of_instant
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hinstant : HasOrdinaryInstantApproximateEquilibria reward) :
    HasOrdinaryApproximateEquilibria reward := by
  intro ε hε
  obtain ⟨profile, hnash, hfirst⟩ := hinstant ε hε
  exact ⟨profile, hnash⟩

/-- The repository's proved Never branch supplies ordinary approximate
witnesses without any borrowed theorem. -/
theorem hasOrdinaryApproximateEquilibria_of_zeroSolo
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hzero : IsQuittingZeroSolo reward) :
    HasOrdinaryApproximateEquilibria reward := by
  intro ε hε
  refine ⟨quittingAlwaysContinueProfile reward, ?_⟩
  intro who deviation
  have hexact :=
    isZeroAsymptoticNash_quittingAlwaysContinue_of_zeroSolo reward hzero
      who deviation
  linarith

/-- **Audited Solan--Solan interface.**

The first two fields are Lemmas 2.6 and 2.10.  The last two fields are the two
parts of Theorem 2.11, whose stated hypotheses are a nonempty recursive normal
core and absence of a nontrivial homogeneous LCP solution.  Part (1) is
ordinary and stationary; part (2) is deliberately typed by the independent
`SunspotApproximateEquilibria` predicate. -/
structure SolanSolanSourceInterface
    (SunspotApproximateEquilibria :
      ({S : Finset ι // S.Nonempty} → Payoff ι) → Prop) where
  allAbnormal_stationary :
    ∀ reward : {S : Finset ι // S.Nonempty} → Payoff ι,
      AllPlayersAbnormal (normalizedSoloMatrix reward) →
        HasOrdinaryStationaryApproximateEquilibria reward
  homogeneous_stationary :
    ∀ reward : {S : Finset ι // S.Nonempty} → Payoff ι,
      HasNormalPlayers (normalizedSoloMatrix reward) →
      HasHomogeneousSimplexSolution
        (normalizedNormalPlayerMatrix reward) →
        HasOrdinaryStationaryApproximateEquilibria reward
  nonQ_stationary :
    ∀ reward : {S : Finset ι // S.Nonempty} → Payoff ι,
      HasNormalPlayers (normalizedSoloMatrix reward) →
      ¬HasHomogeneousSimplexSolution
        (normalizedNormalPlayerMatrix reward) →
      ¬IsStandardQMatrix (normalizedNormalPlayerMatrix reward) →
        HasOrdinaryStationaryApproximateEquilibria reward
  q_sunspot :
    ∀ reward : {S : Finset ι // S.Nonempty} → Payoff ι,
      HasNormalPlayers (normalizedSoloMatrix reward) →
      ¬HasHomogeneousSimplexSolution
        (normalizedNormalPlayerMatrix reward) →
      IsStandardQMatrix (normalizedNormalPlayerMatrix reward) →
        SunspotApproximateEquilibria reward

/-- **Audited transported AGKRS Theorem 5.4 interface.**

`ContinuousEquilibrium` is intentionally abstract because the repository does
not yet identify a continuous absorption path with an ordinary behavior
profile.  The sole hypothesis is projective Q-bar of the fully normalized
singleton matrix.  Instantiating this interface includes the playerwise
translation back from `normalizedQuittingPayoffTable reward`; it does not
include Theorem 4.15 or any terminal-to-uniform compiler. -/
structure AGKRSContinuousSourceInterface
    (ContinuousEquilibrium :
      ({S : Finset ι // S.Nonempty} → Payoff ι) → Prop) where
  continuous_of_projectiveQBar :
    ∀ reward : {S : Finset ι // S.Nonempty} → Payoff ι,
      IsProjectiveQBarMatrix (normalizedSoloMatrix reward) →
        ContinuousEquilibrium reward

end QuittingLCPClassification
end GameTheory
