/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.NormalCore
import UniformEquilibrium.Quitting.Classification.LCP.StrategicTransport
import UniformEquilibrium.Quitting.Stationary.LiveMass
import UniformEquilibrium.Quitting.Punishment.ZeroSoloDisjunct

/-!
# Audited source interfaces for the quitting-game LCP gate

This file does not hide literature results in a broad existence axiom.  It
states narrow interfaces with separately typed strategic conclusions.

* Solan--Solan's ordinary branches conclude **stationary undiscounted**
  approximate equilibria.  Their Q side concludes a separate
  sunspot/public-correlation predicate.
* AGKRS Theorem 5.4 concludes a caller-supplied **continuous absorption-path
  equilibrium** predicate.  It is not identified here with an ordinary
  behavior profile, an approximate Nash equilibrium, or a uniform payoff.

There is one source defect that must remain visible.  Solan--Solan's displayed
recursive normality formula omits `j ≠ i`; after their zero-diagonal
normalization its literal reading never deletes a player.  `NormalCore.lean`
formalizes that printed recursion and proves its collapse.  The interface below
therefore bears the name `DistinctWitnessRepair`: it states the theorem under
the corrected recursion demanded by the adjacent prose and later proof, rather
than silently presenting the printed statement as sound.

Playerwise payoff translation is proved in `StrategicTransport.lean`.  The
source's projective Q convention and the standard Q convention used in the
ordinary split are related by the exact homogeneous-branch theorem in
`MatrixClasses.lean`.
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

/-- The stronger ordinary conclusion of the stationary source branches. -/
def HasOrdinaryStationaryApproximateEquilibria
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ root : ι → PMF Bool,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε
        (quittingStationaryProfile reward root)

/-- The product mixed action played by a behavior profile at the first stage. -/
def quittingFirstStageRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) : ι → PMF Bool :=
  fun who => profile who 0 ((quittingGame reward).emptyHist none)

/-- The source's exact instant condition: the probability of the all-Continue
joint action at the first stage is zero, hence the game terminates there with
probability one. -/
def TerminatesAlmostSurelyAtFirstStage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) : Prop :=
  quittingStationaryContinueMass
      (quittingFirstStageRoot reward profile) = 0

/-- Ordinary approximate equilibria under which the game terminates almost
surely in the first stage.  This is the simple branch excluded in AGKRS
Theorem 4.15; no continuous or public-correlation witness satisfies it merely
by being such a witness. -/
def HasOrdinaryInstantApproximateEquilibria
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) ε profile ∧
        TerminatesAlmostSurelyAtFirstStage reward profile

/-- Stationary ordinary witnesses are ordinary witnesses. -/
theorem hasOrdinaryApproximateEquilibria_of_stationary
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hstationary : HasOrdinaryStationaryApproximateEquilibria reward) :
    HasOrdinaryApproximateEquilibria reward := by
  intro ε hε
  obtain ⟨root, hnash⟩ := hstationary ε hε
  exact ⟨quittingStationaryProfile reward root, hnash⟩

/-- Instant ordinary witnesses are ordinary witnesses after forgetting their
first-stage absorption condition. -/
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

/-- **Solan--Solan distinct-witness repair interface.**

The first two fields correspond to Lemmas 2.6 and 2.10.  The last two fields
correspond to the two parts of Theorem 2.11, under the corrected recursive
normal core and absence of the nontrivial zero-right-hand-side projective LCP
branch.  Part (1) is ordinary and stationary; part (2) is deliberately typed
by the independent `SunspotApproximateEquilibria` predicate.

Because the displayed normality recursion is defective, constructing this
interface is an explicit remaining source-repair obligation, not a hidden
axiom asserting the literal printed theorem. -/
structure SolanSolanDistinctWitnessRepairInterface
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
not identify a continuous absorption path with an ordinary behavior profile.
The sole matrix hypothesis is projective Q-bar of the fully normalized
singleton matrix.  Instantiating this interface includes transport back across
`normalizedQuittingPayoffTable`; it does not include Theorem 4.15 or any
terminal-to-uniform compiler. -/
structure AGKRSContinuousSourceInterface
    (ContinuousEquilibrium :
      ({S : Finset ι // S.Nonempty} → Payoff ι) → Prop) where
  continuous_of_projectiveQBar :
    ∀ reward : {S : Finset ι // S.Nonempty} → Payoff ι,
      IsProjectiveQBarMatrix (normalizedSoloMatrix reward) →
        ContinuousEquilibrium reward

end QuittingLCPClassification
end GameTheory
