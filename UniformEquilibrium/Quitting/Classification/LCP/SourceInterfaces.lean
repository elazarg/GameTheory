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

Source conclusions are stated for `normalizedQuittingPayoffTable reward`.
Ordinary terminal-Nash transport back to the repository payoff is proved below
from `StrategicTransport.lean`.  For continuous and sunspot notions not yet
represented by repository strategy types, translation invariance is a separate
explicit hypothesis supplied through
`IsQuittingPayoffTranslationInvariant`; it is not bundled into either source
interface.
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

/-- Ordinary approximate equilibria evaluated with the fully translated
source payoff, including its nonzero nontermination reward. -/
def HasNormalizedOrdinaryApproximateEquilibria
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingGame reward).IsεAsymptoticNash
        (normalizedQuittingTerminalPayoff reward) ε profile

/-- The stronger ordinary conclusion of the stationary source branches. -/
def HasOrdinaryStationaryApproximateEquilibria
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ root : ι → PMF Bool,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε
        (quittingStationaryProfile reward root)

/-- Stationary approximate equilibria in the translated source payoff. -/
def HasNormalizedOrdinaryStationaryApproximateEquilibria
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ root : ι → PMF Bool,
      (quittingGame reward).IsεAsymptoticNash
        (normalizedQuittingTerminalPayoff reward) ε
        (quittingStationaryProfile reward root)

/-- Exact ordinary transport across the playerwise source normalization. -/
theorem hasNormalizedOrdinaryApproximateEquilibria_iff_original
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    HasNormalizedOrdinaryApproximateEquilibria reward ↔
      HasOrdinaryApproximateEquilibria reward := by
  constructor
  · intro hnormalized ε hε
    obtain ⟨profile, hnash⟩ := hnormalized ε hε
    exact ⟨profile,
      (isεAsymptoticNash_normalized_iff reward ε profile).mp hnash⟩
  · intro horiginal ε hε
    obtain ⟨profile, hnash⟩ := horiginal ε hε
    exact ⟨profile,
      (isεAsymptoticNash_normalized_iff reward ε profile).mpr hnash⟩

/-- Exact stationary ordinary transport across the playerwise source
normalization. -/
theorem hasNormalizedOrdinaryStationaryApproximateEquilibria_iff_original
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    HasNormalizedOrdinaryStationaryApproximateEquilibria reward ↔
      HasOrdinaryStationaryApproximateEquilibria reward := by
  constructor
  · intro hnormalized ε hε
    obtain ⟨root, hnash⟩ := hnormalized ε hε
    exact ⟨root,
      (isεAsymptoticNash_normalized_iff reward ε
        (quittingStationaryProfile reward root)).mp hnash⟩
  · intro horiginal ε hε
    obtain ⟨root, hnash⟩ := horiginal ε hε
    exact ⟨root,
      (isεAsymptoticNash_normalized_iff reward ε
        (quittingStationaryProfile reward root)).mpr hnash⟩

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
by the independent normalized-table `SunspotApproximateEquilibria` predicate.

Because the displayed normality recursion is defective, constructing this
interface is an explicit remaining source-repair obligation, not a hidden
axiom asserting the literal printed theorem. -/
structure SolanSolanDistinctWitnessRepairInterface
    (SunspotApproximateEquilibria : QuittingPayoffTable ι → Prop) where
  allAbnormal_stationary :
    ∀ reward : {S : Finset ι // S.Nonempty} → Payoff ι,
      AllPlayersAbnormal (normalizedSoloMatrix reward) →
        HasNormalizedOrdinaryStationaryApproximateEquilibria reward
  homogeneous_stationary :
    ∀ reward : {S : Finset ι // S.Nonempty} → Payoff ι,
      HasNormalPlayers (normalizedSoloMatrix reward) →
      HasHomogeneousSimplexSolution
        (normalizedNormalPlayerMatrix reward) →
        HasNormalizedOrdinaryStationaryApproximateEquilibria reward
  nonQ_stationary :
    ∀ reward : {S : Finset ι // S.Nonempty} → Payoff ι,
      HasNormalPlayers (normalizedSoloMatrix reward) →
      ¬HasHomogeneousSimplexSolution
        (normalizedNormalPlayerMatrix reward) →
      ¬IsStandardQMatrix (normalizedNormalPlayerMatrix reward) →
        HasNormalizedOrdinaryStationaryApproximateEquilibria reward
  q_sunspot :
    ∀ reward : {S : Finset ι // S.Nonempty} → Payoff ι,
      HasNormalPlayers (normalizedSoloMatrix reward) →
      ¬HasHomogeneousSimplexSolution
        (normalizedNormalPlayerMatrix reward) →
      IsStandardQMatrix (normalizedNormalPlayerMatrix reward) →
        SunspotApproximateEquilibria
          (normalizedQuittingPayoffTable reward)

/-- **Audited AGKRS Theorem 5.4 interface on the normalized table.**

`ContinuousEquilibrium` is intentionally abstract because the repository does
not identify a continuous absorption path with an ordinary behavior profile.
The sole matrix hypothesis is projective Q-bar of the fully normalized
singleton matrix.  Translation back to the repository table is not hidden in
this source interface; it requires an explicit
`IsQuittingPayoffTranslationInvariant ContinuousEquilibrium` hypothesis.  The
interface also does not include Theorem 4.15 or a terminal-to-uniform compiler. -/
structure AGKRSContinuousSourceInterface
    (ContinuousEquilibrium : QuittingPayoffTable ι → Prop) where
  continuous_of_projectiveQBar :
    ∀ reward : {S : Finset ι // S.Nonempty} → Payoff ι,
      IsProjectiveQBarMatrix (normalizedSoloMatrix reward) →
        ContinuousEquilibrium (normalizedQuittingPayoffTable reward)

end QuittingLCPClassification
end GameTheory
