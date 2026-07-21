/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Repeated.MonitoringPublicDraw
import GameTheory.Concepts.Repeated.MonitoringRank
import GameTheory.Concepts.Repeated.MonitoringRankInstances
import GameTheory.Concepts.Repeated.MonitoringPureDeviations
import GameTheory.Concepts.Repeated.MonitoringIncentives
import GameTheory.Concepts.Repeated.MonitoringHyperplanes

/-!
# Tests for Repeated Games with Public Monitoring

Small checked examples exercise stochastic signal-history generation,
stationary payoffs, realized-action monitoring, and the general stationary-Nash
uniform-equilibrium theorem.
-/

noncomputable section

namespace GameTheory

namespace RepeatedMonitoringTests

open KernelGame
open KernelGame.PublicMonitoring
open KernelGame.PublicMonitoring.SelfGenerating

/-- A two-player coordination game whose outcome records the pure profile. -/
abbrev coordinationGame : KernelGame Bool :=
  { Strategy := fun _ => Bool
    Outcome := Bool → Bool
    utility := fun σ _ => if σ false = σ true then 1 else 0
    outcomeKernel := PMF.pure }

/-- The coordinated all-`true` action profile. -/
abbrev allTrueProfile : Profile coordinationGame :=
  fun _ => true

theorem allTrueProfile_isNash : coordinationGame.IsNash allTrueProfile := by
  intro who dev
  simp only [KernelGame.eu, Math.Probability.expect_pure]
  cases who <;> cases dev <;>
    norm_num [allTrueProfile, Function.update]

/-- Outcome monitoring of the deterministic coordination game generates the
expected one-period Dirac history. -/
example :
    coordinationGame.outcomeMonitoring.signalHistoryDist
        (coordinationGame.outcomeMonitoring.stationaryMonitoredProfile allTrueProfile) 1 =
      PMF.pure (fun _ : Fin 1 => allTrueProfile) := by
  rw [PublicMonitoring.signalHistoryDist_succ,
    PublicMonitoring.signalHistoryDist_zero]
  simp only [PMF.pure_bind]
  change PMF.map
    (Fin.snoc (α := fun _ => Profile coordinationGame)
      (fun k : Fin 0 => k.elim0))
      (PMF.pure allTrueProfile) = _
  simp only [PMF.map]
  rw [PMF.pure_bind]
  apply congrArg PMF.pure
  funext k
  refine Fin.lastCases ?_ (fun j => Fin.elim0 j) k
  rw [Fin.snoc_last]

/-- Stationary monitored payoff evaluation is independent of the realized
signal history. -/
example (t : ℕ) :
    coordinationGame.outcomeMonitoring.stageEU
        (coordinationGame.outcomeMonitoring.stationaryMonitoredProfile allTrueProfile)
        t false = 1 := by
  rw [PublicMonitoring.stageEU_stationaryMonitoredProfile]
  simp [KernelGame.eu, allTrueProfile]

/-- Stationary monitored play remains stationary after every public history,
including histories that have zero probability. -/
example {t : ℕ}
    (h : coordinationGame.outcomeMonitoring.SignalHistory t) (n : ℕ) :
    coordinationGame.outcomeMonitoring.stageEU
        (coordinationGame.outcomeMonitoring.after
          (coordinationGame.outcomeMonitoring.stationaryMonitoredProfile
            allTrueProfile) h)
        n false = 1 := by
  rw [PublicMonitoring.after_stationaryMonitoredProfile,
    PublicMonitoring.stageEU_stationaryMonitoredProfile]
  simp [KernelGame.eu, allTrueProfile]

/-- One-signal and arbitrary-history continuation compose without dependent
index casts. -/
example (σ : coordinationGame.outcomeMonitoring.MonitoredProfile)
    {t : ℕ} (h : coordinationGame.outcomeMonitoring.SignalHistory t)
    (y : coordinationGame.outcomeMonitoring.Signal) :
    coordinationGame.outcomeMonitoring.afterSignal
        (coordinationGame.outcomeMonitoring.after σ h) y =
      coordinationGame.outcomeMonitoring.after σ (Fin.snoc h y) :=
  coordinationGame.outcomeMonitoring.afterSignal_after σ h y

/-- The checked stage Nash profile gives a monitored uniform equilibrium. -/
example :
    coordinationGame.outcomeMonitoring.IsUniformEquilibrium
      (coordinationGame.outcomeMonitoring.stationaryMonitoredProfile allTrueProfile) :=
  by
    letI : Finite coordinationGame.Outcome := by
      change Finite (Bool → Bool)
      infer_instance
    exact PublicMonitoring.stationaryMonitoredProfile_isUniformEquilibrium_of_isNash
      (M := coordinationGame.outcomeMonitoring) allTrueProfile_isNash

/-- Dirac mixed actions expose the corresponding pure action profile under
realized-action monitoring. -/
example :
    coordinationGame.realizedActionMonitoring.signalKernel
        (fun i => (PMF.pure (allTrueProfile i) : PMF Bool)) =
      PMF.pure allTrueProfile := by
  exact coordinationGame.realizedActionMonitoring_signalKernel_pure allTrueProfile

/-- The general behavioral lift preserves the original signal law on Dirac
mixed actions. -/
example :
    coordinationGame.outcomeMonitoring.mixedExtension.signalKernel
        (coordinationGame.pureMixedProfile allTrueProfile) =
      coordinationGame.outcomeMonitoring.signalKernel allTrueProfile := by
  exact coordinationGame.outcomeMonitoring.mixedExtension_signalKernel_pure
    allTrueProfile

/-- Lifting observable pure profiles agrees with the dedicated
realized-action monitoring instance. -/
example (σ : Profile coordinationGame.mixedExtension) :
    coordinationGame.profileMonitoring.mixedExtension.signalKernel σ =
      coordinationGame.realizedActionMonitoring.signalKernel σ := by
  exact coordinationGame.profileMonitoring_mixedExtension_signalKernel σ

/-- Stationary monitored play has its stage payoff under normalized
discounting. -/
example :
    coordinationGame.outcomeMonitoring.discountedAveragePayoff (1 / 2)
        (coordinationGame.outcomeMonitoring.stationaryMonitoredProfile
          allTrueProfile) false = 1 := by
  rw [coordinationGame.outcomeMonitoring.discountedAveragePayoff_stationaryMonitoredProfile
    (δ := (1 / 2 : ℝ)) (by norm_num) (by norm_num)]
  simp [KernelGame.eu, allTrueProfile]

/-- The coordination equilibrium is sequentially rational after every public
history under discounted outcome monitoring. -/
example :
    coordinationGame.outcomeMonitoring.IsPerfectPublicEquilibrium (1 / 2)
      (coordinationGame.outcomeMonitoring.stationaryMonitoredProfile
        allTrueProfile) := by
  letI : Finite coordinationGame.Outcome := by
    change Finite (Bool → Bool)
    infer_instance
  exact PublicMonitoring.stationaryMonitoredProfile_isPerfectPublicEquilibrium_of_isNash
    coordinationGame.outcomeMonitoring (by norm_num) (by norm_num)
      allTrueProfile_isNash

/-- The one-shot-deviation test is equivalent to PPE in the finite-outcome
coordination example. -/
example :
    coordinationGame.outcomeMonitoring.IsPerfectPublicEquilibrium (1 / 2)
        (coordinationGame.outcomeMonitoring.stationaryMonitoredProfile
          allTrueProfile) ↔
      coordinationGame.outcomeMonitoring.HasNoProfitableOneShotDeviationAfterEveryHistory
        (1 / 2)
        (coordinationGame.outcomeMonitoring.stationaryMonitoredProfile
          allTrueProfile) := by
  letI : Finite coordinationGame.Outcome := by
    change Finite (Bool → Bool)
    infer_instance
  exact PublicMonitoring.isPerfectPublicEquilibrium_iff_noProfitableOneShotDeviation
    coordinationGame.outcomeMonitoring (by norm_num) (by norm_num) _

/-- Finiteness is not essential: the bounded-payoff statement exposes the
actual hypothesis used by the one-shot-deviation principle. -/
example :
    coordinationGame.outcomeMonitoring.IsPerfectPublicEquilibrium (1 / 2)
        (coordinationGame.outcomeMonitoring.stationaryMonitoredProfile
          allTrueProfile) ↔
      coordinationGame.outcomeMonitoring.HasNoProfitableOneShotDeviationAfterEveryHistory
        (1 / 2)
        (coordinationGame.outcomeMonitoring.stationaryMonitoredProfile
          allTrueProfile) := by
  apply PublicMonitoring.isPerfectPublicEquilibrium_iff_noProfitableOneShotDeviation_of_bounded
    coordinationGame.outcomeMonitoring (by norm_num) (by norm_num)
  intro who
  refine ⟨1, ?_⟩
  intro ρ
  simp only [coordinationGame, KernelGame.eu,
    Math.Probability.expect_pure]
  split <;> norm_num

/-- A suitably scaled local one-shot allowance gives the requested global PPE
allowance. -/
example {ε : ℝ} (hε : 0 ≤ ε)
    (h : PublicMonitoring.HasNoProfitableOneShotDeviationWithinAfterEveryHistory
      coordinationGame.outcomeMonitoring (1 / 2) ((1 - 1 / 2) * ε)
      (coordinationGame.outcomeMonitoring.stationaryMonitoredProfile
        allTrueProfile)) :
    coordinationGame.outcomeMonitoring.IsεPerfectPublicEquilibrium
      (1 / 2) ε
      (coordinationGame.outcomeMonitoring.stationaryMonitoredProfile
        allTrueProfile) := by
  letI : Finite coordinationGame.Outcome := by
    change Finite (Bool → Bool)
    infer_instance
  exact h.isεPPE_of_scaled (by norm_num) (by norm_num) hε

/-- Approximate PPE exposes the corresponding approximate one-shot checks. -/
example {ε : ℝ}
    (h : PublicMonitoring.IsεPerfectPublicEquilibrium
      coordinationGame.outcomeMonitoring (1 / 2) ε
      (coordinationGame.outcomeMonitoring.stationaryMonitoredProfile
        allTrueProfile)) :
    PublicMonitoring.HasNoProfitableOneShotDeviationWithinAfterEveryHistory
      coordinationGame.outcomeMonitoring (1 / 2) ε
      (coordinationGame.outcomeMonitoring.stationaryMonitoredProfile
        allTrueProfile) :=
  h.hasNoProfitableOneShotDeviationWithinAfterEveryHistory

/-- Constant continuation promises reduce APS enforceability to stage Nash. -/
example :
    coordinationGame.outcomeMonitoring.IsEnforceable (1 / 2)
      allTrueProfile
      (coordinationGame.outcomeMonitoring.constantContinuation
        (fun who => coordinationGame.eu allTrueProfile who)) := by
  exact (coordinationGame.outcomeMonitoring.isEnforceable_constant_iff_isNash
    (by norm_num) allTrueProfile _).2 allTrueProfile_isNash

/-- A stationary stage-Nash payoff is a self-generating singleton. -/
example :
    coordinationGame.outcomeMonitoring.SelfGenerating (1 / 2)
      ({fun who => coordinationGame.eu allTrueProfile who} :
        Set (Payoff Bool)) :=
  coordinationGame.outcomeMonitoring.selfGenerating_singleton_eu_of_isNash
    (by norm_num) allTrueProfile_isNash

/-- The APS self-generation theorem converts the stationary singleton into a
PPE payoff. -/
example :
    (fun who => coordinationGame.eu allTrueProfile who) ∈
      coordinationGame.outcomeMonitoring.perfectPublicEquilibriumPayoffs
        (1 / 2) := by
  letI : Finite coordinationGame.Outcome := by
    change Finite (Bool → Bool)
    infer_instance
  let W : Set (Payoff Bool) :=
    {fun who => coordinationGame.eu allTrueProfile who}
  have hW : PublicMonitoring.IsBoundedPayoffSet W := by
    intro who
    refine ⟨|coordinationGame.eu allTrueProfile who|, ?_⟩
    intro v hv
    rw [Set.mem_singleton_iff.mp hv]
  have hself : coordinationGame.outcomeMonitoring.SelfGenerating (1 / 2) W :=
    coordinationGame.outcomeMonitoring.selfGenerating_singleton_eu_of_isNash
      (by norm_num) allTrueProfile_isNash
  exact (selfGenerating_subset_perfectPublicEquilibriumPayoffs_of_finite_outcome
      coordinationGame.outcomeMonitoring (by norm_num) (by norm_num)
      hW hself) (Set.mem_singleton _)

/-- Conversely, the complete PPE payoff set decomposes relative to itself. -/
example :
    coordinationGame.outcomeMonitoring.SelfGenerating (1 / 2)
      (coordinationGame.outcomeMonitoring.perfectPublicEquilibriumPayoffs
        (1 / 2)) := by
  letI : Finite coordinationGame.Outcome := by
    change Finite (Bool → Bool)
    infer_instance
  exact PublicMonitoring.perfectPublicEquilibriumPayoffs_selfGenerating
    coordinationGame.outcomeMonitoring (by norm_num) (by norm_num)

/-- A finite public lottery has the expected convex-hull payoff. -/
example :
    (fun who => coordinationGame.eu allTrueProfile who) ∈
      PublicMonitoring.publicRandomizationHull
        ({fun who => coordinationGame.eu allTrueProfile who} :
          Set (Payoff Bool)) := by
  rw [PublicMonitoring.mem_publicRandomizationHull_iff]
  refine ⟨Unit, inferInstance, PMF.pure (),
    fun _ who => coordinationGame.eu allTrueProfile who, ?_, ?_⟩
  · simp
  · intro who
    simp

/-- Ordinary APS self-generation embeds into publicly randomized
self-generation through degenerate lotteries. -/
example :
    coordinationGame.outcomeMonitoring.PublicSelfGenerating (1 / 2)
      ({fun who => coordinationGame.eu allTrueProfile who} :
        Set (Payoff Bool)) := by
  have hself :
      coordinationGame.outcomeMonitoring.SelfGenerating (1 / 2)
        ({fun who => coordinationGame.eu allTrueProfile who} :
          Set (Payoff Bool)) :=
    coordinationGame.outcomeMonitoring.selfGenerating_singleton_eu_of_isNash
      (by norm_num) allTrueProfile_isNash
  exact hself.publicSelfGenerating

/-- Adding an independent public draw preserves the original monitoring
signal marginal. -/
example (a : Profile coordinationGame) :
    ((coordinationGame.outcomeMonitoring.withPublicDraw (PMF.pure true)).signalKernel
      a).map Prod.snd =
        coordinationGame.outcomeMonitoring.signalKernel a := by
  exact withPublicDraw_signalKernel_map_snd
    coordinationGame.outcomeMonitoring (PMF.pure true) a

/-- A stationary stage Nash equilibrium remains a seeded PPE when a public
draw is observed before play. -/
example :
    coordinationGame.outcomeMonitoring.IsSeededPerfectPublicEquilibrium
      (PMF.pure true) (1 / 2)
      (fun _ =>
        (coordinationGame.outcomeMonitoring.withPublicDraw
          (PMF.pure true)).stationaryMonitoredProfile allTrueProfile) := by
  letI : Finite coordinationGame.Outcome := by
    change Finite (Bool → Bool)
    infer_instance
  apply isSeededPerfectPublicEquilibrium_const
    coordinationGame.outcomeMonitoring (PMF.pure true)
  exact stationaryMonitoredProfile_isPerfectPublicEquilibrium_of_isNash
      (coordinationGame.outcomeMonitoring.withPublicDraw (PMF.pure true))
      (by norm_num) (by norm_num) allTrueProfile_isNash

/-- A unilateral deviation only redistributes public signal probability
mass. -/
example (who : Bool) (dev : Bool) :
    ∑ y,
      coordinationGame.profileMonitoring.deviationSignalVector
        allTrueProfile who dev y = 0 := by
  exact coordinationGame.profileMonitoring.sum_deviationSignalVector_eq_zero
    allTrueProfile who dev

/-- The basis-free pairwise-rank API has the standard decomposition into two
individual rank conditions and disjoint deviation spans. -/
example :
    coordinationGame.profileMonitoring.PairwiseFullRank
        allTrueProfile false true ↔
      coordinationGame.profileMonitoring.IndividualFullRank
          allTrueProfile false ∧
        coordinationGame.profileMonitoring.IndividualFullRank
            allTrueProfile true ∧
          coordinationGame.profileMonitoring.PairwiseIdentifiable
            allTrueProfile false true := by
  exact coordinationGame.profileMonitoring.pairwiseFullRank_iff
    allTrueProfile false true

/-- Individual rank is unchanged by a bijective relabeling of public
signals. -/
example :
    (coordinationGame.profileMonitoring.mapSignal
        (Equiv.refl (Profile coordinationGame))).IndividualFullRank
          allTrueProfile false ↔
      coordinationGame.profileMonitoring.IndividualFullRank
        allTrueProfile false := by
  exact individualFullRank_mapSignal_equiv_iff
    coordinationGame.profileMonitoring allTrueProfile false (Equiv.refl _)

/-- On finite monitoring problems, basis-free individual full rank is exactly
full numerical row rank. -/
example :
    coordinationGame.profileMonitoring.IndividualFullRank
        allTrueProfile false ↔
      coordinationGame.profileMonitoring.individualDeviationRank
          allTrueProfile false =
        Fintype.card
          (PublicMonitoring.NontrivialDeviation allTrueProfile false) := by
  exact individualFullRank_iff_individualDeviationRank_eq_card
    coordinationGame.profileMonitoring allTrueProfile false

/-- Probability normalization gives the sharp codimension-one necessary
signal-count bound for pairwise full rank. -/
example
    (h : coordinationGame.profileMonitoring.PairwiseFullRank
      allTrueProfile false true) :
    Fintype.card
          (PublicMonitoring.NontrivialDeviation allTrueProfile false) +
        Fintype.card
          (PublicMonitoring.NontrivialDeviation allTrueProfile true) ≤
      Fintype.card (Profile coordinationGame) - 1 := by
  exact h.card_deviations_le_card_signal_sub_one

/-- Perfect profile monitoring satisfies individual full rank. -/
example :
    coordinationGame.profileMonitoring.IndividualFullRank
      allTrueProfile false :=
  individualFullRank_profileMonitoring coordinationGame allTrueProfile false

/-- Perfect profile monitoring separates the deviations of distinct
players, hence satisfies pairwise full rank. -/
example :
    coordinationGame.profileMonitoring.PairwiseFullRank
      allTrueProfile false true :=
  pairwiseFullRank_profileMonitoring coordinationGame allTrueProfile
    Bool.false_ne_true

/-- A stochastic coarsening cannot manufacture pairwise full rank. -/
example {S : Type}
    (K : Math.Probability.Kernel (Profile coordinationGame) S)
    (h : (coordinationGame.profileMonitoring.garble K).PairwiseFullRank
      allTrueProfile false true) :
    coordinationGame.profileMonitoring.PairwiseFullRank
      allTrueProfile false true :=
  h.of_garble

/-- The numerical pairwise deviation rank is nonincreasing under finite
stochastic garbling. -/
example :
    (coordinationGame.profileMonitoring.garble PMF.pure).pairwiseDeviationRank
        allTrueProfile false true ≤
      coordinationGame.profileMonitoring.pairwiseDeviationRank
        allTrueProfile false true :=
  pairwiseDeviationRank_garble_le coordinationGame.profileMonitoring
    PMF.pure allTrueProfile false true

/-- Realized-action monitoring satisfies the correct pure-deviation
individual rank condition for the behavioral mixed extension. -/
example :
    coordinationGame.realizedActionMonitoring.PureIndividualFullRank
      allTrueProfile false :=
  pureIndividualFullRank_realizedActionMonitoring coordinationGame
    allTrueProfile false

/-- Distinct players' pure deviations also satisfy pairwise full rank under
realized-action monitoring. -/
example :
    coordinationGame.realizedActionMonitoring.PurePairwiseFullRank
      allTrueProfile false true :=
  purePairwiseFullRank_realizedActionMonitoring coordinationGame
    allTrueProfile Bool.false_ne_true

/-- Pure pairwise full rank has the same individual-rank plus identifiability
decomposition as the unrestricted basis-free rank condition. -/
example :
    coordinationGame.realizedActionMonitoring.PurePairwiseFullRank
        allTrueProfile false true ↔
      coordinationGame.realizedActionMonitoring.PureIndividualFullRank
          allTrueProfile false ∧
        coordinationGame.realizedActionMonitoring.PureIndividualFullRank
            allTrueProfile true ∧
          coordinationGame.realizedActionMonitoring.PurePairwiseIdentifiable
            allTrueProfile false true := by
  exact purePairwiseFullRank_iff coordinationGame.realizedActionMonitoring
    allTrueProfile false true

/-- Pure individual full rank is equivalent to full numerical row rank while
requiring only finiteness, not a chosen enumeration, of signals and rows. -/
example :
    coordinationGame.realizedActionMonitoring.PureIndividualFullRank
        allTrueProfile false ↔
      coordinationGame.realizedActionMonitoring.pureIndividualDeviationRank
          allTrueProfile false =
        Nat.card
          (PublicMonitoring.NontrivialDeviation allTrueProfile false) := by
  exact pureIndividualFullRank_iff_pureIndividualDeviationRank_eq_card
    coordinationGame.realizedActionMonitoring allTrueProfile false

/-- Pure pairwise full rank obeys the sharp codimension-one signal bound. -/
example
    (h : coordinationGame.realizedActionMonitoring.PurePairwiseFullRank
      allTrueProfile false true) :
    Nat.card
          (PublicMonitoring.NontrivialDeviation allTrueProfile false) +
        Nat.card
          (PublicMonitoring.NontrivialDeviation allTrueProfile true) ≤
      Nat.card (Profile coordinationGame) - 1 := by
  exact h.card_deviations_le_card_signal_sub_one

/-- Pure individual rank is invariant under a bijective relabeling of public
signals. -/
example :
    (coordinationGame.realizedActionMonitoring.mapSignal
        (Equiv.refl (Profile coordinationGame))).PureIndividualFullRank
          allTrueProfile false ↔
      coordinationGame.realizedActionMonitoring.PureIndividualFullRank
        allTrueProfile false := by
  exact pureIndividualFullRank_mapSignal_equiv_iff
    coordinationGame.realizedActionMonitoring allTrueProfile false
      (Equiv.refl _)

/-- Numerical pure pairwise rank is also unchanged by signal relabeling. -/
example :
    (coordinationGame.realizedActionMonitoring.mapSignal
        (Equiv.refl (Profile coordinationGame))).purePairwiseDeviationRank
          allTrueProfile false true =
      coordinationGame.realizedActionMonitoring.purePairwiseDeviationRank
        allTrueProfile false true := by
  exact purePairwiseDeviationRank_mapSignal_equiv
    coordinationGame.realizedActionMonitoring allTrueProfile false true
      (Equiv.refl _)

/-- Stochastic coarsening cannot increase numerical pure pairwise deviation
rank. -/
example :
    (coordinationGame.realizedActionMonitoring.garble PMF.pure).purePairwiseDeviationRank
        allTrueProfile false true ≤
      coordinationGame.realizedActionMonitoring.purePairwiseDeviationRank
        allTrueProfile false true := by
  exact purePairwiseDeviationRank_garble_le
    coordinationGame.realizedActionMonitoring PMF.pure
      allTrueProfile false true

/-- Pure individual full rank is exactly surjectivity of the continuation-to-
incentive-effect map. -/
example :
    Function.Surjective
      (coordinationGame.realizedActionMonitoring.pureIndividualIncentiveEffectMap
        allTrueProfile false) := by
  rw [pureIndividualIncentiveEffectMap_surjective_iff]
  exact pureIndividualFullRank_realizedActionMonitoring coordinationGame
    allTrueProfile false

/-- At the realized-action benchmark, the continuation transfer solving any
individual incentive target can be chosen with a uniform linear norm bound. -/
example :
    ∃ (R :
          (PublicMonitoring.NontrivialDeviation allTrueProfile false → ℝ) →ₗ[ℝ]
            (Profile coordinationGame → ℝ))
        (C : ℝ),
      0 ≤ C ∧
        (coordinationGame.realizedActionMonitoring.pureIndividualIncentiveEffectMap
          allTrueProfile false).comp R = LinearMap.id ∧
        ∀ b, ‖R b‖ ≤ C * ‖b‖ := by
  exact
    (pureIndividualFullRank_realizedActionMonitoring coordinationGame
      allTrueProfile false).exists_bounded_incentiveEffect_rightInverse

/-- One continuation-solver bound can cover a finite family of relevant
profile-player constraints without assuming that every profile is finite. -/
example :
    ∃ (R : ∀ who : Bool,
          (PublicMonitoring.NontrivialDeviation allTrueProfile who → ℝ) →ₗ[ℝ]
            (Profile coordinationGame → ℝ))
        (C : ℝ),
      0 ≤ C ∧
        ∀ who,
          (coordinationGame.realizedActionMonitoring.pureIndividualIncentiveEffectMap
            allTrueProfile who).comp (R who) = LinearMap.id ∧
          ∀ b, ‖R who b‖ ≤ C * ‖b‖ := by
  exact exists_uniform_bounded_individualIncentiveEffect_rightInverses
    coordinationGame.realizedActionMonitoring (fun _ => allTrueProfile) id
      (fun who => pureIndividualFullRank_realizedActionMonitoring
        coordinationGame allTrueProfile who)

/-- Every nonzero payoff normal is either coordinate or has two distinct
nonzero coordinates; the classification itself is not finiteness-dependent. -/
example (normal : Bool → ℝ) (hnormal : normal ≠ 0) :
    Math.LinearAlgebra.IsCoordinateDirection normal ∨
      Math.LinearAlgebra.HasTwoNonzeroCoordinates normal :=
  Math.LinearAlgebra.isCoordinateDirection_or_hasTwoNonzeroCoordinates hnormal

/-- Pairwise rank can meet arbitrary incentive targets while keeping every
signal-contingent transfer tangent to a non-coordinate payoff normal. -/
example
    (targetFalse :
      PublicMonitoring.NontrivialDeviation allTrueProfile false → ℝ)
    (targetTrue :
      PublicMonitoring.NontrivialDeviation allTrueProfile true → ℝ) :
    ∃ w : Profile coordinationGame → Payoff Bool,
      (∀ y, w y ∈ Math.LinearAlgebra.normalHyperplane
        (fun _ : Bool => (1 : ℝ))) ∧
      coordinationGame.realizedActionMonitoring.pureIndividualIncentiveEffectMap
          allTrueProfile false (fun y => w y false) = targetFalse ∧
      coordinationGame.realizedActionMonitoring.pureIndividualIncentiveEffectMap
          allTrueProfile true (fun y => w y true) = targetTrue := by
  exact
    (purePairwiseFullRank_realizedActionMonitoring coordinationGame
      allTrueProfile Bool.false_ne_true).exists_pairwiseTangentIncentiveTransfer
        Bool.false_ne_true (fun _ => (1 : ℝ)) (by norm_num) (by norm_num)
          targetFalse targetTrue

/-- Perfect public profile monitoring enforces every pure profile on each
non-coordinate normal hyperplane at every positive discount factor. -/
example :
    coordinationGame.profileMonitoring.IsEnforceableOnNormalHyperplane
      (1 / 2) allTrueProfile (fun _ : Bool => (1 : ℝ)) := by
  exact
    (purePairwiseFullRankAtProfile_profileMonitoring_mixedExtension
      coordinationGame allTrueProfile).isEnforceableOnNormalHyperplane
        coordinationGame.profileMonitoring (by norm_num) allTrueProfile
          (fun _ => (1 : ℝ))
          ⟨false, true, Bool.false_ne_true, by norm_num, by norm_num⟩

/-- Constant public continuation transfers do not change deviation
incentives. -/
example (c : ℝ) :
    coordinationGame.realizedActionMonitoring.purePairwiseIncentiveEffectMap
        allTrueProfile false true (fun _ => c) = 0 := by
  exact purePairwiseIncentiveEffectMap_const
    coordinationGame.realizedActionMonitoring allTrueProfile false true c

/-- An arbitrary behavioral deviation induces the probability-weighted sum
of the pure-deviation signal vectors. -/
example (τ : PMF Bool) :
    coordinationGame.profileMonitoring.mixedExtension.deviationSignalVector
        (coordinationGame.pureMixedProfile allTrueProfile) false τ =
      ∑ dev, (τ dev).toReal •
        coordinationGame.profileMonitoring.deviationSignalVector
          allTrueProfile false dev := by
  exact deviationSignalVector_mixedExtension_eq_sum_pure
    coordinationGame.profileMonitoring allTrueProfile false τ

/-- Mixed deviations add no signal direction beyond the span generated by
pure deviations. -/
example (τ : PMF Bool) :
    coordinationGame.profileMonitoring.mixedExtension.deviationSignalVector
        (coordinationGame.pureMixedProfile allTrueProfile) false τ ∈
      Submodule.span ℝ
        (Set.range
          (coordinationGame.profileMonitoring.deviationSignalMatrix
            allTrueProfile false)) := by
  exact deviationSignalVector_mixedExtension_mem_span_pure
    coordinationGame.profileMonitoring allTrueProfile false τ

/-- At an embedded pure profile, APS enforceability against all behavioral
mixed deviations is equivalent to enforceability against pure deviations. -/
example :
    coordinationGame.outcomeMonitoring.mixedExtension.IsEnforceable
        (1 / 2) (coordinationGame.pureMixedProfile allTrueProfile)
        (coordinationGame.outcomeMonitoring.constantContinuation
          (fun who => coordinationGame.eu allTrueProfile who)) ↔
      coordinationGame.outcomeMonitoring.IsEnforceable
        (1 / 2) allTrueProfile
        (coordinationGame.outcomeMonitoring.constantContinuation
          (fun who => coordinationGame.eu allTrueProfile who)) := by
  exact isEnforceable_mixedExtension_pureMixedProfile_iff
    coordinationGame.outcomeMonitoring (1 / 2) allTrueProfile _

end RepeatedMonitoringTests

end GameTheory
