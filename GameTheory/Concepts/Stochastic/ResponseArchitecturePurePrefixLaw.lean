/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.ResponseArchitectureConfigKernelLaw

/-!
# Pure-prefix response-architecture law

To extract Q96's unilateral target inequality from a history-level uniform
cap, deviate with one pure action at the restarted entry and obey the supplied
architecture thereafter.  This module identifies that experiment exactly:
its first stage uses the selected unilateral row and its tail is the iterated
prescribed configuration kernel from the random successor configuration.

The resulting finite-average identity upgrades ordinary shifted unilateral
caps to owner-arena target superharmonicity (A3/Ti).
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

open Filter Math.Probability
open Math.ProbabilityMassFunction
open scoped Topology

variable {ι : Type} {G : StochasticGame ι}

attribute [local instance] Fintype.ofFinite

namespace FiniteResponseArchitecture

variable {initial : G.State} (A : G.FiniteResponseArchitecture initial)

section PurePrefixProfile

variable [Fintype ι] [DecidableEq ι]

/-- Deviate with `act` at calendar zero and use the architecture's prescribed
row at every positive calendar time. -/
noncomputable def purePrefixDeviation (who : ι) (act : G.Act who) :
    G.BehaviorStrategy who :=
  fun t h => if t = 0 then PMF.pure act else A.play (A.configAt t h) who

/-- The full profile in which only `who` uses `purePrefixDeviation`. -/
noncomputable def purePrefixProfile (who : ι) (act : G.Act who) :
    G.BehaviorProfile :=
  Function.update A.phaseProfile.behaviorProfile who
    (A.purePrefixDeviation who act)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem purePrefixDeviation_zero (who : ι) (act : G.Act who)
    (h : G.Hist 0) :
    A.purePrefixDeviation who act 0 h = PMF.pure act := by
  simp [purePrefixDeviation]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem purePrefixDeviation_succ (who : ι) (act : G.Act who)
    (t : ℕ) (h : G.Hist (t + 1)) :
    A.purePrefixDeviation who act (t + 1) h =
      A.play (A.configAt (t + 1) h) who := by
  simp [purePrefixDeviation]

/-- The initial joint-action law of the pure-prefix profile is the selected
pure unilateral row. -/
theorem stageActionDist_purePrefix_zero (who : ι) (act : G.Act who) :
    G.stageActionDist (A.purePrefixProfile who act)
        (G.emptyHist initial) =
      A.actionDist who A.start (PMF.pure act) := by
  rw [purePrefixProfile, A.stageActionDist_update]
  simp

/-- At every positive calendar time the pure-prefix profile has returned to
the prescribed joint-action row. -/
theorem stageActionDist_purePrefix_succ (who : ι) (act : G.Act who)
    (t : ℕ) (h : G.Hist (t + 1)) :
    G.stageActionDist (A.purePrefixProfile who act) h =
      A.prescribedActionDist (A.configAt (t + 1) h) := by
  rw [purePrefixProfile, A.stageActionDist_update]
  simp only [purePrefixDeviation_succ]
  exact (A.prescribedActionDist_eq who (A.configAt (t + 1) h)).symm

end PurePrefixProfile

section ConfigurationMarginalRecursion

variable [Fintype ι]

/-- Conditional law of the next controller configuration after a supported
history, written before using any Markov property of the behavior profile. -/
noncomputable def historyConfigStepDist (σ : G.BehaviorProfile)
    {t : ℕ} (h : G.Hist t) : PMF A.Config :=
  (G.stageActionDist σ h).bind fun act =>
    (G.transition h.2 act).bind fun s' =>
      PMF.pure (A.step (A.configAt t h) act s')

/-- Projecting the successor history law to configurations binds the current
history law with `historyConfigStepDist`. -/
theorem map_configAt_histDist_succ (σ : G.BehaviorProfile) (t : ℕ) :
    (G.histDist σ initial (t + 1)).map (A.configAt (t + 1)) =
      (G.histDist σ initial t).bind (A.historyConfigStepDist σ) := by
  rw [G.histDist_succ, PMF.map_bind]
  congr 1
  funext h
  rw [PMF.map_bind]
  unfold historyConfigStepDist
  congr 1
  funext act
  rw [PMF.map_bind]
  congr 1
  funext s'
  rw [PMF.pure_map]
  simpa using congrArg PMF.pure (A.configAt_snoc h act s')

/-- If the joint-action row is prescribed on all supported time-`t`
histories, the configuration marginal advances by the prescribed kernel. -/
theorem map_configAt_histDist_succ_eq_bind_prescribed
    (σ : G.BehaviorProfile) (t : ℕ)
    (haction : ∀ h : G.Hist t,
      h ∈ (G.histDist σ initial t).support →
        G.stageActionDist σ h =
          A.prescribedActionDist (A.configAt t h)) :
    (G.histDist σ initial (t + 1)).map (A.configAt (t + 1)) =
      ((G.histDist σ initial t).map (A.configAt t)).bind
        A.prescribedConfigDist := by
  rw [A.map_configAt_histDist_succ σ t]
  rw [bind_congr_on_support (G.histDist σ initial t)
    (A.historyConfigStepDist σ)
    (A.prescribedConfigDist ∘ A.configAt t) (by
      intro h hh
      unfold historyConfigStepDist prescribedConfigDist
      simp only [Function.comp_apply]
      rw [haction h hh,
        A.publicState_configAt_of_mem_support σ h hh])]
  rw [PMF.bind_map]

end ConfigurationMarginalRecursion

section PurePrefixConfigurationLaw

variable [Fintype ι] [DecidableEq ι]

/-- After the pure first row, the configuration law is that row's successor
law followed by `T` prescribed-kernel steps. -/
theorem map_configAt_histDist_purePrefix (who : ι) (act : G.Act who) :
    ∀ T : ℕ,
      (G.histDist (A.purePrefixProfile who act) initial (T + 1)).map
          (A.configAt (T + 1)) =
        (A.nextConfigDist who A.start (PMF.pure act)).bind
          (Math.PMFIter.iter A.prescribedConfigDist T) := by
  intro T
  induction T with
  | zero =>
      rw [A.map_configAt_histDist_succ, G.histDist_zero, PMF.pure_bind]
      change A.historyConfigStepDist (A.purePrefixProfile who act)
          (G.emptyHist initial) =
        (A.nextConfigDist who A.start (PMF.pure act)).bind PMF.pure
      rw [PMF.bind_pure]
      unfold historyConfigStepDist nextConfigDist
      rw [A.stageActionDist_purePrefix_zero who act, A.start_publicState]
      rfl
  | succ T ih =>
      rw [A.map_configAt_histDist_succ_eq_bind_prescribed]
      · rw [ih, PMF.bind_bind]
        congr 1
        funext y
        exact (Math.PMFIter.iter_succ' A.prescribedConfigDist y T).symm
      · intro h _
        exact A.stageActionDist_purePrefix_succ who act T h

/-- The initial expected payoff of the pure-prefix profile is the payoff of
the selected unilateral row. -/
theorem expectedStagePayoff_purePrefix_zero (who : ι) (act : G.Act who) :
    G.expectedStagePayoff (A.purePrefixProfile who act) initial 0 who =
      A.stagePayoffAt who A.start (PMF.pure act) := by
  rw [G.expectedStagePayoff_zero]
  unfold StochasticGame.stageEUAt stagePayoffAt
  rw [A.stageActionDist_purePrefix_zero who act, A.start_publicState]
  rfl

/-- At tail calendar `t + 1`, the expected payoff is the prescribed reward
after the deviating row and `t` prescribed configuration transitions. -/
theorem expectedStagePayoff_purePrefix_succ
    (who : ι) (act : G.Act who) (t : ℕ) :
    G.expectedStagePayoff (A.purePrefixProfile who act) initial (t + 1) who =
      expect (A.nextConfigDist who A.start (PMF.pure act)) fun y =>
        expect (Math.PMFIter.iter A.prescribedConfigDist t y)
          (fun w => A.prescribedStagePayoff w who) := by
  unfold StochasticGame.expectedStagePayoff
  calc
    expect (G.histDist (A.purePrefixProfile who act) initial (t + 1))
        (fun h => G.stageEUAt (A.purePrefixProfile who act) h who) =
        expect (G.histDist (A.purePrefixProfile who act) initial (t + 1))
          (fun h => A.prescribedStagePayoff
            (A.configAt (t + 1) h) who) :=
      expect_congr_on_support _ _ _ fun h hh => by
        unfold StochasticGame.stageEUAt prescribedStagePayoff
        rw [A.stageActionDist_purePrefix_succ who act t h,
          A.publicState_configAt_of_mem_support
            (A.purePrefixProfile who act) h hh]
    _ = expect
          ((G.histDist (A.purePrefixProfile who act) initial (t + 1)).map
            (A.configAt (t + 1)))
          (fun w => A.prescribedStagePayoff w who) := by
      rw [expect_map]
    _ = expect
          ((A.nextConfigDist who A.start (PMF.pure act)).bind
            (Math.PMFIter.iter A.prescribedConfigDist t))
          (fun w => A.prescribedStagePayoff w who) := by
      rw [A.map_configAt_histDist_purePrefix who act t]
    _ = expect (A.nextConfigDist who A.start (PMF.pure act)) (fun y =>
          expect (Math.PMFIter.iter A.prescribedConfigDist t y)
            (fun w => A.prescribedStagePayoff w who)) := by
      rw [expect_bind]

end PurePrefixConfigurationLaw

section PurePrefixFiniteAverageLaw

variable [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ i, Finite (G.Act i)]

/-- Exact finite-average identity for one pure first-stage deviation followed
by prescribed play. -/
theorem finiteAveragePayoff_purePrefix_eq_configCesaro
    (who : ι) (act : G.Act who) (T : ℕ) :
    G.finiteAveragePayoff initial (T + 1)
        (A.purePrefixProfile who act) who =
      A.purePrefixConfigCesaroPayoff who A.start act T := by
  rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff,
    Finset.sum_range_succ']
  rw [A.expectedStagePayoff_purePrefix_zero who act]
  simp_rw [A.expectedStagePayoff_purePrefix_succ who act]
  have hcomm :
      (∑ t ∈ Finset.range T,
        expect (A.nextConfigDist who A.start (PMF.pure act)) (fun y =>
          expect (Math.PMFIter.iter A.prescribedConfigDist t y)
            (fun w => A.prescribedStagePayoff w who))) =
      expect (A.nextConfigDist who A.start (PMF.pure act)) (fun y =>
        ∑ t ∈ Finset.range T,
          expect (Math.PMFIter.iter A.prescribedConfigDist t y)
            (fun w => A.prescribedStagePayoff w who)) := by
    letI : Fintype A.Config := A.configFintype
    simp only [expect_eq_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hcomm]
  have htail :
      expect (A.nextConfigDist who A.start (PMF.pure act)) (fun y =>
        ∑ t ∈ Finset.range T,
          expect (Math.PMFIter.iter A.prescribedConfigDist t y)
            (fun w => A.prescribedStagePayoff w who)) =
      (T : ℝ) * expect (A.nextConfigDist who A.start (PMF.pure act))
        (fun y => A.prescribedConfigCesaroPayoff who y T) := by
    rw [← expect_const_mul]
    apply expect_congr_on_support
    intro y _
    unfold prescribedConfigCesaroPayoff
    rcases Nat.eq_zero_or_pos T with hT | hT
    · subst T
      simp
    · have hTne : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
      field_simp
  rw [htail]
  simp only [purePrefixConfigCesaroPayoff, Nat.cast_add, Nat.cast_one]
  rw [div_eq_mul_inv]
  ring

/-- Rebased form of the exact pure-prefix finite-average identity. -/
theorem finiteAveragePayoff_purePrefix_rebase_eq_configCesaro
    (z : A.Config) (who : ι) (act : G.Act who) (T : ℕ) :
    G.finiteAveragePayoff (A.publicState z) (T + 1)
        ((A.rebase z).purePrefixProfile who act) who =
      A.purePrefixConfigCesaroPayoff who z act T := by
  have hp : (A.rebase z).purePrefixConfigCesaroPayoff who z act T =
      A.purePrefixConfigCesaroPayoff who z act T := by rfl
  rw [← hp]
  exact (A.rebase z).finiteAveragePayoff_purePrefix_eq_configCesaro who act T

end PurePrefixFiniteAverageLaw

section HistorySemanticTargetConverse

variable [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ i, Finite (G.Act i)]

namespace SplitResponseDomain

variable {A : G.FiniteResponseArchitecture initial}

/-- History-level shifted delivery and unilateral caps imply Q96's two target
conditions on their exact split domains.  For the unilateral step it is enough
to instantiate the cap with `purePrefixDeviation`. -/
theorem targetConditions_of_tendsto_finiteAverage_and_unilateralCap
    (D : A.SplitResponseDomain) {u : A.Config → Payoff ι}
    (hdelivery : ∀ (who : ι) (z : A.Config), D.delivery z →
      Tendsto (fun T : ℕ =>
        G.finiteAveragePayoff (A.publicState z) T
          (A.rebase z).phaseProfile.behaviorProfile who)
        atTop (nhds (u z who)))
    (error : ℕ → ℝ) (herror : Tendsto error atTop (nhds 0))
    (hcap : ∀ (who : ι) (z : A.Config), D.unilateral who z →
      ∀ dev : G.BehaviorStrategy who, ∀ᶠ T : ℕ in atTop,
        G.finiteAveragePayoff (A.publicState z) T
          (Function.update (A.rebase z).phaseProfile.behaviorProfile who dev)
          who ≤ u z who + error T) :
    (∀ (who : ι) (z : A.Config), D.delivery z →
      expect (A.prescribedConfigDist z) (fun y => u y who) = u z who) ∧
    (∀ (who : ι) (z : A.Config), D.unilateral who z →
      ∀ act : G.Act who,
        expect (A.nextConfigDist who z (PMF.pure act))
          (fun y => u y who) ≤ u z who) := by
  refine ⟨D.prescribedTargetHarmonic_of_tendsto_finiteAverage hdelivery, ?_⟩
  have hconfig : ∀ (who : ι) (z : A.Config), D.delivery z →
      Tendsto (fun T : ℕ => A.prescribedConfigCesaroPayoff who z T)
        atTop (nhds (u z who)) := by
    intro who z hz
    exact A.tendsto_prescribedConfigCesaroPayoff_of_finiteAverage z who
      (u z who) (hdelivery who z hz)
  intro who z hz act
  have hleft : Tendsto (fun T : ℕ =>
      G.finiteAveragePayoff (A.publicState z) (T + 1)
        ((A.rebase z).purePrefixProfile who act) who) atTop
      (nhds (expect (A.nextConfigDist who z (PMF.pure act))
        (fun y => u y who))) := by
    simpa only [A.finiteAveragePayoff_purePrefix_rebase_eq_configCesaro]
      using D.tendsto_purePrefixConfigCesaroPayoff hconfig who z hz act
  have herrorShift : Tendsto (fun T : ℕ => error (T + 1)) atTop
      (nhds 0) := (tendsto_add_atTop_iff_nat 1).2 herror
  have hright : Tendsto (fun T : ℕ => u z who + error (T + 1)) atTop
      (nhds (u z who + 0)) := tendsto_const_nhds.add herrorShift
  have hcapShift : ∀ᶠ T : ℕ in atTop,
      G.finiteAveragePayoff (A.publicState z) (T + 1)
          ((A.rebase z).purePrefixProfile who act) who ≤
        u z who + error (T + 1) := by
    have h := (tendsto_add_atTop_nat 1).eventually
      (hcap who z hz ((A.rebase z).purePrefixDeviation who act))
    simpa only [purePrefixProfile] using h
  have hle := le_of_tendsto_of_tendsto hleft hright hcapShift
  simpa using hle

end SplitResponseDomain
end HistorySemanticTargetConverse

end FiniteResponseArchitecture
end StochasticGame
end GameTheory
