/-
# EXP-113: a nonconstant stochastic game-path payoff consumer

The game starts with a fair public bit and then remains at that bit forever.
The path payoff is therefore genuinely nonconstant, while the path itself is
still generated solely by the canonical stochastic Protocol runner.
-/

import GameTheory.Experimental.PostArchitecture.ProtocolHistoryCountable
import GameTheory.Experimental.PostArchitecture.StochasticInfinitePlayPayoffConsistency
import Mathlib.Tactic.NormNum

noncomputable section

open scoped BigOperators
open scoped Topology

namespace GameTheory.Experimental.PostArchitecture.StochasticGamePathPayoff

open Filter MeasureTheory ProbabilityTheory
open GameTheory.Math.Probability
open GameTheory.Stochastic
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Experimental.PostArchitecture.StochasticInfinitePlayMeasure
open GameTheory.Experimental.PostArchitecture.StochasticInfinitePlayMeasure.Game
open GameTheory.Experimental.PostArchitecture.StochasticInfinitePlayPayoffBridge
open GameTheory.Experimental.PostArchitecture.StochasticInfinitePlayPayoffBridge.Game
open GameTheory.Experimental.PostArchitecture.StochasticInfinitePlayPayoffConsistency
open GameTheory.Experimental.PostArchitecture.StochasticInfinitePlayPayoffConsistency.Game

def fairBit : FinDist (Option Bool) :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure (some false)) (FinDist.pure (some true))

@[reducible]
def pathGame : Stochastic.Game Unit where
  State := Option Bool
  Action := fun _ => Unit
  transition state _ :=
    match state with
    | none => fairBit
    | some bit => FinDist.pure (some bit)
  stageUtility state _ _ :=
    match state with
    | none => 0
    | some false => 0
    | some true => 1

local instance pathGameActionNonempty :
    ∀ i, Nonempty (pathGame.Action i) :=
  fun _ => ⟨()⟩

local instance pathGameStateCountable : Countable pathGame.State := by
  dsimp [pathGame]
  infer_instance

local instance pathGameActionCountable :
    ∀ i, Countable (pathGame.Action i) := by
  intro i
  dsimp [pathGame]
  infer_instance

local instance pathGameStageRecordCountable : Countable pathGame.StageRecord := by
  apply Function.Injective.countable
    (f := fun record => (record.source, record.joint (), record.target))
  intro first second h
  rcases first with ⟨firstSource, firstJoint, firstTarget⟩
  rcases second with ⟨secondSource, secondJoint, secondTarget⟩
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨hsource, hjoint, htarget⟩
  cases hsource
  cases htarget
  have : firstJoint = secondJoint := Subsingleton.elim _ _
  cases this
  rfl

local instance pathGameCanonicalHistoryCountable :
    Countable (CanonicalHistory pathGame none) := by
  exact (pathGame.toExecution none).historyCountable

local instance pathGameChronologicalHistoryCountable :
    ∀ n, Countable (pathGame.ChronologicalHistory n) := by
  intro n
  dsimp [Stochastic.Game.ChronologicalHistory]
  infer_instance

local instance pathHistoryMeasurableSpace' (n : ℕ) :
    MeasurableSpace (PathHistory pathGame none n) := ⊤

local instance pathPlayMeasurableSpace :
    MeasurableSpace (∀ n, PathHistory pathGame none n) := MeasurableSpace.pi

def pathPolicy : (pathGame.perfectMonitoring none).Policy () :=
  fun info => ⟨some (), by
    simp [Stochastic.Game.activeMenu]
    ⟩

def pathProfile : pathGame.BehaviorProfile none :=
  fun _ => (pathPolicy).toBehavioral

private theorem pathBehavioralJoint
    (history : (pathGame.toExecution none).History)
    (hterm : ¬ (pathGame.toExecution none).terminal history.state) :
    (pathGame.perfectMonitoring none).behavioralJoint pathProfile
        history.trace hterm =
      FinDist.pure ⟨fun _ => some (), by
        exact ⟨hterm, by simp [IsLegalJoint]
        ⟩⟩ := by
  rw [(pathGame.perfectMonitoring none).behavioralJoint_eq_map_of_at_most_one_active
    pathProfile history.trace hterm () (fun i _ => Subsingleton.elim _ _)]
  · simp [pathProfile, pathPolicy,
      InformationModel.Policy.toBehavioral]
    apply congrArg FinDist.pure
    apply Subtype.ext
    rfl

theorem fairBit_support :
    some false ∈ fairBit.support ∧ some true ∈ fairBit.support := by
  constructor <;>
    exact FinDist.prob_pos_iff.mp
      (by norm_num [fairBit, FinDist.prob_mix, FinDist.prob_pure_eq_ite])

theorem fairBit_support_iff (state : Option Bool) :
    state ∈ fairBit.support ↔ state = some false ∨ state = some true := by
  rw [fairBit, FinDist.mem_support_mix_pure_iff]
  all_goals norm_num

theorem fairBit_nonconstant :
    FinDist.pure (some false) ≠ FinDist.pure (some true) := by
  intro h
  have := congrArg (fun law => law.prob (some false)) h
  simp [FinDist.prob_pure_eq_ite] at this

theorem pathGame_finite_average_two :
    pathGame.finiteAveragePayoff none 2 pathProfile () = (1 / 4 : ℝ) := by
  norm_num [Stochastic.Game.finiteAveragePayoff, Stochastic.Game.horizonUtility,
    Stochastic.Game.historyAverageUtility, Stochastic.Game.eventUtility,
    Stochastic.Game.horizonForm, InformationModel.runBehavioral,
    InformationModel.runBehavioralFrom, InformationModel.randomizedChooser,
    ExecutionProtocol.runRandomizedFor, pathProfile, pathPolicy, pathGame,
    fairBit, InformationModel.Policy.toBehavioral]
  simp_rw [pathBehavioralJoint]
  simp only [FinDist.pure_bind]
  simp only [pathGame]
  simp only [ExecutionProtocol.initHistory_state]
  unfold expectedUtility
  rw [FinDist.expect_bindOnSupport_congr
    (μ := fairBit)
    (g := fun state _ => FinDist.pure state)
    (v := fun state : Option Bool => if state = some true then 1 / 2 else 0)]
  · rw [FinDist.bindOnSupport_eq_bind, FinDist.expect_bind]
    rw [fairBit, FinDist.expect_mix]
    norm_num
  · intro state hstate
    rcases (fairBit_support_iff state).mp hstate with rfl | rfl
    · simp [Stochastic.Game.horizonUtility,
        Stochastic.Game.historyAverageUtility, Stochastic.Game.eventUtility]
    · simp [Stochastic.Game.horizonUtility,
        Stochastic.Game.historyAverageUtility, Stochastic.Game.eventUtility]

theorem pathGame_integral_canonicalPathAverage_two :
    (∫ play, canonicalPathAverage pathGame none () play 2 ∂
      infinitePlayMeasure pathGame none pathProfile) = (1 / 4 : ℝ) := by
  rw [integral_canonicalPathAverage_eq_finiteAveragePayoff
    pathGame none pathProfile () 2 (C := 1)]
  · exact pathGame_finite_average_two
  · exact Measurable.of_discrete
  · intro history
    have hrecord : ∀ record : pathGame.StageRecord,
        0 ≤ pathGame.stageRecordUtility record () ∧
          pathGame.stageRecordUtility record () ≤ 1 := by
      intro record
      rcases record with ⟨source, joint, target⟩
      cases source with
      | none => norm_num [Stochastic.Game.stageRecordUtility, pathGame]
      | some bit =>
          cases bit <;>
            norm_num [Stochastic.Game.stageRecordUtility, pathGame]
    have hlist : ∀ records : List pathGame.StageRecord,
        |List.sum (List.map (fun record =>
          pathGame.stageRecordUtility record ()) records)| ≤
          records.length := by
      intro records
      induction records with
      | nil => simp
      | cons record records ih =>
          have hrecord' := hrecord record
          rw [List.map_cons, List.sum_cons, List.length_cons]
          have habs : |pathGame.stageRecordUtility record ()| ≤ 1 := by
            rw [abs_of_nonneg hrecord'.1]
            exact hrecord'.2
          calc
            |pathGame.stageRecordUtility record () +
                List.sum (List.map (fun record =>
                  pathGame.stageRecordUtility record ()) records)| ≤
                |pathGame.stageRecordUtility record ()| +
                  |List.sum (List.map (fun record =>
                    pathGame.stageRecordUtility record ()) records)| :=
              abs_add_le _ _
            _ ≤ 1 + records.length := by
              have hh := add_le_add habs ih
              exact hh
            _ = (records.length + 1 : ℕ) := by
              norm_num [Nat.cast_add]
              ring
    have hsum := hlist
      (pathGame.publicHistoryOfChronological history)
    have hlength :
        (pathGame.publicHistoryOfChronological history).length = 2 := by
      simp [Stochastic.Game.publicHistoryOfChronological]
    rw [hlength] at hsum
    norm_num [Stochastic.Game.publicHistoryAverageUtility, pathGame]
    norm_num at hsum ⊢
    linarith

theorem pathGame_expectedFiniteAverage_one :
    expectedFiniteAverage (infinitePlayMeasure pathGame none pathProfile)
      (canonicalStageUtility pathGame none ()) 1 =
        (1 / 4 : ℝ) := by
  unfold expectedFiniteAverage
  rw [show (fun play => pathwiseAverage
      (canonicalStageUtility pathGame none ()) play 1) =
      (fun play => canonicalPathAverage pathGame none () play 2) by
        funext play
        exact pathwiseAverage_canonicalStageUtility
          pathGame none () play 1]
  exact pathGame_integral_canonicalPathAverage_two

private def pathBitUtility
    (play : ∀ n, PathHistory pathGame none n) : ℝ :=
  match (play 1).1.state with
  | none => 0
  | some false => 0
  | some true => 1

private theorem pathState_one_of_coherent
    (play : ∀ n, PathHistory pathGame none n)
    (hcoh : ∀ n : ℕ, ∃ (joint : ∀ i, Option (pathGame.Action i))
      (isLegal : (pathGame.toExecution none).Legal (play n).1.state joint)
      (realized : (play (n + 1)).1.state ∈
        ((pathGame.toExecution none).step
          (play n).1.state ⟨joint, isLegal⟩).support),
      (play (n + 1)).1 = (play n).1.extend isLegal realized) :
    (play 1).1.state = some false ∨ (play 1).1.state = some true := by
  obtain ⟨joint, isLegal, realized, hnext⟩ := hcoh 0
  have hinitial : (play 0).1.state = none := by
    rcases play 0 with ⟨⟨state, trace⟩, hlength⟩
    cases trace with
    | start => rfl
    | extend prior chosen legal result =>
        simp [Trace.length] at hlength
  have hsupport : (play 1).1.state ∈ fairBit.support := by
    simpa [pathGame, hinitial] using realized
  exact (fairBit_support_iff (play 1).1.state).mp hsupport

private theorem pathState_succ_eq_one_of_coherent
    (play : ∀ n, PathHistory pathGame none n)
    (hcoh : ∀ n : ℕ, ∃ (joint : ∀ i, Option (pathGame.Action i))
      (isLegal : (pathGame.toExecution none).Legal (play n).1.state joint)
      (realized : (play (n + 1)).1.state ∈
        ((pathGame.toExecution none).step
          (play n).1.state ⟨joint, isLegal⟩).support),
      (play (n + 1)).1 = (play n).1.extend isLegal realized) :
    ∀ n, (play (n + 1)).1.state = (play 1).1.state := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      obtain ⟨joint, isLegal, realized, hnext⟩ := hcoh (n + 1)
      rcases pathState_one_of_coherent play hcoh with hfalse | htrue
      · have hsource : (play (n + 1)).1.state = some false := ih.trans hfalse
        have htarget : (play (n + 1 + 1)).1.state = some false := by
          simpa [pathGame, hsource, FinDist.mem_support_pure] using realized
        exact htarget.trans hfalse.symm
      · have hsource : (play (n + 1)).1.state = some true := ih.trans htrue
        have htarget : (play (n + 1 + 1)).1.state = some true := by
          simpa [pathGame, hsource, FinDist.mem_support_pure] using realized
        exact htarget.trans htrue.symm

private theorem pathStageUtility_of_coherent
    (play : ∀ n, PathHistory pathGame none n)
    (hcoh : ∀ n : ℕ, ∃ (joint : ∀ i, Option (pathGame.Action i))
      (isLegal : (pathGame.toExecution none).Legal (play n).1.state joint)
      (realized : (play (n + 1)).1.state ∈
        ((pathGame.toExecution none).step
          (play n).1.state ⟨joint, isLegal⟩).support),
      (play (n + 1)).1 = (play n).1.extend isLegal realized) :
    canonicalStageUtility pathGame none () play 0 = 0 ∧
      ∀ n, canonicalStageUtility pathGame none () play (n + 1) =
        pathBitUtility play := by
  constructor
  · obtain ⟨joint, isLegal, realized, hnext⟩ := hcoh 0
    rw [canonicalStageUtility_eq_extension_of_coherent
      pathGame none () play 0 joint isLegal realized hnext]
    have hinitial : (play 0).1.state = none := by
      rcases play 0 with ⟨⟨state, trace⟩, hlength⟩
      cases trace with
      | start => rfl
      | extend prior chosen legal result =>
          simp [Trace.length] at hlength
    simp [Stochastic.Game.stageRecordUtility, pathGame, hinitial]
  · intro n
    obtain ⟨joint, isLegal, realized, hnext⟩ := hcoh (n + 1)
    rw [canonicalStageUtility_eq_extension_of_coherent
      pathGame none () play (n + 1) joint isLegal realized hnext]
    have hstate := pathState_succ_eq_one_of_coherent play hcoh n
    simp [Stochastic.Game.stageRecordUtility, pathGame, pathBitUtility, hstate]
    rfl

private theorem pathStageUtility_sum_of_coherent
    (play : ∀ n, PathHistory pathGame none n)
    (hcoh : ∀ n : ℕ, ∃ (joint : ∀ i, Option (pathGame.Action i))
      (isLegal : (pathGame.toExecution none).Legal (play n).1.state joint)
      (realized : (play (n + 1)).1.state ∈
        ((pathGame.toExecution none).step
          (play n).1.state ⟨joint, isLegal⟩).support),
      (play (n + 1)).1 = (play n).1.extend isLegal realized) :
    ∀ n, (∑ k ∈ Finset.range (n + 1),
      canonicalStageUtility pathGame none () play k) =
        (n : ℝ) * pathBitUtility play := by
  intro n
  induction n with
  | zero => simp [pathStageUtility_of_coherent play hcoh]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      rw [(pathStageUtility_of_coherent play hcoh).2 n]
      norm_num [Nat.cast_add]
      ring

private theorem pathwiseAverage_formula_of_coherent
    (play : ∀ n, PathHistory pathGame none n)
    (hcoh : ∀ n : ℕ, ∃ (joint : ∀ i, Option (pathGame.Action i))
      (isLegal : (pathGame.toExecution none).Legal (play n).1.state joint)
      (realized : (play (n + 1)).1.state ∈
        ((pathGame.toExecution none).step
          (play n).1.state ⟨joint, isLegal⟩).support),
      (play (n + 1)).1 = (play n).1.extend isLegal realized)
    (n : ℕ) :
    pathwiseAverage (canonicalStageUtility pathGame none ()) play n =
      ((n : ℝ) / ((n : ℝ) + 1)) * pathBitUtility play := by
  rw [pathwiseAverage_canonicalStageUtility]
  unfold canonicalPathAverage
  rw [if_neg (Nat.add_one_ne_zero n)]
  rw [pathStageUtility_sum_of_coherent play hcoh n]
  simp only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv]
  ring

private theorem ae_pathwiseAverage_formula (n : ℕ) :
    ∀ᵐ play ∂infinitePlayMeasure pathGame none pathProfile,
      pathwiseAverage (canonicalStageUtility pathGame none ()) play n =
        ((n : ℝ) / ((n : ℝ) + 1)) * pathBitUtility play := by
  filter_upwards [ae_all_path_coherent pathGame none pathProfile] with play hcoh
  exact pathwiseAverage_formula_of_coherent play (fun k => hcoh k) n

private theorem pathBitUtility_measurable : Measurable pathBitUtility := by
  unfold pathBitUtility
  have hmeasurable : Measurable
    ((fun history : PathHistory pathGame none 1 =>
        match history.1.state with
        | none => (0 : ℝ)
        | some false => 0
        | some true => 1) ∘
      (fun play : ∀ n, PathHistory pathGame none n => play 1)) :=
    Measurable.of_discrete.comp (measurable_pi_apply 1)
  simpa [Function.comp_def] using hmeasurable

private theorem pathBitUtility_bound
    (play : ∀ n, PathHistory pathGame none n) :
    ‖pathBitUtility play‖ ≤ 1 := by
  unfold pathBitUtility
  cases (play 1).1.state with
  | none => norm_num
  | some bit => cases bit <;> norm_num

private theorem pathBitUtility_integrable :
    Integrable pathBitUtility
      (infinitePlayMeasure pathGame none pathProfile) := by
  apply Integrable.of_bound pathBitUtility_measurable.aestronglyMeasurable 1
  exact ae_of_all _ pathBitUtility_bound

private theorem pathGame_integral_pathBitUtility :
    (∫ play, pathBitUtility play ∂
      infinitePlayMeasure pathGame none pathProfile) = (1 / 2 : ℝ) := by
  have havg : ∀ᵐ play ∂infinitePlayMeasure pathGame none pathProfile,
      canonicalPathAverage pathGame none () play 2 =
        (1 / 2 : ℝ) * pathBitUtility play := by
    filter_upwards [ae_pathwiseAverage_formula 1] with play hplay
    rw [← pathwiseAverage_canonicalStageUtility pathGame none () play 1]
    norm_num at hplay ⊢
    exact hplay
  have hintegral := integral_congr_ae havg
  rw [pathGame_integral_canonicalPathAverage_two,
    integral_const_mul] at hintegral
  linarith

theorem pathGame_expectedFiniteAverage (n : ℕ) :
    expectedFiniteAverage (infinitePlayMeasure pathGame none pathProfile)
      (canonicalStageUtility pathGame none ()) n =
        ((n : ℝ) / ((n : ℝ) + 1)) * (1 / 2 : ℝ) := by
  unfold expectedFiniteAverage
  rw [integral_congr_ae (ae_pathwiseAverage_formula n)]
  rw [integral_const_mul, pathGame_integral_pathBitUtility]

theorem pathGame_hasExpectedFiniteAverageLimit :
    HasExpectedFiniteAverageLimit
      (infinitePlayMeasure pathGame none pathProfile)
      (canonicalStageUtility pathGame none ()) (1 / 2 : ℝ) := by
  unfold HasExpectedFiniteAverageLimit
  have hfunctions :
      (fun n => expectedFiniteAverage
        (infinitePlayMeasure pathGame none pathProfile)
        (canonicalStageUtility pathGame none ()) n) =
      (fun n : ℕ => ((n : ℝ) / ((n : ℝ) + 1)) * (1 / 2 : ℝ)) := by
    funext n
    exact pathGame_expectedFiniteAverage n
  rw [hfunctions]
  simpa only [one_mul] using
    (tendsto_natCast_div_add_atTop (1 : ℝ)).mul_const (1 / 2 : ℝ)

private theorem pathwiseAverage_tendsto_of_coherent
    (play : ∀ n, PathHistory pathGame none n)
    (hcoh : ∀ n : ℕ, ∃ (joint : ∀ i, Option (pathGame.Action i))
      (isLegal : (pathGame.toExecution none).Legal (play n).1.state joint)
      (realized : (play (n + 1)).1.state ∈
        ((pathGame.toExecution none).step
          (play n).1.state ⟨joint, isLegal⟩).support),
      (play (n + 1)).1 = (play n).1.extend isLegal realized) :
    Tendsto
      (fun n => pathwiseAverage
        (canonicalStageUtility pathGame none ()) play n)
      atTop (𝓝 (pathBitUtility play)) := by
  have hfunctions :
      (fun n => pathwiseAverage
        (canonicalStageUtility pathGame none ()) play n) =
      (fun n : ℕ => ((n : ℝ) / ((n : ℝ) + 1)) * pathBitUtility play) := by
    funext n
    exact pathwiseAverage_formula_of_coherent play hcoh n
  rw [hfunctions]
  simpa only [one_mul] using
    (tendsto_natCast_div_add_atTop (1 : ℝ)).mul_const (pathBitUtility play)

theorem pathGame_expectedPathwiseLiminf :
    expectedPathwiseLiminf
      (infinitePlayMeasure pathGame none pathProfile)
      (canonicalStageUtility pathGame none ()) = (1 / 2 : ℝ) := by
  unfold expectedPathwiseLiminf
  have hliminf : ∀ᵐ play ∂infinitePlayMeasure pathGame none pathProfile,
      Filter.liminf
        (fun n => pathwiseAverage
          (canonicalStageUtility pathGame none ()) play n) atTop =
        pathBitUtility play := by
    filter_upwards [ae_all_path_coherent pathGame none pathProfile] with play hcoh
    exact (pathwiseAverage_tendsto_of_coherent play (fun k => hcoh k)).liminf_eq
  rw [integral_congr_ae hliminf, pathGame_integral_pathBitUtility]

theorem pathGame_expectedPathwiseLimsup :
    expectedPathwiseLimsup
      (infinitePlayMeasure pathGame none pathProfile)
      (canonicalStageUtility pathGame none ()) = (1 / 2 : ℝ) := by
  unfold expectedPathwiseLimsup
  have hlimsup : ∀ᵐ play ∂infinitePlayMeasure pathGame none pathProfile,
      Filter.limsup
        (fun n => pathwiseAverage
          (canonicalStageUtility pathGame none ()) play n) atTop =
        pathBitUtility play := by
    filter_upwards [ae_all_path_coherent pathGame none pathProfile] with play hcoh
    exact (pathwiseAverage_tendsto_of_coherent play (fun k => hcoh k)).limsup_eq
  rw [integral_congr_ae hlimsup, pathGame_integral_pathBitUtility]

end GameTheory.Experimental.PostArchitecture.StochasticGamePathPayoff
