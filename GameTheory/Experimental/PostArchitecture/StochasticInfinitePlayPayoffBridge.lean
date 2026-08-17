/-
# EXP-113: finite-average bridge for canonical stochastic paths

This file only transports a fixed finite marginal through the canonical
infinite-play measure.  It introduces no path-coherence or limit assertion.
-/

import GameTheory.Experimental.PostArchitecture.StochasticAsymptoticPayoffs
import GameTheory.Experimental.PostArchitecture.StochasticInfinitePlayCoherence

noncomputable section

open scoped BigOperators

namespace GameTheory.Experimental.PostArchitecture.StochasticInfinitePlayPayoffBridge

open MeasureTheory
open GameTheory.Math.Probability
open GameTheory.Stochastic
open GameTheory.Experimental.PostArchitecture.StochasticInfinitePlayMeasure
open GameTheory.Experimental.PostArchitecture.StochasticInfinitePlayMeasure.Game

universe uι us ua

namespace Game

variable {ι : Type uι} (G : Stochastic.Game.{uι, us, ua} ι)

variable [Fintype ι]
variable (initial : G.State) [∀ i, Nonempty (G.Action i)]
variable (profile : G.BehaviorProfile initial)
variable [Countable (CanonicalHistory G initial)]

/-- The utility of the `n`th record read from the exact `(n + 1)` projection. -/
def canonicalStageUtility (who : ι)
    (play : ∀ k, PathHistory G initial k) (n : ℕ) : ℝ :=
  G.stageRecordUtility
    (chronologicalProjection G initial (n + 1) play ⟨n, Nat.lt_succ_self n⟩) who

/-- The first `horizon` canonical stage utilities, with the empty average zero. -/
def canonicalPathAverage (who : ι)
    (play : ∀ k, PathHistory G initial k) (horizon : ℕ) : ℝ :=
  if horizon = 0 then 0 else
    (horizon : ℝ)⁻¹ * ∑ n ∈ Finset.range horizon,
      canonicalStageUtility G initial who play n

/-- A finite average read from one fixed exact-horizon projection. -/
def canonicalProjectedAverage (who : ι)
    (play : ∀ k, PathHistory G initial k) (horizon : ℕ) : ℝ :=
  G.publicHistoryAverageUtility horizon
    (G.publicHistoryOfChronological
      (chronologicalProjection G initial horizon play)) who

omit [Fintype ι] [Countable (CanonicalHistory G initial)] in
@[simp]
theorem canonicalProjectedAverage_zero (who : ι)
    (play : ∀ k, PathHistory G initial k) :
    canonicalProjectedAverage G initial who play 0 = 0 := by
  simp [canonicalProjectedAverage,
    GameTheory.Stochastic.Game.publicHistoryAverageUtility]

omit [Fintype ι] [Countable (CanonicalHistory G initial)] in
@[simp]
theorem canonicalPathAverage_zero (who : ι)
    (play : ∀ k, PathHistory G initial k) :
    canonicalPathAverage G initial who play 0 = 0 := by
  simp [canonicalPathAverage]

omit [Fintype ι] [Countable (CanonicalHistory G initial)] in
theorem pathwiseAverage_canonicalStageUtility (who : ι)
    (play : ∀ k, PathHistory G initial k) (n : ℕ) :
    pathwiseAverage (canonicalStageUtility G initial who) play n =
      canonicalPathAverage G initial who play (n + 1) := by
  simp [pathwiseAverage, canonicalPathAverage, cesaroAverage]

def chronologicalStageUtility (who : ι) (n : ℕ)
    (history : G.ChronologicalHistory (n + 1)) : ℝ :=
  G.stageRecordUtility (history ⟨n, Nat.lt_succ_self n⟩) who

omit [Fintype ι] [∀ i, Nonempty (G.Action i)]
    [Countable (CanonicalHistory G initial)] in
private theorem chronologicalStageUtility_bound (who : ι) (n : ℕ) {C : ℝ}
    (hbound : ∀ record : G.StageRecord, ‖G.stageRecordUtility record who‖ ≤ C)
    (history : G.ChronologicalHistory (n + 1)) :
    ‖chronologicalStageUtility G who n history‖ ≤ C := by
  exact hbound _

omit [Fintype ι] [Countable (CanonicalHistory G initial)] in
private theorem canonicalStageUtility_bound (who : ι) (n : ℕ) {C : ℝ}
    (hbound : ∀ record : G.StageRecord, ‖G.stageRecordUtility record who‖ ≤ C)
    (play : ∀ k, PathHistory G initial k) :
    ‖canonicalStageUtility G initial who play n‖ ≤ C := by
  exact hbound _

omit [Fintype ι] [Countable (CanonicalHistory G initial)] in
private theorem canonicalStageUtility_measurable (who : ι) (n : ℕ)
    (hstage_measurable :
      Measurable (fun record : G.StageRecord => G.stageRecordUtility record who)) :
    Measurable (fun play : ∀ k, PathHistory G initial k =>
      canonicalStageUtility G initial who play n) := by
  show Measurable
    (fun play : ∀ k, PathHistory G initial k =>
      G.stageRecordUtility
        ((chronologicalProjection G initial (n + 1) play)
          ⟨n, Nat.lt_succ_self n⟩) who)
  have hprojection : Measurable
      (chronologicalProjection G initial (n + 1)) := by
    show Measurable
      (chronologicalAt G initial (n + 1) ∘
        (fun (play : ∀ k, PathHistory G initial k) => play (n + 1)))
    exact (Measurable.of_discrete).comp (measurable_pi_apply (n + 1))
  have hrecord : Measurable
      (fun history : G.ChronologicalHistory (n + 1) =>
        history ⟨n, Nat.lt_succ_self n⟩) := measurable_pi_apply _
  exact hstage_measurable.comp (hrecord.comp hprojection)

private theorem integral_canonicalStageUtility_eq_expect
    (who : ι) (n : ℕ) {C : ℝ}
    [Countable (G.ChronologicalHistory (n + 1))]
    (hstage_measurable :
      Measurable (fun record : G.StageRecord => G.stageRecordUtility record who))
    (hstage_bound :
      ∀ record : G.StageRecord, ‖G.stageRecordUtility record who‖ ≤ C) :
    (∫ play, canonicalStageUtility G initial who play n ∂
      infinitePlayMeasure G initial profile) =
      (G.chronologicalHistoryLaw initial profile (n + 1)).expect
        (chronologicalStageUtility G who n) := by
  let projection :
      (∀ k, PathHistory G initial k) → G.ChronologicalHistory (n + 1) :=
    chronologicalProjection G initial (n + 1)
  let observable : G.ChronologicalHistory (n + 1) → ℝ :=
    chronologicalStageUtility G who n
  have hprojection : Measurable projection := by
    dsimp [projection]
    show Measurable
      (chronologicalAt G initial (n + 1) ∘
        (fun (play : ∀ k, PathHistory G initial k) => play (n + 1)))
    exact (Measurable.of_discrete).comp (measurable_pi_apply (n + 1))
  have hobservable : Measurable observable := by
    dsimp [observable, chronologicalStageUtility]
    exact hstage_measurable.comp (measurable_pi_apply _)
  have hbound : ∀ history : G.ChronologicalHistory (n + 1),
      ‖observable history‖ ≤ C := by
    intro history
    exact chronologicalStageUtility_bound G who n hstage_bound history
  rw [← finDistMeasure_integral_eq_expect_of_bound
    (G.chronologicalHistoryLaw initial profile (n + 1)) observable hbound]
  rw [← map_chronologicalProjection_infinitePlayMeasure
    G initial profile (n + 1)]
  rw [MeasureTheory.integral_map hprojection.aemeasurable
    hobservable.aestronglyMeasurable]
  rfl

theorem integral_canonicalProjectedAverage_eq_finiteAveragePayoff
    (who : ι) (horizon : ℕ) {C : ℝ}
    [Countable (G.ChronologicalHistory horizon)]
    (hobservable_measurable :
      Measurable (fun history : G.ChronologicalHistory horizon =>
        G.publicHistoryAverageUtility horizon
          (G.publicHistoryOfChronological history) who))
    (hobservable_bound :
      ∀ history : G.ChronologicalHistory horizon,
        ‖G.publicHistoryAverageUtility horizon
          (G.publicHistoryOfChronological history) who‖ ≤ C) :
    (∫ play, canonicalProjectedAverage G initial who play horizon ∂
      infinitePlayMeasure G initial profile) =
      G.finiteAveragePayoff initial horizon profile who := by
  let projection :
      (∀ k, PathHistory G initial k) → G.ChronologicalHistory horizon :=
    chronologicalProjection G initial horizon
  let observable : G.ChronologicalHistory horizon → ℝ := fun history =>
    G.publicHistoryAverageUtility horizon
      (G.publicHistoryOfChronological history) who
  have hprojection : Measurable projection := by
    dsimp [projection]
    show Measurable
      (chronologicalAt G initial horizon ∘
        (fun (play : ∀ k, PathHistory G initial k) => play horizon))
    exact (Measurable.of_discrete).comp (measurable_pi_apply horizon)
  have hobservable : Measurable observable := by
    exact hobservable_measurable
  have hbound : ∀ history : G.ChronologicalHistory horizon,
      ‖observable history‖ ≤ C := by
    exact hobservable_bound
  calc
    (∫ play, canonicalProjectedAverage G initial who play horizon ∂
        infinitePlayMeasure G initial profile) =
        ∫ play, observable (projection play) ∂
          infinitePlayMeasure G initial profile := by
      rfl
    _ = ∫ history, observable history ∂
        (infinitePlayMeasure G initial profile).map projection := by
      rw [MeasureTheory.integral_map hprojection.aemeasurable
        hobservable.aestronglyMeasurable]
    _ = ∫ history, observable history ∂
        finDistMeasure (G.chronologicalHistoryLaw initial profile horizon) := by
      rw [map_chronologicalProjection_infinitePlayMeasure
        G initial profile horizon]
    _ = (G.chronologicalHistoryLaw initial profile horizon).expect observable :=
      finDistMeasure_integral_eq_expect_of_bound
        (G.chronologicalHistoryLaw initial profile horizon) observable hbound
    _ = G.finiteAveragePayoff initial horizon profile who := by
      unfold observable
      rw [← FinDist.expect_map G.publicHistoryOfChronological
        (G.chronologicalHistoryLaw initial profile horizon)
        (G.publicHistoryAverageUtility horizon · who)]
      rw [G.map_publicHistoryOfChronological_chronologicalHistoryLaw]
      show G.publicFiniteAveragePayoff initial horizon profile who =
        G.finiteAveragePayoff initial horizon profile who
      exact G.publicFiniteAveragePayoff_eq_finiteAveragePayoff
        initial horizon profile who


theorem integral_canonicalPathAverage_eq_marginal_sum
    (who : ι) (horizon : ℕ) {C : ℝ}
    (countableChronological :
      ∀ n, Countable (G.ChronologicalHistory n))
    (hstage_measurable :
      Measurable (fun record : G.StageRecord => G.stageRecordUtility record who))
    (hstage_bound :
      ∀ record : G.StageRecord, ‖G.stageRecordUtility record who‖ ≤ C) :
    (∫ play, canonicalPathAverage G initial who play horizon ∂
      infinitePlayMeasure G initial profile) =
      if horizon = 0 then 0 else
        (horizon : ℝ)⁻¹ * ∑ n ∈ Finset.range horizon,
          (G.chronologicalHistoryLaw initial profile (n + 1)).expect
            (chronologicalStageUtility G who n) := by
  classical
  by_cases hhorizon : horizon = 0
  · simp [hhorizon, canonicalPathAverage]
  · simp only [canonicalPathAverage, if_neg hhorizon]
    rw [integral_const_mul]
    rw [integral_finsetSum]
    · congr 1
      apply Finset.sum_congr rfl
      intro n hn
      letI : Countable (G.ChronologicalHistory (n + 1)) :=
        countableChronological (n + 1)
      exact integral_canonicalStageUtility_eq_expect G initial profile who n
        hstage_measurable hstage_bound
    · intro n hn
      apply Integrable.of_bound
        (canonicalStageUtility_measurable G initial who n hstage_measurable).aestronglyMeasurable
        C
      exact ae_of_all _ (fun play =>
        canonicalStageUtility_bound G initial who n hstage_bound play)

/-- Stagewise consistency remains an explicit consumer seam; this transports it. -/
theorem integral_canonicalPathAverage_eq_finiteAveragePayoff_of_ae_stagewiseConsistency
    (who : ι) (horizon : ℕ) {C : ℝ}
    [Countable (G.ChronologicalHistory horizon)]
    (hstage_measurable :
      Measurable (fun history : G.ChronologicalHistory horizon =>
        G.publicHistoryAverageUtility horizon
          (G.publicHistoryOfChronological history) who))
    (hstage_bound :
      ∀ history : G.ChronologicalHistory horizon,
        ‖G.publicHistoryAverageUtility horizon
          (G.publicHistoryOfChronological history) who‖ ≤ C)
    (hstagewise :
      ∀ᵐ play ∂infinitePlayMeasure G initial profile,
        canonicalPathAverage G initial who play horizon =
          canonicalProjectedAverage G initial who play horizon) :
    (∫ play, canonicalPathAverage G initial who play horizon ∂
      infinitePlayMeasure G initial profile) =
      G.finiteAveragePayoff initial horizon profile who := by
  rw [integral_congr_ae hstagewise]
  exact integral_canonicalProjectedAverage_eq_finiteAveragePayoff
    G initial profile who horizon hstage_measurable hstage_bound

end Game

end GameTheory.Experimental.PostArchitecture.StochasticInfinitePlayPayoffBridge
