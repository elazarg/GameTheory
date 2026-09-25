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

omit [Fintype ι] [∀ i, Nonempty (G.Action i)]
    [Countable (CanonicalHistory G initial)] in
/-- A bounded stage payoff integrates under every chronological history law. -/
theorem chronologicalStageUtility_integrable (who : ι) (n : ℕ)
    {C : ℝ}
    (hbound : ∀ record : G.StageRecord, ‖G.stageRecordUtility record who‖ ≤ C)
    (law : PMF (G.ChronologicalHistory (n + 1))) :
    PayoffIntegrable law (chronologicalStageUtility G who n) := by
  apply payoffIntegrable_of_bounded law _ (C := C)
  intro history
  simpa only [Real.norm_eq_abs] using
    chronologicalStageUtility_bound G who n hbound history

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

omit [Countable (CanonicalHistory G initial)] in
private theorem integral_canonicalStageUtility_eq_expect
    (who : ι) (n : ℕ) {C : ℝ}
    [Countable (G.ChronologicalHistory (n + 1))]
    (hstage_measurable :
      Measurable (fun record : G.StageRecord => G.stageRecordUtility record who))
    (hstage_bound :
      ∀ record : G.StageRecord, ‖G.stageRecordUtility record who‖ ≤ C) :
    (∫ play, canonicalStageUtility G initial who play n ∂
      infinitePlayMeasure G initial profile) =
      expect (G.chronologicalHistoryLaw initial profile (n + 1))
        (chronologicalStageUtility G who n)
        (chronologicalStageUtility_integrable G who n hstage_bound
          (G.chronologicalHistoryLaw initial profile (n + 1))) := by
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
  have hμ : PayoffIntegrable
      (G.chronologicalHistoryLaw initial profile (n + 1)) observable := by
    apply payoffIntegrable_of_bounded _ _ (C := C)
    intro history
    simpa only [Real.norm_eq_abs] using hbound history
  rw [expect_eq_integral
    (G.chronologicalHistoryLaw initial profile (n + 1)) observable hμ]
  rw [← map_chronologicalProjection_infinitePlayMeasure
    G initial profile (n + 1)]
  rw [MeasureTheory.integral_map hprojection.aemeasurable
    hobservable.aestronglyMeasurable]
  rfl

omit [Countable (CanonicalHistory G initial)] in
/-- A bounded chronological payoff integrates the actual canonical horizon law. -/
theorem canonicalProjectedAverage_integrable
    (who : ι) (horizon : ℕ) {C : ℝ}
    (hobservable_bound :
      ∀ history : G.ChronologicalHistory horizon,
        ‖G.publicHistoryAverageUtility horizon
          (G.publicHistoryOfChronological history) who‖ ≤ C) :
    UtilityIntegrable (G.horizonUtility initial horizon) who
      ((G.horizonForm initial horizon).play profile) := by
  let observable : G.ChronologicalHistory horizon → ℝ := fun history =>
    G.publicHistoryAverageUtility horizon
      (G.publicHistoryOfChronological history) who
  have hchron : PayoffIntegrable
      (G.chronologicalHistoryLaw initial profile horizon) observable := by
    apply payoffIntegrable_of_bounded _ _ (C := C)
    intro history
    simpa only [Real.norm_eq_abs] using hobservable_bound history
  have hpublic : UtilityIntegrable
      (G.publicHistoryAverageUtility horizon) who
      (G.publicHistoryLaw initial profile horizon) := by
    unfold UtilityIntegrable
    rw [← G.map_publicHistoryOfChronological_chronologicalHistoryLaw
      initial profile horizon]
    exact (payoffIntegrable_map_iff G.publicHistoryOfChronological
      (G.chronologicalHistoryLaw initial profile horizon)
      (fun history => G.publicHistoryAverageUtility horizon history who)).mpr
        (by simpa only [observable, Function.comp_def] using hchron)
  exact (G.publicFiniteAverageIntegrable_iff
    initial horizon profile who).mp hpublic

omit [Countable (CanonicalHistory G initial)] in
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
      G.finiteAveragePayoff initial horizon profile who
        (canonicalProjectedAverage_integrable G initial profile who horizon
          hobservable_bound) := by
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
  have hchron : PayoffIntegrable
      (G.chronologicalHistoryLaw initial profile horizon) observable := by
    apply payoffIntegrable_of_bounded _ _ (C := C)
    intro history
    simpa only [Real.norm_eq_abs] using hbound history
  let hcanonical :=
    canonicalProjectedAverage_integrable G initial profile who horizon
      hobservable_bound
  have hpublic : UtilityIntegrable
      (G.publicHistoryAverageUtility horizon) who
      (G.publicHistoryLaw initial profile horizon) :=
    (G.publicFiniteAverageIntegrable_iff
      initial horizon profile who).mpr hcanonical
  have hmap : PayoffIntegrable
      ((G.chronologicalHistoryLaw initial profile horizon).map
        G.publicHistoryOfChronological)
      (fun history => G.publicHistoryAverageUtility horizon history who) := by
    apply (payoffIntegrable_map_iff G.publicHistoryOfChronological
      (G.chronologicalHistoryLaw initial profile horizon)
      (fun history => G.publicHistoryAverageUtility horizon history who)).mpr
    simpa only [observable, Function.comp_def] using hchron
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
        (G.chronologicalHistoryLaw initial profile horizon).toMeasure := by
      rw [map_chronologicalProjection_infinitePlayMeasure
        G initial profile horizon]
    _ = expect (G.chronologicalHistoryLaw initial profile horizon)
        observable hchron :=
      (expect_eq_integral _ observable hchron).symm
    _ = expect
        ((G.chronologicalHistoryLaw initial profile horizon).map
          G.publicHistoryOfChronological)
        (fun history => G.publicHistoryAverageUtility horizon history who)
        hmap := by
          symm
          exact expect_map G.publicHistoryOfChronological
            (G.chronologicalHistoryLaw initial profile horizon)
            (fun history => G.publicHistoryAverageUtility horizon history who)
            (by simpa only [observable, Function.comp_def] using hchron) hmap
    _ = G.publicFiniteAveragePayoff initial horizon profile who hpublic := by
      exact expect_congr_law
        (G.map_publicHistoryOfChronological_chronologicalHistoryLaw
          initial profile horizon)
        (fun history => G.publicHistoryAverageUtility horizon history who)
        hmap hpublic
    _ = G.finiteAveragePayoff initial horizon profile who hcanonical :=
      G.publicFiniteAveragePayoff_eq_finiteAveragePayoff
        initial horizon profile who hpublic hcanonical


omit [Countable (CanonicalHistory G initial)] in
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
          expect (G.chronologicalHistoryLaw initial profile (n + 1))
            (chronologicalStageUtility G who n)
            (chronologicalStageUtility_integrable G who n hstage_bound
              (G.chronologicalHistoryLaw initial profile (n + 1))) := by
  classical
  by_cases hhorizon : horizon = 0
  · simp [hhorizon, canonicalPathAverage]
  · simp only [canonicalPathAverage, ite_eq_right hhorizon]
    rw [integral_const_mul]
    rw [integral_finsetSum]
    · congr 1
      apply Finset.sum_congr rfl
      intro n hn
      let : Countable (G.ChronologicalHistory (n + 1)) :=
        countableChronological (n + 1)
      exact integral_canonicalStageUtility_eq_expect G initial profile who n
        hstage_measurable hstage_bound
    · intro n hn
      apply Integrable.of_bound
        (canonicalStageUtility_measurable G initial who n hstage_measurable).aestronglyMeasurable
        C
      exact ae_of_all _ (fun play =>
        canonicalStageUtility_bound G initial who n hstage_bound play)

omit [Countable (CanonicalHistory G initial)] in
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
      G.finiteAveragePayoff initial horizon profile who
        (canonicalProjectedAverage_integrable G initial profile who horizon
          hstage_bound) := by
  rw [integral_congr_ae hstagewise]
  exact integral_canonicalProjectedAverage_eq_finiteAveragePayoff
    G initial profile who horizon hstage_measurable hstage_bound

end Game

end GameTheory.Experimental.PostArchitecture.StochasticInfinitePlayPayoffBridge
