/-
# The discounted folk theorem

Feasible payoffs strictly above every opponent-minmax punishment level are
limits of normalized discounted payoff vectors of history-dependent Nash
profiles in the observable mixed-action repeated game.

This is the EXP-031 flagship. Its proof architecture is adapted from the pinned
v1 `FolkTheorem/Main.lean`, while its statement uses the existing
`UtilityGame.mixed`, deterministic repeated path, discounted utility, and
ordinary `IsNash` directly. There is no repeated-equilibrium wrapper and no
probability law over an infinite path.
-/

import GameTheory.Analysis.Repeated.Feasible
import GameTheory.Core.Mixed
import GameTheory.Repeated.Trigger

noncomputable section

namespace GameTheory

open Probability

universe uι

variable {ι : Type uι}

namespace UtilityGame

/-- **Approximate discounted folk theorem.**

The repeated stage game is the observable mixed extension: each public stage
profile records one independent mixed action per player. -/
theorem discounted_folk_theorem_approx
    (G : UtilityGame ι)
    [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.form.sig.Strategy i)]
    [∀ i, Nonempty (G.form.sig.Strategy i)]
    [Fintype G.form.sig.Outcome]
    {value : PayoffVector ι}
    (hvalue :
      value ∈ G.strictIndividuallyRationalPayoffSet
        G.mixed.opponentMinmaxVector) :
    ∀ ε > 0, ∃ threshold : ℝ,
      0 ≤ threshold ∧ threshold < 1 ∧
        ∀ discount : ℝ, threshold < discount → discount < 1 →
          ∃ profile : G.mixed.RepeatedProfile,
            IsNash G.mixed.repeatedForm
              (euPreference (G.mixed.discountedUtility discount)) profile ∧
            ∀ who,
              |G.mixed.discountedPayoff discount profile who - value who| < ε := by
  classical
  let H : UtilityGame ι := G.mixed
  letI : ∀ i, Nonempty (H.form.sig.Strategy i) :=
    fun i => ⟨FinDist.pure (Classical.arbitrary (G.form.sig.Strategy i))⟩
  have hprofileNonempty : Nonempty (Profile H.form.sig) :=
    inferInstance
  letI : Nonempty (Profile H.form.sig) := hprofileNonempty
  intro ε hε
  obtain ⟨margin, hmargin, hvalueMargin⟩ :=
    G.exists_pos_margin_of_mem_strictIndividuallyRationalPayoffSet
      hvalue
  let accuracy : ℝ := min (ε / 2) (margin / 8)
  have haccuracy : 0 < accuracy :=
    lt_min (half_pos hε) (by positivity)
  have haccuracyEpsilon : accuracy ≤ ε / 2 :=
    min_le_left _ _
  have haccuracyMargin : accuracy ≤ margin / 8 :=
    min_le_right _ _
  obtain ⟨boundG, hboundG0, hboundG⟩ :=
    G.exists_uniform_stagePayoff_abs_bound
  obtain ⟨boundH, hboundH0, hboundH⟩ :=
    H.exists_uniform_stagePayoff_abs_bound
  let bound : ℝ := max (max boundG boundH) 0
  have hbound0 : 0 ≤ bound := le_max_right _ _
  have hboundG' :
      ∀ (stage : Profile G.form.sig) (who : ι),
        |G.stagePayoff stage who| ≤ bound := by
    intro stage who
    exact (hboundG stage who).trans
      ((le_max_left boundG boundH).trans (le_max_left _ 0))
  have hboundH' :
      ∀ (who : ι) (stage : Profile H.form.sig),
        |H.stagePayoff stage who| ≤ bound := by
    intro who stage
    exact (hboundH stage who).trans
      ((le_max_right boundG boundH).trans (le_max_left _ 0))
  obtain ⟨n, hn, cycle, hcycleClose⟩ :=
    G.exists_cycleAveragePayoff_close_of_mem_feasibleSet
      hvalue.1 hboundG' hbound0 haccuracy
  letI : NeZero n := hn
  let mixedCycle : Fin n → Profile H.form.sig :=
    fun t => G.form.purify (cycle t)
  have hcyclePayoff :
      ∀ who, H.cycleAveragePayoff mixedCycle who =
        G.cycleAveragePayoff cycle who := by
    intro who
    unfold cycleAveragePayoff
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    exact congrArg (expectedUtility G.utility who)
      (G.form.mixed_play_purify (cycle t))
  have hmixedCycleClose :
      ∀ who, |H.cycleAveragePayoff mixedCycle who - value who| <
        accuracy := by
    intro who
    rw [hcyclePayoff]
    exact hcycleClose who
  let punishmentMargin : ℝ := margin / 4
  have hpunishmentMargin : 0 < punishmentMargin := by positivity
  let cap : PayoffVector ι :=
    fun who => H.opponentMinmaxVector who + margin / 4
  obtain ⟨punishment, hpunishmentApprox⟩ :=
    H.exists_approx_punishmentProfiles hpunishmentMargin
  have hboundedBest :
      ∀ who, BddAbove
        (Set.range fun own : H.form.sig.Strategy who =>
          H.stagePayoff (Profile.update (punishment who) who own) who) := by
    intro who
    refine ⟨bound, ?_⟩
    rintro _ ⟨own, rfl⟩
    exact (abs_le.mp
      (hboundH' who (Profile.update (punishment who) who own))).2
  have hpunishment :
      ∀ (who : ι) (own : H.form.sig.Strategy who),
        H.stagePayoff (Profile.update (punishment who) who own) who ≤
          cap who := by
    intro who own
    exact
      (H.stagePayoff_update_le_bestResponseValue
        who (punishment who) (hboundedBest who) own).trans
        (hpunishmentApprox who).le
  obtain ⟨continuationThreshold, hcontinuation0, hcontinuation1,
      hcontinuation⟩ :=
    H.exists_discountFactor_threshold_periodicAllContinuations
      mixedCycle hboundH' haccuracy
  have hgain : 0 ≤ 2 * bound := by positivity
  obtain ⟨patienceThreshold, hpatience0, hpatience1, hpatience⟩ :=
    exists_discountFactor_threshold_oneStep
      (gain := 2 * bound) (margin := punishmentMargin)
      hgain hpunishmentMargin
  let threshold : ℝ := max continuationThreshold patienceThreshold
  refine ⟨threshold, ?_, ?_, ?_⟩
  · exact hcontinuation0.trans
      (le_max_left continuationThreshold patienceThreshold)
  · exact max_lt hcontinuation1 hpatience1
  · intro discount hdiscount hdiscount1
    have hcontinuationDiscount :
        continuationThreshold < discount :=
      (le_max_left continuationThreshold patienceThreshold).trans_lt
        hdiscount
    have hpatienceDiscount : patienceThreshold < discount :=
      (le_max_right continuationThreshold patienceThreshold).trans_lt
        hdiscount
    have hdiscount0 : 0 ≤ discount :=
      hcontinuation0.trans
        (le_max_left continuationThreshold patienceThreshold) |>
          fun h => h.trans hdiscount.le
    have hcontinuationClose :
        ∀ (who : ι) (start : ℕ),
          |H.discountedContinuationPayoff discount
              (fun t => mixedCycle (Fin.ofNat n t)) start who -
            H.cycleAveragePayoff mixedCycle who| < accuracy :=
      hcontinuation discount hcontinuationDiscount hdiscount1
    have hpatient :
        (1 - discount) * (2 * bound) ≤
          discount * punishmentMargin :=
      (hpatience discount hpatienceDiscount hdiscount1).le
    let path : ℕ → Profile H.form.sig :=
      fun t => mixedCycle (Fin.ofNat n t)
    have hpath :
        ∀ (who : ι) (start : ℕ),
          cap who + punishmentMargin ≤
            H.discountedContinuationPayoff discount path start who := by
      intro who start
      have htail :
          |H.discountedContinuationPayoff discount path start who -
              H.cycleAveragePayoff mixedCycle who| < accuracy := by
        simpa [path] using hcontinuationClose who start
      have hcycle := hmixedCycleClose who
      have htailLower :
          H.cycleAveragePayoff mixedCycle who - accuracy <
            H.discountedContinuationPayoff discount path start who := by
        rcases abs_lt.mp htail with ⟨hlower, _⟩
        linarith
      have hcycleLower :
          value who - accuracy <
            H.cycleAveragePayoff mixedCycle who := by
        rcases abs_lt.mp hcycle with ⟨hlower, _⟩
        linarith
      have hreservation := hvalueMargin who
      have hcap :
          cap who =
            H.opponentMinmaxVector who + margin / 4 := rfl
      dsimp [punishmentMargin]
      rw [hcap]
      nlinarith
    have hnash :
        IsNash H.repeatedForm
          (euPreference (H.discountedUtility discount))
          (H.triggerRepeatedProfile path punishment) :=
      H.triggerRepeatedProfile_isNash
        hdiscount0 hdiscount1 path punishment cap hboundH'
        hpunishment hpath hpatient
    refine ⟨H.triggerRepeatedProfile path punishment, hnash, ?_⟩
    intro who
    have hpayoff :
        H.discountedPayoff discount
            (H.triggerRepeatedProfile path punishment) who =
          H.discountedContinuationPayoff discount path 0 who := by
      rw [H.discountedPayoff_eq_discountedContinuationPayoff_zero]
      apply congrArg
        (fun generated =>
          H.discountedContinuationPayoff discount generated 0 who)
      funext t
      exact H.repeatedPlay_triggerRepeatedProfile_eq_path
        path punishment t
    have hfirst :
        |H.discountedPayoff discount
            (H.triggerRepeatedProfile path punishment) who -
          H.cycleAveragePayoff mixedCycle who| < accuracy := by
      rw [hpayoff]
      exact hcontinuationClose who 0
    have hsecond :
        |H.cycleAveragePayoff mixedCycle who - value who| < accuracy :=
      hmixedCycleClose who
    have htriangle :=
      abs_sub_le
        (H.discountedPayoff discount
          (H.triggerRepeatedProfile path punishment) who)
        (H.cycleAveragePayoff mixedCycle who)
        (value who)
    nlinarith

end UtilityGame

end GameTheory
