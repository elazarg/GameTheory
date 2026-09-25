/-
# The discounted folk theorem

Feasible payoffs strictly above every opponent-minmax punishment level are
limits of normalized discounted payoff vectors of history-dependent Nash
profiles in the observable mixed-action repeated game. The statement uses
`UtilityGame.mixed`, deterministic repeated paths, discounted utility, and
ordinary `IsNash` directly. There is no repeated-equilibrium wrapper and no
probability law over an infinite path.

Primary reference: D. Fudenberg and E. Maskin, “The Folk Theorem in Repeated
Games with Discounting or with Incomplete Information,” *Econometrica* 54
(1986), 533--554.
-/

import GameTheory.Analysis.Repeated.Feasible
import GameTheory.Core.Mixed
import GameTheory.Repeated.Trigger

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι

variable {ι : Type uι}

namespace UtilityGame

/-- **Approximate discounted folk theorem.**

The repeated stage game is the observable mixed extension: each public stage
profile records one independent mixed action per player. -/
theorem discounted_folk_theorem_approx
    (G : UtilityGame ι)
    [Fintype ι] [DecidableEq ι]
    [∀ i, Nonempty (G.form.sig.Strategy i)]
    [Fintype G.form.sig.Outcome]
    {value : PayoffVector ι}
    (hvalue :
      value ∈ G.strictIndividuallyRationalPayoffSet
        (G.form.hasIntegrableUtility_of_finiteOutcome G.utility)
        (G.mixed.opponentMinmaxVector
          (G.mixed.form.hasIntegrableUtility_of_finiteOutcome
            G.mixed.utility))) :
    ∀ ε > 0, ∃ threshold : ℝ,
      0 ≤ threshold ∧ threshold < 1 ∧
        ∀ (discount : ℝ) (hdiscount0 : 0 ≤ discount),
          threshold < discount → (hdiscount1 : discount < 1) →
          ∃ profile : G.mixed.RepeatedProfile,
            IsNash G.mixed.repeatedForm
              (euPreference (G.mixed.discountedUtilityOfFiniteOutcome
                hdiscount0 hdiscount1)) profile ∧
            ∀ who,
              |G.mixed.discountedPayoffOfFiniteOutcome
                hdiscount0 hdiscount1 profile who - value who| < ε := by
  classical
  let H : UtilityGame ι := G.mixed
  let : ∀ i, Nonempty (H.form.sig.Strategy i) :=
    fun i => ⟨PMF.pure (Classical.arbitrary (G.form.sig.Strategy i))⟩
  let hG : G.form.HasIntegrableUtility G.utility :=
    G.form.hasIntegrableUtility_of_finiteOutcome G.utility
  let hH : H.form.HasIntegrableUtility H.utility :=
    H.form.hasIntegrableUtility_of_finiteOutcome H.utility
  have hprofileNonempty : Nonempty (Profile H.form.sig) :=
    inferInstance
  let : Nonempty (Profile H.form.sig) := hprofileNonempty
  intro ε hε
  obtain ⟨margin, hmargin, hvalueMargin⟩ :=
    G.exists_pos_margin_of_mem_strictIndividuallyRationalPayoffSet
      hG hvalue
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
        |G.stagePayoff stage who (hG who stage)| ≤ bound := by
    intro stage who
    exact (hboundG stage who).trans
      ((le_max_left boundG boundH).trans (le_max_left _ 0))
  have hboundH' :
      ∀ (who : ι) (stage : Profile H.form.sig),
        |H.stagePayoff stage who (hH who stage)| ≤ bound := by
    intro who stage
    exact (hboundH stage who).trans
      ((le_max_right boundG boundH).trans (le_max_left _ 0))
  obtain ⟨n, hn, cycle, hcycleClose⟩ :=
    G.exists_cycleAveragePayoff_close_of_mem_feasibleSet
      hG hvalue.1 hboundG' hbound0 haccuracy
  let : NeZero n := hn
  let mixedCycle : Fin n → Profile H.form.sig :=
    fun t => G.form.purify (cycle t)
  have hcyclePayoff :
      ∀ who, H.cycleAveragePayoff mixedCycle who
          (fun t => hH who (mixedCycle t)) =
        G.cycleAveragePayoff cycle who
          (fun t => hG who (cycle t)) := by
    intro who
    unfold cycleAveragePayoff
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    exact expectedUtility_congr_law G.utility who
      (G.form.mixed_play_purify (cycle t)) _ _
  have hmixedCycleClose :
      ∀ who, |H.cycleAveragePayoff mixedCycle who
          (fun t => hH who (mixedCycle t)) - value who| <
        accuracy := by
    intro who
    rw [hcyclePayoff]
    exact hcycleClose who
  let punishmentMargin : ℝ := margin / 4
  have hpunishmentMargin : 0 < punishmentMargin := by positivity
  let cap : PayoffVector ι :=
    fun who => H.opponentMinmaxVector hH who + margin / 4
  obtain ⟨punishment, hpunishmentApprox⟩ :=
    H.exists_approx_punishmentProfiles hH hpunishmentMargin
  have hboundedBest :
      ∀ who, BddAbove
        (Set.range fun own : H.form.sig.Strategy who =>
          H.stagePayoff (Profile.update (punishment who) who own) who
            (hH who _)) := by
    intro who
    refine ⟨bound, ?_⟩
    rintro _ ⟨own, rfl⟩
    exact (abs_le.mp
      (hboundH' who (Profile.update (punishment who) who own))).2
  have hpunishment :
      ∀ (who : ι) (own : H.form.sig.Strategy who),
        H.stagePayoff (Profile.update (punishment who) who own) who
          (hH who _) ≤
          cap who := by
    intro who own
    exact
      (H.stagePayoff_update_le_bestResponseValue
        hH who (punishment who) (hboundedBest who) own).trans
        (hpunishmentApprox who).le
  obtain ⟨continuationThreshold, hcontinuation0, hcontinuation1,
      hcontinuation⟩ :=
    H.exists_discountFactor_threshold_periodicAllContinuations
      mixedCycle (fun who t => hH who (mixedCycle t)) haccuracy
  have hgain : 0 ≤ 2 * bound := by positivity
  obtain ⟨patienceThreshold, hpatience0, hpatience1, hpatience⟩ :=
    GameTheory.Math.exists_discountFactor_threshold_oneStep
      (gain := 2 * bound) (margin := punishmentMargin)
      hgain hpunishmentMargin
  let threshold : ℝ := max continuationThreshold patienceThreshold
  refine ⟨threshold, ?_, ?_, ?_⟩
  · exact hcontinuation0.trans
      (le_max_left continuationThreshold patienceThreshold)
  · exact max_lt hcontinuation1 hpatience1
  · intro discount hdiscount0 hdiscount hdiscount1
    have hcontinuationDiscount :
        continuationThreshold < discount :=
      (le_max_left continuationThreshold patienceThreshold).trans_lt
        hdiscount
    have hpatienceDiscount : patienceThreshold < discount :=
      (le_max_right continuationThreshold patienceThreshold).trans_lt
        hdiscount
    have hcontinuationClose :
        ∀ (who : ι) (start : ℕ),
          |H.discountedContinuationPayoff discount
              (fun t => mixedCycle (Fin.ofNat n t)) start who
              (H.periodicContinuationStageIntegrable mixedCycle start who
                (fun t => hH who (mixedCycle t)))
              (H.periodicContinuationSummable hdiscount0 hdiscount1
                mixedCycle start who (fun t => hH who (mixedCycle t))) -
            H.cycleAveragePayoff mixedCycle who
              (fun t => hH who (mixedCycle t))| < accuracy :=
      hcontinuation discount hdiscount0
        hcontinuationDiscount hdiscount1
    have hpatient :
        (1 - discount) * (2 * bound) ≤
          discount * punishmentMargin :=
      (hpatience discount hpatienceDiscount hdiscount1).le
    let path : ℕ → Profile H.form.sig :=
      fun t => mixedCycle (Fin.ofNat n t)
    have hpath :
        ∀ (who : ι) (start : ℕ),
          cap who + punishmentMargin ≤
            H.discountedContinuationPayoffOfBounded hdiscount0 hdiscount1
              path start who hH (hboundH' who) := by
      intro who start
      have htail :
          |H.discountedContinuationPayoffOfBounded hdiscount0 hdiscount1
              path start who hH (hboundH' who) -
              H.cycleAveragePayoff mixedCycle who
                (fun t => hH who (mixedCycle t))| < accuracy := by
        simpa [path] using hcontinuationClose who start
      have hcycle := hmixedCycleClose who
      have htailLower :
          H.cycleAveragePayoff mixedCycle who
              (fun t => hH who (mixedCycle t)) - accuracy <
            H.discountedContinuationPayoffOfBounded hdiscount0 hdiscount1
              path start who hH (hboundH' who) := by
        rcases abs_lt.mp htail with ⟨hlower, _⟩
        linarith
      have hcycleLower :
          value who - accuracy <
            H.cycleAveragePayoff mixedCycle who
              (fun t => hH who (mixedCycle t)) := by
        rcases abs_lt.mp hcycle with ⟨hlower, _⟩
        linarith
      have hreservation := hvalueMargin who
      have hcap :
          cap who =
            H.opponentMinmaxVector hH who + margin / 4 := rfl
      dsimp [punishmentMargin]
      rw [hcap]
      nlinarith
    have hnash :
        IsNash H.repeatedForm
          (euPreference (H.discountedUtilityOfBounded hdiscount0
            hdiscount1 hH (fun who => ⟨bound, hboundH' who⟩)))
          (H.triggerRepeatedProfile path punishment) :=
      H.triggerRepeatedProfile_isNash
        hdiscount0 hdiscount1 path punishment cap hH
        (fun who stage => hboundH' who stage)
        hpunishment hpath hpatient
    refine ⟨H.triggerRepeatedProfile path punishment, ?_, ?_⟩
    · simpa only [UtilityGame.discountedUtilityOfFiniteOutcome,
        UtilityGame.discountedUtilityOfBounded,
        UtilityGame.discountedUtility] using hnash
    intro who
    have hpayoff :
        H.discountedPayoffOfFiniteOutcome hdiscount0 hdiscount1
            (H.triggerRepeatedProfile path punishment) who =
          H.discountedContinuationPayoffOfBounded hdiscount0 hdiscount1
            path 0 who hH (hboundH' who) := by
      simp only [UtilityGame.discountedPayoffOfFiniteOutcome,
        UtilityGame.discountedPayoffOfBounded]
      rw [H.discountedPayoff_eq_discountedContinuationPayoff_zero]
      apply congrArg
        (fun generated =>
          H.discountedContinuationPayoffOfBounded hdiscount0 hdiscount1
            generated 0 who hH (hboundH' who))
      funext t
      exact H.repeatedPlay_triggerRepeatedProfile_eq_path
        path punishment t
    have hfirst :
        |H.discountedPayoffOfFiniteOutcome hdiscount0 hdiscount1
            (H.triggerRepeatedProfile path punishment) who -
          H.cycleAveragePayoff mixedCycle who
            (fun t => hH who (mixedCycle t))| < accuracy := by
      rw [hpayoff]
      exact hcontinuationClose who 0
    have hsecond :
        |H.cycleAveragePayoff mixedCycle who
          (fun t => hH who (mixedCycle t)) - value who| < accuracy :=
      hmixedCycleClose who
    have htriangle :=
      abs_sub_le
        (H.discountedPayoffOfFiniteOutcome hdiscount0 hdiscount1
          (H.triggerRepeatedProfile path punishment) who)
        (H.cycleAveragePayoff mixedCycle who
          (fun t => hH who (mixedCycle t)))
        (value who)
    nlinarith

end UtilityGame

end GameTheory
