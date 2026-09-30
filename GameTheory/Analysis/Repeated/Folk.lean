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
profile records one independent mixed action per player. Outcome utilities need
only a uniform bound; the outcome and strategy carriers may be infinite. -/
theorem discounted_folk_theorem_approx
    (G : UtilityGame ι)
    [Fintype ι] [DecidableEq ι]
    [∀ i, Nonempty (G.form.sig.Strategy i)]
    {utilityBound : ℝ}
    (hutility : ∀ outcome who, |G.utility outcome who| ≤ utilityBound)
    {value : PayoffVector ι}
    (hvalue :
      value ∈ G.strictIndividuallyRationalPayoffSet
        (G.mixed.opponentMinmaxVector)) :
    ∀ ε > 0, ∃ threshold : ℝ,
      0 ≤ threshold ∧ threshold < 1 ∧
        ∀ (discount : ℝ) (hdiscount0 : 0 ≤ discount),
          threshold < discount → (hdiscount1 : discount < 1) →
          ∃ profile : G.mixed.RepeatedProfile,
            IsNash G.mixed.repeatedForm
              (euPreference (G.mixed.discountedUtilityOfBounded
                hdiscount0 hdiscount1 fun who =>
                  ⟨utilityBound, G.mixed.stagePayoff_abs_le_of_utility_abs_le
                    who (hutility · who)⟩)) profile ∧
            ∀ who,
              |G.mixed.discountedPayoffOfBounded hdiscount0 hdiscount1
                profile who (G.mixed.stagePayoff_abs_le_of_utility_abs_le
                  who (hutility · who)) - value who| < ε := by
  classical
  let H : UtilityGame ι := G.mixed
  have hstage (who : ι) : ∀ stage : Profile H.form.sig,
      |H.stagePayoff stage who| ≤ utilityBound :=
    H.stagePayoff_abs_le_of_utility_abs_le who (hutility · who)
  let : ∀ i, Nonempty (H.form.sig.Strategy i) :=
    fun i => ⟨PMF.pure (Classical.arbitrary (G.form.sig.Strategy i))⟩
  have hprofileNonempty : Nonempty (Profile H.form.sig) :=
    inferInstance
  let : Nonempty (Profile H.form.sig) := hprofileNonempty
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
  let bound : ℝ := max utilityBound 0
  have hbound0 : 0 ≤ bound := le_max_right _ _
  have hboundG' :
      ∀ (stage : Profile G.form.sig) (who : ι),
        |G.stagePayoff stage who| ≤ bound := fun stage who =>
    (G.stagePayoff_abs_le_of_utility_abs_le who (hutility · who) stage).trans
      (le_max_left _ _)
  have hboundH' :
      ∀ (who : ι) (stage : Profile H.form.sig),
        |H.stagePayoff stage who| ≤ bound := fun who stage =>
    (hstage who stage).trans (le_max_left _ _)
  obtain ⟨n, hn, cycle, hcycleClose⟩ :=
    G.exists_cycleAveragePayoff_close_of_mem_feasibleSet
       hvalue.1 hboundG' hbound0 haccuracy
  let : NeZero n := hn
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
    exact expectedUtility_congr_law G.utility who
      (G.form.mixed_play_purify (cycle t))
  have hmixedCycleClose :
      ∀ who, |H.cycleAveragePayoff mixedCycle who
           - value who| <
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
      mixedCycle haccuracy
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
              (H.periodicContinuationSummable hdiscount0 hdiscount1
                mixedCycle start who) -
            H.cycleAveragePayoff mixedCycle who| < accuracy :=
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
              path start who (hboundH' who) := by
      intro who start
      have htail :
          |H.discountedContinuationPayoffOfBounded hdiscount0 hdiscount1
              path start who (hboundH' who) -
              H.cycleAveragePayoff mixedCycle who| < accuracy := by
        simpa [path] using hcontinuationClose who start
      have hcycle := hmixedCycleClose who
      have htailLower :
          H.cycleAveragePayoff mixedCycle who
               - accuracy <
            H.discountedContinuationPayoffOfBounded hdiscount0 hdiscount1
              path start who (hboundH' who) := by
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
          (euPreference (H.discountedUtilityOfBounded hdiscount0
            hdiscount1 (fun who => ⟨bound, hboundH' who⟩)))
          (H.triggerRepeatedProfile path punishment) :=
      H.triggerRepeatedProfile_isNash
        hdiscount0 hdiscount1 path punishment cap
        (fun who stage => hboundH' who stage)
        hpunishment hpath hpatient
    refine ⟨H.triggerRepeatedProfile path punishment, ?_, ?_⟩
    · exact hnash
    intro who
    have hpayoff :
        H.discountedPayoffOfBounded hdiscount0 hdiscount1
            (H.triggerRepeatedProfile path punishment) who (hstage who) =
          H.discountedContinuationPayoffOfBounded hdiscount0 hdiscount1
            path 0 who (hboundH' who) := by
      simp only [UtilityGame.discountedPayoffOfBounded]
      rw [H.discountedPayoff_eq_discountedContinuationPayoff_zero]
      apply congrArg
        (fun generated =>
          H.discountedContinuationPayoffOfBounded hdiscount0 hdiscount1
            generated 0 who (hboundH' who))
      funext t
      exact H.repeatedPlay_triggerRepeatedProfile_eq_path
        path punishment t
    have hfirst :
        |H.discountedPayoffOfBounded hdiscount0 hdiscount1
            (H.triggerRepeatedProfile path punishment) who (hstage who) -
          H.cycleAveragePayoff mixedCycle who| < accuracy := by
      rw [hpayoff]
      exact hcontinuationClose who 0
    have hsecond :
        |H.cycleAveragePayoff mixedCycle who
           - value who| < accuracy :=
      hmixedCycleClose who
    have htriangle :=
      abs_sub_le
        (H.discountedPayoffOfBounded hdiscount0 hdiscount1
          (H.triggerRepeatedProfile path punishment) who (hstage who))
        (H.cycleAveragePayoff mixedCycle who)
        (value who)
    nlinarith

/-- **Approximate discounted folk theorem for finite outcomes.** Finite
outcomes supply the utility bound, so the canonical finite-outcome discounted
evaluators apply. -/
theorem discounted_folk_theorem_approx_of_finiteOutcome
    (G : UtilityGame ι)
    [Fintype ι] [DecidableEq ι]
    [∀ i, Nonempty (G.form.sig.Strategy i)]
    [Finite G.form.sig.Outcome]
    {value : PayoffVector ι}
    (hvalue :
      value ∈ G.strictIndividuallyRationalPayoffSet
        (G.mixed.opponentMinmaxVector)) :
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
  obtain ⟨bound, hbound⟩ := (Set.finite_range fun pair : G.form.sig.Outcome × ι =>
    |G.utility pair.1 pair.2|).bddAbove
  exact G.discounted_folk_theorem_approx
    (fun outcome who => hbound ⟨(outcome, who), rfl⟩) hvalue

end UtilityGame

end GameTheory
