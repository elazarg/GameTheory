module

/- Copyright (c) 2026 VegasCore contributors. Released under MIT; see NOTICE. -/

public import GameTheory.Analysis.Protocol.SequentialLimits

@[expose] public section

/-! # Uniform whole-policy regret at assessment limits

Countably many finite decision menus form a sequentially compact product. Thus
joint continuation-value continuity controls every alternative policy uniformly,
even when the alternative changes with the perturbation. This argument needs
neither recall nor Bayes consistency: it compares whole continuation policies
directly with an assessment already known to be sequentially rational. Only the
deviating player needs finite menus. Histories and the other action carriers
may be arbitrary, and play need not have a uniform horizon. Utilities need only
be bounded on terminal histories.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability Filter

variable {Player : Type*} [DecidableEq Player]
  {E : ExecutionProtocol Player} {M : InformationModel E} [E.FiniteMovers]

omit [DecidableEq Player] [E.FiniteMovers] in
private theorem policy_subsequence (who : Player) [Countable (M.InformationSite who)]
    [∀ site : M.InformationSite who, Finite (M.Choice who site.1)] (policies : ℕ →
      M.BehavioralPolicy who) :
    ∃ policy : M.BehavioralPolicy who, ∃ index : ℕ → ℕ, StrictMono index ∧
      ∀ site : M.InformationSite who,
        PMFConvergesPointwise (fun n => policies (index n) site.1) (policy site.1) := by
  classical
  obtain ⟨laws, index, increasing, converges⟩ :=
    exists_subseq_pmfConvergesPointwise_pi
      (fun n (site : M.InformationSite who) => policies n site.1)
  let policy : M.BehavioralPolicy who := fun info =>
    if decision : M.IsDecisionInfo who info then laws ⟨info, decision⟩ else policies 0 info
  refine ⟨policy, index, increasing, ?_⟩
  intro site
  simp only [policy, site.2, ↓reduceDIte]
  exact converges site

/-- At a fixed site, sequential rationality controls every whole-policy
deviation uniformly along a convergent assessment sequence. The deviating
player needs only countably many sites and finite menus; no recall, Bayes
consistency, finite history carrier or uniform horizon is assumed. -/
theorem BehavioralAssessmentConvergesPointwise.exists_uniform_terminal_policy_gain_bound_at_site
    {sequence : ℕ → M.BehavioralAssessment} {assessment : M.BehavioralAssessment}
    (converges : BehavioralAssessmentConvergesPointwise sequence assessment)
    (who : Player) [Countable (M.InformationSite who)]
    [∀ decision : M.InformationSite who, Finite (M.Choice who decision.1)]
    (site : M.InformationSite who) (certificate : E.WellFoundedHistories)
    (payoff : E.History → ℝ) (C : ℝ) (nonnegativeBound : 0 ≤ C)
    (payoffBound : ∀ final, E.terminal final.state → |payoff final| ≤ C)
    (rational : assessment.IsSequentiallyRationalAt site
      (assessment.continuationContext certificate site payoff)) :
    ∃ error : ℕ → ℝ, (∀ n, 0 ≤ error n) ∧ Tendsto error atTop (nhds 0) ∧
      ∀ n (alternative : M.BehavioralPolicy who),
        ((sequence n).continuationContext certificate site payoff).value alternative -
          ((sequence n).continuationContext certificate site payoff).value
            ((sequence n).strategy who) ≤ error n := by
  classical
  let gain (n : ℕ) (alternative : M.BehavioralPolicy who) : ℝ :=
    ((sequence n).continuationContext certificate site payoff).value alternative -
      ((sequence n).continuationContext certificate site payoff).value ((sequence n).strategy who)
  have integrable (current : M.BehavioralAssessment) (alternative : M.BehavioralPolicy who) :=
    current.continuationContext_integrable_of_bounded_terminal certificate site payoff C
      payoffBound alternative
  have bounds (current : M.BehavioralAssessment) (alternative : M.BehavioralPolicy who) :
      -C ≤ (current.continuationContext certificate site payoff).value alternative ∧
        (current.continuationContext certificate site payoff).value alternative ≤ C := by
    have onSupport (final : E.History)
        (supported : final ∈ ((current.continuationContext certificate site payoff).outcome
          alternative).support) :
        |payoff final| ≤ C := payoffBound final
      (current.continuationContext_support_terminal certificate site payoff alternative final
        supported)
    exact abs_le.mp (expect_abs_le_of_bounded_on_support onSupport)
  have bounded (n : ℕ) : BddAbove (Set.range (gain n)) := by
    refine ⟨2 * C, ?_⟩
    rintro value ⟨alternative, rfl⟩
    have first := (bounds (sequence n) alternative).2
    have second := (bounds (sequence n) ((sequence n).strategy who)).1
    dsimp only [gain]
    linarith
  let error (n : ℕ) := max 0 (sSup (Set.range (gain n)))
  have nonnegative (n : ℕ) : 0 ≤ error n := le_max_left _ _
  have bound (n : ℕ) (alternative : M.BehavioralPolicy who) : gain n alternative ≤ error n :=
    (le_csSup (bounded n) (Set.mem_range_self alternative)).trans (le_max_right _ _)
  refine ⟨error, nonnegative, ?_, bound⟩
  apply tendsto_order.mpr
  constructor
  · intro value negative
    exact Eventually.of_forall fun n => negative.trans_le (nonnegative n)
  · intro epsilon positive
    by_contra fails
    obtain ⟨first, firstIncreasing, bad⟩ :=
      extraction_of_frequently_atTop (not_eventually.mp fails)
    have deviations (n : ℕ) : ∃ alternative : M.BehavioralPolicy who,
        epsilon / 2 < gain (first n) alternative := by
      have large : epsilon ≤ sSup (Set.range (gain (first n))) := by
        have notSmall := not_lt.mp (bad n)
        change epsilon ≤ max 0 (sSup (Set.range (gain (first n)))) at notSmall
        exact (le_max_iff.mp notSmall).resolve_left (not_le.mpr positive)
      obtain ⟨value, ⟨alternative, rfl⟩, greater⟩ := exists_lt_of_lt_csSup
        (show (Set.range (gain (first n))).Nonempty from
          ⟨_, Set.mem_range_self ((sequence (first n)).strategy who)⟩) (show epsilon / 2 <
          sSup (Set.range (gain (first n))) by linarith)
      exact ⟨alternative, greater⟩
    choose alternatives greater using deviations
    obtain ⟨alternative, second, secondIncreasing, policyConverges⟩ :=
      policy_subsequence who alternatives
    have selectedConverges : BehavioralAssessmentConvergesPointwise
        (fun n => sequence (first (second n))) assessment :=
      ⟨fun player decision => (converges.strategy player decision).subseq
          (firstIncreasing.comp secondIncreasing),
        fun player decision => (converges.belief player decision).subseq
          (firstIncreasing.comp secondIncreasing)⟩
    have alternate := M.continuationContext_value_tendsto_of_bounded_terminal certificate
      selectedConverges.strategy who site (selectedConverges.belief who site)
      policyConverges payoff C nonnegativeBound payoffBound
    have prescribed := M.continuationContext_value_tendsto_of_bounded_terminal certificate
      selectedConverges.strategy who site (selectedConverges.belief who site)
      (selectedConverges.strategy who) payoff C nonnegativeBound payoffBound
    have limitBound := le_of_tendsto_of_tendsto tendsto_const_nhds (alternate.sub prescribed)
      (Eventually.of_forall fun n => (greater (second n)).le)
    have optimal := (Context.isLocallyOptimal_iff_of_integrable
      (integrable assessment (assessment.strategy who))
      fun alternative _ => integrable assessment alternative).mp rational alternative
        (Set.mem_univ _)
    linarith

/-- With finitely many sites for the deviating player, one error controls every whole
continuation policy uniformly along any convergent assessment sequence. The
sequence itself need not be fully mixed, Bayesian, or sequentially rational. -/
theorem BehavioralAssessmentConvergesPointwise.exists_uniform_terminal_policy_gain_bound
    {sequence : ℕ → M.BehavioralAssessment} {assessment : M.BehavioralAssessment}
    (converges : BehavioralAssessmentConvergesPointwise sequence assessment)
    (who : Player) [Finite (M.InformationSite who)]
    [∀ site : M.InformationSite who, Finite (M.Choice who site.1)]
    (certificate : E.WellFoundedHistories) (payoff : E.History → ℝ)
    (C : ℝ) (nonnegativeBound : 0 ≤ C)
    (payoffBound : ∀ final, E.terminal final.state → |payoff final| ≤ C)
    (rational : ∀ site : M.InformationSite who, assessment.IsSequentiallyRationalAt site
      (assessment.continuationContext certificate site payoff)) :
    ∃ error : ℕ → ℝ, (∀ n, 0 ≤ error n) ∧ Tendsto error atTop (nhds 0) ∧
      ∀ n (site : M.InformationSite who) (alternative : M.BehavioralPolicy who),
        ((sequence n).continuationContext certificate site payoff).value alternative -
          ((sequence n).continuationContext certificate site payoff).value
            ((sequence n).strategy who) ≤ error n := by
  classical
  let _ := Fintype.ofFinite (M.InformationSite who)
  choose errors nonnegative vanishes bounds using fun site =>
    converges.exists_uniform_terminal_policy_gain_bound_at_site who site certificate payoff C
      nonnegativeBound payoffBound (rational site)
  let error (n : ℕ) := ∑ site, errors site n
  refine ⟨error, (fun n => Finset.sum_nonneg fun site _ => nonnegative site n), ?_, ?_⟩
  · simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun site _ => vanishes site)
  · intro n site alternative
    exact (bounds site n alternative).trans
      (Finset.single_le_sum (fun other _ => nonnegative other n) (Finset.mem_univ site))

end GameTheory.Protocol.InformationModel

