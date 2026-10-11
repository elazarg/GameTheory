/-
# Optimal decisions under a fixed payoff

A supported observation fiber can erase payoff-relevant state differences when
all its supported states share a maximizing action. This characterizes
preservation of coarse optimal laws for a finite action menu. It does not make
the sets of coarse and informed optimal laws equal: informed responses may
introduce extra correlations even for a constant payoff.

Uniform bounds are imposed only on supported states. Priors, their supports,
and observation carriers remain arbitrary. Finite actions are needed for
optimal-policy existence, not for the full-information response criterion or
the optimal-witness transport. Reporting utilities characterize universal
preservation when the retained fact has a finite reporting menu.
-/

import GameTheory.Analysis.DecisionExperiment
import GameTheory.Math.Probability.ExpectationCommutation
import GameTheory.Math.Probability.Bounds

noncomputable section
namespace GameTheory.DecisionExperiment
open GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Math.Probability.ObservationAbstraction
variable {State Signal Action Fact : Type*}

/-- A support-local uniform utility bound makes every response policy integrable. -/
theorem context_integrable_of_bounded (prior : PMF State) (observe : State → Signal)
    (fact : State → Fact) (utility : Fact → Action → ℝ) {C : ℝ}
    (bounded : ∀ state ∈ prior.support, ∀ action, |utility (fact state) action| ≤ C)
    (policy : Signal → PMF Action) : (context prior observe fact utility).IntegrableAt policy := by
  apply payoffIntegrable_of_bounded_on_support (C := C)
  intro pair used
  have retained : pair.1 ∈ (prior.map fact).support := by
    rw [← responseLaw_fst prior observe fact policy]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨pair, used, rfl⟩
  obtain ⟨state, supported, same⟩ := (PMF.mem_support_map_iff _ _ _).mp retained
  change |utility pair.1 pair.2| ≤ C
  rw [← same]
  exact bounded state supported pair.2

/-- The policy value is the prior mean of its statewise response values. -/
theorem context_value_eq (prior : PMF State) (observe : State → Signal)
    (fact : State → Fact) (utility : Fact → Action → ℝ) (policy : Signal → PMF Action)
    (integrable : (context prior observe fact utility).IntegrableAt policy) :
    (context prior observe fact utility).value policy =
      expect prior (fun state => expect (policy (observe state)) (utility (fact state))) := by
  change PayoffIntegrable (responseLaw prior observe fact policy) (fun pair => utility pair.1 pair.2) at integrable
  change expect (responseLaw prior observe fact policy) (fun pair => utility pair.1 pair.2) = _
  rw [responseLaw_eq_bind] at integrable ⊢
  rw [expect_bind_tower _ _ _ integrable]
  simp only [expect_map]
  rfl

/-- Under a uniform support bound, guarded optimality is comparison of real policy values. -/
theorem isOptimal_iff_value_le (prior : PMF State) (observe : State → Signal)
    (fact : State → Fact) (utility : Fact → Action → ℝ) {C : ℝ}
    (bounded : ∀ state ∈ prior.support, ∀ action, |utility (fact state) action| ≤ C)
    (policy : Signal → PMF Action) : IsOptimal prior observe fact utility policy ↔
      ∀ alternative, (context prior observe fact utility).value alternative ≤
        (context prior observe fact utility).value policy := by
  rw [IsOptimal, Context.isLocallyOptimal_iff_of_integrable
    (context_integrable_of_bounded prior observe fact utility bounded policy)
    (fun alternative _ => context_integrable_of_bounded prior observe fact utility bounded alternative)]
  simp only [Set.mem_univ, forall_true_left]

/-- Statewise response means remain integrable for arbitrary priors. -/
theorem response_means_integrable (prior : PMF State) (observe : State → Signal)
    (fact : State → Fact) (utility : Fact → Action → ℝ) {C : ℝ}
    (bounded : ∀ state ∈ prior.support, ∀ action, |utility (fact state) action| ≤ C)
    (policy : Signal → PMF Action) :
    PayoffIntegrable prior (fun state => expect (policy (observe state)) (utility (fact state))) := by
  apply payoffIntegrable_of_bounded_on_support (C := C)
  intro state supported
  obtain ⟨action, -⟩ := (policy (observe state)).support_nonempty
  exact expect_abs_le_of_bounded ((abs_nonneg _).trans (bounded state supported action))
    (bounded state supported)

/-- Full information is optimal exactly when each supported state has an optimal response.
The state carrier, action carrier and prior support may all be infinite. -/
theorem fullInformation_optimal_iff (prior : PMF State) (fact : State → Fact)
    (utility : Fact → Action → ℝ) {C : ℝ}
    (bounded : ∀ state ∈ prior.support, ∀ action, |utility (fact state) action| ≤ C)
    (policy : State → PMF Action) : IsOptimal prior id fact utility policy ↔
      ∀ state ∈ prior.support, ∀ action,
        utility (fact state) action ≤ expect (policy state) (utility (fact state)) := by
  classical
  rw [isOptimal_iff_value_le prior id fact utility bounded]
  constructor
  · intro optimal state supported action
    by_contra notOptimal
    let alternative : State → PMF Action := fun actual =>
      if actual = state then PMF.pure action else policy actual
    have better : expect prior (fun actual => expect (policy actual) (utility (fact actual))) <
        expect prior (fun actual => expect (alternative actual) (utility (fact actual))) := by
      refine expect_lt_of_mem_support
        (response_means_integrable prior id fact utility bounded policy)
        (response_means_integrable prior id fact utility bounded alternative)
        ?_ state supported ?_
      · intro actual _
        by_cases same : actual = state
        · subst actual
          simpa only [alternative, ite_eq_left rfl, expect_pure] using (not_le.mp notOptimal).le
        · simp only [alternative, ite_eq_right same, le_refl]
      · simpa only [alternative, ite_eq_left rfl, expect_pure] using not_le.mp notOptimal
    have comparison := optimal alternative
    rw [context_value_eq _ _ _ _ _ (context_integrable_of_bounded _ _ _ _ bounded alternative),
      context_value_eq _ _ _ _ _ (context_integrable_of_bounded _ _ _ _ bounded policy)] at comparison
    exact (not_lt_of_ge comparison) better
  · intro optimal alternative
    rw [context_value_eq _ _ _ _ _ (context_integrable_of_bounded _ _ _ _ bounded alternative),
      context_value_eq _ _ _ _ _ (context_integrable_of_bounded _ _ _ _ bounded policy)]
    apply expect_mono _ (response_means_integrable prior id fact utility bounded alternative)
      (response_means_integrable prior id fact utility bounded policy)
    intro state supported
    exact expect_le_const _ _ (payoffIntegrable_of_bounded _ _ (bounded state supported)) _
      (fun action _ => optimal state supported action)

/-- A supported response can use only actions maximizing the statewise utility. -/
theorem fullInformation_optimal_iff_support (prior : PMF State) (fact : State → Fact)
    (utility : Fact → Action → ℝ) {C : ℝ}
    (bounded : ∀ state ∈ prior.support, ∀ action, |utility (fact state) action| ≤ C)
    (policy : State → PMF Action) : IsOptimal prior id fact utility policy ↔
      ∀ state ∈ prior.support, ∀ action ∈ (policy state).support,
        ∀ alternative, utility (fact state) alternative ≤ utility (fact state) action := by
  rw [fullInformation_optimal_iff prior fact utility bounded]
  constructor
  · intro optimal state supported action used alternative
    have selected := expect_eq_const_of_le_on_support (policy state) (utility (fact state))
      (expect (policy state) (utility (fact state)))
      (payoffIntegrable_of_bounded _ _ (bounded state supported))
      (fun candidate _ => optimal state supported candidate) rfl action used
    rw [selected]
    exact optimal state supported alternative
  · intro optimal state supported alternative
    calc
      _ = expect (policy state) (fun _ => utility (fact state) alternative) :=
        (expect_constant _ _).symm
      _ ≤ _ := expect_mono (fun action used => optimal state supported action used alternative)
        (payoffIntegrable_constant _ _) (payoffIntegrable_of_bounded _ _ (bounded state supported))

/-- Supported observation fibers admit an action maximizing utility at every supported state.
Unreachable observations impose no constraint. -/
def HasCommonMaximizer (prior : PMF State) (observe : State → Signal)
    (utility : State → Action → ℝ) : Prop :=
  ∀ signal ∈ (prior.map observe).support, ∃ action,
    ∀ state ∈ prior.support, observe state = signal →
      ∀ alternative, utility state alternative ≤ utility state action

/-- A policy can remain optimal under full information precisely when supported fibers
have common maximizing actions. No finite carrier or finite prior is required. -/
theorem exists_optimal_lift_iff_commonMaximizer (prior : PMF State) (observe : State → Signal)
    (fact : State → Fact) (utility : Fact → Action → ℝ) {C : ℝ}
    (bounded : ∀ state ∈ prior.support, ∀ action, |utility (fact state) action| ≤ C) :
    (∃ policy : Signal → PMF Action,
      IsOptimal prior id fact utility (fun state => policy (observe state))) ↔
      HasCommonMaximizer prior observe (fun state => utility (fact state)) := by
  classical
  constructor
  · rintro ⟨policy, optimal⟩ signal _
    obtain ⟨action, used⟩ := (policy signal).support_nonempty
    refine ⟨action, fun state supported same alternative => ?_⟩
    exact ((fullInformation_optimal_iff_support prior fact utility bounded _).mp optimal)
      state supported action (by simpa only [same] using used) alternative
  · intro common
    obtain ⟨signal, supported⟩ := (prior.map observe).support_nonempty
    obtain ⟨fallback, -⟩ := common signal supported
    choose best maximal using common
    let policy : Signal → PMF Action := fun signal =>
      if supported : signal ∈ (prior.map observe).support then PMF.pure (best signal supported)
      else PMF.pure fallback
    refine ⟨policy, (fullInformation_optimal_iff prior fact utility bounded _).mpr ?_⟩
    intro state supported alternative
    have observed : observe state ∈ (prior.map observe).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨state, supported, rfl⟩
    simpa only [policy, dite_eq_left observed, expect_pure] using
      maximal (observe state) observed state supported rfl alternative

/-- Matching the retained law of a fully informed optimum makes the simple lift optimal.
Expectation guards are preserved even when utility is unbounded. -/
theorem optimal_match_iff_lift (prior : PMF State) (observe : State → Signal)
    (fact : State → Fact) (utility : Fact → Action → ℝ) (source : Signal → PMF Action) :
    (∃ target : State → PMF Action, IsOptimal prior id fact utility target ∧
      responseLaw prior id fact target = responseLaw prior observe fact source) ↔
      IsOptimal prior id fact utility (fun state => source (observe state)) := by
  constructor
  · rintro ⟨target, optimal, same⟩
    exact optimal.of_outcome_coverage rfl same.symm
      (fun alternative _ => ⟨alternative, Set.mem_univ _, rfl⟩)
  · intro optimal
    exact ⟨fun state => source (observe state), optimal, rfl⟩

/-- With a common full-information optimum, every coarse optimum remains optimal.
This direction needs neither bounded utilities nor finite actions. -/
theorem isOptimal_lift_of_optimal_witness (prior : PMF State) (observe : State → Signal)
    (fact : State → Fact) (utility : Fact → Action → ℝ)
    (witness : Signal → PMF Action)
    (witnessOptimal : IsOptimal prior id fact utility (fun state => witness (observe state)))
    (source : Signal → PMF Action) (sourceOptimal : IsOptimal prior observe fact utility source) :
    IsOptimal prior id fact utility (fun state => source (observe state)) := by
  refine ⟨sourceOptimal.1, witnessOptimal.2.1, ?_⟩
  intro alternative allowed
  exact (witnessOptimal.2.2 alternative allowed).trans
    (sourceOptimal.2.2 witness (Set.mem_univ _))

open Classical in
/-- A fiber's response value is the response mean of pure-action fiber values. -/
theorem fiber_value_eq (prior : PMF State) (observe : State → Signal)
    (fact : State → Fact) (utility : Fact → Action → ℝ) {C : ℝ}
    (bounded : ∀ state ∈ prior.support, ∀ action, |utility (fact state) action| ≤ C)
    (signal : Signal) (response : PMF Action) :
    expect prior (fun state => if observe state = signal then
      expect response (utility (fact state)) else 0) =
    expect response (fun action => expect prior (fun state =>
      if observe state = signal then utility (fact state) action else 0)) := by
  classical
  have integrable : PayoffIntegrable (bindPairLaw prior (fun _ => response))
      (fun pair => if observe pair.1 = signal then utility (fact pair.1) pair.2 else 0) := by
    apply payoffIntegrable_of_bounded_on_support (C := max C 0)
    intro pair used
    have present : pair.1 ∈ prior.support := by
      rw [← bindPairLaw_map_fst prior (fun _ => response)]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨pair, used, rfl⟩
    split
    · exact (bounded pair.1 present pair.2).trans (le_max_left _ _)
    · simpa only [abs_zero] using le_max_right C 0
  have commute := expect_comm prior response (fun state action =>
    if observe state = signal then utility (fact state) action else 0) integrable
  rw [← commute]
  apply expect_congr_on_support
  intro state _
  by_cases same : observe state = signal
  · simp only [same, ite_eq_left]
  · simp only [same, ↓reduceIte, expect_zero]

/-- Finite action menus admit a deterministic optimum for arbitrary priors and observations.
Only utilities on supported states must share a bound. -/
theorem exists_optimal [Finite Action] [Nonempty Action] (prior : PMF State)
    (observe : State → Signal) (fact : State → Fact) (utility : Fact → Action → ℝ) {C : ℝ}
    (bounded : ∀ state ∈ prior.support, ∀ action, |utility (fact state) action| ≤ C) :
    ∃ policy : Signal → PMF Action, IsOptimal prior observe fact utility policy := by
  classical
  let score : Signal → Action → ℝ := fun signal action =>
    expect prior (fun state => if observe state = signal then utility (fact state) action else 0)
  choose best maximal using fun signal => Finite.exists_max (score signal)
  refine ⟨fun signal => PMF.pure (best signal),
    (isOptimal_iff_value_le prior observe fact utility bounded _).mpr ?_⟩
  intro alternative
  rw [context_value_eq _ _ _ _ _ (context_integrable_of_bounded _ _ _ _ bounded alternative),
    context_value_eq _ _ _ _ _ (context_integrable_of_bounded _ _ _ _ bounded _)]
  apply expect_le_of_fiber_expect_le prior observe
    _ _ (response_means_integrable _ _ _ _ bounded _)
    (response_means_integrable _ _ _ _ bounded alternative)
  intro signal _
  have same (policy : Signal → PMF Action) :
      expect prior (fun state => if state ∈ observe ⁻¹' {signal} then
        expect (policy (observe state)) (utility (fact state)) else 0) =
      expect (policy signal) (score signal) := by
    rw [← fiber_value_eq prior observe fact utility bounded signal (policy signal)]
    apply expect_congr_on_support
    intro state _
    by_cases observed : observe state = signal <;>
      simp only [Set.mem_preimage, Set.mem_singleton_iff, observed, ↓reduceIte]
  rw [same alternative, same (fun signal => PMF.pure (best signal)), expect_pure]
  exact expect_le_const _ _ (payoffIntegrable_of_finite _ _) _ (fun action _ => maximal signal action)

/-- Exact fixed-payoff classification for finite action menus. Every coarse optimum
has a fully informed optimum with the same retained law exactly when supported
observation fibers have common maximizers. Informed optima can still have extra laws. -/
theorem preserves_fixed_payoff_iff_commonMaximizer [Finite Action] [Nonempty Action]
    (prior : PMF State) (observe : State → Signal) (fact : State → Fact)
    (utility : Fact → Action → ℝ) {C : ℝ}
    (bounded : ∀ state ∈ prior.support, ∀ action, |utility (fact state) action| ≤ C) :
    (∀ source : Signal → PMF Action, IsOptimal prior observe fact utility source →
      ∃ target : State → PMF Action, IsOptimal prior id fact utility target ∧
        responseLaw prior id fact target = responseLaw prior observe fact source) ↔
      HasCommonMaximizer prior observe (fun state => utility (fact state)) := by
  constructor
  · intro preserves
    obtain ⟨source, optimal⟩ := exists_optimal prior observe fact utility bounded
    exact (exists_optimal_lift_iff_commonMaximizer prior observe fact utility bounded).mp
      ⟨source, (optimal_match_iff_lift prior observe fact utility source).mp (preserves source optimal)⟩
  · intro common source sourceOptimal
    obtain ⟨witness, witnessOptimal⟩ :=
      (exists_optimal_lift_iff_commonMaximizer prior observe fact utility bounded).mpr common
    exact (optimal_match_iff_lift prior observe fact utility source).mpr
      (isOptimal_lift_of_optimal_witness prior observe fact utility witness witnessOptimal source sourceOptimal)

/-- Reporting utilities already detect every supported fact collision. With a finite
reporting menu, preserving all utilities' coarse optimal laws is equivalent to fact recovery.
The prior support, state and observation carriers need not be finite. -/
theorem all_utilities_optimal_laws_iff_determines [Finite Fact]
    (prior : PMF State) (observe : State → Signal) (fact : State → Fact) :
    (∀ utility : Fact → Fact → ℝ, ∀ source : Signal → PMF Fact,
      IsOptimal prior observe fact utility source →
        ∃ target : State → PMF Fact, IsOptimal prior id fact utility target ∧
          responseLaw prior id fact target = responseLaw prior observe fact source) ↔
      Determines prior observe fact := by
  classical
  let _ : Nonempty Fact := ⟨fact prior.support_nonempty.choose⟩
  constructor
  · intro preserves
    let utility : Fact → Fact → ℝ := fun actual report => if actual = report then 1 else 0
    have bounded : ∀ state ∈ prior.support, ∀ action, |utility (fact state) action| ≤ 1 := by
      intro state _ action
      simp only [utility]
      split <;> norm_num
    have common := (preserves_fixed_payoff_iff_commonMaximizer prior observe fact utility bounded).mp
      (preserves utility)
    intro first second same
    have observed : observe first.1 ∈ (prior.map observe).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨first.1, first.2, rfl⟩
    obtain ⟨action, maximal⟩ := common (observe first.1) observed
    have identifies (state : State) (supported : state ∈ prior.support)
        (sameSignal : observe state = observe first.1) : fact state = action := by
      have bound := maximal state supported sameSignal (fact state)
      by_contra different
      simp only [utility, ite_eq_left rfl, ite_eq_right different] at bound
      norm_num at bound
    exact (identifies first.1 first.2 rfl).trans (identifies second.1 second.2 same.symm).symm
  · intro determines utility source optimal
    exact ⟨fun state => source (observe state),
      isOptimal_lift prior observe fact determines utility source optimal, rfl⟩

end GameTheory.DecisionExperiment
