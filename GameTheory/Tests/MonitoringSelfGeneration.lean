/-
# APS self-generation witness

Perfect public action observation supports cooperation in a two-player
Prisoner's Dilemma by switching to the stage-Nash punishment payoff after any
deviation signal.  The two-payoff set is self-generating at discount `1/2`;
the singleton cooperation payoff is not enforceable with a constant
continuation.  The generic construction therefore yields a perfect public
equilibrium delivering the cooperative payoff.
-/

import GameTheory.Repeated.MonitoringSelfGeneration

noncomputable section

namespace GameTheory.Tests.MonitoringSelfGeneration

open GameTheory GameTheory.Math.Probability
open UtilityGame.PublicMonitoring.SelfGenerating

abbrev Player := Bool
abbrev ActionProfile := Player → Bool

@[reducible]
def signature : GameSignature Player where
  Strategy _ := Bool
  Outcome := ActionProfile

@[reducible]
def form : GameForm Player where
  sig := signature
  play profile := FinDist.pure profile

def stageUtility (profile : ActionProfile) (who : Player) : ℝ :=
  match profile false, profile true, who with
  | false, false, _ => 3
  | true, true, _ => 1
  | true, false, false => 4
  | true, false, true => 0
  | false, true, false => 0
  | false, true, true => 4

@[reducible]
def game : UtilityGame Player where
  form := form
  utility := stageUtility

def cooperate : Profile signature := fun _ => false
def punish : Profile signature := fun _ => true

def cooperativePayoff : Player → ℝ := fun _ => 3
def punishmentPayoff : Player → ℝ := fun _ => 1

@[simp]
theorem stageUtility_cooperate (who : Player) :
    stageUtility cooperate who = 3 := by
  cases who <;> rfl

@[simp]
theorem stageUtility_punish (who : Player) :
    stageUtility punish who = 1 := by
  cases who <;> rfl

theorem cooperate_update_true_ne (who : Player) :
    Profile.update cooperate who true ≠ cooperate := by
  intro hequal
  have := congrFun hequal who
  simp [cooperate] at this

theorem cooperate_update_false (who : Player) :
    Profile.update cooperate who false = cooperate := by
  simpa [cooperate] using Profile.update_eq_self cooperate who

@[reducible]
def monitoring : game.PublicMonitoring where
  Signal := ActionProfile
  signalLaw profile := FinDist.pure profile

def rewardOrPunish : monitoring.ContinuationAssignment :=
  fun signal => if signal = cooperate then cooperativePayoff
    else punishmentPayoff

def payoffSet : Set (Player → ℝ) :=
  {cooperativePayoff, punishmentPayoff}

theorem stagePayoff_eq (profile : Profile signature) (who : Player) :
    game.stagePayoff profile who = stageUtility profile who := by
  simp [UtilityGame.stagePayoff, game, form]

theorem punish_isNash :
    IsNash form (euPreference stageUtility) punish := by
  rw [isNash_iff]
  intro who action
  cases who <;> cases action <;>
    norm_num [euPreference_apply, form, punish, stageUtility]

theorem cooperate_not_isNash :
    ¬ IsNash form (euPreference stageUtility) cooperate := by
  intro hnash
  rw [isNash_iff] at hnash
  have hdeviation := hnash false true
  norm_num [euPreference_apply, form, cooperate, stageUtility] at hdeviation

/-- The tempting stationary-cooperation decomposition with a constant
cooperative continuation is rejected: cooperation is not stage Nash. -/
theorem cooperate_constant_not_enforceable :
    ¬ monitoring.IsEnforceable (1 / 2) cooperate
      (monitoring.constantContinuation cooperativePayoff) := by
  rw [monitoring.isEnforceable_constant_iff_isNash (by norm_num)]
  exact cooperate_not_isNash

theorem rewardOrPunish_mem (signal : monitoring.Signal) :
    rewardOrPunish signal ∈ payoffSet := by
  by_cases hsignal : signal = cooperate
  · simp [rewardOrPunish, payoffSet, hsignal]
  · simp [rewardOrPunish, payoffSet, hsignal]

theorem cooperate_promiseKeeping :
    monitoring.IsPromiseKeeping (1 / 2) cooperativePayoff
      cooperate rewardOrPunish := by
  funext who
  cases who <;>
    norm_num [UtilityGame.PublicMonitoring.IsPromiseKeeping,
      UtilityGame.PublicMonitoring.decomposedPayoff,
      rewardOrPunish, cooperativePayoff, punishmentPayoff,
      monitoring, cooperate, stagePayoff_eq, stageUtility_cooperate]

/-- A unilateral defection earns four now but selects punishment value one;
at discount one half this is no better than cooperation value three. -/
theorem cooperate_enforceable :
    monitoring.IsEnforceable (1 / 2) cooperate rewardOrPunish := by
  have hfalse := cooperate_update_true_ne false
  have htrue := cooperate_update_true_ne true
  intro who action
  cases who <;> cases action <;>
    norm_num [UtilityGame.PublicMonitoring.decomposedDeviationPayoff,
      UtilityGame.PublicMonitoring.decomposedPayoff,
      rewardOrPunish, cooperativePayoff, punishmentPayoff,
      monitoring, cooperate, stagePayoff_eq, stageUtility,
      cooperate_update_false, hfalse, htrue]

theorem punish_promiseKeeping :
    monitoring.IsPromiseKeeping (1 / 2) punishmentPayoff punish
      (monitoring.constantContinuation punishmentPayoff) := by
  funext who
  cases who <;>
    norm_num [UtilityGame.PublicMonitoring.IsPromiseKeeping,
      punishmentPayoff, punish, stagePayoff_eq, stageUtility_punish]

theorem punish_enforceable :
    monitoring.IsEnforceable (1 / 2) punish
      (monitoring.constantContinuation punishmentPayoff) :=
  (monitoring.isEnforceable_constant_iff_isNash (by norm_num)
    punish punishmentPayoff).2 punish_isNash

/-- The cooperative and punishment promises form a genuinely two-state
self-generating set. -/
theorem payoffSet_selfGenerating :
    monitoring.SelfGenerating (1 / 2) payoffSet := by
  intro payoff hpayoff
  simp only [payoffSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hpayoff
  rcases hpayoff with rfl | rfl
  · exact ⟨cooperate, rewardOrPunish, rewardOrPunish_mem,
      cooperate_promiseKeeping, cooperate_enforceable⟩
  · refine ⟨punish, monitoring.constantContinuation punishmentPayoff,
      ?_, punish_promiseKeeping, punish_enforceable⟩
    intro signal
    simp [payoffSet]

theorem payoffSet_bounded :
    UtilityGame.PublicMonitoring.IsBoundedPayoffSet payoffSet := by
  intro who
  refine ⟨3, ?_⟩
  intro payoff hpayoff
  simp only [payoffSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hpayoff
  rcases hpayoff with rfl | rfl <;>
    cases who <;> norm_num [cooperativePayoff, punishmentPayoff]

theorem stagePayoff_bounded :
    ∀ who : Player, ∃ bound : ℝ,
      ∀ profile : Profile signature,
        |game.stagePayoff profile who| ≤ bound := by
  intro who
  refine ⟨4, ?_⟩
  intro profile
  rw [stagePayoff_eq]
  cases hfalse : profile false <;>
    cases htrue : profile true <;>
      cases who <;> norm_num [stageUtility, hfalse, htrue]

/-- The general self-generation theorem produces a PPE payoff, rather than
stopping at an algebraic decomposition certificate. -/
theorem cooperativePayoff_mem_perfectPublicEquilibriumPayoffs :
    cooperativePayoff ∈
      monitoring.perfectPublicEquilibriumPayoffs (1 / 2) := by
  apply (selfGenerating_subset_perfectPublicEquilibriumPayoffs
      monitoring (by norm_num) (by norm_num) stagePayoff_bounded
      payoffSet_bounded payoffSet_selfGenerating)
  simp [payoffSet]

end GameTheory.Tests.MonitoringSelfGeneration
