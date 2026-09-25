/-
EXP-130: an infinite-prior Bayesian equilibrium consumer.

The geometric private type is unbounded. Every contingent Boolean deviation
has an integrable whole outcome law, while constant accepting play earns the
maximal bounded action bonus at each type.
-/

import GameTheory.Core.BayesianEquilibrium
import GameTheory.Experimental.PostArchitecture.PMFStaticGate

noncomputable section

namespace GameTheory.Experimental.PMFBayesianGate

open GameTheory GameTheory.Math.Probability
open GameTheory.Experimental.PMFRestoration
open GameTheory.Experimental.PMFStaticGate

def typeProfile (n : ℕ) : Unit → ℕ := fun _ => n

theorem typeProfile_injective : Function.Injective typeProfile := by
  intro n m h
  exact congrFun h ()

def prior : PMF (Unit → ℕ) :=
  geometric.map typeProfile

theorem prior_infinite_support : prior.support.Infinite := by
  apply (Set.infinite_range_of_injective typeProfile_injective).mono
  rintro _ ⟨n, rfl⟩
  rw [prior, PMF.mem_support_map_iff]
  exact ⟨n, (geometric_positive n).ne', rfl⟩

@[reducible]
def game : BayesianGame Unit where
  Ty _ := ℕ
  Act _ := Bool
  prior := prior
  payoff types actions _ :=
    (types () : ℝ) + 1 + if actions () then 1 else 0

def alwaysAccept : Profile game.signature := fun _ _ => true

theorem accepting_bonus (n : ℕ) :
    game.payoff (typeProfile n) (fun _ => true) () =
      game.payoff (typeProfile n) (fun _ => false) () + 1 := by
  simp [typeProfile]

theorem game_utility_unbounded :
    ¬ ∃ C : ℝ, ∀ outcome : game.signature.Outcome,
      |game.utility outcome ()| ≤ C := by
  rintro ⟨C, hC⟩
  apply linearUtility_unbounded
  refine ⟨C, ?_⟩
  intro n
  have h := hC (typeProfile n, fun _ => false)
  simpa [linearUtility, BayesianGame.utility, game, typeProfile] using h

/-- The geometric base plus any Boolean bonus remains integrable. -/
theorem plan_integrable (plan : Profile game.signature) (who : Unit) :
    UtilityIntegrable game.utility who (game.toForm.play plan) := by
  cases who
  have hlinear : PayoffIntegrable geometric
      (fun n => (n : ℝ) + 1) :=
    linearUtility_integrable_geometric
  have hbonus : PayoffIntegrable geometric
      (fun n => if plan () n then (1 : ℝ) else 0) :=
    payoffIntegrable_of_bounded geometric _ (C := 1) (by
      intro n
      split <;> norm_num)
  have hsum : PayoffIntegrable geometric
      (fun n => ((n : ℝ) + 1) + if plan () n then 1 else 0) :=
    payoffIntegrable_add hlinear hbonus
  have hsource : PayoffIntegrable geometric
      ((game.planPayoff () plan) ∘ typeProfile) :=
    payoffIntegrable_congr_on_support (fun n _ => by
      simp [BayesianGame.planPayoff, BayesianGame.actionsOf,
        game, typeProfile]
      rfl) hsum
  have hprior : PayoffIntegrable prior (game.planPayoff () plan) :=
    (payoffIntegrable_map_iff typeProfile geometric
      (game.planPayoff () plan)).mpr hsource
  exact (game.planPayoff_integrable_iff () plan).mpr hprior

theorem whole_deviation_integrable
    (who : Unit) (deviation : game.Ty who → game.Act who) :
    UtilityIntegrable game.utility who
      (game.toForm.play (Profile.update alwaysAccept who deviation)) :=
  plan_integrable _ who

theorem alwaysAccept_isNash :
    IsNash game.toForm (euPreference game.utility) alwaysAccept := by
  rw [isNash_iff]
  intro who replacement
  let deviated := Profile.update alwaysAccept who replacement
  have hbase := plan_integrable alwaysAccept who
  have hdev := plan_integrable deviated who
  apply (euPreference_iff game.utility who
    (game.toForm.play alwaysAccept) (game.toForm.play deviated)
    hbase hdev).2
  rw [game.expectedUtility_eq_prior who alwaysAccept hbase,
    game.expectedUtility_eq_prior who deviated hdev]
  apply expect_mono
  intro types _
  cases who
  simp [BayesianGame.planPayoff, BayesianGame.actionsOf,
    deviated, game, alwaysAccept]
  split <;> norm_num

/-- The general interim theorem is used with arbitrary Nat-indexed plans. -/
theorem alwaysAccept_interim_optimal :
    ∀ (who : Unit) (ownType : game.Ty who) (respond : game.Act who),
      game.interimValueOfDeviation who ownType alwaysAccept respond
        (game.singleTypeDeviation alwaysAccept who ownType respond) (by
          simp [BayesianGame.singleTypeDeviation])
        (whole_deviation_integrable who
          (game.singleTypeDeviation alwaysAccept who ownType respond)) ≤
      game.interimValueOfDeviation who ownType alwaysAccept
        (alwaysAccept who ownType) (fun t => alwaysAccept who t) rfl
        (by simpa only [Profile.update_eq_self] using
          whole_deviation_integrable who (alwaysAccept who)) :=
  (game.isNash_iff_interim alwaysAccept whole_deviation_integrable).1
    alwaysAccept_isNash

/-- Conditioning on an observed type can integrate a payoff whose whole-prior
expectation does not exist. -/
def zeroTypeEvent : Set (Unit → ℕ) := {types | types () = 0}

theorem zeroTypeEvent_positive :
    ∃ types ∈ zeroTypeEvent, types ∈ prior.support := by
  refine ⟨typeProfile 0, rfl, ?_⟩
  rw [prior, PMF.mem_support_map_iff]
  exact ⟨0, (geometric_positive 0).ne', rfl⟩

theorem exploding_prior_not_integrable :
    ¬ PayoffIntegrable prior (fun types => exploding (types ())) := by
  intro hprior
  have hsource :
      PayoffIntegrable geometric
        ((fun types : Unit → ℕ => exploding (types ())) ∘ typeProfile) :=
    (payoffIntegrable_map_iff typeProfile geometric
      (fun types : Unit → ℕ => exploding (types ()))).mp hprior
  apply explodingUtility_not_integrable
  simpa [UtilityIntegrable, explodingUtility, typeProfile,
    Function.comp_def] using hsource

theorem exploding_zero_type_integrable :
    PayoffIntegrable (prior.filter zeroTypeEvent zeroTypeEvent_positive)
      (fun types => exploding (types ())) := by
  have hconst :
      PayoffIntegrable (prior.filter zeroTypeEvent zeroTypeEvent_positive)
        (fun _ => exploding 0) :=
    payoffIntegrable_constant _ _
  apply payoffIntegrable_congr_on_support _ hconst
  intro types htypes
  have hzero : types () = 0 := by
    have hmem := htypes
    rw [PMF.mem_support_filter_iff] at hmem
    exact hmem.1
  simp [hzero]

theorem exploding_zero_type_value :
    expect (prior.filter zeroTypeEvent zeroTypeEvent_positive)
        (fun types => exploding (types ())) exploding_zero_type_integrable =
      exploding 0 := by
  have hconst :
      PayoffIntegrable (prior.filter zeroTypeEvent zeroTypeEvent_positive)
        (fun _ => exploding 0) :=
    payoffIntegrable_constant _ _
  calc
    _ = expect (prior.filter zeroTypeEvent zeroTypeEvent_positive)
        (fun _ => exploding 0) hconst := by
          apply expect_congr_on_support
          intro types htypes
          have hzero : types () = 0 := by
            have hmem := htypes
            rw [PMF.mem_support_filter_iff] at hmem
            exact hmem.1
          simp [hzero]
    _ = exploding 0 := expect_constant _ _ _

@[reducible]
def explodingGame : BayesianGame Unit where
  Ty _ := ℕ
  Act _ := Bool
  prior := prior
  payoff types _ _ := exploding (types ())

def explodingPlan : Profile explodingGame.signature := fun _ _ => true

theorem exploding_plan_not_integrable :
    ¬ UtilityIntegrable explodingGame.utility ()
      (explodingGame.toForm.play explodingPlan) := by
  intro hplan
  have hprior := explodingGame.planPayoff_integrable () explodingPlan hplan
  apply exploding_prior_not_integrable
  exact payoffIntegrable_congr_on_support
    (fun types _ => by
      simp [BayesianGame.planPayoff]) hprior

theorem exploding_zero_indicator_integrable :
    PayoffIntegrable prior
      (zeroTypeEvent.indicator (fun types => exploding (types ()))) :=
  (payoffIntegrable_filter_iff prior zeroTypeEvent zeroTypeEvent_positive
    (fun types => exploding (types ()))).mp exploding_zero_type_integrable

theorem exploding_interimPayoff_integrable :
    PayoffIntegrable explodingGame.prior
      (explodingGame.interimPayoff () 0 explodingPlan true) := by
  have hpoint : ∀ types : Unit → ℕ,
      zeroTypeEvent.indicator (fun types => exploding (types ())) types =
        explodingGame.interimPayoff () 0 explodingPlan true types := by
    intro types
    by_cases ht : types () = 0
    · simp [zeroTypeEvent, BayesianGame.interimPayoff,
        explodingGame, ht]
    · simp [zeroTypeEvent, BayesianGame.interimPayoff,
        explodingGame, ht]
  exact payoffIntegrable_congr_on_support
    (fun types _ => hpoint types) exploding_zero_indicator_integrable

theorem exploding_interimValue_nonnegative :
    0 ≤ explodingGame.interimValue () 0 explodingPlan true
      exploding_interimPayoff_integrable := by
  have hzero : PayoffIntegrable prior (fun _ : Unit → ℕ => (0 : ℝ)) :=
    payoffIntegrable_constant prior 0
  have hle := expect_mono
    (μ := prior)
    (f := fun _ : Unit → ℕ => (0 : ℝ))
    (g := explodingGame.interimPayoff () 0 explodingPlan true)
    (by
      intro types _
      by_cases ht : types () = 0
      · simp [BayesianGame.interimPayoff, explodingGame, exploding, ht]
      · simp [BayesianGame.interimPayoff, explodingGame, ht])
    hzero exploding_interimPayoff_integrable
  rw [expect_constant prior 0 hzero] at hle
  exact hle

end GameTheory.Experimental.PMFBayesianGate
