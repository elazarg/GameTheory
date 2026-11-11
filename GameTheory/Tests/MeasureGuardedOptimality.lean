module

/-
# Guarded choice of measures

Evaluation-domain membership and which alternatives are offered are independent
decisions. Filtering deviations by integrability retains the incumbent guard;
requiring every offered deviation to be integrable is a stronger contract.
Totalized Bochner integrals alone do not enforce either contract.
-/

public import GameTheory.Math.GuardedOptimality
public import GameTheory.Math.Probability.Measure
public import GameTheory.Tests.InfiniteExpectation

@[expose] public section

noncomputable section

namespace GameTheory.Tests.MeasureGuardedOptimality

open GameTheory.Math GameTheory.Math.Probability MeasureTheory

/-- The guarded predicate specializes directly to arbitrary measure-valued
choices, without a common probability carrier or a new decision record. -/
theorem filtered_measure_optimal_iff
    {Action Outcome : Type*} [MeasurableSpace Outcome]
    (laws : Action → Measure Outcome) (payoff : Outcome → ℝ)
    (offered : Set Action) (chosen : Action) :
    IsOptimalOn (fun action => Integrable payoff (laws action))
      (fun preferred alternative =>
        (∫ value, payoff value ∂laws alternative) ≤ ∫ value, payoff value ∂laws preferred)
      {action | action ∈ offered ∧ Integrable payoff (laws action)} chosen ↔
      Integrable payoff (laws chosen) ∧
        ∀ alternative ∈ offered, Integrable payoff (laws alternative) →
          (∫ value, payoff value ∂laws alternative) ≤ ∫ value, payoff value ∂laws chosen := by
  constructor
  · rintro ⟨incumbent, _, comparisons⟩
    exact ⟨incumbent, fun alternative available defined =>
      comparisons alternative ⟨available, defined⟩⟩
  · rintro ⟨incumbent, comparisons⟩
    exact ⟨incumbent, fun _ available => available.2,
      fun alternative available => comparisons alternative available.1 available.2⟩

local instance : MeasurableSpace (Option ℕ) := ⊤

def laws (action : Bool) : Measure (Option ℕ) :=
  if action then (PMF.pure none).toMeasure
  else (InfiniteExpectation.halving.map some).toMeasure

instance laws_isProbabilityMeasure (action : Bool) : IsProbabilityMeasure (laws action) := by
  cases action <;> dsimp [laws] <;> infer_instance

def payoff (outcome : Option ℕ) : ℝ := InfiniteExpectation.utility outcome ()

def admissible (action : Bool) : Prop := Integrable payoff (laws action)

def score (action : Bool) : ℝ := ∫ value, payoff value ∂laws action

theorem home_admissible : admissible true := by
  apply (payoffIntegrable_iff_integrable (PMF.pure none) payoff).mp
  exact payoffIntegrable_pure _ _

theorem gamble_not_admissible : ¬ admissible false := by
  intro defined
  apply InfiniteExpectation.gamble_not_integrable
  exact (payoffIntegrable_iff_integrable (InfiniteExpectation.halving.map some) payoff).mpr
    defined

theorem home_score : score true = 0 := by
  simp [score, laws, payoff, PMF.toMeasure_pure, InfiniteExpectation.utility]

theorem gamble_score : score false = 0 :=
  integral_undef gamble_not_admissible

/-- The invalid gamble even maximizes the totalized integral on the full menu. -/
theorem raw_integral_gamble_maximizes : IsMaxOn score Set.univ false := by
  intro alternative _
  cases alternative <;> simp [gamble_score, home_score]

/-- Integrable-deviation filtering keeps the valid incumbent and omits the
invalid alternative, exactly as in the measure-based equilibrium contract. -/
theorem filtered_home_optimal :
    IsOptimalOn admissible (fun first second => score second ≤ score first)
      {action | admissible action} true := by
  refine ⟨home_admissible, fun _ defined => defined, fun alternative _ => ?_⟩
  cases alternative <;> simp [gamble_score, home_score]

/-- Filtering alternatives still cannot legitimize an invalid incumbent. -/
theorem filtered_gamble_not_optimal :
    ¬ IsOptimalOn admissible (fun first second => score second ≤ score first)
      {action | admissible action} false :=
  fun optimal => gamble_not_admissible optimal.1

/-- Keeping the original full menu instead requires all alternatives to lie
in the evaluation domain, so it is a different mathematical contract. -/
theorem full_menu_home_not_optimal :
    ¬ IsOptimalOn admissible (fun first second => score second ≤ score first)
      Set.univ true :=
  fun optimal => gamble_not_admissible (optimal.2.1 false (Set.mem_univ _))

end GameTheory.Tests.MeasureGuardedOptimality
